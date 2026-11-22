package gezi.rewritetrace

import gezi.frontend.Defunctionalization
import gezi.frontend.TermMap
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Instruction
import gezi.ir.{Apply, Choice, Parallel, Slot, Thunk}
import gezi.locations.BinderOrigin
import gezi.locations.MadeBy
import gezi.locations.SourceMap
import gezi.ir.TailRecFolds
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** Where the places of each term of a trace come from, carried from the
  * start's source map (`TraceStart.readLocated`) through the steps, and what a person reads
  * of each step: the rule it applies and where.
  *
  * A step replaces the subterm at its position. Every place outside that
  * position keeps its map: a location locates a place's own layer, the places
  * below having their own (`SourceMap`), and a place above the position
  * keeps its layer, a thunk's code and holes included, while the step
  * changes what is below it, but for the maps of a replaced filling's
  * occurrences that its code's map holds (`replacedAt`). Inside the replacement, a place that the step's
  * provenance takes from the replaced subterm (a variable's subtree, moved
  * from a position of the replaced subterm to a position of the
  * replacement) keeps the map the replaced subterm had there; every other
  * place of the replacement is one the step made, and is unlocated, so that
  * no place is made up for it.
  *
  * The binders of a thunk the step made take origins: a thunk whose code the trace has
  * met keeps that code's map and the origins of its binders, counted from
  * its last hole, since a β step fills the first ones (`CodeOrigins`); a
  * `Rewrite`'s replacement takes its map from the side its equation states
  * (`StatedReplacement`), whose codes are the replaced term's or the
  * lemma's, carried onto the replay's spelling of it
  * (`Defunctionalization.relocatedMap`) with the binder origins only; the
  * abstraction rule's thunk takes the binders of the thunk it opened and
  * the map its steps carry in the body; any other binder is `Made` by the
  * kind of the step.
  */
object TraceSourceMaps:

  /** The source map of the start and of the term after each step, in order. */
  def carried(startMap: SourceMap, steps: Vector[ReplayedStep]): Vector[SourceMap] =
    carriedLazily(startMap, steps).toVector

  /** `carried`, each map made the first time it is read, after the maps
    * before it, and kept: a player reads the maps of the steps it shows
    * only.
    */
  def carriedLazily(startMap: SourceMap, steps: Vector[ReplayedStep]): LazyList[SourceMap] =
    startMap #:: steps.headOption.fold(LazyList.empty[SourceMap])(first =>
      val met = indexed(first.before, startMap, Map.empty, Set.empty).result
      steps.to(LazyList).scanLeft((startMap, met)) { case ((map, known), step) => stepped(map, known, step) }.drop(1).map(_._1)
    )

  /** The map of each thunk's code met so far, and its holes and the origins
    * of its binders, both by their positions counted from its last hole: a
    * thunk of the code takes a binder's origins only where its hole at that
    * position is the same, since one code is the body of thunks whose holes
    * differ (`λz. x g` and `λa. a g`, of one code with an ignored hole and a
    * bound one).
    */
  private final case class CodeOrigins(codeMap: SourceMap, holesFromLast: Vector[Hole], fromLast: Vector[Set[BinderOrigin]])

  /** The maps of the start and of each step, each with the codes met up to it. */
  private def carriedFrom(
      startMap: SourceMap,
      met: Map[Code, Vector[CodeOrigins]],
      steps: Vector[ReplayedStep]
  ): Vector[(SourceMap, Map[Code, Vector[CodeOrigins]])] =
    steps.scanLeft((startMap, met)) { case ((map, known), step) => stepped(map, known, step) }

  /** The map of the term after the step, from the map of the term before it,
    * and the codes met once the step is made.
    */
  private def stepped(map: SourceMap, known: Map[Code, Vector[CodeOrigins]], step: ReplayedStep): (SourceMap, Map[Code, Vector[CodeOrigins]]) =
    val replacedMap = at(map, step.before, step.command.at)
    val copies = step.provenance.flatMap(found =>
      found.before.headOption.toVector.flatMap(from =>
        val copied = at(replacedMap, step.replaced, from)
        found.after.map(to => (to, copied))
      )
    ).toMap
    val replacementMap = step.command match
      case TraceCommand.Rewrite(reason, _, _, _) =>
        val by = reason match
          case ProvedReason.Lemma(_)    => MadeBy.Lemma
          case ProvedReason.Equation(_) => MadeBy.Equation
          case ProvedReason.Fill(_)     => MadeBy.Beta
          case ProvedReason.Body(_)     => MadeBy.Beta
          case ProvedReason.Eta(_)      => MadeBy.Eta
        val stated = step.stated.getOrElse(throw IllegalStateException(s"a rewrite replayed with no stated side: ${step.command}"))
        val variableMaps = step.provenance.flatMap(found =>
          found.before.headOption.map(from => (found.variable, at(replacedMap, step.replaced, from)))
        ).toMap
        val statedMap = statedSideMap(stated.side, stated.bound, variableMaps, known, by).result
        val instance = stated.instance
        if instance eq step.replacement then statedMap
        else
          // TODO (https://github.com/Atry/private-overlay/issues/1689, D2, and
          // #1504 step 8): the places of the replay's spelling keep only
          // their binder origins, not the locations of the stated side's
          // codes, since a respelled thunk is another layer than the code at
          // that location; the backend's source positions need them.
          withoutLocationsCopied(Defunctionalization.relocatedMap(instance, statedMap, step.replacement), step.replacement, Vector.empty, copies).result
      case TraceCommand.Abstraction(_, count, _) => abstractionMap(step, replacedMap, count, known)
      case TraceCommand.Native(_, _)              => built(step.replacement, Vector.empty, copies, known, MadeBy.Native).result
      case TraceCommand.Convert(conversion, _, direction, _) =>
        // FIXME: a conversion's replacement takes origins from the codes met https://github.com/Atry/private-overlay/issues/2051
        // only, so a binder that the conversion's pattern carries from the
        // replaced subterm loses the name its text wrote when the replay
        // respells its thunk: measured on the higher-order snapshot
        // (`TraceSourceMapsLawTest`, trace-source-maps/higher-order-names.txt,
        // sample 0), where the source's `x` of `λx z. x g` is printed
        // `abstracted` after the β conversion backward at the function,
        // which writes the thunk's body anew. Candidate fix: carry the replaced
        // instance's thunk origins through the pattern's thunks into
        // `Conversions.normalForm` and back, as a `Rewrite` carries its stated
        // side's.
        // A higher-order conversion forward contracts its pattern's instance
        // to the normal form; a root reverse β forward builds the redex.
        val by = (conversion, direction) match
          case (Conversion.HigherOrder(_, _, _), RewriteDirection.Forward)  => MadeBy.Beta
          case (Conversion.HigherOrder(_, _, _), RewriteDirection.Backward) => MadeBy.ReverseBeta
          case (Conversion.RootReverseBeta(_), RewriteDirection.Forward)    => MadeBy.ReverseBeta
          case (Conversion.RootReverseBeta(_), RewriteDirection.Backward)   => MadeBy.Beta
        built(step.replacement, Vector.empty, copies, known, by).result
    // A subtree the step moves, kept with the map the replaced subterm had
    // there, was walked with that map when that map was made.
    val moved = step.provenance.flatMap(found =>
      found.before.headOption.toVector.flatMap(from =>
        found.after.filter(to =>
          (Positions.subterm(step.replacement, to) eq Positions.subterm(step.replaced, from)) &&
            (at(replacementMap, step.replacement, to) eq at(replacedMap, step.replaced, from))
        )
      )
    )
    (
      replacedAt(map, step.before, step.command.at, replacementMap),
      indexed(step.replacement, replacementMap, known, moved.map(path(step.replacement, _)).toSet).result
    )

  /** The map of the abstraction rule's thunk: the body opened at
    * eigenvariables takes the map of the thunk it opened (`openedMap`), its
    * steps carry that map, and the thunk written back over the body takes
    * the body's map under binders whose origins are those of the thunk
    * opened, or `Made` by the abstraction rule where it has none. A step
    * with no steps in the body writes back the thunk it opened.
    */
  private def abstractionMap(step: ReplayedStep, replacedMap: SourceMap, count: Int, known: Map[Code, Vector[CodeOrigins]]): SourceMap =
    step.inner.headOption match
      case None => withoutLocations(Defunctionalization.relocatedMap(step.replaced, replacedMap, step.replacement)).result
      case Some(first) =>
        val opened = openedMap(step.replaced, replacedMap, count)
        val (bodyMap, _) = carriedFrom(opened, known, step.inner).last
        val body = step.inner.last.after
        val origins = Vector.tabulate(count)(position =>
          replacedMap.binders.lift(position).filter(_.nonEmpty).getOrElse(Set(BinderOrigin.Made(MadeBy.Eigenvariable)))
        )
        val termMap = origins.foldRight(Defunctionalization.readbackMap(body, bodyMap))((binder, inner) =>
          TermMap.Abstraction(Set.empty, binder, inner)
        )
        withoutLocations(Defunctionalization.mapOfReadback(step.replacement, termMap)).result

  /** The map of a thunk opened at `count` eigenvariables as
    * `Conversions.opened` opens it: the thunk of the holes left, its fillings'
    * maps with an unlocated place for each bound hole's leaf, or with no hole
    * left the code read at the fillings.
    */
  private def openedMap(thunk: Instruction, map: SourceMap, count: Int): SourceMap = thunk match
    case Instruction.Thunk(code, holes, fillings) =>
      val (rest, filledMaps) = holes.take(count).foldLeft((holes, map.children.padTo(fillings.size, SourceMap.unlocated))) {
        case ((remaining, current), _) =>
          remaining match
            case Hole.Bound(slot) +: others =>
              (others, current.patch(Defunctionalization.fillingPosition(others, slot), Vector(SourceMap.unlocated), 0))
            case _ +: others => (others, current)
            case _           => throw IllegalStateException(s"no hole is left to open in $thunk")
      }
      if rest.nonEmpty then SourceMap(Set.empty, map.code, filledMaps, map.binders.drop(count))
      else codeInstanceMap(code, map.code.getOrElse(SourceMap.unlocated), Defunctionalization.slotValues(Vector.empty, Vector.empty, filledMaps)).result
    case other => throw IllegalArgumentException(s"the abstraction rule opens no thunk: $other")

  /** The map of a code read at the slots' maps, as `Statements.codeInstance`
    * reads the code: each layer the code's place, each slot the map of its
    * occurrence where the slot's place holds one, its value's map otherwise,
    * an inner thunk the code's map of it over its fillings read alike.
    */
  private def codeInstanceMap(code: Code, codeMap: SourceMap, slots: Vector[SourceMap]): TailRec[SourceMap] =
    def child(position: Int): SourceMap = codeMap.children.lift(position).getOrElse(SourceMap.unlocated)
    def parts(codes: Vector[Code]): TailRec[Vector[SourceMap]] =
      Statements.traversed(codes.zipWithIndex)((part, position) => tailcall(codeInstanceMap(part, child(position), slots)))
    code.layer match
      case Slot(index)          => done(if codeMap.bare then slots.lift(index).getOrElse(SourceMap.unlocated) else codeMap)
      case Thunk(_, _, fillings) => parts(fillings).map(SourceMap(codeMap.locations, codeMap.code, _, codeMap.binders))
      case Apply(function, argument) => parts(Vector(function, argument)).map(SourceMap(codeMap.locations, None, _, Vector.empty))
      case Choice(left, right)       => parts(Vector(left, right)).map(SourceMap(codeMap.locations, None, _, Vector.empty))
      case Parallel(left, right)     => parts(Vector(left, right)).map(SourceMap(codeMap.locations, None, _, Vector.empty))

  /** The map of a side as its equation states it, under the bindings: a
    * variable the map of the subterm the replaced side had there, or of the
    * bound term as the step made it where the replaced side has none; a
    * stored term as the step made it; a thunk the map of its code as met
    * (`thunkMap`); another layer a place over its parts' maps.
    */
  private def statedSideMap(
      side: StatementTerm,
      bound: Map[String, Instruction],
      variableMaps: Map[String, SourceMap],
      known: Map[Code, Vector[CodeOrigins]],
      by: MadeBy
  ): TailRec[SourceMap] =
    side match
      case StatementTerm.Variable(name) =>
        variableMaps.get(name) match
          case Some(copied) => done(copied)
          case None =>
            tailcall(built(bound.getOrElse(name, throw IllegalStateException(s"the stated side's $name is unbound")), Vector.empty, Map.empty, known, by))
      case StatementTerm.Stored(term) => tailcall(built(term, Vector.empty, Map.empty, known, by))
      case StatementTerm.Layered(layer) =>
        Statements.traversed(layer.children)(child => tailcall(statedSideMap(child, bound, variableMaps, known, by))).map(children =>
          layer match
            case Thunk(code, holes, _) => thunkMap(code, holes, children, known, by)
            case _                     => SourceMap(Set.empty, None, children, Vector.empty)
        )

  /** The map of a thunk of the code and holes over its fillings' maps: the
    * map of the code as met and the origins of its binders, counted from the
    * last hole, `Made` by the step where the code was not met or gives a
    * binder none.
    */
  private def thunkMap(code: Code, holes: Vector[Hole], fillingMaps: Vector[SourceMap], known: Map[Code, Vector[CodeOrigins]], by: MadeBy): SourceMap =
    val met = known.getOrElse(code, Vector.empty)
    val codeMap = met.headOption.fold(madeCodeMap(code, known, by).result)(_.codeMap)
    SourceMap(Set.empty, Some(codeMap), fillingMaps, originsFromLast(met, holes, by))

  /** The origins of the binders of a thunk of the holes, in lambda order:
    * of the first thunk met of the code that agrees with the most of its
    * holes counted from the last (a β step fills the first ones, and a
    * conversion may add one in front), those of the binders where they
    * agree; else `Made` by the step.
    */
  private def originsFromLast(met: Vector[CodeOrigins], holes: Vector[Hole], by: MadeBy): Vector[Set[BinderOrigin]] =
    val holesFromLast = holes.reverse
    def agreeing(origins: CodeOrigins): Int = origins.holesFromLast.zip(holesFromLast).takeWhile(_ == _).size
    val chosen = met.maxByOption(agreeing)
    val agreed = chosen.fold(0)(agreeing)
    Vector.tabulate(holes.size)(position =>
      val fromLast = holes.size - 1 - position
      chosen
        .filter(_ => fromLast < agreed)
        .flatMap(_.fromLast.lift(fromLast))
        .filter(_.nonEmpty)
        .getOrElse(Set(BinderOrigin.Made(by)))
    )

  /** The map of a code the trace has not met: no location, and each inner
    * thunk's binders the origins of its code as met, else `Made` by the step.
    */
  private def madeCodeMap(code: Code, known: Map[Code, Vector[CodeOrigins]], by: MadeBy): TailRec[SourceMap] =
    def parts(codes: Vector[Code]): TailRec[Vector[SourceMap]] =
      Statements.traversed(codes)(part => tailcall(madeCodeMap(part, known, by)))
    code.layer match
      case Slot(_)                    => done(SourceMap.unlocated)
      case Thunk(inner, holes, fillings) =>
        parts(fillings).flatMap(fillingMaps =>
          val met = known.getOrElse(inner, Vector.empty)
          met.headOption.fold(tailcall(madeCodeMap(inner, known, by)))(found => done(found.codeMap)).map(innerMap =>
            SourceMap(Set.empty, Some(innerMap), fillingMaps, originsFromLast(met, holes, by))
          )
        )
      case Apply(function, argument) => parts(Vector(function, argument)).map(SourceMap(Set.empty, None, _, Vector.empty))
      case Choice(left, right)       => parts(Vector(left, right)).map(SourceMap(Set.empty, None, _, Vector.empty))
      case Parallel(left, right)     => parts(Vector(left, right)).map(SourceMap(Set.empty, None, _, Vector.empty))

  /** The codes met: those already met, and each thunk under the term whose
    * code and holes are not, with its map and its binders' origins from the
    * term's map, after those met before of its code; a thunk whose map gives
    * neither, or whose binders have only `Made` origins, is not met. The
    * subterms at the paths `indexedBefore` (`path`'s indices) are not walked:
    * the caller has walked each, with its map, before, and walking a term
    * with its map again adds no code, since the codes met only grow.
    */
  private def indexed(
      term: Instruction,
      map: SourceMap,
      known: Map[Code, Vector[CodeOrigins]],
      indexedBefore: Set[Vector[Int]]
  ): TailRec[Map[Code, Vector[CodeOrigins]]] =
    def entered(code: Code, holes: Vector[Hole], thunkMap: SourceMap, found: Map[Code, Vector[CodeOrigins]]): Map[Code, Vector[CodeOrigins]] =
      // A `Made` origin says which step made that binder, so it is not
      // handed to another thunk of the code; nor are the maps of this
      // thunk's fillings a slot's place may hold (`SourceMap.codeAlone`).
      val written = thunkMap.binders.map(_.filter {
        case BinderOrigin.Made(_) => false
        case _                    => true
      })
      val met = found.getOrElse(code, Vector.empty)
      val nothingWritten = (thunkMap.code.isEmpty && thunkMap.binders.isEmpty) || (written.nonEmpty && written.forall(_.isEmpty))
      if met.exists(_.holesFromLast == holes.reverse) || nothingWritten then found
      else found.updated(code, met :+ CodeOrigins(SourceMap.codeAlone(code, thunkMap.code.getOrElse(SourceMap.unlocated)), holes.reverse, written.reverse))
    def child(at: SourceMap, position: Int): SourceMap = at.children.lift(position).getOrElse(SourceMap.unlocated)
    def codeIndexed(code: Code, codeMap: SourceMap, found: Map[Code, Vector[CodeOrigins]]): TailRec[Map[Code, Vector[CodeOrigins]]] =
      val inner = code.layer match
        case Thunk(innerCode, holes, _) => entered(innerCode, holes, codeMap, found)
        case _                          => found
      val below = code.layer match
        case Thunk(innerCode, _, fillings) => (innerCode, codeMap.code.getOrElse(SourceMap.unlocated)) +: fillings.zipWithIndex.map((filling, position) => (filling, child(codeMap, position)))
        case Apply(function, argument)     => Vector((function, child(codeMap, 0)), (argument, child(codeMap, 1)))
        case Choice(left, right)           => Vector((left, child(codeMap, 0)), (right, child(codeMap, 1)))
        case Parallel(left, right)         => Vector((left, child(codeMap, 0)), (right, child(codeMap, 1)))
        case Slot(_)                       => Vector.empty
      TailRecFolds.folded(below, inner)((current, part) => codeIndexed(part._1, part._2, current))
    def walked(subterm: Instruction, subtermMap: SourceMap, place: Vector[Int], found: Map[Code, Vector[CodeOrigins]]): TailRec[Map[Code, Vector[CodeOrigins]]] =
      if subterm.opaque || indexedBefore.contains(place) then done(found)
      else
        val withCode = subterm match
          case Instruction.Thunk(code, holes, _) =>
            val entry = entered(code, holes, subtermMap, found)
            tailcall(codeIndexed(code, subtermMap.code.getOrElse(SourceMap.unlocated), entry))
          case _ => done(found)
        subterm.layered.children.zipWithIndex.foldLeft(withCode)((before, part) =>
          before.flatMap(current => tailcall(walked(part._1, child(subtermMap, part._2), place :+ part._2, current)))
        )
    walked(term, map, Vector.empty, known)

  /** The map of the term with every location dropped, its binders' origins
    * only, but at each position of `copies` the copied map, with the
    * places above it as many as the term's parts there: `withoutLocations`
    * and then each copy put at its position (`replacedAt`), without walking
    * the maps the copies replace, which are as large as the subtrees a step
    * moves.
    */
  private def withoutLocationsCopied(
      map: SourceMap,
      term: Instruction,
      position: Vector[PositionSegment],
      copies: Map[Vector[PositionSegment], SourceMap]
  ): TailRec[SourceMap] =
    copies.get(position) match
      case Some(copied) => done(copied)
      case None if !copies.keys.exists(_.startsWith(position)) => tailcall(withoutLocations(map))
      case None =>
        val layer = term.layered
        for
          code <- map.code.fold(done(Option.empty[SourceMap]))(codeMap => tailcall(withoutLocations(codeMap)).map(Some(_)))
          children <- Statements.traversed(layer.children.zip(Positions.roles(layer)).zipWithIndex)((part, index) =>
            tailcall(withoutLocationsCopied(map.children.lift(index).getOrElse(SourceMap.unlocated), part._1, position :+ part._2, copies))
          )
        yield SourceMap(Set.empty, code, children, map.binders)

  /** The map with every location dropped: its binders' origins only. */
  private def withoutLocations(map: SourceMap): TailRec[SourceMap] =
    for
      code <- map.code.fold(done(Option.empty[SourceMap]))(codeMap => tailcall(withoutLocations(codeMap)).map(Some(_)))
      children <- Statements.traversed(map.children)(child => tailcall(withoutLocations(child)))
    yield SourceMap(Set.empty, code, children, map.binders)

  /** The map at the position of the term, unlocated where the map does not
    * reach.
    */
  def at(map: SourceMap, term: Instruction, position: Vector[PositionSegment]): SourceMap =
    position
      .foldLeft((map, term)) { case ((current, subterm), segment) =>
        val index = childIndex(subterm, segment)
        (current.children.lift(index).getOrElse(SourceMap.unlocated), Positions.subterm(subterm, Vector(segment)))
      }
      ._1

  /** The indices of `Layer.children` the position goes through in the term:
    * the path the player keys its nodes by.
    */
  def path(term: Instruction, position: Vector[PositionSegment]): Vector[Int] =
    position
      .foldLeft((Vector.empty[Int], term)) { case ((indices, subterm), segment) =>
        (indices :+ childIndex(subterm, segment), Positions.subterm(subterm, Vector(segment)))
      }
      ._1

  /** The subtrees a step moves, each as the path of the node it was in the
    * term before the step and a path of a node it is in the term after it,
    * one pair for each place its provenance puts it (a copied subtree has
    * several): what the player's transition flies from one place to the
    * other. A step with no provenance moves nothing.
    */
  def moves(step: ReplayedStep): Vector[(Vector[Int], Vector[Int])] =
    step.provenance.flatMap(found =>
      found.before.headOption.toVector.flatMap(from =>
        found.after.map(to => (path(step.before, step.command.at ++ from), path(step.after, step.command.at ++ to)))
      )
    )

  /** What a person reads of a command: the rule or the lemma it applies,
    * by its number in the trace, the direction of a proved step, and its
    * position. A lemma's location stays in the trace's LEMMA, for the
    * backends and for finding its proof in Lean, and is not shown
    * in a step's label, which writes no `uri#char=…` either.
    */
  def label(command: TraceCommand): String = labelWith(command, index => s"lemma ${index + 1}")

  /** `label`, each lemma shown by `lemmaShown` of its index in the trace,
    * such as its number with its two sides printed (the player's page).
    */
  def labelWith(command: TraceCommand, lemmaShown: Int => String): String =
    def where(position: Vector[PositionSegment]): String =
      if position.isEmpty then "at the root" else s"at ${position.map(segmentName).mkString(".")}"
    def direction(of: RewriteDirection): String = of match
      case RewriteDirection.Forward  => "forward"
      case RewriteDirection.Backward => "backward"
    command match
      case TraceCommand.Rewrite(reason, position, turned, _) =>
        val rule = reason match
          case ProvedReason.Lemma(index)     => lemmaShown(index)
          case ProvedReason.Equation(number) => s"equation ($number)"
          case ProvedReason.Fill(_)          => "the β rule"
          case ProvedReason.Body(_)          => "the body equation"
          case ProvedReason.Eta(_)           => "the η rule"
        s"$rule, ${direction(turned)}, ${where(position)}"
      case TraceCommand.Convert(conversion, position, turned, _) =>
        val rule = conversion match
          case Conversion.HigherOrder(lemma, _, _) => s"β conversion of ${lemmaShown(lemma)}"
          case Conversion.RootReverseBeta(lemma)  => s"root reverse β of ${lemmaShown(lemma)}"
        s"$rule, ${direction(turned)}, ${where(position)}"
      case TraceCommand.Native(position, _) => s"native value, ${where(position)}"
      case TraceCommand.Abstraction(position, count, commands) =>
        s"the abstraction rule (ξ) over $count binders, ${commands.size} steps in the body, ${where(position)}"

  private def segmentName(segment: PositionSegment): String = segment match
    case PositionSegment.Function       => "function"
    case PositionSegment.Argument       => "argument"
    case PositionSegment.Left           => "left"
    case PositionSegment.Right          => "right"
    case PositionSegment.Filling(index) => s"filling $index"

  private def childIndex(term: Instruction, segment: PositionSegment): Int =
    val index = Positions.roles(term.layered).indexOf(segment)
    require(index >= 0, s"the term $term has no subterm at $segment")
    index

  /** The map of the term at the path of the replacement: the copied map
    * where the provenance gives one, else an unlocated place over the maps
    * of the terms under it, a thunk's binders named as `thunkMap` names them.
    * A trampoline: a replacement is as deep as a term.
    */
  private def built(
      term: Instruction,
      position: Vector[PositionSegment],
      copies: Map[Vector[PositionSegment], SourceMap],
      known: Map[Code, Vector[CodeOrigins]],
      by: MadeBy
  ): TailRec[SourceMap] =
    copies.get(position) match
      case Some(copied) => done(copied)
      case None if term.opaque => done(SourceMap.unlocated)
      case None =>
        val layer = term.layered
        TailRecFolds.folded(layer.children.zip(Positions.roles(layer)).toVector, Vector.empty[SourceMap]) { case (maps, (child, role)) =>
          built(child, position :+ role, copies, known, by).map(maps :+ _)
        }
          .map(children =>
            term match
              case Instruction.Thunk(code, holes, _) => thunkMap(code, holes, children, known, by)
              case _                                 => SourceMap(Set.empty, None, children, Vector.empty)
          )

  /** The map with the map at the position of the term replaced. A thunk
    * above the position whose filling the position goes through keeps its
    * code's map, but not the maps of that filling's occurrences that the
    * code's places of the slots reading it hold (`codeTermOf` of
    * `gezi.frontend.Defunctionalization` reads a filling with such a map):
    * they are maps of the filling replaced, and each of those places reads
    * the filling's own map once they are leaves. Kept, they named the
    * binders of a replacement by the replaced term's, and threw where the
    * replacement has more binders: an inlined occurrence of a filling a
    * `Native` step made with three binders, over one the start wrote twice
    * with two.
    */
  private def replacedAt(map: SourceMap, term: Instruction, position: Vector[PositionSegment], replacement: SourceMap): SourceMap =
    val ancestors = position
      .scanLeft((map, term)) { case ((current, subterm), segment) =>
        val index = childIndex(subterm, segment)
        (current.children.lift(index).getOrElse(SourceMap.unlocated), Positions.subterm(subterm, Vector(segment)))
      }
    position.indices.foldRight(replacement) { (place, inner) =>
      val (ancestor, subterm) = ancestors(place)
      val index = childIndex(subterm, position(place))
      val count = subterm.layered.children.size
      val children = Vector.tabulate(count)(child =>
        if child == index then inner else ancestor.children.lift(child).getOrElse(SourceMap.unlocated)
      )
      val replacedBelow = ancestor.copy(children = children)
      subterm match
        case Instruction.Thunk(code, holes, _) =>
          replacedBelow.copy(code = replacedBelow.code.map(codeMap => occurrencesDropped(code, codeMap, Set(filledSlot(holes, index))).result))
        case _ => replacedBelow
    }

  /** The slot of a thunk of the holes that its filling at the position, from
    * 0, fills: the fillings fill the slots no hole binds, in slot order.
    */
  private def filledSlot(holes: Vector[Hole], filling: Int): Int =
    LazyList.from(0).filterNot(slot => holes.contains(Hole.Bound(slot)))(filling)

  /** The map of the code with the places of the slots `reading` a leaf at
    * their locations, an inner thunk's slots included whose fillings are
    * those slots.
    */
  private def occurrencesDropped(code: Code, map: SourceMap, reading: Set[Int]): TailRec[SourceMap] =
    if map.bare || reading.isEmpty then done(map)
    else
      code.layer match
        case Slot(index)               => done(if reading.contains(index) then SourceMap.leaf(map.locations) else map)
        case Apply(function, argument) => partsDropped(Vector(function, argument), map, reading)
        case Choice(left, right)       => partsDropped(Vector(left, right), map, reading)
        case Parallel(left, right)     => partsDropped(Vector(left, right), map, reading)
        case Thunk(inner, innerHoles, fillings) =>
          val innerReading = fillings.zipWithIndex.collect {
            case (filling, position) if filling.layer match
                  case Slot(slot) => reading.contains(slot)
                  case _          => false
                => filledSlot(innerHoles, position)
          }.toSet
          for
            innerMap <- map.code.fold(done(Option.empty[SourceMap]))(found => tailcall(occurrencesDropped(inner, found, innerReading)).map(Some(_)))
            dropped <- partsDropped(fillings, map, reading)
          yield dropped.copy(code = innerMap)

  /** `occurrencesDropped` on the parts of a code, at the places below its own. */
  private def partsDropped(parts: Vector[Code], map: SourceMap, reading: Set[Int]): TailRec[SourceMap] =
    Statements
      .traversed(parts.zip(map.children))((part, partMap) => tailcall(occurrencesDropped(part, partMap, reading)))
      .map(children => map.copy(children = children ++ map.children.drop(children.size)))
