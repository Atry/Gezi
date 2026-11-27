package gezi.rewritetrace

import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.StorageAccess
import gezi.ir.{Apply, Thunk}
import gezi.ir.{Configured, NativeSpecializer}

/** The kind of a union the e-graph made with no step of an article
  * (`gezi.strategies.GraphProof`, its two FIXMEs). The trace does not
  * depend on a proof, a step with none being marked as an axiom: a β conversion is a `TraceCommand.Convert`, an abstraction a
  * `TraceCommand.Abstraction`.
  */
enum UnprovedKind:
  case Abstraction, BetaConversion

/** The equation a proved step instantiates: a lemma, by its place in the
  * trace's lemmas; a numbered equation of the formal definition; or the
  * defunctionalized β rule, body equation or η rule of a thunk. A step
  * forward finds the thunk in the subterm it replaces; a step backward,
  * whose replaced subterm does not determine it, gives its code and holes
  * (`ThunkShape`). The respelling equation (`Statements.respell`) has no
  * reason: the replay works in a spelling where it is an identity
  * (`ReplaySpelling`).
  */
enum ProvedReason[C <: NativeSpecializer & Singleton]:
  case Lemma(index: Int)
  case Equation(number: Int)
  case Fill(thunk: Option[ThunkShape[C]])
  case Body(thunk: Option[ThunkShape[C]])
  case Eta(thunk: Option[ThunkShape[C]])

/** The code and holes of the thunk of a step backward of the β rule, the
  * body equation or the η rule, which are all of the thunk its equation
  * reads (`Statements.fill`, `body`, `eta`), its fillings being the
  * equation's variables: the code of the thunk `codeOf` gives, and the
  * holes. The step's own thunk is often no node of the proof (the β rule of
  * a function of several arguments fills one hole at a time, and the
  * e-graph makes no node for the thunks between), while a thunk of the proof
  * has its code.
  */
final case class ThunkShape[C <: NativeSpecializer & Singleton](codeOf: Given[C], holes: Vector[Hole])

/** The term a value of a trace starts from: the term before a round, by
  * the round's place among the trace's rounds, or an earlier value, by its
  * place among the trace's values.
  */
enum ValueSource:
  case RoundStart(round: Int)
  case Value(index: Int)

/** A term a command uses that the subterm it replaces does not give: a
  * variable of the replacement's side alone, or the thunk of a step backward
  * of the β rule, the body equation or the η rule.
  * Such a term is the term of a node of the proof, which the proof's input
  * holds or one of its unions made, and the trace names it among its values
  * (`TraceValue`) by its place. Nothing a replay computes is written: a
  * binding written in a `Rewrite` or a `Convert` is what a trace avoids.
  *
  * FIXME (2026-11-18): `Written` is a term of the IR in the trace, for a term https://github.com/Atry/private-overlay/issues/1982
  * the trace finds no origin of (`gezi.proofs.RewriteTrace`'s
  * `valueOf`): a term that holds an eigenvariable `HigherOrderSaturator`
  * opened a body at, which no round's start holds; and a term none of the
  * origins reaches without its own value (each refuses a value made from
  * itself). No trace has been seen to write one: measured 2026-11-19 under
  * `ArticleDestination.WrittenWithTraces` with `contest-entries-wren` on the first
  * variant of each of the 50 `RepeatedVariants.families` (seed 20261116,
  * the smallest repetition), 48 traces of 5,807 commands in all, and with
  * `contest-entries-solo` and `contest-entries-wren` on calls_1000_hot and inlined_calls_10000_hot in both
  * spellings (2026-11-19). Candidate fix for the first, once a trace shows
  * one: a value under an opening starts from the body the opening made.
  */
enum Given[C <: NativeSpecializer & Singleton]:
  case Value(index: Int)
  case Written(term: Configured[C])

/** A value of a trace (`Given`): the subterm at `at` of the term `commands`
  * make of its source's term, the commands those of the union that made the
  * node whose term it is, replayed from the union's other node.
  */
final case class TraceValue[C <: NativeSpecializer & Singleton](from: ValueSource, commands: Vector[TraceCommand[C]], at: Vector[PositionSegment])

/** A command of a round, which rewrites the subterm at its position, from
  * the root of the term the round has made so far.
  *
  * `Rewrite` replaces an instance of one side of its reason's equation by
  * the instance of the other side, in its direction. The variables of the
  * replaced side are bound by the subterm it replaces; `bindings` binds the
  * others, the variables of the replacement's side alone, each by its place
  * in `Statement.variables`, in that order, to the term it gives (`Given`).
  * Nothing a replay computes is written: the trace is a list of Scott-encoded
  * commands that transform the IR, and the IR is not part of the trace.
  *
  * `Convert` replaces an instance of one side of its conversion's equation
  * by the other side (`Conversion`), a β conversion the e-graph made with no
  * step of a proof yet; its replacement is computed, as a `Rewrite`'s is
  * A higher-order conversion's equation is "the instance of a thunk pattern =
  * its normal form": a step forward matches the pattern on the subterm it
  * replaces; a step backward of a left side's pattern matches it on the
  * subterm it replaces (`Conversions.expansionSolutions`), and one of a right
  * side's pattern binds all the pattern's variables, each by its place in the
  * pattern's variables, to the term it gives (`Given`), its replaced
  * subterm their normal form. A root reverse β binds nothing.
  *
  * `Native` puts a value at its position: a value the backend computed for a
  * narrow block, or either side of a native's fold in the e-graph, whose
  * equation is the native's trusted obligation; a step of no equation, its
  * value written.
  *
  * `Abstraction` is the abstraction rule ξ: the thunk at its position, of
  * `count` holes, opened at the eigenvariables of its depth
  * (`Conversions.eigenvariables`, the depth the number of `Abstraction`
  * commands it is inside), `commands` replayed on the body, and the body
  * they make written back as the front end spells the lambda
  * (`Conversions.abstraction`). The commands go the way the step goes, so
  * it has no direction.
  */
enum TraceCommand[C <: NativeSpecializer & Singleton]:
  case Rewrite(
      reason: ProvedReason[C],
      position: Vector[PositionSegment],
      direction: RewriteDirection,
      bindings: Vector[(Int, Given[C])]
  )
  case Convert(
      conversion: Conversion,
      position: Vector[PositionSegment],
      direction: RewriteDirection,
      bindings: Vector[(Int, Given[C])]
  )
  case Native(position: Vector[PositionSegment], value: Configured[C])
  case Abstraction(position: Vector[PositionSegment], count: Int, commands: Vector[TraceCommand[C]])

  /** The position the command rewrites at, from the root of the term.
    *
    * FIXME (2026-11-17): every command holds its position whole, so that a https://github.com/Atry/private-overlay/issues/1983
    * trace's positions grow with its commands times their depth: 16,901,930
    * segments for the 117,310 commands of `contest-entries-solo`'s repeated_library_hotspots
    * calls_1000 direct point (seed 20261116), and as the square of the depth
    * on `RewriteTraceLawTest`'s `text-sizes.txt` (2, 9, 35, 135). The text
    * writes each as a move from the one before it (`TraceText`'s MOVE) and
    * grows linearly. Candidate fix: the
    * model holds the moves, and a replay places each command from the one
    * before it as it goes.
    */
  def at: Vector[PositionSegment] = this match
    case Rewrite(_, position, _, _)  => position
    case Convert(_, position, _, _)  => position
    case Native(position, _)         => position
    case Abstraction(position, _, _) => position

/** A lemma a trace uses, by its two closed sides, read as `Statements.lemma`
  * reads them.
  */
final case class TraceLemma[C <: NativeSpecializer & Singleton](left: Configured[C], right: Configured[C]):

  def statement(using C): Statement[Configured[C]] = Statements.lemma(left, right)

  /** Whether the other lemma has the same two sides. */
  def same(other: TraceLemma[C])(using C): Boolean =
    Configured.same(left, other.left) && Configured.same(right, other.right)

/** A trace: the
  * lemmas its commands name, the values they name (`TraceValue`), and its
  * rounds, each the commands of one round in order, a round starting from the
  * term the rounds before it made. A value starts from the start of its round
  * or from an earlier value, and the values of a round come after those of
  * the rounds before it. The term the first round starts from is not part of
  * the trace: a replay is given it (`TraceStart`).
  */
final case class Trace[C <: NativeSpecializer & Singleton](
    lemmas: Vector[TraceLemma[C]],
    values: Vector[TraceValue[C]],
    rounds: Vector[Vector[TraceCommand[C]]]
):

  /** The steps of each round from the start, each with the term it starts
    * from.
    */
  def replayed(start: Configured[C])(using C, StorageAccess): Vector[Vector[ReplayedStep[C]]] =
    val (_, _, steps) = rounds.zipWithIndex.foldLeft((start, Vector.empty[Configured[C]], Vector.empty[Vector[ReplayedStep[C]]])) {
      case ((term, made, done), (round, place)) =>
        val context = Trace.valuesMade(this, made, place, term)
        val (after, steps) = Trace.replayedCommands(context, term, round, 0)
        (after, context.values, done :+ steps)
    }
    steps

  /** The term the rounds make of the start. */
  def output(start: Configured[C])(using C, StorageAccess): Configured[C] = replayed(start).flatten.lastOption.fold(start)(_.after)

/** The side a `Rewrite` puts in place as its equation states it, before the
  * replay's spelling (`ReplaySpelling`), and the bindings of its variables:
  * the side's codes are those of the term or of the lemma the equation is
  * stated over, from which a trace's source maps name the binders of the
  * replacement (`TraceSourceMaps`).
  */
final case class StatedReplacement[C <: NativeSpecializer & Singleton](side: StatementTerm[Configured[C]], bound: Map[String, Configured[C]]):

  /** The side instantiated: the replacement before the replay's spelling. */
  def instance(using C): Configured[C] = Statements.instance(side, bound)

/** A command replayed on the term before it: the subterm it replaced, the
  * subterm it put there, the provenance of its equation's variables oriented
  * from the replaced subterm to the replacement (none for a `Native` or an
  * `Abstraction`), the steps of an `Abstraction`'s commands on the body it
  * opened (none for another command), the side a `Rewrite` puts there as
  * stated (none for another command), and the terms before and after it.
  * The two whole terms are made when they are read, from the replay's spine
  * (`Spine`): a replay rebuilds only each step's path, and interning every
  * term whole made it quadratic on a wide term (69 s for the 117,310 commands
  * of `contest-entries-solo`'s repeated_library_hotspots calls_1000 direct point, whose
  * top-level thunk has 2,468 fillings).
  */
final class ReplayedStep[C <: NativeSpecializer & Singleton](
    val command: TraceCommand[C],
    beforeSpine: Spine[C],
    val replaced: Configured[C],
    val replacement: Configured[C],
    val provenance: Vector[Provenance],
    val inner: Vector[ReplayedStep[C]],
    val stated: Option[StatedReplacement[C]]
)(using C, StorageAccess):

  /** The term before the step. */
  lazy val before: Configured[C] = Spine.materialized(beforeSpine)

  /** The spine of the term after the step. */
  def afterSpine: Spine[C] = Spine.replaced(beforeSpine, command.at, replacement)

  /** The term after the step. */
  lazy val after: Configured[C] = Spine.materialized(afterSpine)

  override def toString: String =
    s"ReplayedStep($command, $replaced, $replacement, $provenance, $inner)"

/** What a replay reads beside the term: the trace's lemmas and the terms of
  * the values made so far, by their places.
  */
final case class ReplayContext[C <: NativeSpecializer & Singleton](lemmas: Vector[TraceLemma[C]], values: Vector[Configured[C]]):

  /** The term given: the term written, or the term of the value at its
    * place. Throws `IllegalArgumentException` for a place no value made so
    * far has.
    */
  def value(named: Given[C]): Configured[C] = named match
    case Given.Written(term) => term
    case Given.Value(place) =>
      values.lift(place).getOrElse(throw IllegalArgumentException(s"the trace has no value $place made before it is named"))

object Trace:

  /** The context of a replay of the round at the place, from the term before
    * it: the terms of the values made so far, followed by those of the values
    * that start from this round or from a value of it, made in order. A value
    * of a later round is left to it.
    */
  def valuesMade[C <: NativeSpecializer & Singleton](trace: Trace[C], made: Vector[Configured[C]], round: Int, roundStart: Configured[C])(using
      C,
      StorageAccess
  ): ReplayContext[C] =
    def rootRound(place: Int): Int = trace.values(place).from match
      case ValueSource.RoundStart(of) => of
      case ValueSource.Value(earlier) =>
        if earlier >= place then throw IllegalArgumentException(s"the value $place starts from the value $earlier, not an earlier one")
        rootRound(earlier)
    val (context, _) = trace.values.indices.drop(made.size).foldLeft((ReplayContext(trace.lemmas, made), false)) {
      case ((current, ended), place) =>
        if ended || rootRound(place) > round then (current, true)
        else
          val value = trace.values(place)
          val source = value.from match
            case ValueSource.RoundStart(of) =>
              if of != round then throw IllegalArgumentException(s"the value $place starts from round $of, not from round $round")
              roundStart
            case ValueSource.Value(earlier) => current.value(Given.Value(earlier))
          val (after, _) = replayedCommands(current, source, value.commands, 0)
          val term = Positions.subterm(after, value.at)
          (current.copy(values = current.values :+ term), false)
    }
    context

  /** The traces of rounds run one after another as one trace
    * (a schedule's rounds in one file), each given with the term it starts
    * from: the lemmas of all of them, each once in the order they first
    * occur, and their rounds in order, each command's lemma places
    * renumbered into the joined lemmas; the joined trace starts from the
    * first's start. Throws `IllegalArgumentException` for no trace, and when
    * a trace does not start from the term the traces before it make: the
    * joined trace would replay otherwise than the rounds.
    */
  def joined[C <: NativeSpecializer & Singleton](traces: Vector[(Configured[C], Trace[C])])(using C, StorageAccess): Trace[C] =
    val (start, first) = traces.headOption.getOrElse(throw IllegalArgumentException("no trace to join"))
    traces.tail.foldLeft(first) { case (joinedSoFar, (nextStart, next)) =>
      val made = joinedSoFar.output(start)
      if !Configured.same(nextStart, made) then
        throw IllegalArgumentException(s"a round starts from $nextStart, not from $made, which the rounds before it make")
      val lemmas = (joinedSoFar.lemmas ++ next.lemmas).foldLeft(Vector.empty[TraceLemma[C]])((kept, lemma) =>
        if kept.exists(_.same(lemma)) then kept else kept :+ lemma
      )
      val renumbering = Renumbering(next.lemmas.map(lemma => lemmas.indexWhere(_.same(lemma))), joinedSoFar.values.size)
      val rounds = joinedSoFar.rounds.size
      val values = next.values.map(value =>
        val shifted = value.from match
          case ValueSource.RoundStart(round) => ValueSource.RoundStart(round + rounds)
          case ValueSource.Value(index)      => ValueSource.Value(index + renumbering.valueOffset)
        TraceValue(shifted, value.commands.map(renumbered(_, renumbering)), value.at)
      )
      Trace(lemmas, joinedSoFar.values ++ values, joinedSoFar.rounds ++ next.rounds.map(_.map(renumbered(_, renumbering))))
    }

  /** The places of a joined trace: each lemma place `i` of a trace becomes
    * `lemmaPlaces(i)`, and each value place is shifted by `valueOffset`.
    */
  private final case class Renumbering(lemmaPlaces: Vector[Int], valueOffset: Int)

  /** The command with the lemma and value places it names renumbered. */
  private def renumbered[C <: NativeSpecializer & Singleton](command: TraceCommand[C], renumbering: Renumbering): TraceCommand[C] =
    def lemma(index: Int): Int = renumbering.lemmaPlaces(index)
    def value(named: Given[C]): Given[C] = named match
      case Given.Value(index)         => Given.Value(index + renumbering.valueOffset)
      case written @ Given.Written(_) => written
    def bound(bindings: Vector[(Int, Given[C])]): Vector[(Int, Given[C])] = bindings.map((place, named) => (place, value(named)))
    command match
      case TraceCommand.Rewrite(reason, position, direction, bindings) =>
        val reasonRenumbered: ProvedReason[C] = reason match
          case ProvedReason.Lemma(index)   => ProvedReason.Lemma(lemma(index))
          case ProvedReason.Fill(thunk)    => ProvedReason.Fill(thunk.map(shape => shape.copy(codeOf = value(shape.codeOf))))
          case ProvedReason.Body(thunk)    => ProvedReason.Body(thunk.map(shape => shape.copy(codeOf = value(shape.codeOf))))
          case ProvedReason.Eta(thunk)     => ProvedReason.Eta(thunk.map(shape => shape.copy(codeOf = value(shape.codeOf))))
          case equation @ ProvedReason.Equation(_) => equation
        TraceCommand.Rewrite(reasonRenumbered, position, direction, bound(bindings))
      case TraceCommand.Convert(Conversion.HigherOrder(index, side, occurrence), position, direction, bindings) =>
        TraceCommand.Convert(Conversion.HigherOrder(lemma(index), side, occurrence), position, direction, bound(bindings))
      case TraceCommand.Convert(Conversion.RootReverseBeta(index), position, direction, bindings) =>
        TraceCommand.Convert(Conversion.RootReverseBeta(lemma(index)), position, direction, bound(bindings))
      case TraceCommand.Abstraction(position, count, commands) =>
        TraceCommand.Abstraction(position, count, commands.map(renumbered(_, renumbering)))
      case native @ TraceCommand.Native(_, _) => native

  /** The commands replayed in order from the term, under `depth` openings:
    * the term they make and their steps.
    */
  def replayedCommands[C <: NativeSpecializer & Singleton](
      context: ReplayContext[C],
      term: Configured[C],
      commands: Vector[TraceCommand[C]],
      depth: Int
  )(using C, StorageAccess): (Configured[C], Vector[ReplayedStep[C]]) =
    val (last, steps) = commands.foldLeft((Spine.Settled(term): Spine[C], Vector.empty[ReplayedStep[C]])) {
      case ((current, earlier), command) =>
        val step = replayedStep(context, current, command, depth)
        (step.afterSpine, earlier :+ step)
    }
    (Spine.materialized(last), steps)

  /** The step of the command on the term. Throws `IllegalArgumentException`
    * when the subterm at its position is no instance of the side it
    * replaces, when its bindings bind a variable of that side or leave one of
    * the other side unbound, and when a reason writes its thunk forward or
    * leaves it out backward; for a conversion, also when the replaced subterm
    * is not the side the conversion computes.
    */
  def replayedStep[C <: NativeSpecializer & Singleton](
      context: ReplayContext[C],
      before: Spine[C],
      command: TraceCommand[C],
      depth: Int
  )(using C, StorageAccess): ReplayedStep[C] =
    val replaced = Spine.materialized(Spine.subterm(before, command.at))
    command match
      case TraceCommand.Abstraction(_, count, commands) =>
        val leaves: Vector[Configured[C]] = Conversions.eigenvariables(depth, count)
        val (body, inner) = replayedCommands(context, Conversions.opened(replaced, leaves), commands, depth + 1)
        ReplayedStep(command, before, replaced, Conversions.abstraction(body, leaves), Vector.empty, inner, None)
      case TraceCommand.Native(_, value) =>
        ReplayedStep(command, before, replaced, value, Vector.empty, Vector.empty, None)
      case TraceCommand.Convert(conversion, _, direction, written) =>
        val (replacement, provenance) = converted(context, conversion, direction, replaced, written)
        ReplayedStep(command, before, replaced, replacement, provenance, Vector.empty, None)
      case TraceCommand.Rewrite(reason, _, direction, written) =>
        // The equation as stated numbers the bindings; its sides in the replay's spelling are matched and
        // instantiated, the replay's terms being in that spelling (`ReplaySpelling`).
        val stated = statement(context, reason, direction, replaced)
        val equation = ReplaySpelling.statement(stated)
        val (replacedSide, replacementSide) = equation.oriented(direction)
        val matched = Statements.bindings(replacedSide, replaced)
        val variables = stated.variables
        val bound = written.foldLeft(matched) { case (current, (place, term)) =>
          val name = variables.lift(place).getOrElse(throw IllegalArgumentException(s"the equation has no variable $place"))
          if current.contains(name) then throw IllegalArgumentException(s"the binding of $name is named and matched")
          current.updated(name, context.value(term))
        }
        val provenance = direction match
          case RewriteDirection.Forward  => equation.provenance
          case RewriteDirection.Backward => equation.provenance.map(_.turned)
        ReplayedStep(
          command,
          before,
          replaced,
          Statements.instance(replacementSide, bound),
          provenance,
          Vector.empty,
          Some(StatedReplacement(stated.oriented(direction)._2, bound))
        )

  /** The replacement of a conversion's step and its provenance, from the
    * replaced subterm to the replacement.
    */
  private def converted[C <: NativeSpecializer & Singleton](
      context: ReplayContext[C],
      conversion: Conversion,
      direction: RewriteDirection,
      replaced: Configured[C],
      written: Vector[(Int, Given[C])]
  )(using C, StorageAccess): (Configured[C], Vector[Provenance]) =
    def lemmaOf(index: Int): Statement[Configured[C]] =
      context.lemmas.lift(index).getOrElse(throw IllegalArgumentException(s"the trace has no lemma $index")).statement
    conversion match
      case Conversion.HigherOrder(lemma, side, occurrence) =>
        val statement = lemmaOf(lemma)
        val pattern = Conversions.pattern(statement, side, occurrence)
        val higherOrderVariables = Conversions.higherOrder(statement)
        val variables = Statements.variables(pattern).distinct
        // The positions of a variable in the instance, in the replay's spelling (`Conversions.instance`).
        val spelledPattern = ReplaySpelling.side(pattern)
        def provenance(normal: Configured[C]): Vector[Provenance] =
          variables.filterNot(higherOrderVariables.contains).map(name =>
            Provenance(name, Statements.occurrences(spelledPattern, name), Positions.occurrences(normal, boundOf(name)))
          )
        lazy val writtenBound = written.map((place, value) =>
          (variables.lift(place).getOrElse(throw IllegalArgumentException(s"the pattern has no variable $place")), context.value(value))
        ).toMap
        lazy val matchedBound = Conversions
          .instanceBindings(pattern, replaced)
          .getOrElse(throw IllegalArgumentException(s"$replaced is no instance of the conversion's pattern $pattern"))
        // A left side's thunk is the pattern the saturator matched on the term
        // the step backward replaces, which determines its solution
        // (`Conversions.expansionSolutions`); a right side's thunk is built
        // under bindings the left side's match found elsewhere, which the
        // replaced term does not determine. So a right side's conversion
        // backward names its bindings, each a value of the trace (`Given`): a
        // path into a term the replay has and the forward commands that build
        // it, since a binding written in a command is what a trace avoids;
        // a term of the IR only where `Given`'s FIXME says.
        lazy val backwardBound = side match
          case LemmaSide.Left =>
            Conversions.expansionSolutions(pattern, replaced, higherOrderVariables) match
              case Vector(only) => only
              case solutions =>
                throw IllegalArgumentException(s"$replaced has ${solutions.size} solutions of the pattern $pattern, not one")
          case LemmaSide.Right => writtenBound
        def boundOf(name: String): Configured[C] = direction match
          case RewriteDirection.Forward  => matchedBound(name)
          case RewriteDirection.Backward => backwardBound(name)
        direction match
          case RewriteDirection.Forward =>
            if written.nonEmpty then throw IllegalArgumentException(s"a conversion forward writes no binding: $written")
            val normal = Conversions.normalForm(pattern, matchedBound, higherOrderVariables)
            (normal, provenance(normal))
          case RewriteDirection.Backward =>
            side match
              case LemmaSide.Left =>
                if written.nonEmpty then
                  throw IllegalArgumentException(s"a left side's conversion backward writes no binding: $written")
              case LemmaSide.Right =>
                if writtenBound.keySet != variables.toSet then
                  throw IllegalArgumentException(s"a conversion backward binds ${variables.mkString(", ")}, not $written")
            val normal = Conversions.normalForm(pattern, backwardBound, higherOrderVariables)
            if !Conversions.spelledAlike(normal, replaced) then
              throw IllegalArgumentException(s"$replaced is not the normal form $normal")
            val instance = Conversions.instance(pattern, backwardBound)
            (instance, provenance(replaced).map(_.turned))
      case Conversion.RootReverseBeta(lemma) =>
        if written.nonEmpty then throw IllegalArgumentException(s"a root reverse β writes no binding: $written")
        val names = Conversions.names(lemmaOf(lemma)).getOrElse(
          throw IllegalArgumentException(s"the lemma $lemma's left side applies no metavariable to names")
        )
        direction match
          case RewriteDirection.Forward =>
            val redex = Conversions.redex(replaced, names)
            (redex, Conversions.redexProvenance(replaced, redex, names.size))
          case RewriteDirection.Backward =>
            val term = Conversions.contracted(replaced, names.size)
            if !Configured.same(Conversions.redex(term, names), replaced) then
              throw IllegalArgumentException(s"$replaced is not the redex of its contraction $term")
            (term, Conversions.redexProvenance(term, replaced, names.size).map(_.turned))

  /** The equation of a proved reason, the thunk of a step forward read off
    * the subterm it replaces.
    */
  def statement[C <: NativeSpecializer & Singleton](
      context: ReplayContext[C],
      reason: ProvedReason[C],
      direction: RewriteDirection,
      replaced: Configured[C]
  )(using C): Statement[Configured[C]] =
    def shapeOf(thunk: Configured[C]): (Code, Vector[Hole]) = thunk.layer match
      case Thunk(code, holes, _) => (code, holes)
      case other                 => throw IllegalArgumentException(s"$other is no thunk")
    def thunkOf(written: Option[ThunkShape[C]], forward: => Configured[C]): (Code, Vector[Hole]) = (written, direction) match
      case (None, RewriteDirection.Forward) => shapeOf(forward)
      case (Some(shape), RewriteDirection.Backward) =>
        val (code, _) = shapeOf(context.value(shape.codeOf))
        (code, shape.holes)
      case _ => throw IllegalArgumentException(s"a step $direction of $reason writes its thunk only backward")
    def functionOf(term: Configured[C]): Configured[C] = term.layer match
      case Apply(function, _) => function
      case other              => throw IllegalArgumentException(s"$other is no application of a thunk")
    reason match
      case ProvedReason.Lemma(index) =>
        context.lemmas.lift(index).getOrElse(throw IllegalArgumentException(s"the trace has no lemma $index")).statement
      case ProvedReason.Equation(number) => Statements.setEquation(number)
      case ProvedReason.Fill(written) =>
        thunkOf(written, functionOf(replaced)) match
          case (code, holes @ Vector(_)) => Statements.betaBody(code, holes)
          case (code, holes)             => Statements.fill(code, holes)
      case ProvedReason.Body(written) =>
        thunkOf(written, replaced) match
          case (code, Vector()) => Statements.body(code)
          case (code, holes)    => throw IllegalArgumentException(s"a thunk of $code with the holes $holes has a hole")
      case ProvedReason.Eta(written) =>
        // A step backward that writes no thunk puts back the front end's
        // spelling of `λx. f x` over the replaced f (`Conversions.etaExpanded`).
        val (code, holes) = (written, direction) match
          case (None, RewriteDirection.Backward) => shapeOf(Conversions.etaExpanded(replaced))
          case _                                 => thunkOf(written, replaced)
        if Statements.etaShaped(code, holes) then Statements.eta(code, holes)
        else throw IllegalArgumentException(s"a thunk of $code with the holes $holes is not eta-shaped")
