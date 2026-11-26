package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.ir.Code
import gezi.ir.CodeLayer
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Layer
import gezi.locations.BinderOrigin
import gezi.locations.Location
import gezi.locations.SourceMap
import gezi.locations.Span
import scala.jdk.StreamConverters.*
import gezi.ir

/** The laws of the source map of the located conversion
  * (`Defunctionalization.locatedThunkInstruction`), on the text of a
  * generated closed term, every node of which the text writes:
  *
  *   - the conversion gives the very instruction `thunkInstruction` gives
  *     (the clearing law: locations change no instruction);
  *   - the map has the instruction's shape: a place below an application, a
  *     choice or a parallel for each side, a thunk's code map of the code's
  *     shape and a map for each filling, unless the place is bare;
  *   - every location at a place of the instruction, and at a slot of a code
  *     that reads a closed subterm, is a span of the text that reads, alone,
  *     to the instruction of that place or of that slot's filling;
  *   - a closed subterm written twice in one body, which takes one slot,
  *     leaves both occurrences on its filling;
  *   - a thunk's place, an instruction's or an inner code's, holds the
  *     origins of each of its binders, at least one, each the name the text
  *     writes at a span that reads the name, one for each occurrence of a
  *     subterm written more than once; the earliest spans in the order of
  *     the binders;
  *   - the readback's map (`readbackMap`) is the map of the term as the
  *     text writes it, a closed subterm written at three places, one under
  *     an abstraction, read back at each with its own span and binder names;
  *   - a closed partial function of a literal binder of several bytes,
  *     written twice in one body, converts to the instruction and reads back
  *     to the term the instruction reads back to: each level of its variable
  *     arguments partial function is a closed subterm written once inside
  *     the level above, and the two occurrences' maps are merged; every
  *     binder the literal spreads into, the binders of the miss top at each
  *     bit included, has an origin.
  *
  * Its purpose is to catch a map misaligned with the conversion (a code's
  * map shifted against its layers, a filling given another slot's
  * occurrences, a slot's occurrence lost when equal subterms merge or when
  * an inner chain hands its slot up, a binder's origin given to another
  * binder or lost, an occurrence read back with the merged map of all
  * occurrences of its filling), a located conversion that converts to
  * another instruction, and a map that holds a filling written once both
  * at its slot's place and as the filling's map, or a readback that reads
  * such a filling again at its occurrence: the levels of a literal binder of
  * n bits are then 2^n places to merge or reads to make, which overrun the
  * deadline; and a binder the reader builds for a literal with no origin,
  * which the printer cannot name once a step moves it out of the literal
  * (top's binders under the markers spelled as tags, 2026-11-19).
  */
class DefunctionalizationSourceMapLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts

  private type NoFactsTerm = Configured[NoFacts.type]

  private val uri: java.net.URI = java.net.URI.create("file:///generated.lambdalattice")

  private def located(text: String): (NoFactsTerm, SourceMap) =
    val read = Lambdalattice.located(text, FreeNames.Rejected)
    Defunctionalization.locatedThunkInstruction(read.term, read.spans, uri)(using gezi.ir.NoFacts)

  property("the located conversion converts to the instruction, its map aligned and reading back") {
    HoasGenerators.closedTerm.forAllWithLog(LambdalatticeText.text).map(term =>
      val text = LambdalatticeText.text(term)
      val (instruction, map) = located(text)
      val codePoints = text.codePoints.toScala(Vector).map(_.toInt)
      val problems =
        (if Configured.same(instruction, Defunctionalization.thunkInstruction(Lambdalattice.term(text))(using gezi.ir.NoFacts)) then Vector.empty
         else Vector("another instruction")) ++ instructionProblems(instruction, map, codePoints)
      Result.assert(problems.isEmpty).log(problems.mkString("\n"))
    )
  }

  property("a closed subterm written twice in one body leaves both occurrences on its filling") {
    HoasGenerators.closedTerm.forAllWithLog(LambdalatticeText.text).map(term =>
      val closed = s"(${LambdalatticeText.text(term)})"
      val text = s"λx. x $closed $closed"
      val (_, map) = located(text)
      val first = text.indexOf(closed)
      val second = text.lastIndexOf(closed)
      def spanned(start: Int): Location =
        Location.Source(uri, Span(text.codePointCount(0, start + 1), text.codePointCount(0, start + closed.length - 1)))
      val fillingLocations = map.children.flatMap(_.locations).toSet
      Result.assert(Set(spanned(first), spanned(second)).subsetOf(fillingLocations)).log(s"$fillingLocations")
    )
  }

  property("the readback's map is the text's own: each node at its span, each binder the name written there") {
    HoasGenerators.closedTerm.forAllWithLog(LambdalatticeText.text).map(term =>
      val closed = s"(${LambdalatticeText.text(term)})"
      val text = s"λf. f $closed (λx. f $closed) $closed"
      val read = Lambdalattice.located(text, FreeNames.Rejected)
      val (instruction, map) = Defunctionalization.locatedThunkInstruction(read.term, read.spans, uri)(using gezi.ir.NoFacts)
      val readback = Defunctionalization.readbackMap(instruction, map)
      val written = textMap(read.term, read.spans, chained = false)
      Result.assert(readback == written).log(s"readback $readback\nwritten $written")
    )
  }

  property("a closed partial function of several bytes written twice converts and reads back to the instruction's term") {
    val texts = for
      key <- Gen.string(Gen.alphaNum, Range.linear(2, 12))
      body <- HoasGenerators.closedTerm.map(LambdalatticeText.text)
    yield s"""λg. g (λ"$key". $body) (λ"$key". $body)"""
    texts.forAllWithLog(identity).map(text =>
      val (instruction, map) = located(text)
      val (readback, _, _) = Defunctionalization.locatedInstructionTerm(instruction, map, Set.empty)
      Result
        .assert(Configured.same(instruction, Defunctionalization.thunkInstruction(Lambdalattice.term(text))(using gezi.ir.NoFacts)))
        .log("the located conversion converts to another instruction")
        .and(Result.assert(readback == Defunctionalization.instructionTerm(instruction)).log("the readback reads another term"))
        .and(Result.assert(originless(instruction, map).isEmpty).log(s"binders with no origin: ${originless(instruction, map).take(3)}"))
    )
  }

  /** The thunk places, an instruction's or an inner code's, with a binder
    * that has no origin, each by the binders' origins there.
    */
  private def originless(instruction: NoFactsTerm, map: SourceMap): Vector[Vector[Set[BinderOrigin]]] =
    def missing(holeCount: Int, at: SourceMap): Vector[Vector[Set[BinderOrigin]]] =
      if at.binders.size < holeCount || at.binders.exists(_.isEmpty) then Vector(at.binders) else Vector.empty
    def part(parts: Vector[SourceMap], position: Int): SourceMap = parts.lift(position).getOrElse(SourceMap.unlocated)
    def inCode(code: Code, at: SourceMap): Vector[Vector[Set[BinderOrigin]]] = code.layer match
      case ir.Slot(_)                   => Vector.empty
      case ir.Apply(function, argument) => inCode(function, part(at.children, 0)) ++ inCode(argument, part(at.children, 1))
      case ir.Choice(left, right)       => inCode(left, part(at.children, 0)) ++ inCode(right, part(at.children, 1))
      case ir.Parallel(left, right)     => inCode(left, part(at.children, 0)) ++ inCode(right, part(at.children, 1))
      case ir.Thunk(inner, holes, fillings) =>
        missing(holes.size, at) ++ inCode(inner, at.code.getOrElse(SourceMap.unlocated)) ++
          fillings.zipWithIndex.flatMap((filling, position) => inCode(filling, part(at.children, position)))
    def inInstruction(current: NoFactsTerm, at: SourceMap): Vector[Vector[Set[BinderOrigin]]] = current.layer match
      case ir.Apply(function, argument) => inInstruction(function, part(at.children, 0)) ++ inInstruction(argument, part(at.children, 1))
      case ir.Choice(left, right)       => inInstruction(left, part(at.children, 0)) ++ inInstruction(right, part(at.children, 1))
      case ir.Parallel(left, right)     => inInstruction(left, part(at.children, 0)) ++ inInstruction(right, part(at.children, 1))
      case ir.Thunk(code, holes, fillings) =>
        missing(holes.size, at) ++ inCode(code, at.code.getOrElse(SourceMap.unlocated)) ++
          fillings.zipWithIndex.flatMap((filling, position) => inInstruction(filling, part(at.children, position)))
      case _ => Vector.empty
    inInstruction(instruction, map)

  /** The map of a term as the text writes it, in `TermMap`'s convention: a
    * node located at its own span, an abstraction inside a chain at none,
    * each abstraction with the origin of the binder the text gives it.
    */
  private def textMap(term: DeBruijnTerm, spans: SyntaxSpans, chained: Boolean): TermMap =
    val here = Set[Location](Location.Source(uri, spans.span))
    term match
      case DeBruijnTerm.Lambda(body) =>
        val origins: Set[BinderOrigin] = spans.nodeBinder.toSet.map {
          case SpelledBinder.Named(name, span) => BinderOrigin.Written(name, Location.Source(uri, span))
          case SpelledBinder.LiteralBit(literal, bit, span) =>
            BinderOrigin.LiteralBit(literal.bytes.toVector, bit, Location.Source(uri, span))
          case SpelledBinder.Enclosing(name) => BinderOrigin.Enclosing(name)
        }
        TermMap.Abstraction(if chained then Set.empty else here, origins, textMap(body, spans.child(0), chained = true))
      case DeBruijnTerm.Apply(function, argument) =>
        TermMap.Pair(here, textMap(function, spans.child(0), chained = false), textMap(argument, spans.child(1), chained = false))
      case DeBruijnTerm.Choice(left, right) =>
        TermMap.Pair(here, textMap(left, spans.child(0), chained = false), textMap(right, spans.child(1), chained = false))
      case DeBruijnTerm.Parallel(left, right) =>
        TermMap.Pair(here, textMap(left, spans.child(0), chained = false), textMap(right, spans.child(1), chained = false))
      case DeBruijnTerm.Variable(_) | DeBruijnTerm.Constant(_) | DeBruijnTerm.Free(_) => TermMap.Leaf(here)

  private def readsBack(locations: Set[Location], instruction: NoFactsTerm, codePoints: Vector[Int]): Vector[String] =
    locations.toVector.flatMap {
      case Location.Source(_, span) =>
        val text = span.of(codePoints)
        val read = scala.util.Try(Defunctionalization.thunkInstruction(Lambdalattice.term(text))(using gezi.ir.NoFacts)).toOption
        if read.exists(Configured.same(_, instruction)) then Vector.empty else Vector(s"the span $span, `$text`, reads another term")
      case other => Vector(s"a reader's location that is no span: $other")
    }

  private def instructionProblems(instruction: NoFactsTerm, map: SourceMap, codePoints: Vector[Int]): Vector[String] =
    val own = readsBack(map.locations, instruction, codePoints)
    if map.bare then own
    else
      own ++ (instruction.layer match
        case storage: ir.NativeStorage    => Vector(s"the front end of no facts made the storage $storage")
        case ir.Apply(function, argument) => pairProblems(Vector(function, argument), map, codePoints)
        case ir.Choice(left, right)       => pairProblems(Vector(left, right), map, codePoints)
        case ir.Parallel(left, right)     => pairProblems(Vector(left, right), map, codePoints)
        case ir.Thunk(code, holes, fillings) =>
          if map.children.size != fillings.size then Vector(s"${map.children.size} filling maps for ${fillings.size} fillings")
          else
            val slotFillings = slotValues(holes, fillings)
            binderProblems(holes.size, map, codePoints) ++
              map.code.fold(Vector("a thunk's map with no code map"))(codeProblems(code, _, slotFillings, codePoints)) ++
              fillings.lazyZip(map.children).flatMap(instructionProblems(_, _, codePoints))
        case ir.UriNode(_) | ir.Opaque(_) => Vector("an opaque instruction's map with places below it")
      )

  /** The violations of the origins of a thunk's binders: origins for each
    * binder, at least one, each the name the text writes at the origin's
    * span, the earliest spans increasing along the chain.
    */
  private def binderProblems(holeCount: Int, map: SourceMap, codePoints: Vector[Int]): Vector[String] =
    if map.binders.size != holeCount then Vector(s"${map.binders.size} binder origins for $holeCount binders")
    else
      val earliest = map.binders.map(origins =>
        val starts = origins.toVector.collect {
          case BinderOrigin.Written(name, Location.Source(_, span)) if span.of(codePoints) == name => span.start
        }
        Option.when(origins.nonEmpty && starts.size == origins.size)(starts.min).toRight(s"a binder's origins $origins")
      )
      earliest.collect { case Left(problem) => problem } ++
        earliest.collect { case Right(start) => start }.sliding(2).collect {
          case Seq(before, after) if before >= after => s"binder spans out of order at $before and $after"
        }

  private def pairProblems(sides: Vector[NoFactsTerm], map: SourceMap, codePoints: Vector[Int]): Vector[String] =
    if map.code.isDefined || map.children.size != sides.size then Vector(s"a map of ${map.children.size} sides for ${sides.size}")
    else sides.lazyZip(map.children).flatMap(instructionProblems(_, _, codePoints))

  /** The filling each slot of a thunk's code reads, none for a hole. */
  private def slotValues(holes: Vector[gezi.ir.Hole], fillings: Vector[NoFactsTerm]): Map[Int, NoFactsTerm] =
    val holeSlots = holes.collect { case gezi.ir.Hole.Bound(slot) => slot }.toSet
    val filledSlots = (0 until holeSlots.size + fillings.size).filterNot(holeSlots.contains).toVector
    filledSlots.zip(fillings).toMap

  /** The violations at a code of the thunk whose slots read `slotFillings`:
    * a slot reading a filling has the locations of the closed subterm it
    * stands for; an inner thunk's code is read with its own slots, which the
    * law does not follow.
    */
  private def codeProblems(
      code: Code,
      map: SourceMap,
      slotFillings: Map[Int, NoFactsTerm],
      codePoints: Vector[Int]
  ): Vector[String] =
    code.layer match
      case ir.Slot(slot) =>
        slotFillings.get(slot).fold(Vector.empty)(readsBack(map.locations, _, codePoints))
      case ir.Apply(function, argument) => codePairProblems(Vector(function, argument), map, slotFillings, codePoints)
      case ir.Choice(left, right)       => codePairProblems(Vector(left, right), map, slotFillings, codePoints)
      case ir.Parallel(left, right)     => codePairProblems(Vector(left, right), map, slotFillings, codePoints)
      case ir.Thunk(_, holes, fillings) =>
        if map.code.isEmpty || map.children.size != fillings.size then Vector("an inner thunk's map of another shape")
        else binderProblems(holes.size, map, codePoints)

  private def codePairProblems(
      sides: Vector[Code],
      map: SourceMap,
      slotFillings: Map[Int, NoFactsTerm],
      codePoints: Vector[Int]
  ): Vector[String] =
    if map.code.isDefined || map.children.size != sides.size then Vector(s"a code map of ${map.children.size} sides for ${sides.size}")
    else sides.lazyZip(map.children).flatMap(codeProblems(_, _, slotFillings, codePoints))
