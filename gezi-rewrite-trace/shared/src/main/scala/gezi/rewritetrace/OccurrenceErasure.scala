package gezi.rewritetrace

import gezi.frontend.OccurrenceMarkers
import gezi.ir.Instruction
import gezi.ir.{Apply, Choice, Parallel, Thunk}
import gezi.ir.TailRecFolds
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** The certificate of the occurrence tagging: a trace of one round that starts from the program the front
  * end tagged (`gezi.frontend.Occurrences.tagged`) and erases every tag,
  * each erasure a step forward of the marker's erasure lemma,
  * `N t x = x` for a name marker N and `C t c = c` for a closure marker C
  * (`OccurrenceMarkers.erasing`), whose variables the erased subterm binds,
  * so that the trace names no value. The equation is symmetric, so the trace
  * proves the tagged program equal to the program the trace ends at, whose
  * readback is the untagged program's.
  *
  * A tag on a closed subterm is a filling of a thunk or the root, and is
  * erased where it is. A closure tag on a lambda chain that reads a binder
  * outside it is applied in a code, with no position: the thunk whose code
  * applies it is opened by an `Abstraction` command, the tag erased in its
  * body, and the body written back as the front end spells the lambda. The
  * erased program keeps the replay's spelling where no thunk was opened, so
  * that a name used twice in a body is two equal fillings where the front end
  * makes it one: the end is the untagged program up to that respelling, not
  * the same instruction.
  */
object OccurrenceErasure:

  /** The erasure trace of the tagged program, its lemmas the erasure lemmas
    * of the two markers among `lemmas`, each in the orientation it has there.
    * Throws `IllegalArgumentException` when `lemmas` has no erasure lemma of a
    * marker.
    */
  def trace(tagged: Instruction, markers: OccurrenceMarkers, lemmas: Vector[TraceLemma]): Trace =
    val name = erasure(markers.name, lemmas)
    val closure = erasure(markers.closure, lemmas)
    val traceLemmas = Vector(name.lemma, closure.lemma).distinct
    val erasing = Erasing(
      Map(
        markers.name -> Step(traceLemmas.indexOf(name.lemma), name.direction),
        markers.closure -> Step(traceLemmas.indexOf(closure.lemma), closure.direction)
      ),
      markers
    )
    val (commands, _) = erased(tagged, erasing, 0, markedSubterms(tagged, erasing)).result
    Trace(traceLemmas, Vector.empty, Vector(commands))

  /** An erasure lemma and the direction that erases. */
  private final case class Erasure(lemma: TraceLemma, direction: RewriteDirection)

  private def erasure(marker: Instruction, lemmas: Vector[TraceLemma]): Erasure =
    val erasing = OccurrenceMarkers.erasing(marker)
    val erased = OccurrenceMarkers.erased
    lemmas
      .collectFirst {
        case lemma if lemma.left == erasing && lemma.right == erased => Erasure(lemma, RewriteDirection.Forward)
        case lemma if lemma.left == erased && lemma.right == erasing => Erasure(lemma, RewriteDirection.Backward)
      }
      .getOrElse(throw IllegalArgumentException(s"no lemma λt. λx. M t x = λt. λx. x of the marker $marker is given"))

  /** The place of a marker's lemma among the trace's lemmas and the direction
    * that erases its tag.
    */
  private final case class Step(lemma: Int, direction: RewriteDirection)

  /** The markers with the step of each, and the tag constructors, under which
    * no tag is ever found.
    */
  private final case class Erasing(steps: Map[Instruction, Step], markers: OccurrenceMarkers):

    /** Whether the term is a tag, `next (… (next first))`. */
    def tag(term: Instruction): Boolean =
      term == markers.firstTag || (term.layer match
        case Apply(function, _) => function == markers.nextTag
        case _                  => false)

    /** The step of the marker the term is or is applied to; none for any
      * other term.
      */
    def headStep(term: Instruction): Option[Step] =
      steps.get(term).orElse(term.layer match
        case Apply(function, _) => steps.get(function)
        case _                  => None)

  /** The commands that erase every tag in the term, from its root, under
    * `depth` openings, and the term they make of it, `marked` the term's
    * subterms that hold a marker (`markedSubterms`). A trampoline: a program
    * is as deep as it is written.
    */
  private def erased(
      term: Instruction,
      erasing: Erasing,
      depth: Int,
      marked: Set[Instruction]
  ): TailRec[(Vector[TraceCommand], Instruction)] =
    def walked(current: Instruction): TailRec[(Vector[TraceCommand], Instruction)] =
      // A marker on its own is no instance of its lemma, and its definition holds no tag.
      if !marked.contains(current) || erasing.steps.contains(current) then done((Vector.empty, current))
      else
        current.layer match
          case Apply(markerApplied, operand) if isApplication(markerApplied) && erasing.steps.contains(headOf(markerApplied)) =>
            val Step(lemma, direction) = erasing.steps(headOf(markerApplied))
            val step = TraceCommand.Rewrite(ProvedReason.Lemma(lemma), Vector.empty, direction, Vector.empty)
            tailcall(walked(operand)).map((rest, after) => (step +: rest, after))
          case Thunk(code, holes, fillings) =>
            tailcall(children(fillings, fillings.indices.map(PositionSegment.Filling(_)).toVector)).flatMap((commands, erasedFillings) =>
              val thunk = Instruction.Thunk(code, holes, erasedFillings)
              if holes.isEmpty then done((commands, thunk))
              else
                val leaves = Conversions.eigenvariables(depth, holes.size)
                val body = Conversions.opened(thunk, leaves)
                val markedInBody = markedSubterms(body, erasing)
                if !markedInBody.contains(body) then done((commands, thunk))
                else
                  tailcall(erased(body, erasing, depth + 1, markedInBody)).map((inner, erasedBody) =>
                    (commands :+ TraceCommand.Abstraction(Vector.empty, holes.size, inner), Conversions.abstraction(erasedBody, leaves))
                  )
            )
          case Apply(function, argument) =>
            tailcall(children(Vector(function, argument), Vector(PositionSegment.Function, PositionSegment.Argument)))
              .map((commands, after) =>
                val Vector(erasedFunction, erasedArgument) = after: @unchecked
                (commands, Instruction.Apply(erasedFunction, erasedArgument))
              )
          case Choice(left, right) =>
            tailcall(children(Vector(left, right), Vector(PositionSegment.Left, PositionSegment.Right))).map((commands, after) =>
              val Vector(erasedLeft, erasedRight) = after: @unchecked
              (commands, Instruction.Choice(erasedLeft, erasedRight))
            )
          case Parallel(left, right) =>
            tailcall(children(Vector(left, right), Vector(PositionSegment.Left, PositionSegment.Right))).map((commands, after) =>
              val Vector(erasedLeft, erasedRight) = after: @unchecked
              (commands, Instruction.Parallel(erasedLeft, erasedRight))
            )
          case _ => done((Vector.empty, current))
    def children(
        terms: Vector[Instruction],
        roles: Vector[PositionSegment]
    ): TailRec[(Vector[TraceCommand], Vector[Instruction])] =
      TailRecFolds.folded(terms.zip(roles), (Vector.empty[TraceCommand], Vector.empty[Instruction])) {
        case ((commands, made), (child, role)) =>
          walked(child).map((childCommands, after) => (commands ++ childCommands.map(placed(role, _)), made :+ after))
      }
    walked(term)

  /** The function of an application of the marker to a tag, `M T`, or the
    * term itself.
    */
  private def headOf(term: Instruction): Instruction = term.layer match
    case Apply(function, _) => function
    case _                  => term

  private def isApplication(term: Instruction): Boolean = term.layer match
    case Apply(_, _) => true
    case _           => false

  /** The command with its position under the segment. */
  private def placed(segment: PositionSegment, command: TraceCommand): TraceCommand = command match
    case TraceCommand.Rewrite(reason, position, direction, bindings) => TraceCommand.Rewrite(reason, segment +: position, direction, bindings)
    case TraceCommand.Convert(conversion, position, direction, bindings) =>
      TraceCommand.Convert(conversion, segment +: position, direction, bindings)
    case TraceCommand.Native(position, value)                => TraceCommand.Native(segment +: position, value)
    case TraceCommand.Abstraction(position, count, commands) => TraceCommand.Abstraction(segment +: position, count, commands)

  /** The subterms of the term, each once, that hold a marker: the marker
    * itself or applied, `M` or `M T`, at or below them, a tag and an opaque
    * term holding none. One walk of the term's graph, so that a part a
    * program shares is visited once.
    */
  private def markedSubterms(term: Instruction, erasing: Erasing): Set[Instruction] =
    def visited(pending: List[(Instruction, Boolean)], known: Map[Instruction, Boolean]): Map[Instruction, Boolean] = pending match
      case Nil => known
      case (current, true) :: rest =>
        visited(rest, known.updated(current, current.layer.children.exists(known(_))))
      case (current, false) :: rest =>
        if known.contains(current) then visited(rest, known)
        else if erasing.headStep(current).isDefined then visited(rest, known.updated(current, true))
        else if current.opaque || erasing.tag(current) then visited(rest, known.updated(current, false))
        else
          val below = current.layer.children.filterNot(known.contains)
          visited(below.map((_, false)).toList ++ ((current, true) :: rest), known)
    visited(List((term, false)), Map.empty).collect { case (subterm, true) => subterm }.toSet
