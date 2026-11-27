package gezi.rewritetrace

import gezi.frontend.OccurrenceMarkers
import gezi.ir.StorageAccess
import gezi.ir.{Apply, Choice, Parallel, Thunk}
import gezi.ir.TailRecFolds
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Configured, NativeSpecializer}

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
  def trace[C <: NativeSpecializer & Singleton](tagged: Configured[C], markers: OccurrenceMarkers, lemmas: Vector[TraceLemma[C]])(using
      specializer: C,
      access: StorageAccess
  ): Trace[C] =
    val name = erasure(markers.name, lemmas)
    val closure = erasure(markers.closure, lemmas)
    val traceLemmas = Vector(name.lemma, closure.lemma).foldLeft(Vector.empty[TraceLemma[C]])((kept, lemma) =>
      if kept.exists(_.same(lemma)) then kept else kept :+ lemma
    )
    def place(lemma: TraceLemma[C]): Int = traceLemmas.indexWhere(_.same(lemma))
    val erasing = Erasing(
      Map(
        Configured.fromPure[C](specializer)(markers.name) -> Step(place(name.lemma), name.direction),
        Configured.fromPure[C](specializer)(markers.closure) -> Step(place(closure.lemma), closure.direction)
      ),
      Configured.fromPure[C](specializer)(markers.firstTag),
      Configured.fromPure[C](specializer)(markers.nextTag)
    )
    val (commands, _) = erased(tagged, erasing, 0, markedSubterms(tagged, erasing)).result
    Trace(traceLemmas, Vector.empty, Vector(commands))

  /** An erasure lemma and the direction that erases. */
  private final case class Erasure[C <: NativeSpecializer & Singleton](lemma: TraceLemma[C], direction: RewriteDirection)

  private def erasure[C <: NativeSpecializer & Singleton](marker: gezi.ir.Pure, lemmas: Vector[TraceLemma[C]])(using C): Erasure[C] =
    val erasing = OccurrenceMarkers.erasing[C](marker)
    val erased = OccurrenceMarkers.erased[C]
    lemmas
      .collectFirst {
        case lemma if Configured.same(lemma.left, erasing) && Configured.same(lemma.right, erased) =>
          Erasure(lemma, RewriteDirection.Forward)
        case lemma if Configured.same(lemma.left, erased) && Configured.same(lemma.right, erasing) =>
          Erasure(lemma, RewriteDirection.Backward)
      }
      .getOrElse(throw IllegalArgumentException(s"no lemma λt. λx. M t x = λt. λx. x of the marker $marker is given"))

  /** The place of a marker's lemma among the trace's lemmas and the direction
    * that erases its tag.
    */
  private final case class Step(lemma: Int, direction: RewriteDirection)

  /** The markers with the step of each, and the tag constructors, under which
    * no tag is ever found.
    */
  private final case class Erasing[C <: NativeSpecializer & Singleton](
      steps: Map[Configured[C], Step],
      firstTag: Configured[C],
      nextTag: Configured[C]
  ):

    /** Whether the term is a tag, `next (… (next first))`. */
    def tag(term: Configured[C])(using C): Boolean =
      Configured.same(term, firstTag) || (term.layer match
        case Apply(function, _) => Configured.same(function, nextTag)
        case _                  => false)

    /** The step of the marker the term is or is applied to; none for any
      * other term.
      */
    def headStep(term: Configured[C])(using C): Option[Step] =
      steps.get(term).orElse(term.layer match
        case Apply(function, _) => steps.get(function)
        case _                  => None)

  /** The commands that erase every tag in the term, from its root, under
    * `depth` openings, and the term they make of it, `marked` the term's
    * subterms that hold a marker (`markedSubterms`). A trampoline: a program
    * is as deep as it is written. A storage is no marker and no tag, and
    * holds none of them (`markedSubterms` does not read under it).
    */
  private def erased[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      erasing: Erasing[C],
      depth: Int,
      marked: Set[Configured[C]]
  )(using specializer: C, access: StorageAccess): TailRec[(Vector[TraceCommand[C]], Configured[C])] =
    def walked(current: Configured[C]): TailRec[(Vector[TraceCommand[C]], Configured[C])] =
      // A marker on its own is no instance of its lemma, and its definition holds no tag.
      if !marked.contains(current) || erasing.steps.contains(current) then done((Vector.empty, current))
      else
        current.layer match
          case Apply(markerApplied, operand) if isApplication(markerApplied) && erasing.steps.contains(headOf(markerApplied)) =>
            val Step(lemma, direction) = erasing.steps(headOf(markerApplied))
            val step = TraceCommand.Rewrite[C](ProvedReason.Lemma(lemma), Vector.empty, direction, Vector.empty)
            tailcall(walked(operand)).map((rest, after) => (step +: rest, after))
          case layer @ Thunk(code, holes, fillings) =>
            tailcall(children(fillings, fillings.indices.map(PositionSegment.Filling(_)).toVector)).flatMap((commands, erasedFillings) =>
              val thunk = Positions.built(layer, erasedFillings)
              val leaves: Vector[Configured[C]] = Conversions.eigenvariables(depth, holes.size)
              val body = Conversions.opened(thunk, leaves)
              val markedInBody = markedSubterms(body, erasing)
              if !markedInBody.contains(body) then done((commands, thunk))
              else
                tailcall(erased(body, erasing, depth + 1, markedInBody)).map((inner, erasedBody) =>
                  (commands :+ TraceCommand.Abstraction(Vector.empty, holes.size, inner), Conversions.abstraction(erasedBody, leaves))
                )
            )
          case layer @ Apply(function, argument) =>
            tailcall(children(Vector(function, argument), Vector(PositionSegment.Function, PositionSegment.Argument)))
              .map((commands, after) => (commands, Positions.built(layer, after)))
          case layer @ Choice(left, right) =>
            tailcall(children(Vector(left, right), Vector(PositionSegment.Left, PositionSegment.Right)))
              .map((commands, after) => (commands, Positions.built(layer, after)))
          case layer @ Parallel(left, right) =>
            tailcall(children(Vector(left, right), Vector(PositionSegment.Left, PositionSegment.Right)))
              .map((commands, after) => (commands, Positions.built(layer, after)))
          case _ => done((Vector.empty, current))
    def children(
        terms: Vector[Configured[C]],
        roles: Vector[PositionSegment]
    ): TailRec[(Vector[TraceCommand[C]], Vector[Configured[C]])] =
      TailRecFolds.folded(terms.zip(roles), (Vector.empty[TraceCommand[C]], Vector.empty[Configured[C]])) {
        case ((commands, made), (child, role)) =>
          walked(child).map((childCommands, after) => (commands ++ childCommands.map(placed(role, _)), made :+ after))
      }
    walked(term)

  /** The function of an application of the marker to a tag, `M T`, or the
    * term itself.
    */
  private def headOf[C <: NativeSpecializer & Singleton](term: Configured[C])(using C): Configured[C] = term.layer match
    case Apply(function, _) => function
    case _                  => term

  private def isApplication[C <: NativeSpecializer & Singleton](term: Configured[C])(using C): Boolean = term.layer match
    case Apply(_, _) => true
    case _           => false

  /** The command with its position under the segment. */
  private def placed[C <: NativeSpecializer & Singleton](segment: PositionSegment, command: TraceCommand[C]): TraceCommand[C] = command match
    case TraceCommand.Rewrite(reason, position, direction, bindings) => TraceCommand.Rewrite(reason, segment +: position, direction, bindings)
    case TraceCommand.Convert(conversion, position, direction, bindings) =>
      TraceCommand.Convert(conversion, segment +: position, direction, bindings)
    case TraceCommand.Native(position, value)                => TraceCommand.Native(segment +: position, value)
    case TraceCommand.Abstraction(position, count, commands) => TraceCommand.Abstraction(segment +: position, count, commands)

  /** The subterms of the term, each once, that hold a marker: the marker
    * itself or applied, `M` or `M T`, at or below them, a tag, an opaque term
    * and a storage holding none. One walk of the term's graph, so that a part
    * a program shares is visited once.
    */
  private def markedSubterms[C <: NativeSpecializer & Singleton](term: Configured[C], erasing: Erasing[C])(using C): Set[Configured[C]] =
    @scala.annotation.tailrec
    def visited(pending: List[(Configured[C], Boolean)], known: Map[Configured[C], Boolean]): Map[Configured[C], Boolean] = pending match
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
