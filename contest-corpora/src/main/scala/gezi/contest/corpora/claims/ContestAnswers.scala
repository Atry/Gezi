package gezi.contest.corpora.claims

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamily

import scala.annotation.tailrec
import gezi.weakhead.Computation
import gezi.weakhead.Computed
import gezi.weakhead.Head
import gezi.weakhead.Mode
import gezi.weakhead.ParallelSet
import gezi.weakhead.ParallelView
import gezi.weakhead.Reading
import gezi.weakhead.ReadingOutcome
import gezi.weakhead.ReadingState
import gezi.weakhead.Resource
import gezi.weakhead.Value
import gezi.weakhead.Values
import gezi.weakhead.WeakHead
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Term

/** A decoding of a head by observation (`contest_answers:verdict/5`):
  * `decoded(Value)` or `failure(Reason)`.
  */
enum Decoding:
  case Decoded(value: String)
  case Failure(reason: String)

/** The contest's verdict on a reading: `matches`, `differs` or
  * `decode_failure(Reason)` for a head that is no value of the kind; or that
  * the reading or the decode stopped, which is no verdict.
  */
enum Verdict:
  case Matches, Differs
  case DecodeFailure(reason: String)

  /** The decode ran past its budget of steps (`resource` none) or out of a
    * resource: no verdict. The Prolog verdict said
    * `decode_failure(inference_limit)` or `decode_failure(exhausted(R))`;
    * a stop under a budget is never a verdict.
    */
  case DecodeStopped(resource: Option[Resource])

  /** The reading ran past its budget or out of a resource: no verdict. The
    * Prolog verdict said `differs` of any outcome other than `heads(...)`.
    */
  case ReadingStopped(outcome: ReadingOutcome)

/** The contest's verdict on a reading and the evaluator steps its decode
  * took (`verdict/5`'s Verdict and Spent), 0 when nothing was decoded.
  */
final case class Judged(verdict: Verdict, spent: Long)

/** The contest's answer tables and verdict,
  * the Prolog file deleted with `problems/answers` as its data
  * (`git show 91b3f11e1^:lambda_jit/corpora/contest_answers.pl`): the points' intended answers and
  * limits, read from the family `gezi/problems/answers`, and the
  * verdict on a reading, which
  * decodes every head BY OBSERVATION (`verdict/5`, whose comment the
  * definitions here follow): a head is applied to two markers and the
  * application evaluated under tabling(weak_head), every head of it taken; a Scott
  * boolean chooses one marker; a Scott natural answers the zero marker or
  * the successor marker applied to its predecessor, which, applied four
  * times, answers the predecessor, decoded again; a value
  * `certificate(Name)` matches a head whose readback is the readback of the
  * certificate's head. A parallel is read out, each side observed whole, its
  * decodings the values both sides decode to. The decode runs
  * under its own budget, `decode_limits(limits(10, 256, 256))`, its seconds
  * a budget of evaluator steps (`Reading.budgetSteps`) where the Prolog
  * counted inferences.
  *
  * `certificates` are the closed terms the corpora name by `certificate/2`
  * (`HardClauses.certificates`).
  */
final class ContestAnswers(corpora: Corpora, certificates: Map[String, () => Term]):

  private def file: ProblemFamily = corpora.contestAnswers

  /** `intended(Point, Outcome, Value)`. */
  def intended(point: String): Option[Intended] =
    file.rows("intended").collectFirst {
      case Vector(key, outcome, value) if ProblemData.text(key) == point =>
        Intended(IntendedOutcome.read(outcome), IntendedValue.read(value))
    }

  /** The points of `intended/3`, in order. */
  def points: Vector[String] = file.rows("intended").map(arguments => ProblemData.text(arguments(0)))

  /** `point_limits(Point, Limits)`: the raised limits, or 1 s and 32 MB. */
  def pointLimits(point: String): Limits =
    file.rows("raised_limits").collectFirst {
      case Vector(key, limits) if ProblemData.text(key) == point => Limits.read(limits)
    }.getOrElse(Limits.of(1, 32, 32))

  /** `verdict(failed, none, Outcome, Verdict, 0)`: a point intended to have
    * no head matches a reading with no head, whose heads are `headCount`.
    */
  def failedVerdict(headCount: Int): Verdict = if headCount == 0 then Verdict.Matches else Verdict.Differs

  /** `decodings_verdict(Decodings, Value, Verdict)`: a decode failure when
    * some decoding failed (the least reason in the standard order, as the
    * sorted set gives it first), `matches` when the decodings are exactly
    * the intended value, `differs` otherwise.
    */
  def decodingsVerdict(decodings: Set[Decoding], value: IntendedValue): Verdict =
    decodings.collect { case Decoding.Failure(reason) => reason }.minOption match
      case Some(reason) => Verdict.DecodeFailure(reason)
      case None =>
        if decodings == Set(Decoding.Decoded(value.written)) then Verdict.Matches else Verdict.Differs

  /** The verdict on the point's reading (`matches_intended/2`, which holds
    * when the verdict is `Matches`). Throws for a point with no intended
    * answer.
    */
  def pointVerdict(point: String, outcome: ReadingOutcome): Judged =
    verdict(intended(point).getOrElse(throw IllegalArgumentException(s"$point has no intended answer")), outcome)

  /** `verdict(Intended, Value, Outcome, Verdict, Spent)`: the verdict on a
    * reading of a program (the class comment). A reading that stopped gets no verdict, `ReadingStopped`.
    */
  def verdict(intended: Intended, outcome: ReadingOutcome): Judged =
    (intended, outcome) match
      case (_, stopped @ (ReadingOutcome.StepLimit | ReadingOutcome.Exhausted(_))) =>
        Judged(Verdict.ReadingStopped(stopped), 0)
      case (Intended(IntendedOutcome.Failed, IntendedValue.NoValue), ReadingOutcome.Heads(heads)) =>
        Judged(failedVerdict(heads.size), 0)
      case (Intended(IntendedOutcome.Head, value), ReadingOutcome.Heads(heads)) if heads.nonEmpty =>
        headsVerdict(value, heads)
      case (Intended(IntendedOutcome.Head, _), ReadingOutcome.Heads(_)) => Judged(Verdict.Differs, 0)
      case (other, _) =>
        throw IllegalArgumentException(s"no intended answer ${other.outcome.written} ${other.value.written}")

  /** The decodings of every head within the decode's budget, then
    * `decodingsVerdict`; a decode that stops is `DecodeStopped`.
    */
  private def headsVerdict(value: IntendedValue, heads: Vector[ParallelSet]): Judged =
    val (zeroMarker, successorMarker) = ContestAnswers.markers
    val observation = Observation(zeroMarker, successorMarker)
    val decodings = Computation
      .traversed(heads)(set => observation.decodings(value, set, certificateTerm))
      .map(_.flatten)
      .result(ReadingState.knowingTop(ContestAnswers.decodeLimit))
    decodings match
      case Computed.Done(found, after) => Judged(decodingsVerdict(found.toSet, value), after.budget.spent)
      case Computed.Stopped(after)     => Judged(Verdict.DecodeStopped(after.exhausted), after.budget.spent)

  /** `certificate_head_term(Name, Term)`: the readback of the certificate's
    * one head. Throws for a name no certificate has, or a certificate with
    * other than one head within the decode's budget.
    */
  private def certificateTerm(name: String): DeBruijnTerm =
    val certificate = certificates.getOrElse(name, throw IllegalArgumentException(s"no_certificate($name)"))()
    val value = Values.ofInstruction(Defunctionalization.thunkInstruction(certificate.deBruijnTerm(Map.empty)), Set.empty)
    Reading.termReading(Mode.TablingWeakHead, value, ContestAnswers.decodeLimit) match
      case ReadingOutcome.Heads(Vector(set)) =>
        set.view match
          case ParallelView.Single(head) => ContestAnswers.headTerm(head)
          case _ => throw IllegalArgumentException(s"certificate_not_one_head($name, $set)")
      case other => throw IllegalArgumentException(s"certificate_not_one_head($name, $other)")

/** The markers, the decode's budget and the readback of a head. */
object ContestAnswers:

  /** The decode's own budget, `decode_limits(limits(10, 256, 256))`: its 10
    * seconds as a budget of steps; its megabytes are not applied, as the
    * Prolog decode ran under the process's limits.
    */
  val decodeLimit: Long = Reading.budgetSteps(10)

  /** `\a.\b.\c. c` and `\p.\a.\b.\c.\d. p` as heads (`marker_heads/2`): no
    * Scott boolean or natural has three or four binders, so neither marker
    * is mistaken for a value.
    */
  def markers: (Head, Head) =
    import DeBruijnTerm.{Lambda, Variable}
    val zeroValue = Values.ofInstruction(Defunctionalization.thunkInstruction(Lambda(Lambda(Lambda(Variable(0))))), Set.empty)
    val successorValue =
      Values.ofInstruction(Defunctionalization.thunkInstruction(Lambda(Lambda(Lambda(Lambda(Lambda(Variable(4))))))), Set.empty)
    (asHead(zeroValue), asHead(successorValue))

  private def asHead(value: Value): Head = value match
    case Value.Thunk(code, holes, fillings) if holes.nonEmpty => Head.Lambda(code, holes, fillings)
    case other => throw IllegalStateException(s"a marker is a lambda, not $other")

  /** `head_term(Head, Term)`: the de Bruijn readback of a plain head, read
    * whole. Every value being interned, a library name is the term it was
    * written as, so a head holds no instruction apart from its term.
    */
  def headTerm(head: Head): DeBruijnTerm =
    Defunctionalization.instructionTerm(Values.instruction(head.value))

/** The observation of heads against the two markers (`observed_decoding/3`
  * and the predicates under it), each evaluation under tabling(weak_head)
  * in the decode's state.
  */
private final case class Observation(zeroMarker: Head, successorMarker: Head):

  private type Decodings = Computation[ReadingState, Vector[Decoding]]

  private def heads(term: Value): Computation[ReadingState, Vector[ParallelSet]] =
    WeakHead.heads(Mode.TablingWeakHead, term).collected

  private def appliedToMarkers(term: Value): Value =
    Value.Apply(Value.Apply(term, zeroMarker.value), successorMarker.value)

  /** The parallel set as a value. The decode's state lists no least term
    * (`ReadingState.knowingTop`), so the evaluator answers no empty parallel
    * set.
    */
  private def valueOf(set: ParallelSet): Value =
    set.value.getOrElse(throw IllegalStateException("a state that lists no least term answers no empty parallel set"))

  /** `observed_decoding(Value, Head, Decoding)`, every decoding. */
  def decodings(value: IntendedValue, set: ParallelSet, certificate: String => DeBruijnTerm): Decodings =
    value match
      case IntendedValue.BooleanValue(_) =>
        heads(appliedToMarkers(valueOf(set))).flatMap(choices =>
          if choices.isEmpty then Computation.pure(Vector(Decoding.Failure("not_a_boolean")))
          else Computation.traversed(choices)(chosenBoolean).map(_.flatten)
        )
      case IntendedValue.NaturalValue(_) => observedNatural(valueOf(set), 0)
      case IntendedValue.CertificateValue(name) => certificateObserved(set, name, certificate(name))
      case IntendedValue.NoValue => throw IllegalArgumentException("a head is not observed against no value")

  /** The values of the two sides of a parallel set of several heads
    * (`ParallelView.Several`), each observed whole, that both sides decode
    * to. A side's failure, a head of the side that is no value of the kind,
    * is no value of the side and is dropped before the two sides are
    * compared, so a set both of whose sides fail has no decoding where it
    * had the failure; and when the left side decodes to no value the right
    * side is not observed, the set having none whatever the right side does.
    * With it top = Y (λz. λx. z ∥ x), the term that stands for no answer, has
    * no decoding: top applied to the markers is a parallel set that holds the
    * abstraction λx. top ∥ x, a head that is no value.
    */
  private def shared(left: Value, right: Value)(chosen: ParallelSet => Decodings): Decodings =
    def side(term: Value): Decodings =
      heads(term).flatMap(sideHeads =>
        Computation.traversed(sideHeads)(chosen).map(_.flatten.distinct.collect { case value @ Decoding.Decoded(_) => value })
      )
    side(left).flatMap(leftDecodings =>
      if leftDecodings.isEmpty then Computation.pure(Vector.empty)
      else side(right).map(rightDecodings => leftDecodings.filter(rightDecodings.contains))
    )

  /** `chosen_boolean(Chosen, ZeroHead, SuccessorHead, Decoding)`. */
  private def chosenBoolean(chosen: ParallelSet): Decodings =
    chosen.view match
      case ParallelView.Single(head) if head == zeroMarker =>
        Computation.pure(Vector(Decoding.Decoded("boolean(true)")))
      case ParallelView.Single(head) if head == successorMarker =>
        Computation.pure(Vector(Decoding.Decoded("boolean(false)")))
      case ParallelView.Several(left, right) => shared(left, right)(chosenBoolean)
      case _                                 => Computation.pure(Vector(Decoding.Failure("not_a_boolean")))

  /** `observed_natural(Head, ZeroHead, SuccessorHead, Accumulated, Decoding)`. */
  private def observedNatural(term: Value, accumulated: Int): Decodings =
    heads(appliedToMarkers(term)).flatMap(choices =>
      if choices.isEmpty then Computation.pure(Vector(Decoding.Failure("not_a_natural")))
      else Computation.traversed(choices)(chosenNatural(_, accumulated)).map(_.flatten)
    )

  /** Whether the head is the successor marker applied to one argument, the
    * head a Scott successor answers the markers with: the marker's code with
    * the marker's holes but the first.
    */
  private def successorOfAPredecessor(chosen: Head): Boolean = (chosen, successorMarker) match
    case (Head.Lambda(code, holes, _), Head.Lambda(markerCode, markerHoles, _)) =>
      code == markerCode && holes == markerHoles.tail
    case _ => false

  /** `chosen_natural(Chosen, ZeroHead, SuccessorHead, Accumulated, Decoding)`.
    * Only the successor marker applied to a predecessor is applied four
    * times to answer the predecessor; any other head is no natural, so that
    * the decode ends on a head that would answer itself again after the six
    * arguments, such as `λb. λc. c`, and on top's `λx. top ∥ x`.
    */
  private def chosenNatural(chosen: ParallelSet, accumulated: Int): Decodings =
    chosen.view match
      case ParallelView.Single(head) if head == zeroMarker =>
        Computation.pure(Vector(Decoding.Decoded(s"natural($accumulated)")))
      case ParallelView.Several(left, right) => shared(left, right)(chosenNatural(_, accumulated))
      case ParallelView.Single(head) if head != successorMarker && successorOfAPredecessor(head) =>
        val zero = zeroMarker.value
        heads(Value.Apply(Value.Apply(Value.Apply(Value.Apply(head.value, zero), zero), zero), zero))
          .flatMap(predecessors =>
            if predecessors.isEmpty then Computation.pure(Vector(Decoding.Failure("not_a_natural")))
            else
              Computation
                .traversed(predecessors)(predecessor => observedNatural(valueOf(predecessor), accumulated + 1))
                .map(_.flatten)
          )
      case _ => Computation.pure(Vector(Decoding.Failure("not_a_natural")))

  /** `certificate_observed(Head, Name, CertificateTerm, Decoding)`. */
  private def certificateObserved(set: ParallelSet, name: String, certificateTerm: DeBruijnTerm): Decodings =
    set.view match
      case ParallelView.Several(left, right) => shared(left, right)(certificateObserved(_, name, certificateTerm))
      case ParallelView.Single(head) =>
        Computation.pure(
          if ContestAnswers.headTerm(head) == certificateTerm then Vector(Decoding.Decoded(s"certificate($name)"))
          else Vector(Decoding.Decoded(s"not_the_certificate($name)"))
        )
      case ParallelView.Bottom => throw IllegalStateException("the plain evaluator answers no empty parallel set")
