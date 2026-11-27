package gezi.weakhead

import gezi.ir.NoFacts
import gezi.ir.Configured
import gezi.ir.Value
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.frontend.Term.*
import gezi.ir.{Configured, NativeSpecializer}

/** How the judge's claim on one test ended. */
enum Ending:
  case Succeeded
  case Failed
  case Stopped

/** The witness the judge applies a test to, the Prolog judge's
  * `neutral(witness, [])`: a value a closed program cannot name.
  *
  * A neutral value, a free variable (`CONTRIBUTING.md`, "Types live only in the
  * term"), left as it is after review: the judge's reading is the contest's
  * rule for reading an output, kept as `ContestClaims.ClaimWitness` is.
  */
case object JudgeWitness extends NeutralVariable

/** The value an intended head decodes to. */
enum Intended:
  case Truth(value: Boolean)
  case Natural(value: Int)

/** The contest's verdict on a reading, or that the reading or the decode
  * stopped before it could be given.
  */
enum Verdict:

  /** The decodings are exactly the intended value. */
  case Matches

  /** The reading finished with other heads, or its heads decode otherwise. */
  case Differs

  /** A head is no value of the kind (`not_a_boolean`, `not_a_natural`). */
  case DecodeFailure(reason: String)

  /** The decode ran past its budget: no verdict (the Prolog verdict's
    * `decode_failure(inference_limit)`).
    */
  case DecodeLimitReached

  /** The reading ran past its budget or out of a resource: no verdict (the
    * Prolog verdict said `differs`; a stop is no answer).
    */
  case ReadingStopped(outcome: ReadingOutcome)

/** The judge and the verdict that `reading.plt` reads, ported as test helpers
  * in the front end's HOAS: of the deleted Prolog file (`git show
  * 91b3f11e1^:lambda_jit/corpora/contest_claims.pl`), `claims_answered/4` for
  * tests with no free variable (a HOAS term has none); of the deleted Prolog
  * file (`git show 91b3f11e1^:lambda_jit/corpora/contest_answers.pl`),
  * `verdict/5` for an intended head that is a boolean or a natural. The module
  * `corpora` ports them whole.
  */
object Judge:

  given NoFacts.type = NoFacts

  /** For each test of the suite in order, its ending and the steps its reading
    * took (claims_answered/4): a reading past its budget or out of a resource
    * ends `Stopped`, never `Failed`. The root of a test T is the closed program
    * \x0. T x0, interned, applied to the witness; the suite's readings share
    * one store and its tables (`Reading.witnessReadings`).
    */
  def claimsAnswered(
      mode: Mode,
      tests: Vector[Term],
      limit: Long
  ): Vector[(Ending, Long)] =
    val roots = tests.map { test =>
      assert(
        test.isInstanceOf[Term.Abstraction],
        "a test is an abstraction (test_not_an_abstraction)"
      )
      val program = Defunctionalization.thunkInstruction[NoFacts.type](
        λ(argument => test(argument)).deBruijnTerm(Map.empty)
      )
      Value.Apply(Value.of(program), witness)
    }
    Reading
      .witnessReadings(
        mode,
        roots,
        witness,
        limit,
        ReadingConfiguration.withoutFacts
      )
      .map(reading =>
        val ending = reading.outcome match
          case WitnessOutcome.Found        => Ending.Succeeded
          case WitnessOutcome.NotFound     => Ending.Failed
          case WitnessOutcome.StepLimit    => Ending.Stopped
          case WitnessOutcome.Exhausted(_) => Ending.Stopped
        (ending, reading.spent)
      )

  private val witness: Value[NoFacts.type] =
    NeutralValue(JudgeWitness, Vector.empty)

  /** The decode's own budget, the Prolog verdict's `decode_limits(limits(10,
    * 256, 256))`: 10 seconds as a budget of steps.
    */
  val decodeLimit: Long = Reading.budgetSteps(10)

  /** The contest's verdict on a reading whose intended answer is a head of the
    * value (verdict/5 with `head`): every head is applied to two markers and
    * evaluated under weak_head, every head of that taken; a boolean chooses one
    * marker; a natural answers the zero marker or an abstraction that, applied
    * four times, answers its predecessor, decoded again; a parallel is read
    * out, each side observed whole, its decodings those the two sides share.
    * `Matches` when the set of decodings is exactly the intended value.
    */
  def verdict(intended: Intended, outcome: ReadingOutcome): Verdict =
    outcome match
      case ReadingOutcome.Heads(heads) if heads.nonEmpty =>
        val (zeroMarker, successorMarker) = markers
        val decodings = Computation
          .traversed(heads)(set =>
            observedDecodings(intended, set, zeroMarker, successorMarker)
          )
          .map(_.flatten.distinct)
          .result(
            ReadingState.fresh(
              decodeLimit,
              gezi.weakhead.ReadingConfiguration.withoutFacts
            )
          )
        decodings match
          case Computed.Stopped(_)     => Verdict.DecodeLimitReached
          case Computed.Done(found, _) =>
            found.collectFirst { case Left(reason) => reason } match
              case Some(reason) => Verdict.DecodeFailure(reason)
              case None         =>
                if found == Vector(Right(intended)) then Verdict.Matches
                else Verdict.Differs
      case ReadingOutcome.Heads(_) => Verdict.Differs
      case stopped @ (ReadingOutcome.StepLimit | ReadingOutcome.Exhausted(_)) =>
        Verdict.ReadingStopped(stopped)

  /** `\a.\b.\c. c` and `\p.\a.\b.\c.\d. p` as heads. */
  private def markers: (Head[NoFacts.type], Head[NoFacts.type]) =
    val zero = DeBruijnTerm.Lambda(
      DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0)))
    )
    val successor = DeBruijnTerm.Lambda(
      DeBruijnTerm.Lambda(
        DeBruijnTerm.Lambda(
          DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(4)))
        )
      )
    )
    val zeroValue = Values.ofInstruction(
      Defunctionalization.thunkInstruction(zero)(using gezi.ir.NoFacts),
      Set.empty
    )
    val successorValue = Values.ofInstruction(
      Defunctionalization.thunkInstruction(successor)(using gezi.ir.NoFacts),
      Set.empty
    )
    (asHead(zeroValue), asHead(successorValue))

  private def asHead[C <: NativeSpecializer & Singleton](value: Value[C])(using
      C
  ): Head[C] = value match
    case Value.Thunk(code, holes, fillings) if holes.nonEmpty =>
      Head.Lambda(code, holes, fillings)
    case other =>
      throw IllegalStateException(s"a marker is a lambda, not $other")

  private type Decoding = Either[String, Intended]

  private def heads[C <: NativeSpecializer & Singleton](term: Value[C])(using
      C
  ) = WeakHead.heads(Mode.WeakHead, term).collected

  /** The parallel set as a value. The judge runs the plain evaluator, which
    * answers no empty parallel set.
    */
  private def valueOf[C <: NativeSpecializer & Singleton](
      set: ParallelSet[C]
  )(using C): Value[C] =
    set
      .value(summon[C])
      .getOrElse(
        throw IllegalStateException(
          "the plain evaluator answers no empty parallel set"
        )
      )

  private def observedDecodings(
      intended: Intended,
      set: ParallelSet[NoFacts.type],
      zeroMarker: Head[NoFacts.type],
      successorMarker: Head[NoFacts.type]
  ): Computation[ReadingState[NoFacts.type], Vector[Decoding]] =
    intended match
      case Intended.Truth(_) =>
        heads(
          Value.Apply(
            Value.Apply(valueOf(set), zeroMarker.value),
            successorMarker.value
          )
        ).flatMap(choices =>
          if choices.isEmpty then
            Computation.pure(Vector(Left("not_a_boolean")))
          else
            Computation
              .traversed(choices)(chosenBoolean(_, zeroMarker, successorMarker))
              .map(_.flatten)
        )
      case Intended.Natural(_) =>
        observedNatural(valueOf(set), zeroMarker, successorMarker, 0)

  private def chosenBoolean(
      chosen: ParallelSet[NoFacts.type],
      zeroMarker: Head[NoFacts.type],
      successorMarker: Head[NoFacts.type]
  ): Computation[ReadingState[NoFacts.type], Vector[Decoding]] =
    chosen.view(NoFacts) match
      case ParallelView.Single(head) if head == zeroMarker =>
        Computation.pure(Vector(Right(Intended.Truth(true))))
      case ParallelView.Single(head) if head == successorMarker =>
        Computation.pure(Vector(Right(Intended.Truth(false))))
      case ParallelView.Several(left, right) =>
        def side(term: Value[NoFacts.type]) =
          heads(term).flatMap(sideHeads =>
            Computation
              .traversed(sideHeads)(
                chosenBoolean(_, zeroMarker, successorMarker)
              )
              .map(_.flatten.distinct)
          )
        for
          leftDecodings <- side(left)
          rightDecodings <- side(right)
        yield leftDecodings.filter(rightDecodings.contains)
      case _ => Computation.pure(Vector(Left("not_a_boolean")))

  private def observedNatural[C <: NativeSpecializer & Singleton](
      term: Value[C],
      zeroMarker: Head[C],
      successorMarker: Head[C],
      accumulated: Int
  )(using C): Computation[ReadingState[C], Vector[Decoding]] =
    heads(
      Value.Apply(Value.Apply(term, zeroMarker.value), successorMarker.value)
    ).flatMap(choices =>
      if choices.isEmpty then Computation.pure(Vector(Left("not_a_natural")))
      else
        Computation
          .traversed(choices)(
            chosenNatural(_, zeroMarker, successorMarker, accumulated)
          )
          .map(_.flatten)
    )

  private def chosenNatural(
      chosen: ParallelSet[NoFacts.type],
      zeroMarker: Head[NoFacts.type],
      successorMarker: Head[NoFacts.type],
      accumulated: Int
  ): Computation[ReadingState[NoFacts.type], Vector[Decoding]] =
    chosen.view(NoFacts) match
      case ParallelView.Single(head) if head == zeroMarker =>
        Computation.pure(Vector(Right(Intended.Natural(accumulated))))
      case ParallelView.Single(head) if head == successorMarker =>
        Computation.pure(Vector(Left("not_a_natural")))
      case ParallelView.Several(left, right) =>
        def side(term: Value[NoFacts.type]) =
          heads(term).flatMap(sideHeads =>
            Computation
              .traversed(sideHeads)(
                chosenNatural(_, zeroMarker, successorMarker, accumulated)
              )
              .map(_.flatten.distinct)
          )
        for
          leftDecodings <- side(left)
          rightDecodings <- side(right)
        yield leftDecodings.filter(rightDecodings.contains)
      case ParallelView.Single(head) =>
        val zero = zeroMarker.value
        heads(
          Value.Apply(
            Value.Apply(Value.Apply(Value.Apply(head.value, zero), zero), zero),
            zero
          )
        )
          .flatMap(predecessors =>
            if predecessors.isEmpty then
              Computation.pure(Vector(Left("not_a_natural")))
            else
              Computation
                .traversed(predecessors)(predecessor =>
                  observedNatural(
                    valueOf(predecessor),
                    zeroMarker,
                    successorMarker,
                    accumulated + 1
                  )
                )
                .map(_.flatten)
          )
      case ParallelView.Bottom() =>
        Computation.pure(Vector(Left("not_a_natural")))
