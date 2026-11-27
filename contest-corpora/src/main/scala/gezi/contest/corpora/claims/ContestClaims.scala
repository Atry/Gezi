package gezi.contest.corpora.claims

import gezi.contest.corpora.common.ProblemData

import gezi.weakhead.Mode
import gezi.weakhead.NeutralValue
import gezi.weakhead.NeutralVariable
import gezi.weakhead.Reading
import gezi.ir.Value
import gezi.weakhead.WitnessOutcome
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.ir.{Configured, NativeSpecializer, NoFacts}

/** The corpora are read under no facts. */
private given contestClaimsNoFacts: NoFacts.type = NoFacts

/** A test program of rule 30 with its free variables: `build` is the test, an
  * abstraction `\a. Body`, as a function of its `freeCount` free variables in
  * the order of `contest_claims:free_variables/2` (first occurrence, left to
  * right). A HOAS term is closed by construction, so a Prolog test's free
  * Prolog variables are its parameters here.
  */
final case class OpenTest(
    freeCount: Int,
    build: Vector[ProblemTerm] => ProblemTerm
)

/** How a claim's goal ended (`claims_answered/4`): it succeeded, the setting
  * proves the claim; it failed, finitely, the setting has no proof (not proved,
  * never proved false); or it was stopped by its budget of steps or an
  * exhausted resource, which answers nothing.
  */
enum Ending:
  case Succeeded, Failed, Stopped

  /** The Prolog atom of the ending. */
  def written: String = this match
    case Succeeded => "succeeded"
    case Failed    => "failed"
    case Stopped   => "stopped"

/** One test's answer: its ending and the evaluator steps its reading took
  * (`answer(Ending, Spent)`).
  */
final case class ClaimAnswer(ending: Ending, spent: Long)

/** The judge's witness, `neutral(witness, [])`: a value of the evaluator a
  * closed program cannot name.
  *
  * A neutral value, a free variable, used here as an exception argued at its
  * declaration (`CONTRIBUTING.md`, "Types live only in the term"): the judge's
  * reading of a claim opens the test at values a closed program cannot name.
  */
case object ClaimWitness extends NeutralVariable

/** The neutral value the judge gives a test's free variable of the number (from
  * 1), `neutral(free(Number), [])`.
  *
  * A neutral value, a free variable, used here as an exception argued at its
  * declaration (`CONTRIBUTING.md`, "Types live only in the term"): the judge's
  * reading of a claim opens the test at values a closed program cannot name.
  */
final case class FreeValue(number: Int) extends NeutralVariable

/** The judge of rule 30, the code of the deleted Prolog file (`git show
  * 91b3f11e1^:lambda_jit/corpora/contest_claims.pl`): the tests' roots and
  * their readings on the evaluator.
  *
  * THE JUDGE reads each test once on the weak-head evaluator under `weak_head`
  * or `tabling(weak_head)`, or on the JIT under `Mode.Jit`. The tests of one
  * call of `claimsAnswered` are a SUITE, read one after another with one store
  * and its tables kept from one test to the next (`Reading.witnessReadings`).
  * The root of a test T with free variables y1, ..., yk is the closed program
  * `(\y1. ... \yk. \x0. T x0) n1 ... nk w`, its codes interned, applied to one
  * neutral value per free variable (`FreeValue`) and to the witness
  * (`ClaimWitness`). The claim SUCCEEDS when some head of the reading reads out
  * as the witness, FAILS when the evaluation finishes and none does, and is
  * STOPPED when the reading runs past its budget of steps or out of a resource.
  * A stop is never a verdict: it is neither a success nor a failure. Why a
  * success proves the claim is the Prolog module comment's derivation: R ⊑ H ⊑
  * w for the root R, a head H and the witness w, so the closed test is below
  * the curried identity in ⊑_O. The check is sound and not complete.
  *
  * The budget is a count of evaluator steps, where the Prolog judge counted
  * SWI-Prolog's inferences.
  */
object ContestClaims:

  /** For each test of the suite in order, its answer (`claims_answered/4`):
    * each reading within the limit of steps. Every test's root is built before
    * the first reading. Throws `IllegalArgumentException` with
    * `test_not_an_abstraction` for a test that is not an abstraction, before
    * any test is read.
    */
  def claimsAnswered(
      mode: Mode,
      tests: Vector[OpenTest],
      limit: Long
  ): Vector[ClaimAnswer] =
    val roots = tests.map(testRoot)
    Reading
      .witnessReadings(
        mode,
        roots,
        witness,
        limit,
        gezi.weakhead.ReadingConfiguration.withoutFacts
      )
      .map(reading =>
        val ending = reading.outcome match
          case WitnessOutcome.Found        => Ending.Succeeded
          case WitnessOutcome.NotFound     => Ending.Failed
          case WitnessOutcome.StepLimit    => Ending.Stopped
          case WitnessOutcome.Exhausted(_) => Ending.Stopped
        ClaimAnswer(ending, reading.spent)
      )

  /** The judge's witness as a value. */
  val witness: Value[NoFacts.type] = NeutralValue(ClaimWitness, Vector.empty)

  /** `test_root(Test, Witness, Root)`: the test closed over its free variables
    * as `\y1. ... \yk. \x0. T x0`, interned, applied to one neutral value per
    * free variable and to the witness. Throws `IllegalArgumentException` with
    * `test_not_an_abstraction` when the test is not an abstraction (the user's
    * decision of 2026-09-28, enforced).
    */
  def testRoot(test: OpenTest): Value[NoFacts.type] = testRootIn(NoFacts)(test)

  /** `testRoot` in the configuration of the specializer: the closed test,
    * written with no facts, crossed into it
    * (`NativeSpecializer.crossedAllFromNoFacts`), then applied to the neutral
    * values and the witness there, so that no neutral value is crossed.
    */
  def testRootIn[C <: NativeSpecializer & Singleton](specializer: C)(
      test: OpenTest
  ): Value[C] =
    given C = specializer
    val closed = curried(
      test.freeCount,
      Vector.empty,
      free =>
        test.build(free) match
          case abstraction @ Term.Abstraction(_) =>
            λ(argument => abstraction(argument))
          case other =>
            throw IllegalArgumentException(s"test_not_an_abstraction: $other")
    )
    val written = Defunctionalization.thunkInstruction[NoFacts.type](
      closed.deBruijnTerm(Map.empty)
    )(using NoFacts)
    val instruction: Configured[C] =
      (specializer: C).crossedAllFromNoFacts(Vector(written))(written)
    val applied = (1 to test.freeCount).foldLeft(Value.of(instruction))(
      (function, number) =>
        Value.Apply(function, NeutralValue[C](FreeValue(number), Vector.empty))
    )
    Value.Apply(applied, NeutralValue[C](ClaimWitness, Vector.empty))

  /** `test_program(Test, Program, Expected)`: the test as a closed program,
    * `\y1. ... \yk. Test`, its free variables curried in their order, and the
    * curried identity `\y1. ... \yk. \a. a` it is asked for.
    */
  def testProgram(test: OpenTest): (ProblemTerm, ProblemTerm) =
    (
      curried(test.freeCount, Vector.empty, test.build),
      identityUnder(test.freeCount)
    )

  private def curried(
      remaining: Int,
      bound: Vector[ProblemTerm],
      build: Vector[ProblemTerm] => ProblemTerm
  ): ProblemTerm =
    if remaining == 0 then build(bound)
    else λ(variable => curried(remaining - 1, bound :+ variable, build))

  /** `identity_under(Count, \a. a)`. */
  def identityUnder(count: Int): ProblemTerm =
    (1 to count).foldLeft(λ(argument => argument))((term, _) => λ(_ => term))
