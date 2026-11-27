package gezi.strategies

import hedgehog.Gen
import hedgehog.Result
import gezi.egraph.Justification
import gezi.egraph.MemoRetention
import gezi.ematching.closures.ClosureCompilation
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.ir.BuiltInRule
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import gezi.orientation.StandardOrientationCompiler
import gezi.saturation.Run
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibraryIndex
import gezi.ir.LemmaIdentifier

/** The laws of the built-in rules being opt-in, δ and β included
  * (`BuiltInRule`): a rule the round does not enable unites nothing, and the
  * same round with it enabled unites what the rule says. The values are closed
  * βη normal forms of the pure calculus (`HoasGenerators.normalForm`), so that
  * no rule but the one under test can unite them.
  */
class BuiltInRuleLawTest extends GeneratedProperties:

  private given NoFacts.type = NoFacts

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of BuiltInRuleLawTest, "without β no union is the β rule's, with β the redex is united with its contractum", takes 5.698 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(10, "s")

  /** The library of the β rule on a program's closures: the lemma of
    * `closure_application` builds the application the β rule reads, and the
    * Prolog backend's preset brings `native_types`, which declares the
    * occurrence roles the front end tags the program's closures by; the
    * knowledge is the one field of
    * tests/library_fixtures/prolog_backend_closure_application.lambdalattice,
    * their choice.
    */
  // Native typing comes through the preset only;
  // closure_application needs native_types' declarations.
  private lazy val closureLibrary =
    StrategyTesting.compiled(
      "tests/library_fixtures/prolog_backend_closure_application.lambdalattice"
    )

  /** The budget of a run, in instances: the inputs below reach their fixed
    * points within a few.
    */
  private val budget = 100

  /** The lemmas of the round of `closure_application`, read once: the round
    * depends on no drawn input, and reading its entry's imports for every draw
    * took the property past munit's 30 seconds.
    */
  private lazy val round = BaselineRounds.lemmas(
    closureLibrary,
    StrategyTesting.round("closure_application")
  )

  /** The library and the round's lemmas, forced before the first test and not
    * charged to it (FailFastSuite).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => closureLibrary, _ => round)

  private def saturated(
      index: StandardLibraryIndex[NoFacts.type],
      lemmas: Vector[LemmaIdentifier],
      rules: Set[BuiltInRule],
      inputs: Vector[Configured[NoFacts.type]],
      stop: StopSignal
  ): Run[NoFacts.type] =
    FixpointEgraph.saturated(
      index,
      inputs,
      SaturationOptions(
        lemmas,
        rules,
        budget,
        BaselineLemmaEncoding,
        ClosureCompilation,
        StandardIndexer.of[gezi.ir.NoFacts.type],
        StandardOrientationCompiler,
        MemoRetention.Kept,
        gezi.ir.TermConstruction(gezi.ir.NoFacts)
      ),
      explained = false,
      stop
    )

  private val term: Gen[Term] = HoasGenerators.normalForm

  /** Purpose: catch a β step worked, or counted, in a round that does not
    * enable the β rule, or one not worked in a round that does: in a round of
    * `closure_application`, whose lemma builds the application the β rule
    * reads, the program `(λx. x N) A` is united with its contractum by a union
    * justified by the β rule (`Justification.Beta`) with `Beta` and by none
    * without it, no β step taken. The contractum is not given as a second
    * program: the front end tags each program's closures by their occurrences,
    * so a closure inside A carries other tags in `A N` than in the reduct, and
    * the two would stay apart with β too. N and A are drawn before the
    * abstraction is built, so that its body is the same term on every
    * conversion.
    */
  stoppableProperty(
    "without β no union is the β rule's, with β the redex is united with its contractum"
  ) { stopped =>
    for
      argument <- term.forAll
      applied <- term.forAll
    yield
      val redex = StrategyTesting.programInput(
        closureLibrary,
        λ(bound => bound(applied))(argument)
      )
      val without = saturated(
        closureLibrary.index,
        round,
        BuiltInRule.beforeOptIn - BuiltInRule.Beta,
        Vector(redex),
        StopSignal.completedWith(stopped)
      )
      val enabled = saturated(
        closureLibrary.index,
        round,
        BuiltInRule.beforeOptIn,
        Vector(redex),
        StopSignal.completedWith(stopped)
      )
      def betaUnions(run: Run[NoFacts.type]): Int =
        run.graph.unions.count(_.justification match
          case Justification.Beta(_) => true
          case _                     => false)
      Result.all(
        List(
          Result
            .diff(betaUnions(without), 0)(_ == _)
            .log("without β, a union is the β rule's"),
          Result
            .diff(without.graph.betaSteps, 0)(_ == _)
            .log("without β, a β step was taken"),
          Result
            .assert(betaUnions(enabled) > 0)
            .log("with β, no union is the β rule's")
        )
      )
  }
