package gezi.interfacelaws

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import gezi.frontend.Term
import gezi.frontend.Term.*
import gezi.generatedinputs.GeneratedProperties
import gezi.hotspot.baselines.BaselineCaches
import gezi.ir.Instruction
import gezi.jit.BackendChecks
import gezi.jit.BackendFacts
import gezi.jit.ClosureBackend
import gezi.jit.CompilationStrategy
import gezi.jit.DispatchMode
import gezi.jit.Jit
import gezi.jit.JitConfiguration
import gezi.jit.NativeBlockMechanism
import gezi.jit.NoNativeBlocks
import gezi.jit.PredicatePerCode
import gezi.jit.StrategyDispatch
import gezi.jit.NativesTesting.normalFormLimit
import gezi.jit.NativesTesting.normalFormsSpent
import gezi.strategies.BaselineRounds
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibrary
import gezi.strategies.DispatchStrategies
import gezi.jit.JitTesting
import gezi.knowledgereading.KnowledgeReading
import gezi.standardlibrary.LibraryFiles
import gezi.strategies.Round
import gezi.strategies.StrategyTesting
import gezi.weakhead.Bounded
import gezi.weakhead.Mode
import gezi.weakhead.Value

/** The laws of the native block interface `NativeBlockMechanism`, run on any
  * implementation: a suite that extends this class with the mechanism checks
  * it ([[gezi.interfacelaws]]). On a
  * program compiled by the native route, the baseline JIT with the
  * mechanism's blocks reads the normal forms the JIT without blocks reads;
  * and a reading with them that a budget may stop answers those normal forms
  * or nothing.
  * Its purpose is to catch a block that changes an answer: an elimination
  * that picks the wrong case, a native called on a value that is not of its
  * place, a recursion taken for a call that is not the block's own, or a
  * block that returns a partial value when the budget runs out inside it.
  *
  * The programs are generated recursive functions over the naturals, the
  * shape of `CompiledRunBenchmark`'s count: `fixpoint (λself. λt. t base
  * (λu. step (self u)))` applied to successor^size zero, with the base and
  * the step drawn from closed terms of the library's names, so that the
  * blocks meet eliminations, natives and recursive calls.
  */
abstract class NativeBlockMechanismLaws(mechanism: NativeBlockMechanism) extends GeneratedProperties:


  /** The library of the knowledge `NativeBlockMechanismLaws.libraryFile` holds as the one field of its tuple,
    * the nine knowledge files of the compiler directories native_types,
    * native_arithmetic, hindley_milner_unions, native_arithmetic_unions,
    * closure_application, occurrence_erasure, prolog_backend,
    * native_arithmetic_prolog_backend and prolog_backend_shapes, compiled
    * with the backend's checks: the file read by projection under the
    * compilation's reading state and the member compiled after it.
    */
  private lazy val library: StandardLibrary =
    val root = LibraryFiles.buildRoot
    val (group, afterEntry) = StandardLibrary.entryGroup(
      StandardLibrary.entryTerm(root, root.resolve(NativeBlockMechanismLaws.libraryFile), KnowledgeReading.compilationState)
    )
    val knowledge = KnowledgeReading.term(group, Set.empty)
    StandardLibrary.compiled(knowledge, Vector(BackendChecks), afterEntry)._1

  private lazy val facts = BackendFacts.of(library)

  /** The schedule of `NativeRouteCompilationTest`'s tests of costs, each
    * round within 20,000 instances, which it measured enough for the count
    * of successor^128 zero: the type check enabling the lemmas of the tests'
    * round `prolog_backend_type_check` (hindley_milner_unions,
    * native_arithmetic_unions and prolog_backend_shapes), the erasure those
    * of the round `occurrence_erasure` (`BaselineRounds.nativeRouteSchedule`).
    */
  private lazy val schedule: Vector[Round] =
    BaselineRounds.nativeRouteSchedule(library, StrategyTesting.round("prolog_backend_type_check"), 20000)

  private def configuration(nativeBlocks: NativeBlockMechanism): JitConfiguration =
    JitConfiguration(
      facts,
      JitConfiguration.defaultBudget,
      PredicatePerCode,
      ClosureBackend,
      DispatchMode.Dispatch(DispatchStrategies.fallback),
      instanceTable = false,
      nativeBlocks = nativeBlocks
    )

  private lazy val withoutBlocks = Jit(configuration(nativeBlocks = NoNativeBlocks))

  private lazy val withBlocks = Jit(configuration(nativeBlocks = mechanism))

  /** The library terms the generated recursive functions over the naturals
    * are written with, closed instructions read by projection off the JIT
    * tests' fixture file (`JitTesting.libraryTerm`).
    */
  private lazy val zero: Term = JitTesting.libraryTerm("zero")

  private lazy val successor: Term = JitTesting.libraryTerm("successor")

  private lazy val fixpoint: Term = JitTesting.libraryTerm("fixpoint")

  private lazy val double: Term = JitTesting.libraryTerm("double")

  private def numeral(size: Int): Term = (1 to size).foldLeft(zero)((value, _) => successor(value))

  private val bases: Gen[Term] = Gen.element1(zero, successor(zero), numeral(3))

  /** The steps, each with the largest size it is drawn at: the normal form
    * is read back as a Scott numeral, so a step that doubles is drawn only
    * up to 5 levels (base 3 doubled 5 times is 96), where 24 levels of it
    * read back a numeral of up to 3 · 2^24 layers, and a run drawn so
    * exhausted the test JVM's 256 MB heap (2026-11-02).
    */
  private val steps: Gen[(Term => Term, Int)] =
    Gen.element1((successor(_), 24), (value => successor(successor(value)), 24), (double(_), 5), (value => value, 24))

  private val programs: Gen[Term] =
    for
      (step, largest) <- steps
      size <- Gen.int(Range.linear(0, largest))
      base <- bases
    yield fixpoint(λ(self => λ(t => t(base)(λ(u => step(self(u)))))))(numeral(size))

  /** The program compiled by the native route under `fallback`. */
  private def refined(program: Term, stop: StopSignal): Instruction =
    StrategyDispatch
      .dispatched(
        CompilationStrategy(DispatchStrategies.fallback, schedule),
        StrategyTesting.programInput(library, program),
        facts,
        BaselineCaches.provider(),
        stop
      )
      .refined

  stoppableProperty("the mechanism's blocks read the normal forms the machine reads", _.copy(testLimit = SuccessCount(20))) { stopped =>
    for program <- programs.forAll
    yield
      val compiled = refined(program, StopSignal.completedWith(stopped))
      (
        normalFormsSpent(Mode.Jit(withBlocks), compiled, normalFormLimit).outcome,
        normalFormsSpent(Mode.Jit(withoutBlocks), compiled, normalFormLimit).outcome
      ) match
        case (Bounded.Finished(blocked), Bounded.Finished(machine)) => Result.diff(blocked, machine)(_ == _)
        case (blocked, machine)                                     => Result.failure.log(s"a reading did not finish: $blocked, $machine")
  }

  stoppableProperty("a reading with the mechanism's blocks that a budget stops answers the machine's normal forms or nothing", _.copy(testLimit = SuccessCount(20))) { stopped =>
    for
      program <- programs.forAll
      limit <- Gen.long(Range.linear(1L, 4000L)).forAll
    yield
      val compiled = refined(program, StopSignal.completedWith(stopped))
      normalFormsSpent(Mode.Jit(withoutBlocks), compiled, normalFormLimit).outcome match
        case Bounded.Finished(machine) =>
          normalFormsSpent(Mode.Jit(withBlocks), compiled, limit).outcome match
            case Bounded.Finished(blocked) => Result.diff(blocked, machine)(_ == _)
            case _                         => Result.success
        case other => Result.failure.log(s"the machine's reading did not finish: $other")
  }

object NativeBlockMechanismLaws:

  /** The fixture file, under Gezi's directory, whose member
    * `knowledge` is the laws' library's knowledge.
    */
  val libraryFile: String = "tests/interface_law_fixtures/native_block_mechanism.lambdalattice"
