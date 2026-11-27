package com.yang_bo.gezi.interfacelaws

import com.yang_bo.gezi.ir.Configured
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.*
import com.yang_bo.gezi.frontend.TermOf
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.hotspot.baselines.BaselineCaches
import com.yang_bo.gezi.jit.BackendChecks
import com.yang_bo.gezi.jit.BackendFacts
import com.yang_bo.gezi.jit.ClosureBackend
import com.yang_bo.gezi.jit.CompilationStrategy
import com.yang_bo.gezi.jit.ConvertedTermConstruction
import com.yang_bo.gezi.jit.DispatchMode
import com.yang_bo.gezi.jit.Jit
import com.yang_bo.gezi.jit.JitConfiguration
import com.yang_bo.gezi.jit.NativeBlockMechanism
import com.yang_bo.gezi.jit.NoNativeBlocks
import com.yang_bo.gezi.jit.PredicatePerCode
import com.yang_bo.gezi.jit.StrategyDispatch
import com.yang_bo.gezi.jit.NativesTesting.normalFormLimit
import com.yang_bo.gezi.jit.NativesTesting.normalFormsSpent
import com.yang_bo.gezi.strategies.BaselineModules
import com.yang_bo.gezi.strategies.BaselineRounds
import com.yang_bo.gezi.strategies.CountedExtractor
import com.yang_bo.gezi.strategies.NativeRouteCompilation
import com.yang_bo.gezi.strategies.RoundModules
import com.yang_bo.gezi.strategies.StandardIndexer
import com.yang_bo.gezi.strategies.StandardSaturator
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.StandardLibrary
import com.yang_bo.gezi.strategies.DispatchStrategies
import com.yang_bo.gezi.jit.JitTesting
import com.yang_bo.gezi.knowledgereading.KnowledgeReading
import com.yang_bo.gezi.standardlibrary.LibraryFiles
import com.yang_bo.gezi.strategies.Round
import com.yang_bo.gezi.strategies.StrategyTesting
import com.yang_bo.gezi.weakhead.Bounded

/** The laws of the native block interface `NativeBlockMechanism`, run on any
  * implementation: a suite that extends this class with the mechanism checks it
  * ([[com.yang_bo.gezi.interfacelaws]]). On a program compiled by the native route, the
  * baseline JIT with the mechanism's blocks reads the normal forms the JIT
  * without blocks reads; and a reading with them that a budget may stop answers
  * those normal forms or nothing. Its purpose is to catch a block that changes
  * an answer: an elimination that picks the wrong case, a native called on a
  * value that is not of its place, a recursion taken for a call that is not the
  * block's own, or a block that returns a partial value when the budget runs
  * out inside it.
  *
  * The programs are generated recursive functions over the naturals, the shape
  * of `CompiledRunBenchmark`'s count: `fixpoint (λself. λt. t base (λu. step
  * (self u)))` applied to successor^size zero, with the base and the step drawn
  * from closed terms of the library's names, so that the blocks meet
  * eliminations, natives and recursive calls.
  */
abstract class NativeBlockMechanismLaws(mechanism: NativeBlockMechanism)
    extends GeneratedProperties:

  /** The library of the knowledge `NativeBlockMechanismLaws.libraryFile` holds
    * as the one field of its tuple, the nine knowledge files of the compiler
    * directories native_types, native_arithmetic, hindley_milner_unions,
    * native_arithmetic_unions, closure_application, occurrence_erasure,
    * prolog_backend, native_arithmetic_prolog_backend and
    * prolog_backend_shapes, compiled with the backend's checks: the file read
    * by projection under the compilation's reading state and the member
    * compiled after it.
    */
  private lazy val library: StandardLibrary =
    given com.yang_bo.gezi.ir.NoFacts.type = com.yang_bo.gezi.ir.NoFacts
    val root = LibraryFiles.buildRoot
    val (group, afterEntry) = StandardLibrary.entryGroup(
      StandardLibrary.entryTerm(
        root,
        root.resolve(NativeBlockMechanismLaws.libraryFile),
        KnowledgeReading.compilationState
      )
    )
    val knowledge = KnowledgeReading.term(group, Set.empty)
    StandardLibrary.compiled(knowledge, Vector(BackendChecks), afterEntry)._1

  private lazy val facts = BackendFacts.of(library)

  /** The configuration of the laws' terms and JITs: the encoding of the
    * library's backend facts.
    */
  private type E = facts.storageEncoding.type

  private lazy val encoding: E = facts.storageEncoding

  private given E = encoding

  // The laws set up their JITs as an entry does, so they grant the capability here.
  private lazy val storageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()

  /** The schedule of `NativeRouteCompilationTest`'s tests of costs, each round
    * within 20,000 instances, which it measured enough for the count of
    * successor^128 zero: the type check enabling the lemmas of the tests' round
    * `prolog_backend_type_check` (hindley_milner_unions,
    * native_arithmetic_unions and prolog_backend_shapes), the erasure those of
    * the round `occurrence_erasure` (`BaselineRounds.nativeRouteSchedule`).
    */
  private lazy val schedule: Vector[Round[E]] =
    NativeRouteCompilation.nativeRouteSchedule[E](
      encoding.operations.index,
      BaselineRounds
        .lemmas(library, StrategyTesting.round("prolog_backend_type_check")),
      BaselineRounds
        .lemmas(library, StrategyTesting.round("occurrence_erasure")),
      20000,
      RoundModules[E](
        StandardSaturator[E](_),
        CountedExtractor(
          NativeRouteCompilation.extraction,
          BaselineModules.table[E]
        ),
        BaselineRounds.modules.lemmaEncoding,
        StandardIndexer.of[E],
        BaselineRounds.modules.backend,
        BaselineRounds.modules.orientationCompiler,
        ConvertedTermConstruction[E](encoding)(storageAccess)
      )
    )

  private def configuration(
      nativeBlocks: NativeBlockMechanism
  ): JitConfiguration[E] =
    JitConfiguration[E](
      encoding,
      JitConfiguration.defaultBudget,
      PredicatePerCode,
      ClosureBackend,
      DispatchMode.Dispatch(DispatchStrategies.fallback),
      instanceTable = false,
      nativeBlocks = nativeBlocks,
      storageAccess = storageAccess
    )

  private lazy val withoutBlocks = Jit(
    configuration(nativeBlocks = NoNativeBlocks)
  )

  private lazy val withBlocks = Jit(configuration(nativeBlocks = mechanism))

  /** The library terms the generated recursive functions over the naturals are
    * written with, closed instructions read by projection off the JIT tests'
    * fixture file (`JitTesting.libraryTerm`).
    */
  private type Program = TermOf[Configured[E]]

  private lazy val zero: Program = JitTesting.libraryTerm[E]("zero")

  private lazy val successor: Program = JitTesting.libraryTerm[E]("successor")

  private lazy val fixpoint: Program = JitTesting.libraryTerm[E]("fixpoint")

  private lazy val double: Program = JitTesting.libraryTerm[E]("double")

  private def numeral(size: Int): Program =
    (1 to size).foldLeft(zero)((value, _) => successor(value))

  private def bases: Gen[Program] =
    Gen.element1(zero, successor(zero), numeral(3))

  /** The steps, each with the largest size it is drawn at: the normal form is
    * read back as a Scott numeral, so a step that doubles is drawn only up to 5
    * levels (base 3 doubled 5 times is 96), where 24 levels of it read back a
    * numeral of up to 3 · 2^24 layers, and a run drawn so exhausted the test
    * JVM's 256 MB heap (2026-11-02).
    */
  private def steps: Gen[(Program => Program, Int)] =
    Gen.element1(
      (successor(_), 24),
      (value => successor(successor(value)), 24),
      (double(_), 5),
      (value => value, 24)
    )

  private def programs: Gen[Program] =
    for
      (step, largest) <- steps
      size <- Gen.int(Range.linear(0, largest))
      base <- bases
    yield fixpoint(λ(self => λ(t => t(base)(λ(u => step(self(u)))))))(
      numeral(size)
    )

  /** The program compiled by the native route under `fallback`. */
  private def refined(program: Program, stop: StopSignal): Configured[E] =
    StrategyDispatch
      .dispatched[E](
        CompilationStrategy(DispatchStrategies.fallback, schedule),
        StrategyTesting.programInputIn[E](library, program),
        encoding,
        BaselineCaches.provider(),
        stop
      )(using storageAccess)
      .refined

  stoppableProperty(
    "the mechanism's blocks read the normal forms the machine reads",
    _.copy(testLimit = SuccessCount(20))
  ) { stopped =>
    for program <- programs.forAll
    yield
      val compiled = JitTesting.instructionValue(
        refined(program, StopSignal.completedWith(stopped))
      )
      (
        normalFormsSpent(withBlocks, compiled, normalFormLimit).outcome,
        normalFormsSpent(withoutBlocks, compiled, normalFormLimit).outcome
      ) match
        case (Bounded.Finished(blocked), Bounded.Finished(machine)) =>
          Result
            .assert(JitTesting.sameTerms(blocked, machine))
            .log(s"the blocks read $blocked, the machine $machine")
        case (blocked, machine) =>
          Result.failure.log(s"a reading did not finish: $blocked, $machine")
  }

  stoppableProperty(
    "a reading with the mechanism's blocks that a budget stops answers the machine's normal forms or nothing",
    _.copy(testLimit = SuccessCount(20))
  ) { stopped =>
    for
      program <- programs.forAll
      limit <- Gen.long(Range.linear(1L, 4000L)).forAll
    yield
      val compiled = JitTesting.instructionValue(
        refined(program, StopSignal.completedWith(stopped))
      )
      normalFormsSpent(withoutBlocks, compiled, normalFormLimit).outcome match
        case Bounded.Finished(machine) =>
          normalFormsSpent(withBlocks, compiled, limit).outcome match
            case Bounded.Finished(blocked) =>
              Result
                .assert(JitTesting.sameTerms(blocked, machine))
                .log(s"the blocks read $blocked, the machine $machine")
            case _ => Result.success
        case other =>
          Result.failure.log(s"the machine's reading did not finish: $other")
  }

object NativeBlockMechanismLaws:

  /** The fixture file, under Gezi's directory, whose member `knowledge` is the
    * laws' library's knowledge.
    */
  val libraryFile: String =
    "tests/interface_law_fixtures/native_block_mechanism.lambdalattice"
