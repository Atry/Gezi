package gezi.jit

import scala.annotation.tailrec

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.hotspot.baselines.BaselineCaches
import gezi.ir.Instruction
import gezi.saturation.StopSignal
import gezi.strategies.BaselineRounds
import gezi.strategies.DispatchStrategies
import gezi.strategies.StrategyTesting

/** The law of the native-bound leaves: a term that a knowledge file's `natives` binds to a native is among
  * the leaves of the round, and stays an instruction through the native route's
  * schedule and the refinement, so that the JIT finds it where the program
  * wrote it and calls the native there. Its purpose is to catch a
  * native-bound term that a round opens or the refinement unfolds, the
  * defect of JitNativesTest's natural_even cases before such terms were leaves: even's
  * application was β-contracted, and natural_even was never called.
  *
  * The inputs: a native-bound term of the natives-on library
  * (`NativesTesting.nativesOn`) applied to a closed term of
  * `HoasGenerators.openTermOver` of at most six nodes over the native route
  * library's terms other than the native-bound ones, so that an occurrence
  * in the refined output comes from the application the program wrote.
  */
class NativeInstructionsLawTest extends GeneratedProperties:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of NativeInstructionsLawTest, "a native-bound term applied stays an instruction in the refined output", takes 9.270 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(15, "s")

  /** Measured on 2026-11-14: `NativesTesting.nativesOn` with
    * `BackendFacts` take 6.2 s, and the native route schedule of 600
    * instances about 5.3 s; they are not charged to a test.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => library, _ => facts, _ => nativeBound, _ => schedule, _ => argumentLeaves)

  private lazy val library = NativesTesting.nativesOn

  private lazy val facts = BackendFacts.of(library)

  /** The terms bound by the library's `natives`, each once. */
  private lazy val nativeBound: Vector[Instruction] = library.index.nativeBound.map(_.instruction).distinct

  /** The schedule of JitNativesTest, each round within its 600 instances. */
  private lazy val schedule =
    BaselineRounds.nativeRouteSchedule(library, StrategyTesting.round("prolog_backend_type_check"), 600)

  private lazy val argumentLeaves: Vector[Term] =
    JitTesting.nativeRouteLeaves.filter {
      case Term.Closed(instruction) => !nativeBound.contains(instruction)
      case _                        => true
    }

  /** Whether the instruction occurs in the term, not looking under a leaf other
    * than the instruction: a library term's body is not the program's.
    */
  private def occurs(instruction: Instruction, term: Instruction): Boolean =
    @tailrec
    def from(pending: List[Instruction], seen: Set[Instruction]): Boolean = pending match
      case Nil => false
      case head :: rest =>
        if head == instruction then true
        else if seen.contains(head) || facts.leaves.contains(head) then from(rest, seen)
        else from(head.layer.children.toList ++ rest, seen + head)
    from(List(term), Set.empty)

  test("every term the natives bind is a leaf") {
    assert(nativeBound.nonEmpty, "the natives-on library binds no term to a native")
    assertEquals(nativeBound.filterNot(facts.leaves.contains), Vector.empty[Instruction])
  }

  stoppableProperty("a native-bound term applied stays an instruction in the refined output", _.copy(testLimit = SuccessCount(10))) { stopped =>
    for
      bound <- Gen.int(Range.constant(0, nativeBound.size - 1)).map(nativeBound).forAll
      nodes <- Gen.int(Range.linear(1, 6)).forAll
      open <- HoasGenerators.openTermOver(0, nodes, argumentLeaves).forAll
    yield
      val program = Term.closed(bound)(open(Vector.empty))
      val input = StrategyTesting.programInput(library, program)
      val Dispatched(refined, _, _) = StrategyDispatch.dispatched(
        CompilationStrategy(DispatchStrategies.fallback, schedule),
        input,
        facts,
        BaselineCaches.provider(),
        StopSignal.completedWith(stopped)
      )
      Result.assert(occurs(bound, refined)).log(s"refined: $refined")
  }
