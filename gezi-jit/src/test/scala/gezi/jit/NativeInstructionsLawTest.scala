package gezi.jit

import scala.annotation.tailrec

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import gezi.frontend.Term
import gezi.frontend.TermOf
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.hotspot.baselines.BaselineCaches
import gezi.ir.{Configured, NoFacts, Pure}
import gezi.saturation.StopSignal
import gezi.strategies.BaselineRounds
import gezi.strategies.DispatchStrategies
import gezi.strategies.StrategyTesting

/** The law of the native-bound leaves: a term that a knowledge file's `natives`
  * binds to a native is among the leaves of the round, and stays an instruction
  * through the native route's schedule and the refinement, so that the JIT
  * finds it where the program wrote it and calls the native there. Its purpose
  * is to catch a native-bound term that a round opens or the refinement
  * unfolds, the defect of JitNativesTest's natural_even cases before such terms
  * were leaves: even's application was β-contracted, and natural_even was never
  * called.
  *
  * The inputs: a native-bound term of the natives-on library
  * (`NativesTesting.nativesOn`) applied to a closed term of
  * `HoasGenerators.openTermOver` of at most six nodes over the native route
  * library's terms other than the native-bound ones, so that an occurrence in
  * the refined output comes from the application the program wrote.
  */
class NativeInstructionsLawTest extends GeneratedProperties:

  given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of NativeInstructionsLawTest, "a native-bound term applied stays an instruction in the refined output", takes 9.270 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(15, "s")

  /** Measured on 2026-11-14: `NativesTesting.nativesOn` with `BackendFacts`
    * take 6.2 s, and the native route schedule of 600 instances about 5.3 s;
    * they are not charged to a test.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(
      _ => library,
      _ => facts,
      _ => nativeBound,
      _ => schedule,
      _ => argumentLeaves
    )

  private lazy val library = NativesTesting.nativesOn
  private lazy val facts = BackendFacts.of(library)

  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encoding.type = encoding

  /** The terms bound by the library's `natives`, each once. */
  private lazy val nativeBound: Vector[Pure] =
    library.index.nativeBound.map(_.instruction).distinct

  private def boundTerm(pure: Pure): Configured[encoding.type] =
    Configured.fromPure(encoding)(pure)

  /** The schedule of JitNativesTest, each round within its 600 instances. */
  private lazy val schedule =
    BaselineRounds.nativeRouteSchedule[encoding.type](
      library,
      StrategyTesting.round("prolog_backend_type_check"),
      600
    )

  /** The leaves of the generated programs: the native route's library terms,
    * closed terms of no facts, but the native-bound ones.
    */
  private lazy val argumentLeaves: Vector[TermOf[Configured[NoFacts.type]]] =
    JitTesting.nativeRouteLeaves[NoFacts.type](using NoFacts).filter {
      case Term.Closed(instruction) =>
        !nativeBound.exists(pure =>
          Configured.same(Configured.fromPure(NoFacts)(pure), instruction)(using
            NoFacts
          )
        )
      case _ => true
    }

  /** Whether the instruction occurs in the term, not looking under a leaf other
    * than the instruction: a library term's body is not the program's.
    */
  private def occurs(
      instruction: Configured[encoding.type],
      term: Configured[encoding.type]
  ): Boolean =
    @tailrec
    def from(
        pending: List[Configured[encoding.type]],
        seen: Set[Configured[encoding.type]]
    ): Boolean = pending match
      case Nil          => false
      case head :: rest =>
        if Configured.same(head, instruction) then true
        else if seen.contains(head) || encoding.operations.leaves.contains(head)
        then from(rest, seen)
        else from(head.layer.children.toList ++ rest, seen + head)
    from(List(term), Set.empty)

  test("every term the natives bind is a leaf") {
    assert(
      nativeBound.nonEmpty,
      "the natives-on library binds no term to a native"
    )
    assertEquals(
      nativeBound.filterNot(facts.leaves.contains),
      Vector.empty[Pure]
    )
  }

  stoppableProperty(
    "a native-bound term applied stays an instruction in the refined output",
    _.copy(testLimit = SuccessCount(10))
  ) { stopped =>
    for
      bound <- Gen
        .int(Range.constant(0, nativeBound.size - 1))
        .map(nativeBound)
        .forAll
      nodes <- Gen.int(Range.linear(1, 6)).forAll
      open <- HoasGenerators.openTermOver(0, nodes, argumentLeaves).forAll
    yield
      val program =
        Term.closed(Configured.fromPure(NoFacts)(bound))(open(Vector.empty))
      val inputWithoutFacts = StrategyTesting.programInput(library, program)
      val input = encoding.crossedAllFromNoFacts(Vector(inputWithoutFacts))(
        inputWithoutFacts
      )
      val Dispatched(refined, _, _) =
        StrategyDispatch.dispatched[encoding.type](
          CompilationStrategy(DispatchStrategies.fallback, schedule),
          input,
          encoding,
          BaselineCaches.provider(),
          StopSignal.completedWith(stopped)
        )
      Result.assert(occurs(boundTerm(bound), refined)).log(s"refined: $refined")
  }
