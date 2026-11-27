package gezi.backendcomparison

import hedgehog.Result
import hedgehog.core.SuccessCount
import gezi.ematching.closures.ClosureCompilation
import gezi.ematching.indexing.Indexing
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.GeneratedStore
import gezi.generatedinputs.OrientationGenerators
import gezi.generatedinputs.StandInStorages
import gezi.generatedinputs.StoreGenerators
import gezi.ir.BuiltInRule
import gezi.ir.Pattern
import gezi.orientation.Orientation
import gezi.orientation.Orientations
import gezi.saturation.End
import gezi.saturation.Saturation
import gezi.saturation.StopSignal

/** Laws of the saturation's fixed point, on generated stores and orientations
  * over them (`StoreGenerators`, `OrientationGenerators`): (1) the fixed point
  * is one least fixed point, so the saturation of the store's instructions
  * under the orientations reaches the same form (`FixedPoint.form`) whatever
  * the order of the orientations and of the inputs, when both orders reach a
  * fixed point within the budget, which the stores without thunks
  * (`StoreGenerators.storeWithoutThunks`) do by construction: with no β redex,
  * every instance the budget counts joins two classes (an orientation's added
  * side is an instruction of the store, so it makes no node), at most one fewer
  * than the store's at most 37 instructions, below the budget of 40; (2) a
  * fixed point saturated again ends as it did, adding no instance, and keeps
  * its form; (3) a fixed point is closed under the orientations: every class
  * where the naive matching (`NaiveMatching`) finds an orientation's matched
  * side is the class of its added side, an instruction in the generated
  * orientations.
  *
  * Purpose: catch a saturation whose fixed point depends on the order of its
  * lemmas or of its inputs, or that stops before its fixed point and calls it
  * one: one that skips the deltas of its merges is caught by (3) alone. The
  * stores and orientations are generated, so the laws hold of the saturation
  * and not of the configurations' knowledge.
  */
class FixedPointOrderLawTest extends GeneratedProperties:

  private type C = StandInStorages.type

  private given StandInStorages.type = StandInStorages

  private val budget = 40

  /** The graph the orientations saturate the inputs to, and how it ended. */
  private def saturated(
      generated: GeneratedStore,
      orientations: Vector[Orientation[C]],
      inputs: Vector[StandInStorages.Term],
      stop: StopSignal
  ) =
    val program = Indexing.program(orientations, generated.codes)
    val compiled = ClosureCompilation.compiled(program)
    val initial = Saturation.initialGraph(
      generated.store,
      Orientations.headArityBounds(orientations),
      Vector.empty,
      explained = false
    )
    val (withInputs, _) = Saturation.inputsAdded(initial, inputs)
    val (graph, ending) = Saturation.saturated(
      program,
      compiled,
      BuiltInRule.beforeOptIn,
      withInputs,
      budget,
      stop
    )
    (graph, ending, program, compiled)

  private def reachedFixedPoint(end: End): Boolean = end match
    case End.FixedPoint(_) => true
    case _                 => false

  stoppableProperty(
    "the fixed point does not depend on the order of the orientations or of the inputs",
    _.copy(testLimit = SuccessCount(100))
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val generated = for
      store <- StoreGenerators.store
      orientations <- OrientationGenerators.orientationsOver(store)
    yield (store, orientations)
    val withoutThunks = for
      store <- StoreGenerators.storeWithoutThunks
      orientations <- OrientationGenerators.orientationsOver(store)
    yield (store, orientations)
    // Both orders' saturations, and whether both reached a fixed point.
    def bothOrders(
        store: GeneratedStore,
        orientations: Vector[Orientation[C]]
    ) =
      val (inOrder, inOrderEnd, _, _) =
        saturated(store, orientations, store.instructions, stop)
      // The index numbers orientations in their order, so the reversed ones are numbered again.
      val reversedOrientations = orientations.reverse.zipWithIndex.map(
        (orientation, index) => orientation.copy(index = index)
      )
      val (reversed, reversedEnd, _, _) =
        saturated(store, reversedOrientations, store.instructions.reverse, stop)
      (
        inOrder,
        reversed,
        reachedFixedPoint(inOrderEnd) && reachedFixedPoint(reversedEnd)
      )
    for
      (store, orientations) <- generated.forAll
      (storeWithoutThunks, orientationsWithoutThunks) <- withoutThunks.forAll
    yield
      val (inOrder, reversed, reached) = bothOrders(store, orientations)
      val (inOrderWithoutThunks, reversedWithoutThunks, reachedWithoutThunks) =
        bothOrders(storeWithoutThunks, orientationsWithoutThunks)
      Result.all(
        List(
          if reached then
            Result.diff(FixedPoint.form(reversed), FixedPoint.form(inOrder))(
              _ == _
            )
          else Result.success,
          Result
            .assert(reachedWithoutThunks)
            .log(
              "a store without thunks did not reach its fixed point in both orders"
            ),
          Result.diff(
            FixedPoint.form(reversedWithoutThunks),
            FixedPoint.form(inOrderWithoutThunks)
          )(_ == _)
        )
      )
  }

  stoppableProperty(
    "a fixed point saturated again adds nothing and keeps its form",
    _.copy(testLimit = SuccessCount(100))
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val generated = for
      store <- StoreGenerators.store
      orientations <- OrientationGenerators.orientationsOver(store)
    yield (store, orientations)
    for (store, orientations) <- generated.forAll
    yield
      val (graph, ending, program, compiled) =
        saturated(store, orientations, store.instructions, stop)
      ending match
        case End.FixedPoint(_) =>
          val (again, againEnd) = Saturation.saturated(
            program,
            compiled,
            BuiltInRule.beforeOptIn,
            graph,
            budget,
            stop
          )
          Result.all(
            List(
              // An end carries the graph's instances from its start (`Saturation.saturated`).
              Result.diff(againEnd, ending)(_ == _),
              Result.diff(FixedPoint.form(again), FixedPoint.form(graph))(
                _ == _
              )
            )
          )
        case _ => Result.success
  }

  stoppableProperty(
    "a fixed point is closed under the orientations",
    _.copy(testLimit = SuccessCount(100))
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val generated = for
      store <- StoreGenerators.store
      orientations <- OrientationGenerators.orientationsOver(store)
    yield (store, orientations)
    for (store, orientations) <- generated.forAll
    yield
      val (graph, ending, _, _) =
        saturated(store, orientations, store.instructions, stop)
      if !reachedFixedPoint(ending) then Result.success
      else
        val open = for
          orientation <- orientations
          added <- orientation.added match
            case Pattern.InstructionReference(instruction) =>
              Vector(instruction)
            case other =>
              throw IllegalStateException(
                s"a generated orientation adds an instruction, not $other"
              )
          root <- graph.liveNodes.map(_.root).distinct
          if NaiveMatching
            .matches(graph, orientation.matched, root, Map.empty)
            .nonEmpty
          if !graph.instructionNode(added).exists(graph.root(_) == root)
        yield (orientation.index, root)
        Result.diff(open, Vector.empty)(_ == _)
  }
