package gezi.strategies

import gezi.saturation.StopSignal
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.extraction.CostModel
import gezi.extraction.Entry
import gezi.extraction.Shape
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.standardlibrary.CombinatorProperty
import gezi.standardlibrary.Property
import gezi.standardlibrary.StandardLibraryIndex
import gezi.ir.{Apply, Choice, Parallel, Thunk}

/** The oracle of `ThunkCandidates`: for a thunk's production over entries of
  * its fillings, the best cost of each reading among its candidates is the
  * best cost of that reading among every combination of the entries
  * (`CostModel.candidates`), and the two have the same readings. Its purpose
  * is to catch a decomposition of a code's body that loses a reading or a
  * best combination: a module whose state of a part read through its state
  * differs from its state of the part itself, a filling read by a recognizer
  * that the decomposition reads alone, or a criterion's filling priced.
  *
  * The thunks are generated with one or two holes and one to four fillings,
  * their codes of slots, applications, parallels, choices and inner thunks,
  * a slot occurring any number of times, and chains `s1 (s2 (… (sk y)))`;
  * each filling has one to three entries, the costs of generated terms over
  * instructions that include contracts read as λf. f and occurrence tags. The
  * law is checked for every module the extraction's monotonicity is (all
  * but `filter_attraction`, `CostMonotonicityLawTest`) and for the native
  * route's combination.
  */
class ThunkCandidatesLawTest extends GeneratedProperties:

  private val criterion = Instruction.opaque("thunk-candidates-criterion")
  private val identity = Instruction.Thunk(Code.Slot(0), Vector(Hole.Bound(0)), Vector.empty)
  private val named = Instruction.Thunk(
    Code.Thunk(Code.Slot(1), Vector(Hole.Bound(0)), Vector(Code.Slot(0))),
    Vector(Hole.Bound(0)),
    Vector.empty
  )
  private val nextTag = Instruction.Thunk(Code.Parallel(Code.Slot(0), Code.Slot(1)), Vector(Hole.Bound(0)), Vector(criterion))
  private val identityContract = Instruction.Thunk(
    Code.Apply(Code.Slot(0), Code.Slot(1)),
    Vector(Hole.Bound(0), Hole.Bound(1)),
    Vector.empty
  )
  private val lastArgumentContract = Instruction.Thunk(
    Code.Choice(
      Code.Apply(Code.Slot(0), Code.Slot(1)),
      Code.Parallel(Code.Apply(Code.Slot(0), Code.Parallel(Code.Slot(1), Code.Slot(2))), Code.Slot(2))
    ),
    Vector(Hole.Bound(0), Hole.Bound(1)),
    Vector(criterion)
  )
  private val instructions = Vector(identity, named, nextTag, identityContract, lastArgumentContract)

  private val reading = TermReading(
    StandardLibraryIndex(
      Vector.empty,
      Vector.empty,
      Vector.empty,
      Vector(
        CombinatorProperty(named, Property.NameMarker),
        CombinatorProperty(nextTag, Property.TagNext)
      )
    )
  )

  /** The cost of a generated term: a name, or a layer over generated terms,
    * as the extraction prices it.
    */
  private def termCost(model: ModuleCostModel, depth: Int): Gen[ModuleCost] =
    val name = Gen.element(instructions.head, instructions.tail.toList).map(instruction => model.cost(Shape.Name(instruction), Vector.empty))
    if depth <= 0 then name
    else
      val child = termCost(model, depth - 1)
      Gen.frequency1(
        2 -> name,
        2 -> (for function <- child; argument <- child
        yield model.cost(Shape.Node(0, Apply(1, 2)), Vector(function, argument))),
        1 -> (for left <- child; right <- child
        yield model.cost(Shape.Node(0, Parallel(1, 2)), Vector(left, right))),
        1 -> (for left <- child; right <- child
        yield model.cost(Shape.Node(0, Choice(1, 2)), Vector(left, right))),
        1 -> (for body <- child
        yield model.cost(Shape.Node(0, Thunk(Code.Parallel(Code.Slot(0), Code.Slot(1)), Vector(Hole.Bound(0)), Vector(1))), Vector(body)))
      )

  /** A code over the slots below `slotCount`, inner thunks binding slot 0
    * of their own code.
    */
  private def code(slotCount: Int, depth: Int, innerThunks: Boolean): Gen[Code] =
    val slot = Gen.int(Range.linear(0, slotCount - 1)).map(Code.Slot(_))
    if depth <= 0 then slot
    else
      val child = code(slotCount, depth - 1, innerThunks)
      val layers = Vector(
        3 -> slot,
        3 -> (for function <- child; argument <- child yield Code.Apply(function, argument)),
        2 -> (for left <- child; right <- child yield Code.Parallel(left, right)),
        1 -> (for left <- child; right <- child yield Code.Choice(left, right))
      )
      val inner = 1 -> (for
        fillingCount <- Gen.int(Range.linear(1, 2))
        fillings <- child.list(Range.singleton(fillingCount))
        innerCode <- code(1 + fillingCount, 2, false)
      yield Code.Thunk(innerCode, Vector(Hole.Bound(0)), fillings.toVector))
      val all = if innerThunks then layers :+ inner else layers
      Gen.frequency1(all.head, all.tail*)

  /** `s1 (s2 (… (sk y)))`, y the hole, slot 0. */
  private def chain(fillingCount: Int): Code =
    (fillingCount to 1 by -1).foldLeft(Code.Slot(0))((argument, slot) => Code.Apply(Code.Slot(slot), argument))

  private def thunk(holeCount: Int, fillingCount: Int): Gen[Code] =
    Gen.frequency1(
      4 -> code(holeCount + fillingCount, 4, true),
      1 -> Gen.constant(chain(fillingCount))
    )

  /** The best cost of each reading among the entries. */
  private def bestOfEachReading(model: ModuleCostModel, entries: Vector[Entry[ModuleCost]]): Vector[ModuleCost] =
    entries.map(_.cost).foldLeft(Vector.empty[ModuleCost]) { (kept, cost) =>
      kept.indexWhere(model.sameReading(_, cost)) match
        case -1       => kept :+ cost
        case position => if model.ordering.compare(cost, kept(position)) < 0 then kept.updated(position, cost) else kept
    }

  private def oracle(model: ModuleCostModel) =
    for
      holeCount <- Gen.int(Range.linear(1, 2)).forAll
      fillingCount <- Gen.int(Range.linear(1, 4)).forAll
      body <- (if holeCount == 1 then thunk(1, fillingCount) else code(2 + fillingCount, 4, true)).forAll
      options <- termCost(model, 3).list(Range.linear(1, 3)).list(Range.singleton(fillingCount)).forAll
    yield
      val entries = options.toVector.zipWithIndex.map((costs, position) =>
        costs.toVector.map(cost => Entry(cost, Shape.Name(instructions(position % instructions.size)), Vector.empty))
      )
      val thunkLayer = new Thunk(body, Vector.tabulate(holeCount)(Hole.Bound(_)), Vector.tabulate(fillingCount)(_ + 1))
      val shape = Shape.Node(0, thunkLayer)
      val everyCombination = CostModel.combinations(entries).map(chosen => Entry(model.cost(shape, chosen.map(_.cost)), shape, chosen))
      val decomposed = ThunkCandidates.candidates(model, shape, thunkLayer, entries)
      val expected = bestOfEachReading(model, everyCombination)
      val found = bestOfEachReading(model, decomposed)
      val sameReadings = expected.size == found.size && expected.forall(cost => found.exists(model.sameReading(_, cost)))
      val sameBest = expected.forall(cost =>
        found.find(model.sameReading(_, cost)).exists(other => model.ordering.compare(other, cost) == 0)
      )
      val priced = decomposed.forall(entry => entry.cost == model.cost(shape, entry.childEntries.map(_.cost)))
      Result
        .assert(sameReadings)
        .and(Result.assert(sameBest))
        .and(Result.assert(priced))
        .log(s"thunk $thunkLayer")
        .log(s"every combination's best ranks ${expected.map(_.ranks)}")
        .log(s"the candidates' best ranks ${found.map(_.ranks)}")

  BaselineModules.table.filterNot(_ == FilterAttraction).foreach { module =>
    stoppableProperty(s"theCandidatesOf${module.name}HaveEveryReadingsBestCost") { stopped =>
      oracle(ModuleCostModel(Vector(module), reading, StopSignal.completedWith(stopped)))
    }
  }

  /** The least candidates (`ThunkCandidates.leastCandidates`) against every
    * combination's least of each reading by `ContentOrder`, the fillings'
    * entries of sizes 1 and 3. Its purpose is to catch a decomposition by
    * size that loses a reading or keeps other than the least combination:
    * a part whose least alternative of a reading is not part of the whole's
    * least.
    */
  private def leastOracle(model: ModuleCostModel) =
    for
      holeCount <- Gen.int(Range.linear(1, 2)).forAll
      fillingCount <- Gen.int(Range.linear(1, 4)).forAll
      body <- (if holeCount == 1 then thunk(1, fillingCount) else code(2 + fillingCount, 4, true)).forAll
      options <- (for cost <- termCost(model, 3); large <- Gen.boolean yield (cost, large))
        .list(Range.linear(1, 3)).list(Range.singleton(fillingCount)).forAll
    yield
      val entries = options.toVector.zipWithIndex.map((drawn, position) =>
        drawn.toVector.zipWithIndex.map { case ((cost, large), number) =>
          val name = Entry(cost, Shape.Name(instructions((position + number) % instructions.size)), Vector.empty)
          if large then Entry(cost, Shape.Node(100 + number, Apply(0, 1)), Vector(name, name)) else name
        }
      )
      val thunkLayer = new Thunk(body, Vector.tabulate(holeCount)(Hole.Bound(_)), Vector.tabulate(fillingCount)(_ + 1))
      val shape = Shape.Node(0, thunkLayer)
      val everyCombination = CostModel.combinations(entries).map(chosen => Entry(model.cost(shape, chosen.map(_.cost)), shape, chosen))
      val expected = CostModel.leastOfEachReading(model, everyCombination).toSet
      val found = CostModel.leastOfEachReading(model, ThunkCandidates.leastCandidates(model, shape, thunkLayer, entries)).toSet
      Result.diff(found, expected)(_ == _).log(s"thunk $thunkLayer")

  BaselineModules.table.filterNot(_ == FilterAttraction).foreach { module =>
    stoppableProperty(s"theLeastCandidatesOf${module.name}AreEveryReadingsLeastCombination") { stopped =>
      leastOracle(ModuleCostModel(Vector(module), reading, StopSignal.completedWith(stopped)))
    }
  }

  stoppableProperty("theLeastCandidatesOfTheNativeRouteCombinationAreEveryReadingsLeastCombination") { stopped =>
    leastOracle(
      ModuleCostModel(
        TermOrder.modulesChecked(BaselineModules.table, NativeRouteCompilation.extraction.modules),
        reading,
        StopSignal.completedWith(stopped)
      )
    )
  }

  stoppableProperty("theCandidatesOfTheNativeRouteCombinationHaveEveryReadingsBestCost") { stopped =>
    oracle(
      ModuleCostModel(
        TermOrder.modulesChecked(BaselineModules.table, NativeRouteCompilation.extraction.modules),
        reading,
        StopSignal.completedWith(stopped)
      )
    )
  }
