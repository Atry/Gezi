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
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Pure
import gezi.ir.Layer
import gezi.standardlibrary.CombinatorProperty
import gezi.standardlibrary.Property
import gezi.standardlibrary.StandardLibraryIndex
import gezi.ir.{Apply, Choice, Parallel, Thunk}

/** The oracle of `ThunkCandidates`: for a thunk's production over entries of
  * its fillings, the best cost of each reading among its candidates is the best
  * cost of that reading among every combination of the entries
  * (`CostModel.candidates`), and the two have the same readings. Its purpose is
  * to catch a decomposition of a code's body that loses a reading or a best
  * combination: a module whose state of a part read through its state differs
  * from its state of the part itself, a filling read by a recognizer that the
  * decomposition reads alone, or a criterion's filling priced.
  *
  * The thunks are generated with one or two holes and one to four fillings,
  * their codes of slots, applications, parallels, choices and inner thunks, a
  * slot occurring any number of times, and chains `s1 (s2 (… (sk y)))`; each
  * filling has one to three entries, the costs of generated terms over
  * instructions that include contracts read as λf. f and occurrence tags. The
  * law is checked for every module the extraction's monotonicity is (all but
  * `filter_attraction`, `CostMonotonicityLawTest`) and for the native route's
  * combination.
  */
class ThunkCandidatesLawTest extends GeneratedProperties:

  private given NoFacts.type = NoFacts

  private val criterion = NoFacts.opaque("thunk-candidates-criterion")
  private val identity =
    NoFacts.thunkOrInstance(Code.Slot(0), Vector(Hole.Bound(0)), Vector.empty)
  private val named = NoFacts.thunkOrInstance(
    Code.Thunk(Code.Slot(1), Vector(Hole.Bound(0)), Vector(Code.Slot(0))),
    Vector(Hole.Bound(0)),
    Vector.empty
  )
  private val nextTag = NoFacts.thunkOrInstance(
    Code.Parallel(Code.Slot(0), Code.Slot(1)),
    Vector(Hole.Bound(0)),
    Vector(criterion)
  )
  private val identityContract = NoFacts.thunkOrInstance(
    Code.Apply(Code.Slot(0), Code.Slot(1)),
    Vector(Hole.Bound(0), Hole.Bound(1)),
    Vector.empty
  )
  private val lastArgumentContract = NoFacts.thunkOrInstance(
    Code.Choice(
      Code.Apply(Code.Slot(0), Code.Slot(1)),
      Code.Parallel(
        Code.Apply(Code.Slot(0), Code.Parallel(Code.Slot(1), Code.Slot(2))),
        Code.Slot(2)
      )
    ),
    Vector(Hole.Bound(0), Hole.Bound(1)),
    Vector(criterion)
  )
  private val instructions =
    Vector(identity, named, nextTag, identityContract, lastArgumentContract)

  private val reading = TermReading(
    StandardLibraryIndex(
      NoFacts,
      Vector.empty,
      Vector.empty,
      Vector.empty,
      Vector(
        CombinatorProperty(Pure.required(named), Property.NameMarker),
        CombinatorProperty(Pure.required(nextTag), Property.TagNext)
      )
    )
  )

  /** The cost of a generated term: a name, or a layer over generated terms, as
    * the extraction prices it.
    */
  private def termCost(
      model: ModuleCostModel[NoFacts.type],
      depth: Int
  ): Gen[ModuleCost] =
    val name = Gen
      .element(instructions.head, instructions.tail.toList)
      .map(instruction => model.cost(Shape.Name(instruction), Vector.empty))
    if depth <= 0 then name
    else
      val child = termCost(model, depth - 1)
      Gen.frequency1(
        2 -> name,
        2 -> (for function <- child; argument <- child
        yield model
          .cost(Shape.Node(0, Apply(1, 2)), Vector(function, argument))),
        1 -> (for left <- child; right <- child
        yield model.cost(Shape.Node(0, Parallel(1, 2)), Vector(left, right))),
        1 -> (for left <- child; right <- child
        yield model.cost(Shape.Node(0, Choice(1, 2)), Vector(left, right))),
        1 -> (for body <- child
        yield model.cost(
          Shape.Node(
            0,
            Thunk(
              Code.Parallel(Code.Slot(0), Code.Slot(1)),
              Vector(Hole.Bound(0)),
              Vector(1)
            )
          ),
          Vector(body)
        ))
      )

  /** A code over the slots below `slotCount`, inner thunks binding slot 0 of
    * their own code.
    */
  private def code(
      slotCount: Int,
      depth: Int,
      innerThunks: Boolean
  ): Gen[Code] =
    val slot = Gen.int(Range.linear(0, slotCount - 1)).map(Code.Slot(_))
    if depth <= 0 then slot
    else
      val child = code(slotCount, depth - 1, innerThunks)
      val layers = Vector(
        3 -> slot,
        3 -> (for function <- child; argument <- child
        yield Code.Apply(function, argument)),
        2 -> (for left <- child; right <- child
        yield Code.Parallel(left, right)),
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
    (fillingCount to 1 by -1).foldLeft(Code.Slot(0))((argument, slot) =>
      Code.Apply(Code.Slot(slot), argument)
    )

  private def thunk(holeCount: Int, fillingCount: Int): Gen[Code] =
    Gen.frequency1(
      4 -> code(holeCount + fillingCount, 4, true),
      1 -> Gen.constant(chain(fillingCount))
    )

  /** The best cost of each reading among the entries. */
  private def bestOfEachReading(
      model: ModuleCostModel[NoFacts.type],
      entries: Vector[Entry[NoFacts.type, ModuleCost]]
  ): Vector[ModuleCost] =
    entries.map(_.cost).foldLeft(Vector.empty[ModuleCost]) { (kept, cost) =>
      kept.indexWhere(model.sameReading(_, cost)) match
        case -1       => kept :+ cost
        case position =>
          if model.ordering.compare(cost, kept(position)) < 0 then
            kept.updated(position, cost)
          else kept
    }

  private def oracle(model: ModuleCostModel[NoFacts.type]) =
    for
      holeCount <- Gen.int(Range.linear(1, 2)).forAll
      fillingCount <- Gen.int(Range.linear(1, 4)).forAll
      body <- (if holeCount == 1 then thunk(1, fillingCount)
               else code(2 + fillingCount, 4, true)).forAll
      options <- termCost(model, 3)
        .list(Range.linear(1, 3))
        .list(Range.singleton(fillingCount))
        .forAll
    yield
      val entries = options.toVector.zipWithIndex.map((costs, position) =>
        costs.toVector.map(cost =>
          Entry(
            cost,
            Shape.Name(instructions(position % instructions.size)),
            Vector.empty
          )
        )
      )
      val thunkLayer = Thunk(
        body,
        Vector.tabulate(holeCount)(Hole.Bound(_)),
        Vector.tabulate(fillingCount)(_ + 1)
      )
      val shape = Shape.Node(0, thunkLayer)
      val everyCombination = CostModel
        .combinations(entries)
        .map(chosen =>
          Entry(model.cost(shape, chosen.map(_.cost)), shape, chosen)
        )
      val decomposed =
        ThunkCandidates.candidates(model, shape, thunkLayer, entries)
      val expected = bestOfEachReading(model, everyCombination)
      val found = bestOfEachReading(model, decomposed)
      val sameReadings = expected.size == found.size && expected.forall(cost =>
        found.exists(model.sameReading(_, cost))
      )
      val sameBest = expected.forall(cost =>
        found
          .find(model.sameReading(_, cost))
          .exists(other => model.ordering.compare(other, cost) == 0)
      )
      val priced = decomposed.forall(entry =>
        entry.cost == model.cost(shape, entry.childEntries.map(_.cost))
      )
      Result
        .assert(sameReadings)
        .and(Result.assert(sameBest))
        .and(Result.assert(priced))
        .log(s"thunk $thunkLayer")
        .log(s"every combination's best ranks ${expected.map(_.ranks)}")
        .log(s"the candidates' best ranks ${found.map(_.ranks)}")

  BaselineModules
    .table[gezi.ir.NoFacts.type]
    .filterNot(_.name == FilterAttraction.name)
    .foreach { module =>
      stoppableProperty(
        s"theCandidatesOf${module.name}HaveEveryReadingsBestCost"
      ) { stopped =>
        oracle(
          ModuleCostModel(
            Vector(module),
            reading,
            StopSignal.completedWith(stopped)
          )
        )
      }
    }

  /** The least candidates (`ThunkCandidates.leastCandidates`) against every
    * combination's least of each reading by `ContentOrder`, the fillings'
    * entries of sizes 1 and 3. Its purpose is to catch a decomposition by size
    * that loses a reading or keeps other than the least combination: a part
    * whose least alternative of a reading is not part of the whole's least.
    */
  private def leastOracle(model: ModuleCostModel[NoFacts.type]) =
    for
      holeCount <- Gen.int(Range.linear(1, 2)).forAll
      fillingCount <- Gen.int(Range.linear(1, 4)).forAll
      body <- (if holeCount == 1 then thunk(1, fillingCount)
               else code(2 + fillingCount, 4, true)).forAll
      options <- (for cost <- termCost(model, 3); large <- Gen.boolean
      yield (cost, large))
        .list(Range.linear(1, 3))
        .list(Range.singleton(fillingCount))
        .forAll
    yield
      val entries = options.toVector.zipWithIndex.map((drawn, position) =>
        drawn.toVector.zipWithIndex.map { case ((cost, large), number) =>
          val name = Entry(
            cost,
            Shape.Name(instructions((position + number) % instructions.size)),
            Vector.empty
          )
          if large then
            Entry(
              cost,
              Shape.Node(100 + number, Apply(0, 1)),
              Vector(name, name)
            )
          else name
        }
      )
      val thunkLayer = Thunk(
        body,
        Vector.tabulate(holeCount)(Hole.Bound(_)),
        Vector.tabulate(fillingCount)(_ + 1)
      )
      val shape = Shape.Node(0, thunkLayer)
      val everyCombination = CostModel
        .combinations(entries)
        .map(chosen =>
          Entry(model.cost(shape, chosen.map(_.cost)), shape, chosen)
        )
      val expected = CostModel.leastOfEachReading(model, everyCombination).toSet
      val found = CostModel
        .leastOfEachReading(
          model,
          ThunkCandidates.leastCandidates(model, shape, thunkLayer, entries)
        )
        .toSet
      Result.diff(found, expected)(_ == _).log(s"thunk $thunkLayer")

  BaselineModules
    .table[gezi.ir.NoFacts.type]
    .filterNot(_.name == FilterAttraction.name)
    .foreach { module =>
      stoppableProperty(
        s"theLeastCandidatesOf${module.name}AreEveryReadingsLeastCombination"
      ) { stopped =>
        leastOracle(
          ModuleCostModel(
            Vector(module),
            reading,
            StopSignal.completedWith(stopped)
          )
        )
      }
    }

  stoppableProperty(
    "theLeastCandidatesOfTheNativeRouteCombinationAreEveryReadingsLeastCombination"
  ) { stopped =>
    leastOracle(
      ModuleCostModel(
        TermOrder.modulesChecked(
          BaselineModules.table[gezi.ir.NoFacts.type],
          NativeRouteCompilation.extraction.modules
        ),
        reading,
        StopSignal.completedWith(stopped)
      )
    )
  }

  /** What a thunk's candidates settle (`ThunkCandidates.settledFillings`) is
    * monotone in the numbers of entries: a filling settled at some numbers is
    * settled at numbers at least as large, position by position, under
    * generated bounds, the whole fold bound above the enumeration bound
    * included. Its purpose is to catch a path chosen by the numbers (read whole
    * or by parts) that settles at fewer entries what it does not at more, which
    * `gezi.extraction.CountedExtraction` relies on not happening
    * (`gezi.extraction.CostModel.settledChildren`).
    */
  private def settlingMonotone(model: ModuleCostModel[NoFacts.type]) =
    for
      holeCount <- Gen.int(Range.linear(1, 2)).forAll
      fillingCount <- Gen.int(Range.linear(1, 4)).forAll
      body <- (if holeCount == 1 then thunk(1, fillingCount)
               else code(2 + fillingCount, 4, true)).forAll
      lower <- Gen
        .int(Range.linear(1, 4))
        .list(Range.singleton(fillingCount))
        .map(_.toVector)
        .forAll
      added <- Gen
        .int(Range.linear(0, 3))
        .list(Range.singleton(fillingCount))
        .map(_.toVector)
        .forAll
      enumerationBound <- Gen.long(Range.linear(1L, 8L)).forAll
      wholeFoldBound <- Gen.long(Range.linear(0L, 16L)).forAll
    yield
      val bounded = model.copy(jointReading =
        JointReading(enumerationBound, wholeFoldBound)
      )
      val thunkLayer = Thunk(
        body,
        Vector.tabulate(holeCount)(Hole.Bound(_)),
        Vector.tabulate(fillingCount)(_ + 1)
      )
      val upper = lower.zip(added).map(_ + _)
      val atLower = ThunkCandidates.settledFillings(bounded, thunkLayer, lower)
      val atUpper = ThunkCandidates.settledFillings(bounded, thunkLayer, upper)
      Result
        .assert(
          atLower
            .zip(atUpper)
            .forall((settledLower, settledUpper) =>
              !settledLower || settledUpper
            )
        )
        .log(s"thunk $thunkLayer, bounds $enumerationBound and $wholeFoldBound")
        .log(s"settled at $lower: $atLower; at $upper: $atUpper")

  /** Every candidate of a thunk (`ThunkCandidates.candidates` and
    * `leastCandidates`) has, at each filling the thunk is said to settle at its
    * options' numbers of entries (`ThunkCandidates.settledFillings`), that
    * filling's first entry by size, then content (`CodeCandidates.first`),
    * under generated small bounds. Its purpose is to catch a filling reported
    * settled that the candidates enumerate, as a path chosen apart from
    * `decomposed`'s would: directed by its one recorded reading, such a filling
    * would lose readings the candidates give. A filling the candidates settle
    * and that is not reported is not caught here;
    * `gezi.extraction.CountedExtraction` throws on it when its passes settle
    * apart.
    */
  private def settledAsReported(model: ModuleCostModel[NoFacts.type]) =
    for
      holeCount <- Gen.int(Range.linear(1, 2)).forAll
      fillingCount <- Gen.int(Range.linear(1, 4)).forAll
      body <- (if holeCount == 1 then thunk(1, fillingCount)
               else code(2 + fillingCount, 4, true)).forAll
      options <- termCost(model, 3)
        .list(Range.linear(1, 3))
        .list(Range.singleton(fillingCount))
        .forAll
      enumerationBound <- Gen.long(Range.linear(1L, 4L)).forAll
      wholeFoldBound <- Gen.long(Range.linear(0L, enumerationBound)).forAll
    yield
      val bounded = model.copy(jointReading =
        JointReading(enumerationBound, wholeFoldBound)
      )
      val entries = options.toVector.zipWithIndex.map((costs, position) =>
        costs.toVector.map(cost =>
          Entry(
            cost,
            Shape.Name(instructions(position % instructions.size)),
            Vector.empty
          )
        )
      )
      val thunkLayer = Thunk(
        body,
        Vector.tabulate(holeCount)(Hole.Bound(_)),
        Vector.tabulate(fillingCount)(_ + 1)
      )
      val shape = Shape.Node(0, thunkLayer)
      val settled = ThunkCandidates.settledFillings(
        bounded,
        thunkLayer,
        entries.map(_.size)
      )
      val found = ThunkCandidates.candidates(
        bounded,
        shape,
        thunkLayer,
        entries
      ) ++ ThunkCandidates.leastCandidates(bounded, shape, thunkLayer, entries)
      Result
        .assert(
          found.forall(entry =>
            settled.indices.forall(position =>
              !settled(position) || entry.childEntries(
                position
              ) == CodeCandidates.first(entries(position))
            )
          )
        )
        .log(
          s"thunk $thunkLayer, bounds $enumerationBound and $wholeFoldBound, settled $settled"
        )

  stoppableProperty(
    "theNativeRouteCombinationsCandidatesHaveTheFirstEntryAtEveryFillingSaidToSettle"
  ) { stopped =>
    settledAsReported(
      ModuleCostModel(
        TermOrder.modulesChecked(
          BaselineModules.table[gezi.ir.NoFacts.type],
          NativeRouteCompilation.extraction.modules
        ),
        reading,
        StopSignal.completedWith(stopped)
      )
    )
  }

  stoppableProperty(
    "theCandidatesOfAModelWithNoCodeFoldingHaveTheFirstEntryAtEveryFillingSaidToSettle"
  ) { stopped =>
    settledAsReported(
      ModuleCostModel(
        BaselineModules
          .table[gezi.ir.NoFacts.type]
          .filter(_.codeFolding.isEmpty)
          .take(1),
        reading,
        StopSignal.completedWith(stopped)
      )
    )
  }

  /** The same law on the thunk `(f1 + f2) y`, y its hole, whose two fillings
    * are read once each under a choice: read whole they are read jointly and
    * settled above the enumeration bound; read by parts they are not. Its
    * purpose is to catch a whole fold bound above the enumeration bound reading
    * such a thunk whole, and so settling it, at fewer entries than those at
    * which it is read by parts and settles nothing; the generated law above
    * reaches such a thunk too rarely.
    */
  private def choiceSettlingMonotone(model: ModuleCostModel[NoFacts.type]) =
    for
      lower <- Gen
        .int(Range.linear(1, 4))
        .list(Range.singleton(2))
        .map(_.toVector)
        .forAll
      added <- Gen
        .int(Range.linear(0, 4))
        .list(Range.singleton(2))
        .map(_.toVector)
        .forAll
      enumerationBound <- Gen.long(Range.linear(1L, 4L)).forAll
      above <- Gen.long(Range.linear(enumerationBound + 1L, 16L)).forAll
    yield
      // Each iteration checks the whole fold bound equal to the enumeration
      // bound and one above it, the case the law is for, by construction.
      val thunkLayer = Thunk(
        Code.Apply(Code.Choice(Code.Slot(1), Code.Slot(2)), Code.Slot(0)),
        Vector(Hole.Bound(0)),
        Vector(1, 2)
      )
      val upper = lower.zip(added).map(_ + _)
      Result.all(
        List(enumerationBound, above).map(wholeFoldBound =>
          val bounded = model.copy(jointReading =
            JointReading(enumerationBound, wholeFoldBound)
          )
          val atLower =
            ThunkCandidates.settledFillings(bounded, thunkLayer, lower)
          val atUpper =
            ThunkCandidates.settledFillings(bounded, thunkLayer, upper)
          Result
            .assert(
              atLower
                .zip(atUpper)
                .forall((settledLower, settledUpper) =>
                  !settledLower || settledUpper
                )
            )
            .log(
              s"bounds $enumerationBound and $wholeFoldBound; settled at $lower: $atLower; at $upper: $atUpper"
            )
        )
      )

  stoppableProperty(
    "whatTheNativeRouteCombinationSettlesOfAChoiceOfTwoFillingsIsMonotoneInTheNumbersOfEntries",
    _.copy(testLimit = hedgehog.core.SuccessCount(200))
  ) { stopped =>
    choiceSettlingMonotone(
      ModuleCostModel(
        TermOrder.modulesChecked(
          BaselineModules.table[gezi.ir.NoFacts.type],
          NativeRouteCompilation.extraction.modules
        ),
        reading,
        StopSignal.completedWith(stopped)
      )
    )
  }

  stoppableProperty(
    "whatTheNativeRouteCombinationSettlesIsMonotoneInTheNumbersOfEntries"
  ) { stopped =>
    settlingMonotone(
      ModuleCostModel(
        TermOrder.modulesChecked(
          BaselineModules.table[gezi.ir.NoFacts.type],
          NativeRouteCompilation.extraction.modules
        ),
        reading,
        StopSignal.completedWith(stopped)
      )
    )
  }

  stoppableProperty(
    "whatAModelWithNoCodeFoldingSettlesIsMonotoneInTheNumbersOfEntries"
  ) { stopped =>
    settlingMonotone(
      ModuleCostModel(
        BaselineModules
          .table[gezi.ir.NoFacts.type]
          .filter(_.codeFolding.isEmpty)
          .take(1),
        reading,
        StopSignal.completedWith(stopped)
      )
    )
  }

  stoppableProperty(
    "theCandidatesOfTheNativeRouteCombinationHaveEveryReadingsBestCost"
  ) { stopped =>
    oracle(
      ModuleCostModel(
        TermOrder.modulesChecked(
          BaselineModules.table[gezi.ir.NoFacts.type],
          NativeRouteCompilation.extraction.modules
        ),
        reading,
        StopSignal.completedWith(stopped)
      )
    )
  }
