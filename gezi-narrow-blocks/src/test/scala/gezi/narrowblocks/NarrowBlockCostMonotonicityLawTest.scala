package gezi.narrowblocks

import gezi.saturation.StopSignal
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Pure
import gezi.jit.NativeName
import gezi.jit.NativesProvider
import gezi.standardlibrary.NativeBound
import gezi.strategies.CostMonotonicityLaws
import gezi.strategies.ModuleCostModel
import gezi.ir.{Apply, Choice, Parallel}

private given narrowBlockCostMonotonicityLawTestNoFacts: NoFacts.type = NoFacts

/** The laws of the extraction's contract (`CostMonotonicityLaws`: monotone
  * within a reading, a child read by its cost and its reading only, an unpriced
  * child by its reading only, strictly monotone at priced positions) on the
  * combination the lemma compilation's extraction runs, read from it
  * (`LemmaCompilation.extractor`'s modules: the narrow blocks over the natives
  * the tree loads, then compression), on terms built over instructions bound to
  * loaded natives as well, so that the narrow blocks' module reads native
  * calls, partial ones and their `Closed` operands. Its purpose is to catch a
  * combination whose first module masks a child, so that a later one decides
  * against the first: a narrow call ranked 0 whatever its `Closed` operand
  * ranks, while compression reads the operand's size, made a worse operand give
  * a better call (a practice read).
  */
class NarrowBlockCostMonotonicityLawTest extends CostMonotonicityLaws:

  /** The narrow blocks' module reads a name's layers through its fillings
    * (`NarrowBlocks.nameKind`), and an opaque criterion has none.
    */
  override protected def withOpaqueCriteria: Boolean = false

  private val natives = NativesProvider.loaded

  private val modules = LemmaCompilation.extractorModules(natives)

  /** Instructions of no other kind (neither a boolean nor the fixed point
    * combinator): λx y. y x and λx y z. z y x.
    */
  private val bindableInstructions = Vector(
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Slot(1), Code.Slot(0)),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector.empty
    ),
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Apply(Code.Slot(2), Code.Slot(1)), Code.Slot(0)),
      Vector(Hole.Bound(0), Hole.Bound(1), Hole.Bound(2)),
      Vector.empty
    )
  )

  /** The first loaded native function of two parameters and the first of one,
    * by name, each bound to an instruction of `bindableInstructions`. Throws
    * `IllegalStateException` when the loaded natives have neither.
    */
  override protected def nativeBindings: Vector[NativeBound] =
    val names = Vector(2, 1).flatMap(arity =>
      natives.natives
        .collect {
          case (NativeName.Function(name), native)
              if native.parameterCount == arity =>
            name
        }
        .toVector
        .sorted
        .headOption
    )
    if names.isEmpty then
      throw IllegalStateException(
        "the loaded natives have no function of one or two parameters"
      )
    names
      .zip(bindableInstructions)
      .map((name, instruction) => NativeBound(Pure.required(instruction), name))

  stoppableProperty("theLemmaCompilationsCombinationIsMonotoneInItsChildren") {
    stopped =>
      monotone(
        ModuleCostModel(modules, reading, StopSignal.completedWith(stopped))
      )
  }

  stoppableProperty(
    "theLemmaCompilationsCombinationReadsOfAChildItsCostAndItsReadingOnly"
  ) { stopped =>
    tiesAreIndistinguishable(
      ModuleCostModel(modules, reading, StopSignal.completedWith(stopped))
    )
  }

  stoppableProperty(
    "theLemmaCompilationsCombinationIsStrictlyMonotoneInItsPricedChildren"
  ) { stopped =>
    strictlyMonotone(
      ModuleCostModel(modules, reading, StopSignal.completedWith(stopped))
    )
  }

  /** The strict law at the seed that falsified it on main 4e59a1471 (a run of
    * 2026-11-13: a narrow choice ranked its chosen member while compression
    * counted a child in a member the backend drops, the parent ranking (0, 17)
    * over the better child and (0, 13) over the worse). Its purpose is to keep
    * that generated input under the law: every module now reads a dropped
    * member as unpriced (`ModuleCostModel.droppedChildren`).
    */
  stoppableTest("theStrictLawHoldsAtTheSeedThatFalsifiedIt") { stopped =>
    val report = hedgehog.Property.check(
      hedgehog.core.PropertyConfig.default,
      strictlyMonotone(
        ModuleCostModel(modules, reading, StopSignal.completedWith(stopped))
      ),
      hedgehog.core.Seed.fromLong(150715495590311L)
    )
    assertEquals(report.status, hedgehog.core.OK, report.toString)
  }

  stoppableProperty(
    "theLemmaCompilationsCombinationReadsAnUnpricedChildByItsReading"
  ) { stopped =>
    unpricedChildrenAreReadByTheirReading(
      ModuleCostModel(modules, reading, StopSignal.completedWith(stopped))
    )
  }

  stoppableProperty(
    "theLemmaCompilationsModulesFoldAThunksCodeByPartsAsTheyFoldItWhole"
  ) { stopped =>
    foldedByParts(
      ModuleCostModel(modules, reading, StopSignal.completedWith(stopped))
    )
  }

  stoppableProperty(
    "theLemmaCompilationsCandidatesByPartsHaveEveryReadingsLeastUnderEachOrdering"
  ) { stopped =>
    candidatesByParts(
      ModuleCostModel(modules, reading, StopSignal.completedWith(stopped))
    )
  }

  stoppableProperty(
    "theLemmaCompilationsCombinationReadsAThunkOfJointProductOneWholeAsItsPartsWouldBeRead"
  ) { stopped =>
    productOneReadWhole(
      ModuleCostModel(modules, reading, StopSignal.completedWith(stopped))
    )
  }

  stoppableProperty(
    "theLemmaCompilationsCandidatesHaveEveryReadingsLeastAtEitherWholeFoldBound"
  ) { stopped =>
    wholeFoldBoundKeepsLeastCosts(
      ModuleCostModel(modules, reading, StopSignal.completedWith(stopped))
    )
  }

  /** A criterion function of a native specialization: λx. x x x. */
  private val criterionFunction =
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Apply(Code.Slot(0), Code.Slot(0)), Code.Slot(0)),
      Vector(Hole.Bound(0)),
      Vector.empty
    )

  override protected def criterionFunctions: Vector[Configured[NoFacts.type]] =
    Vector(criterionFunction)

  /** The truth λt _. t, a thunk of two holes (`NarrowBlocks.thunkKind`). */
  private val truth = NoFacts.thunkOrInstance(
    Code.Slot(0),
    Vector(Hole.Bound(0), Hole.Ignored),
    Vector.empty
  )

  /** A filter `x ∥ c t`, x a closed term of no narrow kind and `c t` a
    * criterion, is narrow (`NarrowBlocks.parallelKind`) although its criterion
    * is an unpriced child: the module reads an unpriced child's kind from its
    * reading. Its purpose is to catch an unpriced criterion read as `Closed`,
    * which left every filter interpreted and no hot program compiled to a block
    * (a practice read: 16,684,081 steps on calls_10000_hot direct, against 0.55
    * s as a block before).
    */
  stoppableProperty("aFilterOverAnUnpricedCriterionIsNarrow") { stopped =>
    val operands = Vector(
      NoFacts.thunkOrInstance(
        Code.Apply(Code.Slot(0), Code.Slot(0)),
        Vector(Hole.Bound(0)),
        Vector.empty
      ),
      NoFacts.thunkOrInstance(
        Code.Apply(Code.Slot(0), Code.Apply(Code.Slot(0), Code.Slot(0))),
        Vector(Hole.Bound(0)),
        Vector.empty
      )
    )
    for operand <- hedgehog.Gen
        .element(operands.head, operands.tail.toList)
        .forAll
    yield
      val model =
        ModuleCostModel(modules, reading, StopSignal.completedWith(stopped))
      val named = (instruction: Configured[NoFacts.type]) =>
        model.cost(gezi.extraction.Shape.Name(instruction), Vector.empty)
      val criterion = model.cost(
        gezi.extraction.Shape.Node(0, Apply(1, 2)),
        Vector(named(criterionFunction), named(truth))
      )
      val filter = model.cost(
        gezi.extraction.Shape.Node(0, Parallel(1, 2)),
        Vector(named(operand), criterion)
      )
      val kinds = filter.states.collect { case NarrowBlockState(kind, _) =>
        kind
      }
      hedgehog.Result
        .assert(kinds.nonEmpty && kinds.forall(NarrowBlocks.narrow))
        .log(s"criterion states ${criterion.states}")
        .log(s"filter states ${filter.states}")
  }

  /** A native's call is monotone in a `Closed` operand within its reading: of
    * two operands of the reading `Closed`, a closed wrapper `w (… (w (f a)))`
    * over a narrow call of a native f of one place, whose rank is small and
    * whose size is large, and an interpreted chain `w (… (w w))`, whose rank is
    * its size, the better under the order gives the call of a native g of two
    * places over it a cost no worse. The generic terms of
    * `CostMonotonicityLaws` never pair two such operands. Its purpose is to
    * catch a narrow call that ranks 0 whatever its operand ranks while
    * compression reads the operand's size (a practice read: a stale (k | 69)
    * operand gave the call (0 | 71), its better (2 | 73) gave (0 | 75), and
    * CountedExtraction.settled threw).
    */
  stoppableProperty("aNativeCallIsMonotoneInItsClosedOperand") { stopped =>
    val wrapper = NoFacts.thunkOrInstance(
      Code.Apply(Code.Slot(0), Code.Slot(0)),
      Vector(Hole.Bound(0)),
      Vector.empty
    )
    val byPlaces = (places: Int) =>
      nativeBindings.find(bound =>
        natives.natives
          .get(NativeName.Function(bound.native))
          .exists(_.parameterCount == places)
      )
    (byPlaces(1), byPlaces(2)) match
      case (Some(onePlace), Some(twoPlaces)) =>
        for
          wrappings <- hedgehog.Gen.int(hedgehog.Range.linear(1, 6)).forAll
          chainLength <- hedgehog.Gen.int(hedgehog.Range.linear(0, 12)).forAll
        yield
          val model =
            ModuleCostModel(modules, reading, StopSignal.completedWith(stopped))
          val named = (instruction: Configured[NoFacts.type]) =>
            model.cost(gezi.extraction.Shape.Name(instruction), Vector.empty)
          val applied = (
              function: gezi.strategies.ModuleCost,
              argument: gezi.strategies.ModuleCost
          ) =>
            model.cost(
              gezi.extraction.Shape.Node(0, Apply(1, 2)),
              Vector(function, argument)
            )
          val narrowCall = applied(named(onePlace.instruction), named(wrapper))
          val wrapped = (1 to wrappings).foldLeft(narrowCall)((inner, _) =>
            applied(named(wrapper), inner)
          )
          val chain = (1 to chainLength).foldLeft(named(wrapper))((inner, _) =>
            applied(named(wrapper), inner)
          )
          if !model.sameReading(wrapped, chain) then hedgehog.Result.success
          else
            val (better, worse) =
              if model.ordering.compare(wrapped, chain) <= 0 then
                (wrapped, chain)
              else (chain, wrapped)
            val overBetter = applied(named(twoPlaces.instruction), better)
            val overWorse = applied(named(twoPlaces.instruction), worse)
            hedgehog.Result
              .assert(model.ordering.compare(overBetter, overWorse) <= 0)
              .log(s"better operand ${better.ranks}, worse ${worse.ranks}")
              .log(
                s"call over the better ${overBetter.ranks}, over the worse ${overWorse.ranks}"
              )
      case _ =>
        throw IllegalStateException(
          "the loaded natives have no function of one place and one of two"
        )
  }

  /** A choice ranks what its compiled member leaves outside blocks: with a
    * narrow member, the backend compiles the first narrow one and drops the
    * others (`NarrowBlocks.chosenMember`), so the choice ranks that member's
    * outside size whatever the other member's; with none, it is `Closed` and
    * ranks one and its members' ranks. The members are generated: an
    * interpreted chain `w (… (w w))` of a generated length, and either a filter
    * `w ∥ c t` (narrow) or another chain (not narrow), in either order. Its
    * purpose is to catch a narrow choice that counts its dropped members, which
    * made `F A + T` never rank below `F A` and left every hot program
    * interpreted, and a choice of no narrow member ranked as if it had one.
    */
  stoppableProperty("aChoiceRanksWhatItsCompiledMemberLeavesOutside") {
    stopped =>
      val wrapper = NoFacts.thunkOrInstance(
        Code.Apply(Code.Slot(0), Code.Slot(0)),
        Vector(Hole.Bound(0)),
        Vector.empty
      )
      for
        untypedLength <- hedgehog.Gen.int(hedgehog.Range.linear(0, 12)).forAll
        otherLength <- hedgehog.Gen.int(hedgehog.Range.linear(0, 12)).forAll
        typedIsFilter <- hedgehog.Gen.boolean.forAll
        untypedFirst <- hedgehog.Gen.boolean.forAll
      yield
        val model =
          ModuleCostModel(modules, reading, StopSignal.completedWith(stopped))
        val named = (instruction: Configured[NoFacts.type]) =>
          model.cost(gezi.extraction.Shape.Name(instruction), Vector.empty)
        val applied = (
            function: gezi.strategies.ModuleCost,
            argument: gezi.strategies.ModuleCost
        ) =>
          model.cost(
            gezi.extraction.Shape.Node(0, Apply(1, 2)),
            Vector(function, argument)
          )
        val chain = (length: Int) =>
          (1 to length).foldLeft(named(wrapper))((inner, _) =>
            applied(named(wrapper), inner)
          )
        val criterion = applied(named(criterionFunction), named(truth))
        val filter = model.cost(
          gezi.extraction.Shape.Node(0, Parallel(1, 2)),
          Vector(named(wrapper), criterion)
        )
        val untyped = chain(untypedLength)
        val typed = if typedIsFilter then filter else chain(otherLength)
        val members = if untypedFirst then Vector(untyped, typed)
        else Vector(typed, untyped)
        val choice =
          model.cost(gezi.extraction.Shape.Node(0, Choice(1, 2)), members)
        val state = (cost: gezi.strategies.ModuleCost) =>
          cost.states.collectFirst { case narrowState: NarrowBlockState =>
            narrowState
          }
        val expected =
          if typedIsFilter then state(typed).map(_.residual)
          else
            val memberStates = members.flatMap(state)
            Option.when(memberStates.size == members.size)(
              1 + memberStates.map(_.residual).sum
            )
        hedgehog.Result
          .assert(state(choice).map(_.residual) == expected)
          .log(s"members ${members.map(_.states)}")
          .log(s"choice ${choice.states}, expected rank $expected")
  }
