package com.yang_bo.gezi.strategies

import com.yang_bo.gezi.saturation.StopSignal
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.extraction.CostModel
import com.yang_bo.gezi.extraction.Shape
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.StandInStorages
import com.yang_bo.gezi.ir.NotTerm
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Fallback
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.Pure
import com.yang_bo.gezi.ir.Layer
import com.yang_bo.gezi.ir.Specialization
import com.yang_bo.gezi.ir.SpecializationRange
import com.yang_bo.gezi.standardlibrary.CombinatorProperty
import com.yang_bo.gezi.standardlibrary.NativeBound
import com.yang_bo.gezi.standardlibrary.Property
import com.yang_bo.gezi.standardlibrary.StandardLibraryIndex
import com.yang_bo.gezi.ir.{Apply, Choice, Parallel, Thunk}

/** The contract of a cost model of the extraction (`com.yang_bo.gezi.extraction.CostModel`,
  * THE CONTRACT): for every production and every child position, replacing the
  * child's cost by one of the same reading that is not worse under the model's
  * ordering gives a cost of the same reading that is not worse.
  * `com.yang_bo.gezi.extraction.CountedExtraction` keeps a class's best entry of each
  * reading, read to its fixed point; under a cost that breaks the law a re-made
  * entry over a child's better entry ranks worse than the entry kept, which
  * then stays over a child entry its class no longer keeps, and which stale
  * entries survive depends on the order the productions were entered (the
  * native route's 4..40 series, 2026-11-12).
  *
  * Its purpose is to catch a module, or a lexicographic combination of modules,
  * whose production cost is not monotone in its children's costs within a
  * reading, or whose reading does not follow from its children's readings. The
  * law is checked on generated terms through `ModuleCostModel.cost`, the path
  * the extraction takes: a parent production (a layer, a specialization choice
  * or a judgment), one of its children, and the first of some generated terms
  * whose cost has the child's reading; the parent over the better of the two
  * must not rank worse than the parent over the other, and the two parents have
  * one reading. A choice folds both its members, a specialization choice its
  * typed member and a judgment is its value's entry (`ModuleCostModel`, THE
  * PRICE OF A CHOICE); the generator makes choices of a term and a parallel
  * over it too.
  *
  * `filter_attraction` is left out: it is not monotone, and no finite reading
  * makes it so (the FIXME at `FilterAttraction`).
  */
trait CostMonotonicityLaws extends GeneratedProperties:

  private given NoFacts.type = NoFacts

  // A generated term is no term of the IR: it is the tests' own tree over which layers are built.
  private given NotTerm[GeneratedTerm] = NotTerm.granted

  /** Instructions with a layer, as the names a production of the extraction
    * reads are: `λx. x`, `λx. x x`, `λx. λy. x` and `λx. x ∥ c` with c opaque;
    * the last two with an occurrence role, so that the occurrence tags of
    * `specialization_attraction` are read.
    */
  private val identity =
    NoFacts.thunkOrInstance(Code.Slot(0), Vector(Hole.Bound(0)), Vector.empty)
  private val selfApplication = NoFacts.thunkOrInstance(
    Code.Apply(Code.Slot(0), Code.Slot(0)),
    Vector(Hole.Bound(0)),
    Vector.empty
  )
  private val named = NoFacts.thunkOrInstance(
    Code.Thunk(Code.Slot(1), Vector(Hole.Bound(0)), Vector(Code.Slot(0))),
    Vector(Hole.Bound(0)),
    Vector.empty
  )
  private val nextTag = NoFacts.thunkOrInstance(
    Code.Parallel(Code.Slot(0), Code.Slot(1)),
    Vector(Hole.Bound(0)),
    Vector(NoFacts.opaque("cost-monotonicity-criterion"))
  )

  /** Contracts read as λf. f (`TermReading.identityContract`): `λf y. f y`, and
    * `λf y. f y + (f (y ∥ c)) ∥ c`, the contract of a curried function's last
    * argument, which the refinement runs as `f y` up to its judgments.
    */
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
    Vector(NoFacts.opaque("cost-monotonicity-criterion"))
  )
  private val allInstructions = Vector(
    identity,
    selfApplication,
    named,
    nextTag,
    identityContract,
    lastArgumentContract
  )

  /** The instructions the terms are built over: all of them, unless a suite
    * leaves out those whose layers hold an opaque criterion (`nextTag`,
    * `lastArgumentContract`), which a module that reads a name's layers through
    * its fillings, such as the narrow blocks', cannot read; no IR term of the
    * tree holds an opaque instruction.
    */
  protected def withOpaqueCriteria: Boolean = true

  private def instructions: Vector[Configured[NoFacts.type]] =
    (if withOpaqueCriteria then allInstructions
     else Vector(identity, selfApplication, named, identityContract)) ++
      nativeBindings.map(binding =>
        Configured.fromPure(NoFacts)(binding.instruction)
      ) ++ criterionFunctions

  /** Instructions the suite's index binds to natives (`native` declarations),
    * added to the instructions the terms are built over, so that a module that
    * reads a native's arity, such as the narrow blocks', reads its calls and
    * their operands; none by default.
    */
  protected def nativeBindings: Vector[NativeBound] = Vector.empty

  /** Instructions the suite's index declares criterion functions of a native
    * specialization (`combinator_property` `native_specialization`), added to
    * the instructions the terms are built over, so that a filter `x ∥ c t` over
    * a truth t reads as a filter; none by default.
    */
  protected def criterionFunctions: Vector[Configured[NoFacts.type]] =
    Vector.empty

  protected lazy val reading: TermReading[NoFacts.type] = TermReading(
    StandardLibraryIndex(
      NoFacts,
      Vector.empty,
      Vector.empty,
      nativeBindings,
      Vector(
        CombinatorProperty(Pure.required(named), Property.NameMarker),
        CombinatorProperty(Pure.required(nextTag), Property.TagNext)
      ) ++ criterionFunctions.map(function =>
        CombinatorProperty(
          Pure.required(function),
          Property.NativeSpecialization("binary")
        )
      )
    )
  )

  /** A term as the extraction builds it: a name, or a layer over terms. */
  private enum GeneratedTerm:
    case Name(instruction: Configured[NoFacts.type])
    case Node(layer: Layer[GeneratedTerm])

  /** The thunks of one binder, slot 0, whose fillings are the slots from 1,
    * with their numbers of fillings: a filter `λx. x ∥ T`, a constant closure
    * `λx. M`, `λx. M x`, `λx. M + N`, a choice inside a code, which the modules
    * read themselves, and `λx. F x + C (F (x ∥ D))`, a curried specialization
    * choice whose price turns on whether the filling C is read as λf. f.
    */
  private val thunkCodes = Vector(
    (Code.Parallel(Code.Slot(0), Code.Slot(1)), 1),
    (Code.Slot(1), 1),
    (Code.Apply(Code.Slot(1), Code.Slot(0)), 1),
    (Code.Choice(Code.Slot(1), Code.Slot(2)), 2),
    (
      Code.Choice(
        Code.Apply(Code.Slot(1), Code.Slot(0)),
        Code.Apply(
          Code.Slot(2),
          Code.Apply(Code.Slot(1), Code.Parallel(Code.Slot(0), Code.Slot(3)))
        )
      ),
      3
    )
  )

  private def name: Gen[GeneratedTerm] = Gen
    .element(instructions.head, instructions.tail.toList)
    .map(GeneratedTerm.Name(_))

  private def layer(depth: Int): Gen[Layer[GeneratedTerm]] =
    val child = term(depth - 1)
    Gen.frequency1(
      3 -> (for function <- child; argument <- child
      yield Apply(function, argument)),
      2 -> (for left <- child; right <- child yield Parallel(left, right)),
      2 -> (for left <- child; right <- child yield Choice(left, right)),
      2 -> (for
        value <- child
        criterion <- child
        parallelFirst <- Gen.boolean
      yield
        val parallel = GeneratedTerm.Node(Parallel(value, criterion))
        if parallelFirst then Choice(parallel, value)
        else Choice(value, parallel)),
      2 -> (for
        (code, fillingCount) <- Gen
          .element(thunkCodes.head, thunkCodes.tail.toList)
        fillings <- child.list(Range.singleton(fillingCount))
      yield Thunk(code, Vector(Hole.Bound(0)), fillings.toVector))
    )

  private def term(depth: Int): Gen[GeneratedTerm] =
    if depth <= 0 then name
    else Gen.frequency1(1 -> name, 3 -> layer(depth).map(GeneratedTerm.Node(_)))

  /** The class of a term: equal terms are one class. */
  private def classOf(generated: GeneratedTerm): Int = generated.hashCode

  /** A production of the extraction over generated children: a layer, a
    * specialization choice of each kind of typed member, or a judgment
    * (`Shape`).
    */
  private enum Parent:
    case OfLayer(layer: Layer[GeneratedTerm])
    case OfSpecialization(specialization: Specialization[GeneratedTerm])
    case OfJudgment(fallback: Fallback[GeneratedTerm])

    def children: Vector[GeneratedTerm] = this match
      case OfLayer(layer)                   => layer.children
      case OfSpecialization(specialization) => specialization.parts
      case OfJudgment(fallback)             => fallback.parts

  private def parent(depth: Int): Gen[Parent] =
    val child = term(depth - 1)
    Gen.frequency1(
      6 -> layer(depth).map(Parent.OfLayer(_)),
      2 -> (for
        function <- child
        argument <- child
        domain <- child
        kind <- Gen.int(Range.linear(0, 2))
        outer <- child
        untypedFirst <- Gen.boolean
      yield
        val range = kind match
          case 0 => SpecializationRange.Absent
          case 1 => SpecializationRange.Filtered(outer)
          case _ => SpecializationRange.Contracted(outer)
        Parent.OfSpecialization(
          Specialization(function, argument, domain, range, untypedFirst)
        )),
      1 -> (for value <- child; criterion <- child; valueFirst <- Gen.boolean
      yield Parent.OfJudgment(Fallback(value, criterion, valueFirst)))
    )

  /** The cost of the parent's production, its children the classes of the
    * parent's children, over the costs of the entries given for them.
    */
  private def productionCost(
      model: ModuleCostModel[NoFacts.type],
      parent: Parent,
      entries: Vector[GeneratedTerm]
  ): ModuleCost =
    model.cost(shapeOf(parent), entries.map(cost(model, _)))

  private def shapeOf(parent: Parent): Shape[NoFacts.type] = parent match
    case Parent.OfLayer(layer) => Shape.Node(0, layer.map(classOf))
    case Parent.OfSpecialization(specialization) =>
      Shape.Specialized(0, specialization.map(classOf))
    case Parent.OfJudgment(fallback) =>
      Shape.Judged(
        0,
        Fallback(
          classOf(fallback.value),
          classOf(fallback.criterion),
          fallback.valueFirst
        )
      )

  private def cost(
      model: ModuleCostModel[NoFacts.type],
      generated: GeneratedTerm
  ): ModuleCost = generated match
    case GeneratedTerm.Name(instruction) =>
      model.cost(Shape.Name(instruction), Vector.empty)
    case GeneratedTerm.Node(nodeLayer) =>
      productionCost(model, Parent.OfLayer(nodeLayer), nodeLayer.children)

  /** The parent's production keeps its children's classes, and the entry at the
    * position is replaced by another of the same reading, as the extraction
    * replaces a child entry by a better one of its class.
    */
  protected def monotone(model: ModuleCostModel[NoFacts.type]) =
    for
      parentProduction <- parent(3).forAll
      position <- Gen
        .int(Range.linear(0, parentProduction.children.size - 1))
        .forAll
      generated <- term(3).list(Range.linear(1, 16)).forAll
    yield
      val children = parentProduction.children
      val original = children(position)
      val originalCost = cost(model, original)
      generated.find(candidate =>
        model.sameReading(cost(model, candidate), originalCost)
      ) match
        case None              => Result.success
        case Some(replacement) =>
          val (better, worse) =
            if model.ordering.compare(
                cost(model, replacement),
                originalCost
              ) <= 0
            then (replacement, original)
            else (original, replacement)
          val parentOverBetter = productionCost(
            model,
            parentProduction,
            children.updated(position, better)
          )
          val parentOverWorse = productionCost(
            model,
            parentProduction,
            children.updated(position, worse)
          )
          Result
            .assert(
              model.ordering.compare(parentOverBetter, parentOverWorse) <= 0
            )
            .and(
              Result.assert(
                model.sameReading(parentOverBetter, parentOverWorse)
              )
            )
            .log(s"parent $parentProduction at position $position")
            .log(s"better child $better ranks ${cost(model, better).ranks}")
            .log(s"worse child $worse ranks ${cost(model, worse).ranks}")
            .log(
              s"parent over the better child ranks ${parentOverBetter.ranks}"
            )
            .log(s"parent over the worse child ranks ${parentOverWorse.ranks}")

  /** A native storage leaf of constant size ranks no worse than any generated
    * term under the model given: the storage leaf, a name of the extractor,
    * ranks first or ties. On the native route's combination it holds because
    * the leaf's ranks are each module's least, (0, Filter, 0) under
    * `specialization_attraction` and size 1 under `compression`, which no
    * production goes below, a specialization or a judgment included (a judgment
    * costs its value's entry, a specialization its typed member's fold); the
    * generated terms sample that claim. It compares ranks across readings: it
    * does not make the leaf the best entry of every reading of its class, so it
    * is not by itself a license to stop the extraction at such a class. Its
    * purpose is to catch a model that prices a storage leaf above another
    * spelling, under which a folded storage loses to a written member.
    */
  protected def constantStorageLeast(
      model: ModuleCostModel[StandInStorages.type]
  ) =
    for generated <- term(3).forAll
    yield
      // The storage is a term of the stand-in configuration, so the generated term is priced there too: its names, all
      // keys of the facts, entered by `Configured.fromPure`, its layers built over the same classes as `cost` does.
      def standInCost(term: GeneratedTerm): ModuleCost = term match
        case GeneratedTerm.Name(instruction) =>
          model.cost(
            Shape.Name(
              Configured.fromPure(StandInStorages)(Pure.required(instruction))
            ),
            Vector.empty
          )
        case GeneratedTerm.Node(nodeLayer) =>
          model.cost(
            Shape.Node(0, nodeLayer.map(classOf)),
            nodeLayer.children.map(standInCost)
          )
      val storage: StandInStorages.Term =
        StandInStorages.stored(
          ExtractedStorage(
            StandInStorages.opaque("cost law storage value"),
            StandInStorages.opaque("cost law storage criterion")
          )
        )
      val storageCost = model.cost(Shape.Name(storage), Vector.empty)
      val generatedCost = standInCost(generated)
      Result
        .assert(model.ordering.compare(storageCost, generatedCost) <= 0)
        .log(
          s"$generated ranks ${generatedCost.ranks}, the storage leaf ${storageCost.ranks}"
        )

  /** The suite's reading in the stand-in configuration, the library's index
    * crossed into it.
    */
  protected lazy val standInReading: TermReading[StandInStorages.type] =
    TermReading(StandardLibraryIndex.crossed(reading.index, StandInStorages))

  protected def tiesAreIndistinguishable(model: ModuleCostModel[NoFacts.type]) =
    for
      parentProduction <- parent(3).forAll
      position <- Gen
        .int(Range.linear(0, parentProduction.children.size - 1))
        .forAll
      generated <- term(3).list(Range.linear(1, 16)).forAll
    yield
      val children = parentProduction.children
      val original = children(position)
      val originalCost = cost(model, original)
      generated.find(candidate =>
        val candidateCost = cost(model, candidate)
        candidate != original && model.sameReading(
          candidateCost,
          originalCost
        ) &&
        model.ordering.compare(candidateCost, originalCost) == 0
      ) match
        case None              => Result.success
        case Some(replacement) =>
          val parentOverOriginal =
            productionCost(model, parentProduction, children)
          val parentOverReplacement = productionCost(
            model,
            parentProduction,
            children.updated(position, replacement)
          )
          Result
            .assert(
              model.ordering.compare(
                parentOverOriginal,
                parentOverReplacement
              ) == 0
            )
            .and(
              Result.assert(
                model.sameReading(parentOverOriginal, parentOverReplacement)
              )
            )
            .log(s"parent $parentProduction at position $position")
            .log(s"child $original, states ${originalCost.states}")
            .log(
              s"tied child $replacement, states ${cost(model, replacement).states}"
            )
            .log(
              s"parent over the first ranks ${parentOverOriginal.ranks}, states ${parentOverOriginal.states}"
            )
            .log(
              s"parent over the tied one ranks ${parentOverReplacement.ranks}, states ${parentOverReplacement.states}"
            )

  /** What an unpriced position means (`ModuleCostModel.pricedChildren`): at a
    * position the model does not price, replacing the child by another of the
    * same reading, whatever its cost, gives the parent the same cost and
    * reading. Its purpose is to catch a module that reads an unpriced child's
    * cost, or a model that hands it one.
    */
  protected def unpricedChildrenAreReadByTheirReading(
      model: ModuleCostModel[NoFacts.type]
  ) =
    for
      parentProduction <- parent(3).forAll
      position <- Gen
        .int(Range.linear(0, parentProduction.children.size - 1))
        .forAll
      generated <- term(3).list(Range.linear(1, 16)).forAll
    yield
      val children = parentProduction.children
      val original = children(position)
      val originalCost = cost(model, original)
      val priced = CostModel.pricedUnder(
        model,
        shapeOf(parentProduction),
        children.map(cost(model, _))
      )
      generated.find(candidate =>
        candidate != original && model.sameReading(
          cost(model, candidate),
          originalCost
        )
      ) match
        case Some(replacement) if !priced(position) =>
          val parentOverOriginal =
            productionCost(model, parentProduction, children)
          val parentOverReplacement = productionCost(
            model,
            parentProduction,
            children.updated(position, replacement)
          )
          Result
            .assert(
              model.ordering.compare(
                parentOverOriginal,
                parentOverReplacement
              ) == 0
            )
            .and(
              Result.assert(
                model.sameReading(parentOverOriginal, parentOverReplacement)
              )
            )
            .log(s"parent $parentProduction at unpriced position $position")
            .log(s"child $original ranks ${originalCost.ranks}")
            .log(
              s"replacement $replacement ranks ${cost(model, replacement).ranks}"
            )
            .log(s"parent over the first ranks ${parentOverOriginal.ranks}")
            .log(
              s"parent over the replacement ranks ${parentOverReplacement.ranks}"
            )
        case _ => Result.success

  /** The contract's strictness at priced positions
    * (`com.yang_bo.gezi.extraction.CostModel`, THE CONTRACT): at a position the model
    * prices (`ModuleCostModel.pricedChildren`), replacing the child's cost by a
    * strictly costlier one of the same reading gives a strictly costlier
    * parent. `com.yang_bo.gezi.extraction.CountedExtraction`'s last pass reads a priced
    * child by its class's entries at their least cost; under a cost that
    * saturates at a priced position the least tree may take a costlier child at
    * no change of the parent's cost, which that pass never tries. Its purpose
    * is to catch a module, or a combination of modules, that does not count a
    * priced child's cost strictly.
    */
  protected def strictlyMonotone(model: ModuleCostModel[NoFacts.type]) =
    for
      parentProduction <- parent(3).forAll
      position <- Gen
        .int(Range.linear(0, parentProduction.children.size - 1))
        .forAll
      generated <- term(3).list(Range.linear(1, 16)).forAll
    yield
      val children = parentProduction.children
      val original = children(position)
      val originalCost = cost(model, original)
      val priced = CostModel.pricedUnder(
        model,
        shapeOf(parentProduction),
        children.map(cost(model, _))
      )
      generated.find(candidate =>
        val candidateCost = cost(model, candidate)
        model.sameReading(candidateCost, originalCost) && model.ordering
          .compare(candidateCost, originalCost) != 0
      ) match
        case Some(replacement) if priced(position) =>
          val (better, worse) =
            if model.ordering.compare(
                cost(model, replacement),
                originalCost
              ) < 0
            then (replacement, original)
            else (original, replacement)
          val parentOverBetter = productionCost(
            model,
            parentProduction,
            children.updated(position, better)
          )
          val parentOverWorse = productionCost(
            model,
            parentProduction,
            children.updated(position, worse)
          )
          Result
            .assert(
              model.ordering.compare(parentOverBetter, parentOverWorse) < 0
            )
            .log(s"parent $parentProduction at priced position $position")
            .log(s"better child $better ranks ${cost(model, better).ranks}")
            .log(s"worse child $worse ranks ${cost(model, worse).ranks}")
            .log(
              s"parent over the better child ranks ${parentOverBetter.ranks}"
            )
            .log(s"parent over the worse child ranks ${parentOverWorse.ranks}")
        case _ => Result.success

  /** A code that the extraction folds by parts (`CodeCandidates.foldsByParts`),
    * over the slots below `slotCount`: choices of two members, read as one
    * choice, as a specialization or as a judgment, outside inner thunks; a
    * parallel's criterion one of `criterionSlots`, the slots that hold the
    * thunk's fillings; and inner thunks, most of them lets `(λh. M) N` whose
    * fillings are slots of the code around them, read once or more, as the
    * front end spells a β residual (beta-canonical-residual's thunks of 18 to
    * 83 fillings).
    */
  private def foldableCode(
      slotCount: Int,
      criterionSlots: Vector[Int],
      depth: Int
  ): Gen[Code] =
    val slot = Gen.int(Range.linear(0, slotCount - 1)).map(Code.Slot(_))
    if depth <= 0 then slot
    else
      val child = foldableCode(slotCount, criterionSlots, depth - 1)
      val criterion = Gen
        .element(criterionSlots.head, criterionSlots.tail.toList)
        .map(Code.Slot(_))
      val innerThunk =
        for
          fillingCount <- Gen.int(Range.linear(0, 3))
          fillings <- slot.list(Range.singleton(fillingCount))
          inner <- innerCode(1 + fillingCount, depth - 1)
        yield Code.Thunk(inner, Vector(Hole.Bound(0)), fillings.toVector)
      // A right member is never a choice, whose members would lengthen the
      // spine, which `CodeCandidates.foldsByParts` does not fold by parts: a
      // choice there stands as its leftmost member.
      val member = child.map(leftmostMember)
      // A choice of two members, which the dispatch patterns may read as a
      // specialization (its typed member `F (A ∥ D)`, under a range R or a
      // contract slot C) or a judgment `X + (X ∥ D)`, in either order; a
      // choice of two other members is read as one choice unless they
      // happen to make one of those.
      val specialization =
        for
          function <- child
          argument <- child
          domain <- criterion
          range <- criterion
          // A filling's slot, whose flag λf. f the dispatch reads; a hole's
          // flag is false, as `CodeCandidates` reads it.
          contract <- criterion
          // Of the same likelihood at every size, as a linear range would
          // keep small samples at the first form; the contract's twice as
          // likely, since a property of twenty samples covers a contract
          // filling that is λf. f only through it.
          form <- Gen.frequency1(
            1 -> Gen.constant(0),
            1 -> Gen.constant(1),
            2 -> Gen.constant(2)
          )
          untypedFirst <- Gen.boolean
        yield
          val application =
            Code.Apply(function, Code.Parallel(argument, domain))
          val typed = form match
            case 0 => application
            case 1 => Code.Parallel(application, range)
            case _ => Code.Apply(contract, application)
          val untyped = Code.Apply(function, argument)
          if untypedFirst then Code.Choice(untyped, typed)
          else Code.Choice(typed, untyped)
      val judgment =
        for
          value <- child
          domain <- criterion
          valueFirst <- Gen.boolean
          last <- member
        yield
          if valueFirst then Code.Choice(value, Code.Parallel(value, domain))
          else Code.Choice(Code.Parallel(last, domain), last)
      Gen.frequency1(
        2 -> slot,
        3 -> (for function <- child; argument <- child
        yield Code.Apply(function, argument)),
        2 -> (for left <- child; right <- criterion
        yield Code.Parallel(left, right)),
        3 -> (for thunk <- innerThunk; argument <- child
        yield Code.Apply(thunk, argument)),
        1 -> innerThunk,
        1 -> (for left <- child; right <- member
        yield Code.Choice(left, right)),
        2 -> specialization,
        1 -> judgment
      )

  /** Whether the code holds, outside its inner thunks, a choice the dispatch
    * patterns read as a specialization or a judgment under some value of a
    * contract's flag (`dispatched`), or one they read as one choice under both
    * (not `dispatched`).
    */
  private def holdsChoice(code: Code, dispatched: Boolean): Boolean =
    code.layer match
      case com.yang_bo.gezi.ir.Choice(left, right) =>
        val read = Vector(true, false).map(flag =>
          CodeCandidates.choiceReading(left, right, _ => flag)
        )
        val here = if dispatched then
          read.exists(_ != CodeCandidates.ChoiceReading.Plain)
        else read.forall(_ == CodeCandidates.ChoiceReading.Plain)
        here || holdsChoice(left, dispatched) || holdsChoice(right, dispatched)
      case com.yang_bo.gezi.ir.Apply(function, argument) =>
        holdsChoice(function, dispatched) || holdsChoice(argument, dispatched)
      case com.yang_bo.gezi.ir.Parallel(left, right) =>
        holdsChoice(left, dispatched) || holdsChoice(right, dispatched)
      case _ => false

  /** The code, or a choice's leftmost member, its left members followed. */
  @scala.annotation.tailrec
  private def leftmostMember(code: Code): Code = code.layer match
    case com.yang_bo.gezi.ir.Choice(left, _) => leftmostMember(left)
    case _                       => code

  /** An inner thunk's code over its hole, slot 0, and its fillings: no
    * parallel, whose criterion would have to be a filling of the thunk whose
    * candidates are found.
    */
  private def innerCode(slotCount: Int, depth: Int): Gen[Code] =
    val slot = Gen.int(Range.linear(0, slotCount - 1)).map(Code.Slot(_))
    if depth <= 0 then slot
    else
      val child = innerCode(slotCount, depth - 1)
      Gen.frequency1(
        2 -> slot,
        3 -> (for function <- child; argument <- child
        yield Code.Apply(function, argument)),
        1 -> (for
          fillingCount <- Gen.int(Range.linear(0, 2))
          fillings <- slot.list(Range.singleton(fillingCount))
          inner <- innerCode(1 + fillingCount, depth - 1)
          argument <- child
        yield Code.Apply(
          Code.Thunk(inner, Vector(Hole.Bound(0)), fillings.toVector),
          argument
        ))
      )

  /** A thunk folded by parts: its holes, its fillings' slots and its code. */
  private def foldableThunk: Gen[(Vector[Hole], Int, Code)] =
    for
      holeCount <- Gen.int(Range.linear(0, 2))
      fillingCount <- Gen.int(Range.linear(1, 4))
      code <- foldableCode(
        holeCount + fillingCount,
        Vector.tabulate(fillingCount)(holeCount + _),
        4
      )
    yield (Vector.tabulate(holeCount)(Hole.Bound(_)), fillingCount, code)

  /** A thunk folded by parts whose code holds every case the laws below are
    * for, by construction: `(S + (Slot i + Slot j)) (Slot r Slot r)` where S is
    * a specialization whose typed member is under a contract slot C,
    * `F (A ∥ D)` applied to C, beside `F A` (a choice the dispatch reads as a
    * specialization when C's flag is λf. f, `CodeCandidates.choiceReading`),
    * `Slot i + Slot j` a choice it reads as one choice under either flag, and r
    * a filling read twice, which is read jointly
    * (`ThunkCandidates.jointFillings`) and repeated
    * (`CodeCandidates.repeatedFillings`).
    */
  private def everyCaseThunk: Gen[(Vector[Hole], Int, Code)] =
    for
      holeCount <- Gen.int(Range.linear(0, 2))
      fillingCount <- Gen.int(Range.linear(1, 4))
      slotCount = holeCount + fillingCount
      fillingSlots = Vector.tabulate(fillingCount)(holeCount + _)
      child = foldableCode(slotCount, fillingSlots, 2)
      fillingSlot = Gen.element(fillingSlots.head, fillingSlots.tail.toList)
      anySlot = Gen.int(Range.constant(0, slotCount - 1))
      function <- child
      argument <- child
      domain <- fillingSlot
      contract <- fillingSlot
      repeated <- fillingSlot
      left <- anySlot
      right <- anySlot
      untypedFirst <- Gen.boolean
    yield
      val typed = Code.Apply(
        Code.Slot(contract),
        Code.Apply(function, Code.Parallel(argument, Code.Slot(domain)))
      )
      val untyped = Code.Apply(function, argument)
      val specialization = if untypedFirst then Code.Choice(untyped, typed)
      else Code.Choice(typed, untyped)
      val code = Code.Apply(
        Code.Apply(
          specialization,
          Code.Choice(Code.Slot(left), Code.Slot(right))
        ),
        Code.Apply(Code.Slot(repeated), Code.Slot(repeated))
      )
      (Vector.tabulate(holeCount)(Hole.Bound(_)), fillingCount, code)

  /** Whether the code holds every case `everyCaseThunk` constructs. */
  private def holdsEveryCase(
      code: Code,
      holes: Vector[Hole],
      fillingCount: Int
  ): Boolean =
    holdsChoice(code, dispatched = true) && holdsChoice(
      code,
      dispatched = false
    ) &&
      CodeCandidates.contractFillings(code, holes, fillingCount).nonEmpty &&
      CodeCandidates.repeatedFillings(code, holes, fillingCount).nonEmpty &&
      ThunkCandidates.jointFillings(code, holes, fillingCount).nonEmpty

  /** `CodeFolding`'s contract for each module of the model that folds codes:
    * closing a thunk's code folded part by part
    * (`CodeCandidates.closedByParts`) gives the state the module's `folded`
    * gives the thunk whole, over the same fillings. Its purpose is to catch a
    * module whose fold of a code's part reads more or less than its fold of the
    * whole thunk does, such as a part summary that counts a filling once per
    * occurrence where the module counts a thunk's children once, or that misses
    * an inner thunk's unread filling.
    */
  protected def foldedByParts(model: ModuleCostModel[NoFacts.type]) =
    for
      generated <- foldableThunk.forAll
      constructed <- everyCaseThunk.forAll
      generatedFillings <- term(2).list(Range.singleton(generated._2)).forAll
      constructedFillings <- term(2)
        .list(Range.singleton(constructed._2))
        .forAll
    yield
      val (holes, fillingCount, code) = constructed
      Result.all(
        List(
          foldedByPartsChecked(model, generated, generatedFillings.toVector),
          Result
            .assert(holdsEveryCase(code, holes, fillingCount))
            .log(s"the constructed code holds not every case: $code"),
          foldedByPartsChecked(model, constructed, constructedFillings.toVector)
        )
      )

  /** `foldedByParts` on one thunk and its fillings. */
  private def foldedByPartsChecked(
      model: ModuleCostModel[NoFacts.type],
      thunk: (Vector[Hole], Int, Code),
      fillings: Vector[GeneratedTerm]
  ): Result =
    val (holes, fillingCount, code) = thunk
    val costs = fillings.map(cost(model, _))
    Result
      .assert(CodeCandidates.foldsByParts(code, holes, fillingCount))
      .log(s"the generated code is not folded by parts: $code")
      .and(
        Result.all(
          model.modules.indices.toList.flatMap(position =>
            model.modules(position).codeFolding.toList.map { folding =>
              val terms = costs.map(each =>
                OrderTerm.Folded[NoFacts.type](
                  each.states(position),
                  each.identityContract
                )
              )
              val byParts = CodeCandidates
                .closedByParts(folding, reading, code, holes, terms)
              val whole = model
                .modules(position)
                .folded(OrderTerm.Thunk(code, holes, terms), reading)
              Result
                .diff(byParts, whole)(_ == _)
                .log(
                  s"${model.modules(position).name}: thunk $code, holes $holes"
                )
            }
          )
        )
      )

  /** The extraction's candidates of a thunk folded by parts (`CodeCandidates`,
    * every module of the model folding codes) against every combination of its
    * fillings' entries: each reading's least cost under each of the model's
    * orderings is the same, and the two have the same readings. Its purpose is
    * to catch a dynamic program over a code that drops a reading or a least
    * cost: a part kept as least of its reading although a part around it reads
    * more of it than its reading, or a filling read twice that two parts choose
    * differently. A filling read more than once counts only when the thunk is
    * closed (`CodeFold.Closing`), which is sound when the parts compared at a
    * node read the same entry of it; each iteration also checks a thunk that
    * holds such a filling with entries of two readings, by construction
    * (`everyCaseThunk`, `options`), the case that argument rests on.
    */
  protected def candidatesByParts(model: ModuleCostModel[NoFacts.type]) =
    everyReadingsLeast(model) { (shape, code, holes, entries) =>
      Vector(
        "by parts" -> CodeCandidates.candidates(
          model,
          model.modules.flatMap(_.codeFolding),
          shape,
          code,
          holes,
          entries,
          costFirst = true
        )
      )
    }

  /** The extraction's candidates of a thunk the model could fold by parts, read
    * at a whole fold bound of 0 (`ThunkCandidates.candidates` takes the dynamic
    * program) and at the largest (it reads the thunk whole), against every
    * combination of its fillings' entries: each reading's least cost under each
    * of the model's orderings is the same, and the readings are the same. Its
    * purpose is to catch a bound (`JointReading.wholeFoldBound`) at which the
    * path it chooses drops a reading or a least cost, so that an entry's choice
    * of the bound changes no reading's least cost while the products stay
    * within the enumeration bound, as the drawn ones do.
    */
  protected def wholeFoldBoundKeepsLeastCosts(
      model: ModuleCostModel[NoFacts.type]
  ) =
    everyReadingsLeast(model) { (shape, code, holes, entries) =>
      Vector(0L, Long.MaxValue).map(bound =>
        val bounded = model.copy(jointReading =
          JointReading(JointReading.measured.enumerationBound, bound)
        )
        s"whole fold bound $bound" -> ThunkCandidates.candidates(
          bounded,
          shape,
          Thunk(code, holes, Vector.tabulate(entries.size)(_ + 1)),
          entries
        )
      )
    }

  /** The law of `candidatesByParts` on the candidate vectors `found` lists,
    * each named, of a generated thunk folded by parts.
    */
  private def everyReadingsLeast(model: ModuleCostModel[NoFacts.type])(
      found: (
          Shape[NoFacts.type],
          Code,
          Vector[Hole],
          Vector[Vector[com.yang_bo.gezi.extraction.Entry[NoFacts.type, ModuleCost]]]
      ) => Vector[
        (String, Vector[com.yang_bo.gezi.extraction.Entry[NoFacts.type, ModuleCost]])
      ]
  ) =
    for
      generated <- foldableThunk.forAll
      generatedOptions <- options(generated, twoReadings = false).forAll
      constructed <- everyCaseThunk.forAll
      constructedOptions <- options(constructed, twoReadings = true).forAll
    yield
      val (holes, fillingCount, code) = constructed
      val repeatedReadTwoWays = CodeCandidates
        .repeatedFillings(code, holes, fillingCount)
        .exists(position =>
          val costs = constructedOptions(position).map(cost(model, _))
          costs.exists(left =>
            costs.exists(right => !model.sameReading(left, right))
          )
        )
      val contractIdentity =
        CodeCandidates
          .contractFillings(code, holes, fillingCount)
          .exists(position =>
            constructedOptions(position).exists(cost(model, _).identityContract)
          )
      Result.all(
        List(
          readingsLeastChecked(model, found, generated, generatedOptions),
          Result
            .assert(
              holdsEveryCase(
                code,
                holes,
                fillingCount
              ) && repeatedReadTwoWays && contractIdentity
            )
            .log(
              s"the constructed case holds not every case: $code, $constructedOptions"
            ),
          readingsLeastChecked(model, found, constructed, constructedOptions)
        )
      )

  /** The entries of each filling of a thunk folded by parts: one to three terms
    * each, a filling read more than once one more, so that it has two entries
    * at least, and a filling in a contract slot also λf. f, so that the
    * dispatch reads the choice both ways; with `twoReadings`, one or two terms
    * each, and a filling read more than once `λf y. f y` and `λx. x x` in place
    * of the one more, whose costs differ in their identity contract, so that
    * its entries have two readings, the case the argument of
    * `candidatesByParts` rests on.
    */
  private def options(
      thunk: (Vector[Hole], Int, Code),
      twoReadings: Boolean
  ): Gen[Vector[Vector[GeneratedTerm]]] =
    val (holes, fillingCount, code) = thunk
    val repeated = CodeCandidates.repeatedFillings(code, holes, fillingCount)
    val contracts = CodeCandidates.contractFillings(code, holes, fillingCount)
    term(2)
      .list(Range.linear(1, if twoReadings then 2 else 3))
      .list(Range.singleton(fillingCount))
      .flatMap(drawn =>
        term(2)
          .list(Range.singleton(fillingCount))
          .map(extra =>
            drawn.zip(extra).zipWithIndex.toVector.map {
              case ((terms, more), position) =>
                val withRepeated =
                  if !repeated.contains(position) then terms.toVector
                  else if twoReadings then
                    terms.toVector ++ Vector(
                      GeneratedTerm.Name(identityContract),
                      GeneratedTerm.Name(selfApplication)
                    )
                  else terms.toVector :+ more
                if contracts.contains(position) then
                  withRepeated :+ GeneratedTerm.Name(identityContract)
                else withRepeated
            }
          )
      )

  /** The law of `candidatesByParts` on one thunk and its fillings' entries. */
  private def readingsLeastChecked(
      model: ModuleCostModel[NoFacts.type],
      found: (
          Shape[NoFacts.type],
          Code,
          Vector[Hole],
          Vector[Vector[com.yang_bo.gezi.extraction.Entry[NoFacts.type, ModuleCost]]]
      ) => Vector[
        (String, Vector[com.yang_bo.gezi.extraction.Entry[NoFacts.type, ModuleCost]])
      ],
      thunk: (Vector[Hole], Int, Code),
      options: Vector[Vector[GeneratedTerm]]
  ): Result =
    val (holes, fillingCount, code) = thunk
    val entries = options.toVector.zipWithIndex.map((terms, position) =>
      terms.toVector.map(generated =>
        com.yang_bo.gezi.extraction.Entry(
          cost(model, generated),
          Shape.Name(instructions(position % instructions.size)),
          Vector.empty
        )
      )
    )
    val thunkLayer = Thunk(code, holes, Vector.tabulate(fillingCount)(_ + 1))
    val shape = Shape.Node(0, thunkLayer)
    val everyCombination = CostModel
      .combinations(entries)
      .map(chosen => model.cost(shape, chosen.map(_.cost)))
    // Of each reading, a cost of it and its least cost under the order.
    val orderings = Vector(model.ordering)
    def leastOfEachReading(
        costs: Vector[ModuleCost]
    ): Vector[(ModuleCost, Vector[ModuleCost])] =
      costs
        .foldLeft(Vector.empty[(ModuleCost, Vector[ModuleCost])]) {
          case (kept, next) =>
            kept.indexWhere((reading, _) =>
              model.sameReading(reading, next)
            ) match
              case -1       => kept :+ (next, orderings.map(_ => next))
              case position =>
                val (reading, least) = kept(position)
                kept.updated(
                  position,
                  (
                    reading,
                    orderings
                      .lazyZip(least)
                      .map((order, sofar) =>
                        if order.lt(next, sofar) then next else sofar
                      )
                  )
                )
        }
    val expected = leastOfEachReading(everyCombination)
    Result
      .assert(
        model.modules.forall(_.codeFolding.isDefined) && CodeCandidates
          .foldsByParts(code, holes, fillingCount)
      )
      .log(s"the case is not folded by parts: $code")
      .and(Result.all(found(shape, code, holes, entries).toList.map {
        (name, candidates) =>
          val read = leastOfEachReading(candidates.map(_.cost))
          Result
            .assert(
              expected.forall((reading, least) =>
                read.exists((other, foundLeast) =>
                  model.sameReading(reading, other) && foundLeast
                    .lazyZip(least)
                    .forall((a, b) => orderings.forall(_.equiv(a, b)))
                )
              )
            )
            .and(
              Result.assert(
                read.forall((other, _) =>
                  expected
                    .exists((reading, _) => model.sameReading(reading, other))
                )
              )
            )
            .log(s"$name ${read.map(_._2.map(_.ranks))}")
      }))
      .log(s"thunk $code, holes $holes, fillings $fillingCount")
      .log(
        s"every combination's least of each reading ${expected.map(_._2.map(_.ranks))}"
      )

  /** A thunk folded by parts whose jointly read fillings have one entry each
    * (`ThunkCandidates.jointProduct` 1) is read whole, and the extraction reads
    * the same of its candidates as of the dynamic program's (`CodeCandidates`):
    * the same readings, and of each reading the same least entry, the entry
    * itself and not only its cost, both by cost then content (what
    * `CountedExtraction` keeps of `candidates`) and by size then content (what
    * `leastCandidates` gives). The law compares what the extraction consumes,
    * not the two candidate vectors, which may differ in the entries no
    * reading's least is. Its purpose is to catch a thunk the split sends to the
    * whole fold where the two paths would extract differently, ties included. A
    * thunk that reads no filling jointly has product 1 whatever its entries and
    * tests nothing the split changes, so each iteration also checks a thunk
    * that reads a filling jointly by construction (`everyCaseThunk`, a filling
    * read twice), each such filling given one entry.
    */
  protected def productOneReadWhole(model: ModuleCostModel[NoFacts.type]) =
    for
      generated <- foldableThunk.forAll
      constructed <- everyCaseThunk.forAll
      generatedOptions <- term(2)
        .list(Range.linear(1, 3))
        .list(Range.singleton(generated._2))
        .forAll
      constructedOptions <- term(2)
        .list(Range.linear(1, 3))
        .list(Range.singleton(constructed._2))
        .forAll
    yield
      val (holes, fillingCount, code) = constructed
      Result.all(
        List(
          productOneChecked(
            model,
            generated,
            generatedOptions.map(_.toVector).toVector
          ),
          Result
            .assert(holdsEveryCase(code, holes, fillingCount))
            .log(s"the constructed code holds not every case: $code"),
          productOneChecked(
            model,
            constructed,
            constructedOptions.map(_.toVector).toVector
          )
        )
      )

  /** `productOneReadWhole` on one thunk and its fillings' entries. */
  private def productOneChecked(
      model: ModuleCostModel[NoFacts.type],
      thunk: (Vector[Hole], Int, Code),
      options: Vector[Vector[GeneratedTerm]]
  ): Result =
    val (holes, fillingCount, code) = thunk
    val joint = ThunkCandidates.jointFillings(code, holes, fillingCount).toSet
    val entries = options.toVector.zipWithIndex.map((terms, position) =>
      terms.toVector
        .take(if joint.contains(position) then 1 else terms.size)
        .map(generated =>
          com.yang_bo.gezi.extraction.Entry(
            cost(model, generated),
            Shape.Name(instructions(position % instructions.size)),
            Vector.empty
          )
        )
    )
    val thunkLayer = Thunk(code, holes, Vector.tabulate(fillingCount)(_ + 1))
    val shape = Shape.Node(0, thunkLayer)
    val foldings = model.modules.flatMap(_.codeFolding)
    def leastByCost(
        found: Vector[com.yang_bo.gezi.extraction.Entry[NoFacts.type, ModuleCost]]
    ) =
      found.foldLeft(
        Vector.empty[com.yang_bo.gezi.extraction.Entry[NoFacts.type, ModuleCost]]
      ) { (kept, next) =>
        kept.indexWhere(entry => model.sameReading(entry.cost, next.cost)) match
          case -1       => kept :+ next
          case position =>
            val order = model.ordering.compare(next.cost, kept(position).cost)
            if order < 0 || (order == 0 && com.yang_bo.gezi.extraction.ContentOrder
                .compare(next, kept(position)) < 0)
            then kept.updated(position, next)
            else kept
      }
    def sameEntries(
        left: Vector[com.yang_bo.gezi.extraction.Entry[NoFacts.type, ModuleCost]],
        right: Vector[com.yang_bo.gezi.extraction.Entry[NoFacts.type, ModuleCost]]
    ) =
      left.size == right.size && left.forall(right.contains)
    val wholeByCost = leastByCost(
      ThunkCandidates.candidates(model, shape, thunkLayer, entries)
    )
    val partsByCost = leastByCost(
      CodeCandidates.candidates(
        model,
        foldings,
        shape,
        code,
        holes,
        entries,
        costFirst = true
      )
    )
    val wholeLeast =
      ThunkCandidates.leastCandidates(model, shape, thunkLayer, entries)
    val partsLeast = CostModel.leastOfEachReading(
      model,
      CodeCandidates.candidates(
        model,
        foldings,
        shape,
        code,
        holes,
        entries,
        costFirst = false
      )
    )
    Result
      .assert(
        ThunkCandidates.jointProduct(
          thunkLayer,
          entries.map(_.size)
        ) == 1 && CodeCandidates.foldsByParts(code, holes, fillingCount)
      )
      .log(s"the case is not of product 1 folded by parts: $code")
      .and(
        Result
          .assert(sameEntries(wholeByCost, partsByCost))
          .log(s"by cost: whole $wholeByCost, by parts $partsByCost")
      )
      .and(
        Result
          .assert(sameEntries(wholeLeast, partsLeast))
          .log(s"by size: whole $wholeLeast, by parts $partsLeast")
      )
      .log(s"thunk $code, holes $holes, fillings $fillingCount, joint $joint")

/** The laws of `CostMonotonicityLaws` on each module of the table and on the
  * combinations the tree's extractions run: the native route's
  * (`NativeRouteCompilation.extraction`), read from its options. The narrow
  * blocks' combination is checked in narrow-blocks
  * (`NarrowBlockCostMonotonicityLawTest`), whose module it is.
  */
class CostMonotonicityLawTest extends CostMonotonicityLaws:

  /** The modules the monotonicity law is checked on: every module of the table
    * but `filter_attraction`, which is not monotone (see the FIXME at
    * `FilterAttraction`).
    */
  private val monotoneModules = BaselineModules
    .table[com.yang_bo.gezi.ir.NoFacts.type]
    .filterNot(_.name == FilterAttraction.name)

  /** The modules the strictness law is checked on: also not
    * `choice_attraction`, which is monotone but not strictly at priced
    * positions (an application's depth is the shallower of its children's; the
    * documentation at `ChoiceAttraction.meetsExtractionContract`).
    */
  private val strictlyMonotoneModules =
    monotoneModules.filterNot(_.name == "choice_attraction")

  private val nativeRoute = TermOrder.modulesChecked(
    BaselineModules.table[com.yang_bo.gezi.ir.NoFacts.type],
    NativeRouteCompilation.extraction.modules
  )

  monotoneModules.foreach { module =>
    stoppableProperty(s"theCostOf${module.name}IsMonotoneInItsChildren") {
      stopped =>
        monotone(
          ModuleCostModel(
            Vector(module),
            reading,
            StopSignal.completedWith(stopped)
          )
        )
    }
  }

  stoppableProperty("theNativeRouteCombinationIsMonotoneInItsChildren") {
    stopped =>
      monotone(
        ModuleCostModel(nativeRoute, reading, StopSignal.completedWith(stopped))
      )
  }

  // The modules that say they meet the extraction's contract: an extraction
  // refuses the others (`TermOrder.extractionModulesChecked`), and
  // `filter_attraction`'s ranks read less of a child's state than its fold
  // does (the FIXME at `FilterAttraction`).
  BaselineModules
    .table[com.yang_bo.gezi.ir.NoFacts.type]
    .filter(_.meetsExtractionContract)
    .foreach { module =>
      stoppableProperty(
        s"theCostOf${module.name}ReadsOfAChildItsCostAndItsReadingOnly"
      ) { stopped =>
        tiesAreIndistinguishable(
          ModuleCostModel(
            Vector(module),
            reading,
            StopSignal.completedWith(stopped)
          )
        )
      }
    }

  // TODO: the law on the narrow blocks' combination, whose reading of a storage leaf (NarrowKind.Closed) is to change
  // with a block backend that reads storages (https://github.com/Atry/private-overlay/issues/2176).
  stoppableProperty(
    "theNativeRouteCombinationPricesAConstantStorageLeafNoHigherThanAnyProduction"
  ) { stopped =>
    constantStorageLeast(
      ModuleCostModel(
        TermOrder.modulesChecked(
          BaselineModules.table[StandInStorages.type],
          NativeRouteCompilation.extraction.modules
        ),
        standInReading,
        StopSignal.completedWith(stopped)
      )
    )
  }

  stoppableProperty(
    "theNativeRouteCombinationReadsOfAChildItsCostAndItsReadingOnly"
  ) { stopped =>
    tiesAreIndistinguishable(
      ModuleCostModel(nativeRoute, reading, StopSignal.completedWith(stopped))
    )
  }

  BaselineModules
    .table[com.yang_bo.gezi.ir.NoFacts.type]
    .filter(_.meetsExtractionContract)
    .foreach { module =>
      stoppableProperty(
        s"theCostOf${module.name}ReadsAnUnpricedChildByItsReading"
      ) { stopped =>
        unpricedChildrenAreReadByTheirReading(
          ModuleCostModel(
            Vector(module),
            reading,
            StopSignal.completedWith(stopped)
          )
        )
      }
    }

  stoppableProperty(
    "theNativeRouteCombinationReadsAnUnpricedChildByItsReading"
  ) { stopped =>
    unpricedChildrenAreReadByTheirReading(
      ModuleCostModel(nativeRoute, reading, StopSignal.completedWith(stopped))
    )
  }

  strictlyMonotoneModules.foreach { module =>
    stoppableProperty(
      s"theCostOf${module.name}IsStrictlyMonotoneInItsPricedChildren"
    ) { stopped =>
      strictlyMonotone(
        ModuleCostModel(
          Vector(module),
          reading,
          StopSignal.completedWith(stopped)
        )
      )
    }
  }

  stoppableProperty(
    "theNativeRouteCombinationIsStrictlyMonotoneInItsPricedChildren"
  ) { stopped =>
    strictlyMonotone(
      ModuleCostModel(nativeRoute, reading, StopSignal.completedWith(stopped))
    )
  }

  stoppableProperty(
    "theNativeRouteCombinationsModulesFoldAThunksCodeByPartsAsTheyFoldItWhole"
  ) { stopped =>
    foldedByParts(
      ModuleCostModel(nativeRoute, reading, StopSignal.completedWith(stopped))
    )
  }

  stoppableProperty(
    "theNativeRouteCombinationsCandidatesByPartsHaveEveryReadingsLeastUnderEachOrdering"
  ) { stopped =>
    candidatesByParts(
      ModuleCostModel(nativeRoute, reading, StopSignal.completedWith(stopped))
    )
  }

  stoppableProperty(
    "theNativeRouteCombinationReadsAThunkOfJointProductOneWholeAsItsPartsWouldBeRead"
  ) { stopped =>
    productOneReadWhole(
      ModuleCostModel(nativeRoute, reading, StopSignal.completedWith(stopped))
    )
  }

  stoppableProperty(
    "theNativeRouteCombinationsCandidatesHaveEveryReadingsLeastAtEitherWholeFoldBound"
  ) { stopped =>
    wholeFoldBoundKeepsLeastCosts(
      ModuleCostModel(nativeRoute, reading, StopSignal.completedWith(stopped))
    )
  }

  /** Every module that says it meets the extraction's contract is among those
    * both laws check, and the two that do not are the two the laws leave out.
    * Its purpose is to catch a module whose flag and whose laws disagree.
    */
  test("theModulesThatMeetTheExtractionsContractAreTheModulesTheLawsCheck") {
    assertEquals(
      BaselineModules
        .table[com.yang_bo.gezi.ir.NoFacts.type]
        .filter(_.meetsExtractionContract)
        .map(_.name),
      strictlyMonotoneModules.map(_.name)
    )
  }
