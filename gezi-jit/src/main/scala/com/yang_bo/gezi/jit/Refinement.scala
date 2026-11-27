package com.yang_bo.gezi.jit

import com.yang_bo.gezi.strategies.DispatchStrategy
import com.yang_bo.gezi.strategies.Round
import com.yang_bo.gezi.strategies.Schedule
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.hotspot.Cache
import com.yang_bo.gezi.hotspot.CacheNamespace
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.DispatchPattern
import com.yang_bo.gezi.ir.Specialization
import com.yang_bo.gezi.ir.SpecializationRange
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.Layer
import com.yang_bo.gezi.saturation.StopSignal
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import com.yang_bo.gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Thunk}
import com.yang_bo.gezi.ir.{
  Configured,
  IrLayer,
  LayerWith,
  NativeSpecializer,
  NativeStorage,
  Opaque,
  UriNode,
  Value
}

/** A strategy chosen when a program is compiled (jit_strategies.pl's
  * `strategy(Kind, Configuration)`): a dispatch strategy, a schedule, the
  * rounds `com.yang_bo.gezi.strategies.Schedule` runs, which this module does not read, and
  * the refinement of the schedule's output, the baseline's `StandardRefinement`
  * unless an entry gives its own.
  */
final case class CompilationStrategy[C <: NativeSpecializer & Singleton](
    dispatch: DispatchStrategy,
    schedule: Vector[Round[C]],
    refinement: OutputRefinement = StandardRefinement
):

  /** The JIT's mode under the strategy (strategy_mode/2). */
  def mode: DispatchMode = DispatchMode.Dispatch(dispatch)

/** How the output of a test's schedule becomes the term the JIT runs, under a
  * library's backend facts: the term, interned. It reads spellings and the
  * backend's facts, never a type (`CONTRIBUTING.md`, "Types live only in the
  * term").
  */
trait OutputRefinement:

  /** The refined term of the output, under the facts of the specializer, whose
    * configuration `C` the terms are of.
    */
  def refined[C <: NativeSpecializer & Singleton](
      specializer: StorageEncoding & C,
      output: Configured[C]
  )(using
      com.yang_bo.gezi.ir.StorageAccess
  ): Configured[C]

/** The baseline's refinement, `Refinement`. */
object StandardRefinement extends OutputRefinement:
  def refined[C <: NativeSpecializer & Singleton](
      specializer: StorageEncoding & C,
      output: Configured[C]
  )(using
      com.yang_bo.gezi.ir.StorageAccess
  ): Configured[C] =
    Refinement(specializer).refined(output)

/** The key of a refined term in `DispatchCache`: the test, the schedule with
  * its budgets, the refinement and the backend facts, whose index is the
  * library the schedule runs under, every input of the dispatch. A cache handed
  * to dispatches under two libraries keeps their refinements apart.
  */
final case class DispatchKey[C <: NativeSpecializer & Singleton](
    test: Configured[C],
    schedule: Vector[Round[C]],
    refinement: OutputRefinement,
    facts: BackendFacts
)

/** The namespace of `jit` in the cache service: the refined term of each test
  * met, by test, schedule, refinement and library. Terms only, no verdict
  * (`CONTRIBUTING.md`, "Types live only in the term"): the refined term equals
  * the test under the λ-lattice laws, its assertions in the term, the memo of a
  * rewriting by lemma instances (`CONTRIBUTING.md`, "Tables", kind 2). Its key
  * holds the library (`DispatchKey.facts`), so a cache handed to dispatches of
  * two libraries keeps them apart, and the namespace holds the native
  * specializer whose spelling its terms are in, by identity, so that a term of
  * one configuration is never found by another.
  */
final case class DispatchCache[C <: NativeSpecializer & Singleton](
    specializer: C
) extends CacheNamespace[DispatchKey[C], Configured[C]]("jit.dispatch")

/** What a code's slot holds at a refinement: a hole of the thunk, or the
  * instruction of a filling.
  */
enum SlotHolds[+Term]:
  case HoleOf(slot: Int)
  case Filling(instruction: Term)

/** The term the JIT runs of a test under a strategy, the port of
  * `gezi/prolog/gezi/jit_strategies.pl`, whose module comment this follows (THE
  * TEST IS THE UNIT; THE REFINEMENT, and why the refined term R equals the
  * output O). A test is run through its strategy's schedule, and the output,
  * `f + typed_f` where the type check spells a typed version (a specialization,
  * `CONTRIBUTING.md`, "Terms"), is refined: a SPECIALIZATION CHOICE becomes the
  * application of the refined function to a fallback point on its argument,
  * under a fallback point by its range off the root's path; a JUDGMENT becomes
  * its term; a CONTRACT's code is rewritten the same way inside the closure. A
  * fallback point is written only for a decoding criterion, a backend fact. The
  * refinement reads spellings and the backend property of criteria, never a
  * type, and names no module, lemma or combinator.
  *
  * FIXME (carried from jit_strategies.pl:51; f's compiled result is to be
  * https://github.com/Atry/private-overlay/issues/1944 cached automatically, to
  * speed it up): f's type check is not shared between tests: the schedule runs
  * on each test, and f's part of it is done again for each. In the Prolog
  * baseline zero's type check round took 135,286 inferences and its erasure
  * round 4,462 (measured 2026-10-30 on main 4eeb7b7d5); f's part is the rest,
  * 1,687,332 inferences to saturate nat_fold zero (compose successor successor)
  * alone, against 2,555,000 or so for its tests on successor^n zero. The terms
  * are hash-consed, f one instruction in every test, but the e-graph's state
  * over them is not: a test's unions with f's argument types change it.
  * Candidate: the strategy saturates an application's function part first,
  * always, and keeps that graph; each test that shares it keeps its unions, its
  * class data and its instance keys in a layer of its own and reads the kept
  * graph where its layer has nothing, so that a test costs what it adds and
  * changes, not f's size. Not designed. (The Scala e-graph is immutable, so the
  * kept graph is shared without a copy; the layer's reads and unions are what
  * is not designed.)
  */
object StrategyDispatch:

  /** The term the JIT runs of the closed test under the strategy
    * (strategy_dispatched/3): the output of the strategy's schedule on the
    * test, run by `Schedule.run` with the library's index of the facts, refined
    * by the strategy's refinement; a test met again under the same schedule and
    * refinement reads the cache service's namespace `DispatchCache` and runs no
    * schedule. The schedule runs outside the namespace's lock: the cache is
    * read first, and the refined term is written after it is computed. The
    * strategy after holds the schedule after the run
    * (`Scheduled.scheduleAfter`), or is the strategy given when the cache
    * answered. The schedule reads the stop signal (judge record 4.4); when a
    * stop was requested by the time the schedule returns, its output depends on
    * when the stop came and not on the key alone, so the refined term is
    * returned and not written to the cache (a key holds every input of what it
    * keeps, `CONTRIBUTING.md`, "Tables"). Throws what `Schedule.run` throws.
    */
  def dispatched[C <: NativeSpecializer & Singleton](
      strategy: CompilationStrategy[C],
      test: Configured[C],
      specializer: StorageEncoding & C,
      cache: Cache,
      stop: StopSignal
  )(using com.yang_bo.gezi.ir.StorageAccess): Dispatched[C] =
    given C = specializer
    val facts = specializer.facts
    val key = DispatchKey(test, strategy.schedule, strategy.refinement, facts)
    val namespace = DispatchCache[C](specializer)
    cache.locked(namespace)(_.tryGet(key)) match
      case Some(found) => Dispatched(found, strategy, scheduleRan = false)
      case None        =>
        val scheduled = Schedule.run(
          specializer.operations.index,
          Vector(test),
          strategy.schedule,
          stop
        )
        val output = scheduled.outputs match
          case Vector(found) => found
          case other         =>
            throw IllegalStateException(
              s"the schedule of one test gave ${other.size} outputs"
            )
        val refinement = strategy.refinement.refined(specializer, output)
        val refined =
          if stop.stopRequested then refinement
          else cache.locked(namespace)(_.getOrElseUpdate(key, refinement))
        Dispatched(
          refined,
          strategy.copy(schedule = scheduled.scheduleAfter),
          scheduleRan = true
        )

/** What a dispatch gives: the instruction of the refined term the JIT runs, the
  * compilation strategy after it, and whether the schedule ran
  * (strategy_typing_count/1 counts these runs), false when the cache answered.
  */
final case class Dispatched[C <: NativeSpecializer & Singleton](
    refined: Configured[C],
    strategyAfter: CompilationStrategy[C],
    scheduleRan: Boolean
)

/** Where a layer is refined: on the root's path through choices, whose value
  * the exit reads, or elsewhere.
  */
enum RefinementPosition:
  case Root
  case Inner

/** The refinement under a library's backend facts (jit_strategies.pl, THE
  * REFINEMENT).
  */
final case class Refinement[C <: NativeSpecializer & Singleton](
    specializer: StorageEncoding & C
)(using
    storageAccess: com.yang_bo.gezi.ir.StorageAccess
):

  // The terms of the refinement are terms of `C`, built through its native specializer.
  private type Term = Configured[C]
  private given C = specializer

  private val rules = JitRules[C](
    JitConfiguration.of[C](specializer, instanceTable = false, storageAccess)
  )

  /** The facts' part in this configuration. */
  private val operations: StorageEncodingOperations[C] = specializer.operations

  /** The state a refinement threads: each layer refined at a position
    * (refined_term/5's Seen), so that the refined term shares what the output
    * shares.
    */
  private final case class Refining(seen: Map[(Term, RefinementPosition), Term])

  private type Step[Result] = Refining => TailRec[(Refining, Result)]

  /** The instruction of the refined term of the output (refined/2). Each layer
    * is refined once for each position it is met at and interned over its
    * refined parts' instructions.
    */
  def refined(output: Term): Term =
    val (_, refinedInstruction) =
      refinedTerm(output, RefinementPosition.Root)(Refining(Map.empty)).result
    refinedInstruction

  /** Whether the instruction is a leaf, kept as written: a leaf of the facts
    * (`BackendFacts.leaves`), or a native storage the e-graph keeps as a leaf
    * (`heldAsLeaf`), a constant whose view is not read. Any other storage is a
    * leaf of its layer too (`layered`): the refinement does not take a storage
    * apart.
    */
  private def leaf(instruction: Term): Boolean =
    operations.leaves.contains(instruction) || instruction.heldAsLeaf

  /** The application, built by the configuration's native specializer. */
  private def applicationInterned(function: Term, argument: Term): Step[Term] =
    refining =>
      done((refining, (specializer: C).application(function, argument)))

  /** The choice, built by the configuration's native specializer. */
  private def choiceInterned(left: Term, right: Term): Step[Term] = refining =>
    done((refining, (specializer: C).choice(left, right)))

  /** The thunk, or the instance of its code when it has no hole, built by the
    * configuration's native specializer.
    */
  private def thunkInterned(
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[Term]
  ): Step[Term] = refining =>
    done((refining, (specializer: C).thunkOrInstance(code, holes, fillings)))

  /** The parallel of the two, built by the facts' native specializer. */
  private def parallelInterned(left: Term, right: Term): Step[Term] =
    refining => done((refining, specializer.parallel(left, right)))

  /** The layer of a term, a leaf having none (layer_read/2); a storage that is
    * no leaf reads as its one-layer view.
    */
  private def layerRead(instruction: Term): Option[Layer[Term]] =
    if leaf(instruction) then None
    else
      instruction.layer match
        case application @ Apply(_, _) => Some(application)
        case parallel @ Parallel(_, _) => Some(parallel)
        case choice @ Choice(_, _)     => Some(choice)
        case thunk @ Thunk(_, _, _)    => Some(thunk)
        case storage: NativeStorage    => Some(specializer.viewOf(storage))
        case _: UriNode | _: Opaque    => None

  private def refinedTerm(
      instruction: Term,
      position: RefinementPosition
  ): Step[Term] = refining =>
    refining.seen.get((instruction, position)) match
      case Some(found)               => done((refining, found))
      case None if leaf(instruction) =>
        done(
          (
            refining.copy(seen =
              refining.seen.updated((instruction, position), instruction)
            ),
            instruction
          )
        )
      case None =>
        // A storage is a leaf of its layer, refined as itself.
        tailcall(
          refinedLayer(instruction, instruction.layer, position)(refining)
        ).map((after, refinedInstruction) =>
          (
            after.copy(seen =
              after.seen.updated((instruction, position), refinedInstruction)
            ),
            refinedInstruction
          )
        )

  private def refinedLayer(
      instruction: Term,
      layer: IrLayer[Term],
      position: RefinementPosition
  ): Step[Term] = refining =>
    layer match
      case Apply(function, argument) =>
        contractParts(function) match
          case Some((contracted, domain, range)) =>
            refinedSpecialization(
              contracted,
              argument,
              domain,
              range,
              position
            )(refining)
          case None =>
            for
              (afterFunction, refinedFunction) <- tailcall(
                refinedHead(function)(refining)
              )
              (afterArgument, refinedArgument) <- tailcall(
                refinedTerm(argument, RefinementPosition.Inner)(afterFunction)
              )
              result <- applicationInterned(refinedFunction, refinedArgument)(
                afterArgument
              )
            yield result
      case Thunk(code, holes, fillings) =>
        tailcall(allRefined(fillings, RefinementPosition.Inner)(refining))
          .flatMap((afterFillings, refinedFillings) =>
            val environment = environmentOf(holes, refinedFillings)
            val refinedCode = codeRefined(code, environment)
            def rebuilt =
              thunkInterned(refinedCode, holes, refinedFillings)(afterFillings)
            refinedCode match
              case Code.Apply(Code.Slot(functionSlot), Code.Slot(holeSlot))
                  if holes == Vector(Hole.Bound(holeSlot)) =>
                environment(functionSlot) match
                  case SlotHolds.Filling(function) =>
                    done((afterFillings, function))
                  case SlotHolds.HoleOf(_) => rebuilt
              case _ => rebuilt
          )
      case Parallel(value, criterion) =>
        tailcall(refinedTerm(value, RefinementPosition.Inner)(refining))
          .flatMap((after, refinedValue) =>
            parallelInterned(refinedValue, criterion)(after)
          )
      case Choice(left, right) =>
        DispatchPattern
          .specializations(
            left,
            right,
            instructionLayers,
            DispatchPattern.noContract
          )
          .headOption match
          case Some(specialization) =>
            refinedSpecialization(
              specialization.function,
              specialization.argument,
              Some(specialization.domain),
              specialization.range,
              position
            )(refining)
          case None =>
            DispatchPattern
              .fallbacks(left, right, instructionLayers)
              .headOption match
              case Some(judgment) =>
                tailcall(refinedTerm(judgment.value, position)(refining))
              case None =>
                tailcall(allRefined(Vector(left, right), position)(refining))
                  .flatMap((after, refinedMembers) =>
                    val Vector(refinedLeft, refinedRight) =
                      refinedMembers: @unchecked
                    choiceInterned(refinedLeft, refinedRight)(after)
                  )
      case _: NativeStorage | _: UriNode | _: Opaque =>
        done((refining, instruction))

  private def allRefined(
      instructions: Vector[Term],
      position: RefinementPosition
  ): Step[Vector[Term]] = refining =>
    def from(
        index: Int,
        current: Refining,
        found: Vector[Term]
    ): TailRec[(Refining, Vector[Term])] =
      if index >= instructions.size then done((current, found))
      else
        tailcall(refinedTerm(instructions(index), position)(current)).flatMap(
          (after, next) => from(index + 1, after, found :+ next)
        )
    from(0, refining, Vector.empty)

  /** What each slot of a thunk's code holds: the thunk's holes and its fillings
    * (slot_values/4).
    */
  private def environmentOf(
      holes: Vector[Hole],
      fillings: Vector[Term]
  ): Vector[SlotHolds[Term]] =
    val holeValues: Vector[SlotHolds[Term]] = holes.map {
      case Hole.Bound(slot) => SlotHolds.HoleOf(slot)
      case Hole.Ignored     => SlotHolds.HoleOf(-1)
    }
    Defunctionalization.slotValues(
      holes,
      holeValues,
      fillings.map(SlotHolds.Filling(_): SlotHolds[Term])
    )

  /** The layers of an instruction as the dispatch patterns read it: its layer,
    * a leaf having none, and a storage's one-layer view `x ∥ T` read as that
    * parallel, since the specialized spelling writes a typed member
    * `f (a ∥ T) ∥ T` and a fallback point's `a ∥ T` as storages wherever they
    * are the unique spelling of one.
    */
  private def instructionLayers(instruction: Term): Vector[Layer[Term]] =
    instruction.layer match
      // The view depends on the configuration's families, which the specializer reads.
      case storage: NativeStorage => Vector(specializer.viewOf(storage))
      case _                      => layerRead(instruction).toVector

  /** The instruction's spelling is λf. f by its syntax (identity_contract/1).
    */
  private def instructionIdentity(instruction: Term): Boolean =
    DispatchPattern.identityContract(instruction, instructionLayers)

  /** A specialization choice refined (refined_specialization/8): the refined
    * function applied to the refined argument under a fallback point by the
    * domain; off the root's path, with a range, under one by the range; with a
    * contract, the refined contract applied to that.
    */
  private def refinedSpecialization(
      function: Term,
      argument: Term,
      domain: Option[Term],
      range: SpecializationRange[Term],
      position: RefinementPosition
  ): Step[Term] = refining =>
    for
      (afterFunction, refinedFunction) <- tailcall(
        refinedHead(function)(refining)
      )
      (afterArgument, refinedArgument) <- tailcall(
        refinedTerm(argument, RefinementPosition.Inner)(afterFunction)
      )
      (afterFiltered, filteredArgument) <- fallbackFiltered(
        refinedArgument,
        domain
      )(afterArgument)
      (afterApplication, application) <- applicationInterned(
        refinedFunction,
        filteredArgument
      )(afterFiltered)
      result <- range match
        case SpecializationRange.Filtered(found)
            if position == RefinementPosition.Inner =>
          fallbackFiltered(application, Some(found))(afterApplication)
        case SpecializationRange.Contracted(contract) =>
          tailcall(
            refinedTerm(contract, RefinementPosition.Inner)(afterApplication)
          ).flatMap((after, refinedContract) =>
            applicationInterned(refinedContract, application)(after)
          )
        case _ => done((afterApplication, application))
    yield result

  /** A function at the head of an application refined (refined_head/4): a
    * contract over a filling is the filling, refined in turn.
    */
  private def refinedHead(function: Term): Step[Term] = refining =>
    layerRead(function) match
      case Some(Thunk(code, holes, fillings)) =>
        contractFunction(code, holes, environmentOf(holes, fillings)) match
          case Some(contracted) => tailcall(refinedHead(contracted)(refining))
          case None             =>
            tailcall(refinedTerm(function, RefinementPosition.Inner)(refining))
      case _ =>
        tailcall(refinedTerm(function, RefinementPosition.Inner)(refining))

  /** The code of a thunk of one hole is a specialization choice of the
    * application of a filling to the hole: the filling (contract_function/4).
    */
  private def contractFunction(
      code: Code,
      holes: Vector[Hole],
      environment: Vector[SlotHolds[Term]]
  ): Option[Term] =
    holes match
      case Vector(Hole.Bound(hole)) =>
        codeSpecialization(code, environment).flatMap(specialization =>
          (specialization.function, specialization.argument) match
            case (Code.Slot(functionSlot), Code.Slot(`hole`)) =>
              fillingAt(environment, functionSlot)
            case _ => None
        )
      case _ => None

  private def fillingAt(
      environment: Vector[SlotHolds[Term]],
      slot: Int
  ): Option[Term] =
    environment.lift(slot).collect { case SlotHolds.Filling(instruction) =>
      instruction
    }

  /** The specialization choice the code is read as by the dispatch patterns
    * (code_typed_parts/6, code_curried_parts/6), a slot read as nothing but a
    * contract's spelling read off the filling it holds.
    */
  private def codeSpecialization(
      code: Code,
      environment: Vector[SlotHolds[Term]]
  ): Option[Specialization[Code]] =
    code match
      case Code.Choice(first, second) =>
        DispatchPattern
          .specializations(
            first,
            second,
            DispatchPattern.codeLayers,
            codeIdentity(environment)
          )
          .headOption
      case _ => None

  /** The code is a slot holding a term whose spelling is λf. f. */
  private def codeIdentity(environment: Vector[SlotHolds[Term]])(
      code: Code
  ): Boolean = code match
    case Code.Slot(slot) =>
      fillingAt(environment, slot).exists(instructionIdentity)
    case _ => false

  /** The function is a closure of one hole whose code is the contract of a
    * filling f applied to the hole (contract_parts/2): f, the domain and the
    * range or the contract, the criteria the values of fillings.
    */
  private def contractParts(
      function: Term
  ): Option[(Term, Option[Term], SpecializationRange[Term])] =
    layerRead(function) match
      case Some(Thunk(code, Vector(Hole.Bound(hole)), fillings)) =>
        val environment = environmentOf(Vector(Hole.Bound(hole)), fillings)
        codeSpecialization(code, environment).flatMap(specialization =>
          (
            specialization.function,
            specialization.argument,
            specialization.domain,
            specialization.range
          ) match
            case (
                  Code.Slot(functionSlot),
                  Code.Slot(`hole`),
                  Code.Slot(domainSlot),
                  range
                ) =>
              val outer: Option[SpecializationRange[Term]] = range match
                case SpecializationRange.Absent =>
                  Some(SpecializationRange.Absent)
                case SpecializationRange.Filtered(Code.Slot(rangeSlot)) =>
                  Some(
                    fillingAt(environment, rangeSlot).fold(
                      SpecializationRange.Absent
                    )(SpecializationRange.Filtered(_))
                  )
                case SpecializationRange.Contracted(Code.Slot(contractSlot)) =>
                  fillingAt(environment, contractSlot).map(
                    SpecializationRange.Contracted(_)
                  )
                case _ => None
              for
                contracted <- fillingAt(environment, functionSlot)
                found <- outer
              yield (contracted, fillingAt(environment, domainSlot), found)
            case _ => None
        )
      case _ => None

  /** The code with each specialization choice rewritten into fallback points by
    * the criteria the environment's fillings hold, and every other node kept
    * (code_refined/3).
    */
  private def codeRefined(
      code: Code,
      environment: Vector[SlotHolds[Term]]
  ): Code =
    codeSpecialization(code, environment) match
      case Some(specialization) =>
        val application = Code.Apply(
          codeRefined(specialization.function, environment),
          codeFallback(
            codeRefined(specialization.argument, environment),
            specialization.domain,
            environment
          )
        )
        specialization.range match
          case SpecializationRange.Absent          => application
          case SpecializationRange.Filtered(range) =>
            codeFallback(application, range, environment)
          case SpecializationRange.Contracted(contract) =>
            Code.Apply(codeRefined(contract, environment), application)
      case None =>
        code match
          case Code.Choice(left, right) =>
            Code.Choice(
              codeRefined(left, environment),
              codeRefined(right, environment)
            )
          case Code.Apply(function, argument) =>
            Code.Apply(
              codeRefined(function, environment),
              codeRefined(argument, environment)
            )
          case Code.Parallel(value, criterion) =>
            Code.Parallel(codeRefined(value, environment), criterion)
          case other => other

  /** Whether the instruction is a decoding criterion, read by its syntax
    * (`JitRules.decodingCriterion`).
    */
  private def decodingCriterion(instruction: Term): Boolean =
    rules.decodingCriterion(Value.of[C](instruction)).isDefined

  /** The code under a fallback point of the criterion when the criterion is a
    * slot holding a decoding criterion (code_fallback/4).
    */
  private def codeFallback(
      value: Code,
      criterion: Code,
      environment: Vector[SlotHolds[Term]]
  ): Code =
    criterion match
      case Code.Slot(slot)
          if fillingAt(environment, slot).exists(decodingCriterion) =>
        Code.Choice(value, Code.Parallel(value, criterion))
      case _ => value

  /** The value under a fallback point of the criterion, unless it is one
    * already or the criterion is no decoding criterion (fallback_filtered/3).
    */
  private def fallbackFiltered(
      value: Term,
      criterion: Option[Term]
  ): Step[Term] = refining =>
    criterion match
      case None        => done((refining, value))
      case Some(found) =>
        val already = layerRead(value) match
          case Some(Choice(inner, point)) =>
            DispatchPattern
              .fallbacks(inner, point, instructionLayers)
              .exists(judgment =>
                judgment.valueFirst && Configured
                  .same(judgment.criterion, found)
              )
          case _ => false
        if already then done((refining, value))
        else if decodingCriterion(found) then
          tailcall(parallelInterned(value, found)(refining)).flatMap(
            (after, filtered) => choiceInterned(value, filtered)(after)
          )
        else done((refining, value))
