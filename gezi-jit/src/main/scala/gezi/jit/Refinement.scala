package gezi.jit

import gezi.strategies.DispatchStrategy
import gezi.strategies.Round
import gezi.strategies.Schedule
import gezi.frontend.Defunctionalization
import gezi.hotspot.Cache
import gezi.hotspot.CacheNamespace
import gezi.ir.Code
import gezi.ir.DispatchPattern
import gezi.ir.Instruction
import gezi.ir.Specialization
import gezi.ir.SpecializationRange
import gezi.ir.Hole
import gezi.ir.Layer
import gezi.saturation.StopSignal
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Thunk}

/** A strategy chosen when a program is compiled (jit_strategies.pl's
  * `strategy(Kind, Configuration)`): a dispatch strategy, a schedule, the
  * rounds `gezi.strategies.Schedule` runs, which this module does not
  * read, and the refinement of the schedule's output, the baseline's
  * `StandardRefinement` unless an entry gives its own.
  */
final case class CompilationStrategy(
    dispatch: DispatchStrategy,
    schedule: Vector[Round],
    refinement: OutputRefinement = StandardRefinement
):

  /** The JIT's mode under the strategy (strategy_mode/2). */
  def mode: DispatchMode = DispatchMode.Dispatch(dispatch)

/** How the output of a test's schedule becomes the term the JIT runs, under
  * a library's backend facts: the term, interned. It reads spellings and the backend's facts, never a type
  * (`CONTRIBUTING.md`, "Types live only in the term").
  */
trait OutputRefinement:
  def refined(facts: BackendFacts, output: Instruction): Instruction

/** The baseline's refinement, `Refinement`. */
object StandardRefinement extends OutputRefinement:
  def refined(facts: BackendFacts, output: Instruction): Instruction =
    Refinement(facts).refined(output)

/** The key of a refined term in `DispatchCache`: the test, the schedule
  * with its budgets, the refinement and the backend facts, whose index is
  * the library the schedule runs under, every input of the dispatch. A cache
  * handed to dispatches under two libraries keeps their refinements apart.
  */
final case class DispatchKey(test: Instruction, schedule: Vector[Round], refinement: OutputRefinement, facts: BackendFacts)

/** The namespace of `jit` in the cache service: the
  * refined term of each test met, by test, schedule, refinement and library. Terms
  * only, no verdict (`CONTRIBUTING.md`, "Types live only in the term"): the refined term equals the test
  * under the λ-lattice laws, its assertions in the term, the memo of a
  * rewriting by lemma instances (`CONTRIBUTING.md`, "Tables", kind
  * 2). Its key holds the library (`DispatchKey.facts`), so a cache handed to
  * dispatches of two libraries keeps them apart.
  */
object DispatchCache extends CacheNamespace[DispatchKey, Instruction]("jit.dispatch")

/** What a code's slot holds at a refinement: a hole of the thunk, or the
  * instruction of a filling.
  */
enum SlotHolds:
  case HoleOf(slot: Int)
  case Filling(instruction: Instruction)

/** The term the JIT runs of a test under a strategy, the port of
  * `gezi/prolog/gezi/jit_strategies.pl`, whose module comment
  * this follows (THE TEST IS THE UNIT; THE REFINEMENT, and why the refined
  * term R equals the output O). A test is run through its strategy's
  * schedule, and the output, `f + typed_f` where the type check spells a
  * typed version (a specialization, `CONTRIBUTING.md`, "Terms"), is refined: a SPECIALIZATION
  * CHOICE becomes the application of the refined function to a fallback
  * point on its argument, under a fallback point by its range off the
  * root's path; a JUDGMENT becomes its term; a CONTRACT's code is rewritten
  * the same way inside the closure. A fallback point is written only for a
  * decoding criterion, a backend fact. The refinement reads spellings and
  * the backend property of criteria, never a type,
  * and names no module, lemma or combinator.
  *
  * FIXME (carried from jit_strategies.pl:51; f's compiled result is to be https://github.com/Atry/private-overlay/issues/1944
  * cached automatically, to speed it up):
  * f's type check is not shared between tests: the schedule runs on each
  * test, and f's part of it is done again for each. In the Prolog baseline
  * zero's type check round took 135,286 inferences and its erasure round
  * 4,462 (measured 2026-10-30 on main 4eeb7b7d5); f's part is the rest,
  * 1,687,332 inferences to saturate nat_fold zero (compose successor
  * successor) alone, against 2,555,000 or so for its tests on successor^n
  * zero. The terms are hash-consed, f one instruction in every test, but the
  * e-graph's state over them is not: a test's unions with f's argument
  * types change it. Candidate: the strategy saturates an application's
  * function part first, always, and keeps that graph; each test that shares
  * it keeps its unions, its class data and its instance keys in a layer of
  * its own and reads the kept graph where its layer has nothing, so that a
  * test costs what it adds and changes, not f's size. Not designed. (The
  * Scala e-graph is immutable, so the kept graph is shared without a copy;
  * the layer's reads and unions are what is not designed.)
  */
object StrategyDispatch:

  /** The term the JIT runs of the closed test under the strategy
    * (strategy_dispatched/3): the output of the strategy's schedule on the
    * test, run by `Schedule.run` with the library's index of the facts,
    * refined by the strategy's refinement; a test met again under the same
    * schedule and refinement reads the cache service's namespace
    * `DispatchCache` and runs no schedule. The schedule runs outside the
    * namespace's lock: the cache is read first, and the refined term is
    * written after it is computed. The strategy after holds the schedule
    * after the run (`Scheduled.scheduleAfter`), or is the strategy given
    * when the cache answered.
    * The schedule reads the stop signal (judge record 4.4); when a stop was
    * requested by the time the schedule returns, its output depends on when
    * the stop came and not on the key alone, so the refined term is
    * returned and not written to the cache (a key holds every input of what
    * it keeps, `CONTRIBUTING.md`, "Tables"). Throws what
    * `Schedule.run` throws.
    */
  def dispatched(
      strategy: CompilationStrategy,
      test: Instruction,
      facts: BackendFacts,
      cache: Cache,
      stop: StopSignal
  ): Dispatched =
    val key = DispatchKey(test, strategy.schedule, strategy.refinement, facts)
    cache.locked(DispatchCache)(_.tryGet(key)) match
      case Some(found) => Dispatched(found, strategy, scheduleRan = false)
      case None =>
        val scheduled = Schedule.run(facts.index, Vector(test), strategy.schedule, stop)
        val output = scheduled.outputs match
          case Vector(found) => found
          case other         => throw IllegalStateException(s"the schedule of one test gave ${other.size} outputs")
        val refinement = strategy.refinement.refined(facts, output)
        val refined =
          if stop.stopRequested then refinement
          else cache.locked(DispatchCache)(_.getOrElseUpdate(key, refinement))
        Dispatched(refined, strategy.copy(schedule = scheduled.scheduleAfter), scheduleRan = true)

/** What a dispatch gives: the instruction of the refined term the JIT runs, the
  * compilation strategy after it, and whether the schedule ran
  * (strategy_typing_count/1 counts these runs), false when the cache
  * answered.
  */
final case class Dispatched(
    refined: Instruction,
    strategyAfter: CompilationStrategy,
    scheduleRan: Boolean
)

/** Where a layer is refined: on the root's path through choices, whose
  * value the exit reads, or elsewhere.
  */
enum RefinementPosition:
  case Root
  case Inner

/** The refinement under a library's backend facts (jit_strategies.pl, THE
  * REFINEMENT).
  */
final case class Refinement(facts: BackendFacts):

  private val rules = JitRules(JitConfiguration.of(facts, instanceTable = false))

  /** The state a refinement threads: each layer refined at a position
    * (refined_term/5's Seen), so that the refined term shares what the output shares.
    */
  private final case class Refining(seen: Map[(Instruction, RefinementPosition), Instruction])

  private type Step[Result] = Refining => TailRec[(Refining, Result)]

  /** The instruction of the refined term of the output (refined/2). Each layer is refined once for each position it is met
    * at and interned over its refined parts' instructions.
    */
  def refined(output: Instruction): Instruction =
    val (_, refinedInstruction) = refinedTerm(output, RefinementPosition.Root)(Refining(Map.empty)).result
    refinedInstruction

  /** Whether the instruction is a leaf, kept as written (`BackendFacts.leaves`). */
  private def leaf(instruction: Instruction): Boolean = facts.leaves.contains(instruction)

  private def interned(layer: Layer[Instruction]): Step[Instruction] = refining =>
    done((refining, Instruction(layer)))

  /** The layer of a term, a leaf having none (layer_read/2). */
  private def layerRead(instruction: Instruction): Option[Layer[Instruction]] =
    if leaf(instruction) then None else Some(instruction.layered)

  private def refinedTerm(instruction: Instruction, position: RefinementPosition): Step[Instruction] = refining =>
    refining.seen.get((instruction, position)) match
      case Some(found) => done((refining, found))
      case None if leaf(instruction) => done((refining.copy(seen = refining.seen.updated((instruction, position), instruction)), instruction))
      case None =>
        tailcall(refinedLayer(instruction, instruction.layered, position)(refining)).map((after, refinedInstruction) =>
          (after.copy(seen = after.seen.updated((instruction, position), refinedInstruction)), refinedInstruction)
        )

  private def refinedLayer(instruction: Instruction, layer: Layer[Instruction], position: RefinementPosition): Step[Instruction] = refining =>
    layer match
      case Apply(function, argument) =>
        contractParts(function) match
          case Some((contracted, domain, range)) =>
            refinedSpecialization(contracted, argument, domain, range, position)(refining)
          case None =>
            for
              (afterFunction, refinedFunction) <- tailcall(refinedHead(function)(refining))
              (afterArgument, refinedArgument) <- tailcall(refinedTerm(argument, RefinementPosition.Inner)(afterFunction))
              result <- interned(Apply(refinedFunction, refinedArgument))(afterArgument)
            yield result
      case Thunk(code, holes, fillings) =>
        tailcall(allRefined(fillings, RefinementPosition.Inner)(refining)).flatMap((afterFillings, refinedFillings) =>
          val environment = environmentOf(holes, refinedFillings)
          val refinedCode = codeRefined(code, environment)
          refinedCode match
            case Code.Apply(Code.Slot(functionSlot), Code.Slot(holeSlot))
                if holes == Vector(Hole.Bound(holeSlot)) && environment(functionSlot).isInstanceOf[SlotHolds.Filling] =>
              val SlotHolds.Filling(function) = environment(functionSlot): @unchecked
              done((afterFillings, function))
            case _ =>
              interned(Thunk(refinedCode, holes, refinedFillings))(afterFillings)
        )
      case Parallel(value, criterion) =>
        tailcall(refinedTerm(value, RefinementPosition.Inner)(refining)).flatMap((after, refinedValue) =>
          interned(Parallel(refinedValue, criterion))(after)
        )
      case Choice(left, right) =>
        DispatchPattern.specializations(left, right, instructionLayers, DispatchPattern.noContract).headOption match
          case Some(specialization) =>
            refinedSpecialization(
              specialization.function,
              specialization.argument,
              Some(specialization.domain),
              specialization.range,
              position
            )(refining)
          case None =>
            DispatchPattern.fallbacks(left, right, instructionLayers).headOption match
              case Some(judgment) => tailcall(refinedTerm(judgment.value, position)(refining))
              case None =>
                tailcall(allRefined(Vector(left, right), position)(refining)).flatMap((after, refinedMembers) =>
                  val Vector(refinedLeft, refinedRight) = refinedMembers: @unchecked
                  interned(Choice(refinedLeft, refinedRight))(after)
                )
      case NoinlineLeaf(_) => done((refining, instruction))

  private def allRefined(instructions: Vector[Instruction], position: RefinementPosition): Step[Vector[Instruction]] = refining =>
    def from(index: Int, current: Refining, found: Vector[Instruction]): TailRec[(Refining, Vector[Instruction])] =
      if index >= instructions.size then done((current, found))
      else tailcall(refinedTerm(instructions(index), position)(current)).flatMap((after, next) => from(index + 1, after, found :+ next))
    from(0, refining, Vector.empty)

  /** What each slot of a thunk's code holds: the thunk's holes and its
    * fillings (slot_values/4).
    */
  private def environmentOf(holes: Vector[Hole], fillings: Vector[Instruction]): Vector[SlotHolds] =
    val holeValues = holes.map {
      case Hole.Bound(slot) => SlotHolds.HoleOf(slot)
      case Hole.Ignored     => SlotHolds.HoleOf(-1)
    }
    Defunctionalization.slotValues(holes, holeValues, fillings.map(SlotHolds.Filling(_)))

  /** The layers of an instruction as the dispatch patterns read it: its layer, a
    * leaf having none.
    */
  private def instructionLayers(instruction: Instruction): Vector[Layer[Instruction]] = layerRead(instruction).toVector

  /** The instruction's spelling is λf. f by its syntax (identity_contract/1). */
  private def instructionIdentity(instruction: Instruction): Boolean =
    DispatchPattern.identityContract(instruction, instructionLayers)

  /** A specialization choice refined (refined_specialization/8): the refined
    * function applied to the refined argument under a fallback point by the
    * domain; off the root's path, with a range, under one by the range; with
    * a contract, the refined contract applied to that.
    */
  private def refinedSpecialization(
      function: Instruction,
      argument: Instruction,
      domain: Option[Instruction],
      range: SpecializationRange[Instruction],
      position: RefinementPosition
  ): Step[Instruction] = refining =>
    for
      (afterFunction, refinedFunction) <- tailcall(refinedHead(function)(refining))
      (afterArgument, refinedArgument) <- tailcall(refinedTerm(argument, RefinementPosition.Inner)(afterFunction))
      (afterFiltered, filteredArgument) <- fallbackFiltered(refinedArgument, domain)(afterArgument)
      (afterApplication, application) <- interned(Apply(refinedFunction, filteredArgument))(afterFiltered)
      result <- range match
        case SpecializationRange.Filtered(found) if position == RefinementPosition.Inner =>
          fallbackFiltered(application, Some(found))(afterApplication)
        case SpecializationRange.Contracted(contract) =>
          tailcall(refinedTerm(contract, RefinementPosition.Inner)(afterApplication)).flatMap((after, refinedContract) =>
            interned(Apply(refinedContract, application))(after)
          )
        case _ => done((afterApplication, application))
    yield result

  /** A function at the head of an application refined (refined_head/4): a
    * contract over a filling is the filling, refined in turn.
    */
  private def refinedHead(function: Instruction): Step[Instruction] = refining =>
    layerRead(function) match
      case Some(Thunk(code, holes, fillings)) =>
        contractFunction(code, holes, environmentOf(holes, fillings)) match
          case Some(contracted) => tailcall(refinedHead(contracted)(refining))
          case None             => tailcall(refinedTerm(function, RefinementPosition.Inner)(refining))
      case _ => tailcall(refinedTerm(function, RefinementPosition.Inner)(refining))

  /** The code of a thunk of one hole is a specialization choice of the
    * application of a filling to the hole: the filling (contract_function/4).
    */
  private def contractFunction(code: Code, holes: Vector[Hole], environment: Vector[SlotHolds]): Option[Instruction] =
    holes match
      case Vector(Hole.Bound(hole)) =>
        codeSpecialization(code, environment).flatMap(specialization =>
          (specialization.function, specialization.argument) match
            case (Code.Slot(functionSlot), Code.Slot(`hole`)) => fillingAt(environment, functionSlot)
            case _                                            => None
        )
      case _ => None

  private def fillingAt(environment: Vector[SlotHolds], slot: Int): Option[Instruction] =
    environment.lift(slot).collect { case SlotHolds.Filling(instruction) => instruction }

  /** The specialization choice the code is read as by the dispatch patterns
    * (code_typed_parts/6, code_curried_parts/6), a slot read as nothing but
    * a contract's spelling read off the filling it holds.
    */
  private def codeSpecialization(code: Code, environment: Vector[SlotHolds]): Option[Specialization[Code]] =
    code match
      case Code.Choice(first, second) =>
        DispatchPattern.specializations(first, second, DispatchPattern.codeLayers, codeIdentity(environment)).headOption
      case _ => None

  /** The code is a slot holding a term whose spelling is λf. f. */
  private def codeIdentity(environment: Vector[SlotHolds])(code: Code): Boolean = code match
    case Code.Slot(slot) => fillingAt(environment, slot).exists(instructionIdentity)
    case _               => false

  /** The function is a closure of one hole whose code is the contract of a
    * filling f applied to the hole (contract_parts/2): f, the domain and the
    * range or the contract, the criteria the values of fillings.
    */
  private def contractParts(function: Instruction): Option[(Instruction, Option[Instruction], SpecializationRange[Instruction])] =
    layerRead(function) match
      case Some(Thunk(code, Vector(Hole.Bound(hole)), fillings)) =>
        val environment = environmentOf(Vector(Hole.Bound(hole)), fillings)
        codeSpecialization(code, environment).flatMap(specialization =>
          (specialization.function, specialization.argument, specialization.domain, specialization.range) match
            case (Code.Slot(functionSlot), Code.Slot(`hole`), Code.Slot(domainSlot), range) =>
              val outer: Option[SpecializationRange[Instruction]] = range match
                case SpecializationRange.Absent => Some(SpecializationRange.Absent)
                case SpecializationRange.Filtered(Code.Slot(rangeSlot)) =>
                  Some(fillingAt(environment, rangeSlot).fold(SpecializationRange.Absent)(SpecializationRange.Filtered(_)))
                case SpecializationRange.Contracted(Code.Slot(contractSlot)) =>
                  fillingAt(environment, contractSlot).map(SpecializationRange.Contracted(_))
                case _ => None
              for
                contracted <- fillingAt(environment, functionSlot)
                found <- outer
              yield (contracted, fillingAt(environment, domainSlot), found)
            case _ => None
        )
      case _ => None

  /** The code with each specialization choice rewritten into fallback
    * points by the criteria the environment's fillings hold, and every
    * other node kept (code_refined/3).
    */
  private def codeRefined(code: Code, environment: Vector[SlotHolds]): Code =
    codeSpecialization(code, environment) match
      case Some(specialization) =>
        val application = Code.Apply(
          codeRefined(specialization.function, environment),
          codeFallback(codeRefined(specialization.argument, environment), specialization.domain, environment)
        )
        specialization.range match
          case SpecializationRange.Absent          => application
          case SpecializationRange.Filtered(range) => codeFallback(application, range, environment)
          case SpecializationRange.Contracted(contract) => Code.Apply(codeRefined(contract, environment), application)
      case None =>
        code match
          case Code.Choice(left, right) => Code.Choice(codeRefined(left, environment), codeRefined(right, environment))
          case Code.Apply(function, argument) =>
            Code.Apply(codeRefined(function, environment), codeRefined(argument, environment))
          case Code.Parallel(value, criterion) => Code.Parallel(codeRefined(value, environment), criterion)
          case other => other

  /** The code under a fallback point of the criterion when the criterion is
    * a slot holding a decoding criterion (code_fallback/4).
    */
  private def codeFallback(value: Code, criterion: Code, environment: Vector[SlotHolds]): Code =
    criterion match
      case Code.Slot(slot) if fillingAt(environment, slot).exists(instruction => rules.decodingCriterion(instruction).isDefined) =>
        Code.Choice(value, Code.Parallel(value, criterion))
      case _ => value

  /** The value under a fallback point of the criterion, unless it is one
    * already or the criterion is no decoding criterion (fallback_filtered/3).
    */
  private def fallbackFiltered(value: Instruction, criterion: Option[Instruction]): Step[Instruction] = refining =>
    criterion match
      case None => done((refining, value))
      case Some(found) =>
        val already = layerRead(value) match
          case Some(Choice(inner, point)) =>
            DispatchPattern.fallbacks(inner, point, instructionLayers).exists(judgment =>
              judgment.valueFirst && judgment.criterion == found
            )
          case _ => false
        if already then done((refining, value))
        else if rules.decodingCriterion(found).isDefined then
          tailcall(interned(Parallel(value, found))(refining)).flatMap((after, filtered) =>
            interned(Choice(value, filtered))(after)
          )
        else done((refining, value))
