package com.yang_bo.gezi.saturation

import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.egraph.InstanceKey
import com.yang_bo.gezi.egraph.Justification
import com.yang_bo.gezi.egraph.MadeNodes
import com.yang_bo.gezi.egraph.PendingBeta
import com.yang_bo.gezi.ematching.CompiledProgram
import com.yang_bo.gezi.ematching.Match
import com.yang_bo.gezi.ematching.Program
import com.yang_bo.gezi.ematching.SeedKey
import com.yang_bo.gezi.ematching.SeedKind
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Direction
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.LayerWith
import com.yang_bo.gezi.ir.Store
import scala.annotation.tailrec
import com.yang_bo.gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Thunk}
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** How a saturation ended, with the instances that changed the graph: no delta
  * left, the budget reached, or a stop requested by the caller's signal (judge
  * record 4.4) before a delta was taken.
  */
enum End:
  case FixedPoint(instances: Int)
  case BudgetExhausted(instances: Int)
  case Stopped(instances: Int)

/** A saturation's result: the graph, the node of each input, the nodes made
  * while the inputs were added, and how it ended.
  */
final case class Run[C <: NativeSpecializer & Singleton](
    graph: EGraph[C],
    inputNodes: Vector[Int],
    inputNodesMade: Int,
    end: End
)

/** The fixed-point loop of the Prolog baseline (`fixpoint_egraph_run/3`), over
  * a program and its compiled form, whichever backend compiled it: the deltas
  * matched until none is left, the orientations that only unite before the
  * others; every match of a delta found on one graph and then applied in order;
  * unions and β steps worked after every instance.
  */
object Saturation:

  /** The run of the inputs: the initial graph of the pattern instructions, the
    * inputs added, the agenda worked and the deltas matched, with the built-in
    * rules the round enables; the graph records the terms made when `explained`
    * (a run whose proof is wanted).
    */
  def run[C <: NativeSpecializer & Singleton](
      program: Program[C],
      compiled: CompiledProgram[C],
      rules: Set[BuiltInRule],
      store: Store[C],
      headArityBounds: Map[Configured[C], Int],
      patternInstructions: Vector[Configured[C]],
      inputs: Vector[Configured[C]],
      budget: Int,
      explained: Boolean,
      stop: StopSignal
  )(using C): Run[C] =
    runFrom(
      program,
      compiled,
      rules,
      initialGraph(store, headArityBounds, patternInstructions, explained),
      inputs,
      budget,
      stop
    )

  /** The run of the inputs from the initial graph given, such as the graph of
    * the pattern instructions with a cost analysis (`EGraph.analysed`).
    */
  def runFrom[C <: NativeSpecializer & Singleton](
      program: Program[C],
      compiled: CompiledProgram[C],
      rules: Set[BuiltInRule],
      initial: EGraph[C],
      inputs: Vector[Configured[C]],
      budget: Int,
      stop: StopSignal
  )(using C): Run[C] =
    val (withInputs, inputNodes) = inputsAdded(initial, inputs)
    val (graph, end) =
      saturated(program, compiled, rules, withInputs, budget, stop)
    Run(
      graph,
      inputNodes,
      withInputs.canonicalNodeCount - initial.canonicalNodeCount,
      end
    )

  /** The graph of the instructions the matched sides mention, in the order
    * given (the baseline's `pattern_handles/2`).
    */
  def initialGraph[C <: NativeSpecializer & Singleton](
      store: Store[C],
      headArityBounds: Map[Configured[C], Int],
      patternInstructions: Vector[Configured[C]],
      explained: Boolean
  )(using C): EGraph[C] =
    val empty = EGraph.empty(store, headArityBounds, explained)
    // A construction that builds storages one layer up or folds natives reads
    // the classes' storage leaves (`EGraph.storageConstructed`).
    val constructs =
      store.construction.storageCriteria.nonEmpty || store.construction.foldingDefines.nonEmpty
    val start =
      if constructs then empty.analysed(empty.storageLeaves) else empty
    patternInstructions.foldLeft(start) { (graph, instruction) =>
      val (added, _) = graph.instructionAdded(instruction)
      added
    }

  /** The graph with the inputs added in order, and the node of each. */
  def inputsAdded[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      inputs: Vector[Configured[C]]
  )(using C): (EGraph[C], Vector[Int]) =
    inputs.foldLeft((graph, Vector.empty[Int])) {
      case ((current, nodes), input) =>
        val (next, node) = current.instructionAdded(input)
        (next, nodes :+ node)
    }

  /** The graph saturated: the agenda worked, then, in a round that enables
    * `BuiltInRule.StorageView`, the storage leaves' views added one leaf at a
    * time (`EGraph.storageViewAdded`), each an instance when it changes the
    * graph; then, under a construction that builds storages one layer up
    * (`com.yang_bo.gezi.ir.TermConstruction.storageBuilt`), each waiting parallel's storage
    * built (`EGraph.storageConstructed`), added as a leaf and united with its
    * view (`EGraph.storageViewAdded`, the construction direction), and, under a
    * construction that folds natives (`com.yang_bo.gezi.ir.TermConstruction.folded`), each
    * waiting application's native called on its arguments' storage leaves, its
    * result added as a leaf and united with the application
    * (`com.yang_bo.gezi.egraph.Justification.Folding`), each an instance when it changes
    * the graph; before the deltas are matched, until no leaf waits and no delta
    * is left, the instances that changed the graph reach the budget, or the
    * signal asks for a stop, which is read before each expansion and each
    * delta. A leaf a cut leaves waiting is expanded when the graph is saturated
    * further.
    *
    * The budget counts the graph's instances from its start, so a graph that a
    * run left with `End.BudgetExhausted` or `End.Stopped` is saturated further
    * by passing it back with a budget above its `instances`. Nothing is lost at
    * the cut: a stop is read before a delta is taken, and a delta the budget
    * cut in the middle of its matches is put back on its stack
    * (`EGraph.mergeRestored`, `deltaRestored`), so the resumed run matches it
    * again; an instance of it already applied is skipped by its key, or, its
    * classes joined since, changes nothing and is not counted. The graph the
    * cut leaves is equal to the inputs under the lemmas, as every graph of a
    * run is, so its extraction is sound.
    *
    * FIXME (2026-11-02): the signal is read between deltas only. The
    * https://github.com/Atry/private-overlay/issues/1967 matches of one delta
    * and their instances, and the agenda worked after each (unions and β steps,
    * which the budget does not count either, see `agendaWorked`), run to their
    * end once the delta is taken, so a call stuck in one large delta or one
    * long agenda still outlasts the judge's cancel grace and is killed. Not
    * measured: no point of rounds 13 or 14 is known to spend a grace's length
    * in one delta. Candidate: read the signal in `matchesApplied` before each
    * match and in the agenda's loop, ending `End.Stopped` with the graph as it
    * is; every union made so far is an instance of a lemma or a congruence, so
    * the graph stays sound when cut there.
    */
  def saturated[C <: NativeSpecializer & Singleton](
      program: Program[C],
      compiled: CompiledProgram[C],
      rules: Set[BuiltInRule],
      graph: EGraph[C],
      budget: Int,
      stop: StopSignal
  ): (EGraph[C], End) =
    require(budget >= 0, s"a budget is not negative: $budget")
    loop(
      program,
      compiled,
      rules,
      budget,
      stop,
      agendaWorked(program, compiled, rules, graph)
    )

  /** The outcome of the matches of one delta: go on, or stop on the budget.
    */
  private enum Applied[C <: NativeSpecializer & Singleton]:
    case Continue(graph: EGraph[C])
    case BudgetSpent(graph: EGraph[C])

  /** The baseline's `saturation_loop/4`: the stack of the orientations that
    * only unite first; a duplicate taken is skipped.
    *
    * FIXME: the order of the deltas (the merges first, then the
    * https://github.com/Atry/private-overlay/issues/2032 additions, each a
    * stack) and of the agenda is fixed here, and it decides which instances a
    * budget's cut keeps. The order is to become an option of one interface
    * chosen by configuration (entry data and `Defaults`).
    */
  @tailrec
  private def loop[C <: NativeSpecializer & Singleton](
      program: Program[C],
      compiled: CompiledProgram[C],
      rules: Set[BuiltInRule],
      budget: Int,
      stop: StopSignal,
      graph: EGraph[C]
  ): (EGraph[C], End) =
    val expanded = if rules.contains(BuiltInRule.StorageView) then
      graph.storageViewTaken
    else None
    lazy val constructed = graph.constructionTaken
    expanded match
      case None if constructed.isDefined =>
        if stop.stopRequested then (graph, End.Stopped(graph.instances))
        else
          val Some((node, rest)) = constructed: @unchecked
          rest.storageConstructed(node) match
            case None => loop(program, compiled, rules, budget, stop, rest)
            case Some(step) =>
              val united = step match
                case com.yang_bo.gezi.egraph.StorageStep.Constructed(term) =>
                  val (withLeaf, leaf) = rest.instructionAdded(term)
                  withLeaf.storageViewAdded(leaf)
                case com.yang_bo.gezi.egraph.StorageStep.Folded(
                      term,
                      native,
                      defineNode,
                      argumentClasses
                    ) =>
                  val (withLeaf, leaf) = rest.instructionAdded(term)
                  withLeaf.unionQueued(
                    node,
                    leaf,
                    com.yang_bo.gezi.egraph.Justification
                      .Folding(native, defineNode, argumentClasses),
                    None
                  )
              val worked = agendaWorked(program, compiled, rules, united)
              val counted =
                if worked.canonicalNodeCount > rest.canonicalNodeCount || worked.joiningUnionCount > rest.joiningUnionCount
                then worked.instanceCounted
                else worked
              if counted.instances >= budget then
                (counted, End.BudgetExhausted(counted.instances))
              else loop(program, compiled, rules, budget, stop, counted)
      case Some(_) if stop.stopRequested =>
        (graph, End.Stopped(graph.instances))
      case Some((leaf, rest)) =>
        val worked =
          agendaWorked(program, compiled, rules, rest.storageViewAdded(leaf))
        val counted =
          if worked.canonicalNodeCount > rest.canonicalNodeCount || worked.joiningUnionCount > rest.joiningUnionCount
          then worked.instanceCounted
          else worked
        if counted.instances >= budget then
          (counted, End.BudgetExhausted(counted.instances))
        else loop(program, compiled, rules, budget, stop, counted)
      case None =>
        val taken = graph.mergeTaken
          .map((node, rest) => (SeedKind.Merge, node, rest))
          .orElse(
            graph.deltaTaken.map((node, rest) => (SeedKind.Add, node, rest))
          )
        taken match
          case None => (graph, End.FixedPoint(graph.instances))
          case Some(_) if stop.stopRequested =>
            (graph, End.Stopped(graph.instances))
          case Some((kind, node, rest)) =>
            val outcome =
              if rest.live(node) then
                deltaMatched(program, compiled, rules, kind, node, budget, rest)
              else Applied.Continue(rest)
            outcome match
              case Applied.Continue(next) =>
                loop(
                  program,
                  compiled,
                  rules,
                  budget,
                  stop,
                  agendaWorked(program, compiled, rules, next)
                )
              case Applied.BudgetSpent(next) =>
                val restored = kind match
                  case SeedKind.Merge => next.mergeRestored(node)
                  case SeedKind.Add   => next.deltaRestored(node)
                (restored, End.BudgetExhausted(next.instances))

  /** The baseline's `delta_matched/6`: the matches of the delta under each of
    * its keys (an application's `Apply`, then its heads in filing order), then
    * under `Closure` when its class holds a closure state, then under its first
    * instruction, of either kind: the seeds of the orientations whose matched
    * side is that instruction, and of those that hold it inside their matched
    * side, which a union reaches only from the instruction's node when its
    * class is the smaller one; all found on one graph, counted, then applied in
    * order.
    */
  private def deltaMatched[C <: NativeSpecializer & Singleton](
      program: Program[C],
      compiled: CompiledProgram[C],
      rules: Set[BuiltInRule],
      kind: SeedKind,
      node: Int,
      budget: Int,
      graph: EGraph[C]
  ): Applied[C] =
    // A round that stops at the classes holding a storage of constant size
    // skips a delta whose node is hidden when the delta is taken, not when
    // it was pushed: a node becomes hidden when its class gains such a leaf,
    // after it was made (`ConstantStorageStop`). The matchers read the
    // graph through the stop's view; the choice of a closure seed reads the
    // graph's own `hasClosure`, harmless since the view's then fails.
    val view = ConstantStorageStop.view(graph)
    val matchings =
      if ConstantStorageStop.hidden(graph, node) then Vector.empty
      else
        deltaSeeds(graph, node).map(key =>
          compiled.matches(kind, key, view, node)
        )
    val matches = matchings.flatMap(_.found)
    matchesApplied(
      program,
      compiled,
      rules,
      matches,
      0,
      budget,
      graph
        .matchesCounted(matches.size)
        .entriesReadCounted(matchings.map(_.entriesRead.toLong).sum)
    )

  /** The keys a delta node's seeds are filed under, in the order matched: its
    * shape's keys (`deltaKeys`), `Closure` when its class holds a closure, and
    * its instruction's node key when it is an instruction's node.
    */
  def deltaSeeds[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      node: Int
  ): Vector[SeedKey[C]] =
    deltaKeys(graph, node) ++
      (if graph.hasClosure(graph.root(node)) then Vector(SeedKey.Closure[C]())
       else Vector.empty) ++
      graph.nodeInstruction(node).map(SeedKey.InstructionNode(_)).toVector

  /** The baseline's `delta_keys/2`: a leaf has no key a seed is filed under. */
  private def deltaKeys[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      node: Int
  ): Vector[SeedKey[C]] =
    graph.layer(node) match
      case Apply(_, _) =>
        SeedKey.Apply[C]() +: graph.nodeHeads(node).map(SeedKey.Headed(_))
      case Parallel(_, _)               => Vector(SeedKey.Parallel[C]())
      case Choice(_, _)                 => Vector(SeedKey.Choice[C]())
      case Thunk(code, holes, _)        => Vector(SeedKey.Thunk[C](code, holes))
      case NoinlineLeaf(_)              => Vector.empty
      case view: com.yang_bo.gezi.ir.StorageView[?] =>
        throw IllegalStateException(
          s"a node's layer is never a storage's view: $view"
        )

  /** The baseline's `matches_applied/5`: each match's root and bindings read as
    * roots; its instance key made, which may make nodes; a key there already
    * skipped; otherwise the instance applied, and counted when it made a node
    * or joined two classes, the run stopping as soon as the count reaches the
    * budget.
    */
  @tailrec
  private def matchesApplied[C <: NativeSpecializer & Singleton](
      program: Program[C],
      compiled: CompiledProgram[C],
      rules: Set[BuiltInRule],
      matches: Vector[Match],
      index: Int,
      budget: Int,
      graph: EGraph[C]
  ): Applied[C] =
    if index >= matches.size then Applied.Continue(graph)
    else
      val found = matches(index)
      val root = graph.root(found.root)
      val bindings = found.bindings.map(_.map(graph.root))
      val (keyed, key) =
        instanceKeyMade(
          program,
          compiled,
          found.orientation,
          root,
          bindings,
          graph
        )
      keyed.instanceKeyAdded(key) match
        case None =>
          matchesApplied(
            program,
            compiled,
            rules,
            matches,
            index + 1,
            budget,
            keyed
          )
        case Some(withKey) =>
          val applied = instanceApplied(
            program,
            compiled,
            rules,
            found.orientation,
            root,
            bindings,
            withKey
          )
          if applied.canonicalNodeCount > withKey.canonicalNodeCount ||
            applied.joiningUnionCount > withKey.joiningUnionCount
          then
            val counted = applied.instanceCounted
            if counted.instances >= budget then Applied.BudgetSpent(counted)
            else
              matchesApplied(
                program,
                compiled,
                rules,
                matches,
                index + 1,
                budget,
                counted
              )
          else
            matchesApplied(
              program,
              compiled,
              rules,
              matches,
              index + 1,
              budget,
              applied
            )

  /** The baseline's `instance_key_made/6`: the matched root, the essential
    * metavariables' roots and the classes of the shared subterms, which are
    * built (and may be made) in their order.
    */
  private def instanceKeyMade[C <: NativeSpecializer & Singleton](
      program: Program[C],
      compiled: CompiledProgram[C],
      orientation: Int,
      root: Int,
      bindings: Vector[Option[Int]],
      graph: EGraph[C]
  ): (EGraph[C], InstanceKey) =
    val plan = program.orientations(orientation)
    val (built, classes) =
      plan.shared.indices.foldLeft((graph, Vector.empty[Int])) {
        case ((current, roots), part) =>
          val (next, node) =
            compiled.shared(orientation, part, current, bindings)
          (next, roots :+ next.root(node))
      }
    (
      built,
      InstanceKey(orientation, root, plan.essential.map(bindings(_)), classes)
    )

  /** The baseline's `instance_applied/5`: the added side built and united with
    * the matched root, the lemma's left side first, and the agenda worked.
    */
  private def instanceApplied[C <: NativeSpecializer & Singleton](
      program: Program[C],
      compiled: CompiledProgram[C],
      rules: Set[BuiltInRule],
      orientation: Int,
      root: Int,
      bindings: Vector[Option[Int]],
      graph: EGraph[C]
  ): EGraph[C] =
    val plan = program.orientations(orientation)
    val (built, addedNode) = compiled.added(orientation, graph, bindings)
    val justification = Justification.Lemma(plan.lemma, bindings)
    // The added side is the instance's own node only when the graph did not
    // hold it before (`UnionRecord.made`): a hash-consed hit is an older node.
    val made = Option.when(addedNode >= graph.nodeCount)(
      MadeNodes(graph.nodeCount, addedNode)
    )
    val united = plan.direction match
      case Direction.Forward =>
        built.unionWorked(root, addedNode, justification, made)
      case Direction.Backward =>
        built.unionWorked(addedNode, root, justification, made)
    agendaWorked(program, compiled, rules, united)

  /** The baseline's `agenda_worked/2`: every pending union and β step worked,
    * the unions first, each queue in the order it was filled. In a round that
    * does not enable `BuiltInRule.Beta` a pending β step is taken off its queue
    * and dropped uncounted (`EGraph.betaDiscarded`), so the β rule makes no
    * union, no node and no closure state.
    */
  @tailrec
  def agendaWorked[C <: NativeSpecializer & Singleton](
      program: Program[C],
      compiled: CompiledProgram[C],
      rules: Set[BuiltInRule],
      graph: EGraph[C]
  ): EGraph[C] =
    graph.unionTaken match
      case Some((pending, rest)) =>
        agendaWorked(
          program,
          compiled,
          rules,
          rest.unionWorked(
            pending.first,
            pending.second,
            pending.justification,
            pending.made
          )
        )
      case None =>
        // FIXME (open item, anyone may take it): β steps are not counted https://github.com/Atry/private-overlay/issues/2033
        // against the budget, which counts only the instances that change the
        // graph, so the budget bounds neither the β steps nor their time. One
        // measured case: 57,204,572 β steps in a single type-check round, on
        // a generated program of about 12,000 nodes (2026-10-31). Counting them
        // must keep every HM-checkable program inside its budget; a separate
        // β budget, also linear in the program, is one candidate. The cost is
        // in this saturation loop, which a client replaces by running its own
        // loop over the e-graph's public operations.
        if rules.contains(BuiltInRule.Beta) then
          graph.betaTaken match
            case Some((pending, rest)) =>
              agendaWorked(
                program,
                compiled,
                rules,
                betaWorked(program, compiled, pending, rest)
              )
            case None => graph
        else
          graph.betaDiscarded match
            case Some(rest) => agendaWorked(program, compiled, rules, rest)
            case None       => graph

  /** The baseline's `beta_worked/4`: the application fills the next hole of the
    * closure state: a new state of its class while a hole is left; when none
    * is, the thunk's code read with its slots filled and united with the
    * application. Besides, an application that gives a thunk node its first
    * argument and leaves a hole is united with its residual thunk.
    *
    * The residual thunk (`residualThunk`) is one β step,
    * `(λk. λy. B) c = λy. B[k := c]`, a node the extraction can read; a closure
    * state is no node. It is needed by the curried contracts of
    * `prolog_backend_shapes`, whose right sides `(λk. λy. …) (contract_at g)`
    * are one thunk of two holes once a choice of one member is its member:
    * without the residual the steps of folds stayed untyped (measured
    * 2026-11-07: four tests of `NativeRouteCompilationTest`, cons's native
    * called 4 times instead of 8 on a fold of size 4).
    *
    * Only the first argument of a thunk node makes a residual, and a residual
    * never makes another: it is added without a closure state of its own
    * (`EGraph.residualAdded`), its class holding the application's extended
    * state, which carries the same arguments, so that the residual of a further
    * argument is never reached. A residual for every argument is flat, the k-th
    * of an n-hole thunk k fillings wide, n²/2 in all: the graph's width grew
    * quadratically on the tuple family (criterion 4, production_reads 9447,
    * 22919, 189767, 641607 at 64, 128, 512, 1024; measured 2026-11-07). A
    * residual with its own closure state beside the extended one gave a class
    * one closure state for each depth of partial application: tuple-256's type
    * check took 324 s against 7 s.
    *
    * FIXME (open; 2026-11-07): the residuals of later
    * https://github.com/Atry/private-overlay/issues/2034 arguments are not
    * nodes, an incompleteness of the β rule's reducts, not an unsoundness. A
    * lemma whose right side is a thunk applied to two or more arguments before
    * its closure is read, such as a contract that needs k and f filled in
    * `(λk. λf. λy. …) c d`, finds only k filled in a node: the curried
    * contracts need k only. Candidates: a residual whose fillings share the
    * previous residual's (not expressible as one flat thunk layer), or
    * residuals on demand by a strategy.
    */
  private def betaWorked[C <: NativeSpecializer & Singleton](
      program: Program[C],
      compiled: CompiledProgram[C],
      pending: PendingBeta,
      graph: EGraph[C]
  ): EGraph[C] =
    graph.layer(pending.application) match
      case Apply(_, argument) =>
        val state = pending.state
        if state.left - 1 > 0 then
          val extended = graph.closureStateExtended(
            pending.application,
            state.applied(argument)
          )
          if state.argumentsReversed.nonEmpty then extended
          else
            extended.layer(state.thunk) match
              case Thunk(code, holes, fillings) =>
                val (withResidual, residual) =
                  extended.residualAdded(
                    residualThunk(code, holes, fillings, Vector(argument))
                  )
                withResidual.unionQueued(
                  pending.application,
                  residual,
                  Justification.Beta(state.thunk),
                  Option.when(residual >= extended.nodeCount)(
                    MadeNodes(extended.nodeCount, residual)
                  )
                )
              case other =>
                throw IllegalStateException(
                  s"the closure state's node ${state.thunk} is no thunk: $other"
                )
        else
          graph.layer(state.thunk) match
            case Thunk(code, holes, fillings) =>
              val values =
                slotValues(holes, state.argumentsWith(argument), fillings)
              // A code the program was not built with, such as one the graph made by respelling a thunk in the front
              // end's spelling (`EGraph.layerMade`), is read by the
              // reader of any code, which builds the nodes the compiled body would (children first, an inner thunk's
              // fillings read at the slots and its code kept).
              val (built, body) =
                if program.codes.contains(code) then
                  compiled.body(code, graph, values)
                else HigherOrderMatching.bodyAdded(graph, code, values)
              built.unionQueued(
                pending.application,
                body,
                Justification.Beta(state.thunk),
                Option.when(body >= graph.nodeCount)(
                  MadeNodes(graph.nodeCount, body)
                )
              )
            case other =>
              throw IllegalStateException(
                s"the closure state's node ${state.thunk} is no thunk: $other"
              )
      case other =>
        throw IllegalStateException(
          s"the β step's node ${pending.application} is no application: $other"
        )

  /** The thunk applied to fewer arguments than it has holes: the same code, the
    * holes after the arguments', and each argument of a bound hole among the
    * fillings at its slot's place (the fillings are the values of the slots
    * that are no hole, in the order of their slots).
    */
  def residualThunk(
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[Int],
      arguments: Vector[Int]
  ): Thunk[Int] =
    require(
      arguments.size < holes.size,
      s"${arguments.size} arguments leave no hole of $holes"
    )
    val (residualHoles, residualFillings) =
      arguments.foldLeft((holes, fillings)) {
        case ((remaining, filled), supplied) =>
          val rest = remaining.tail
          remaining.head match
            case Hole.Bound(slot) =>
              val position = (0 until slot).count(candidate =>
                !rest.contains(Hole.Bound(candidate))
              )
              (rest, filled.patch(position, Vector(supplied), 0))
            case Hole.Ignored => (rest, filled)
      }
    Thunk(code, residualHoles, residualFillings)

  /** What each slot of a thunk's code holds, by slot from 0: the slot of the
    * binder at position P of the holes holds the P-th argument, and every other
    * slot the next filling (the IR's `slot_values/4`).
    */
  def slotValues(
      holes: Vector[Hole],
      arguments: Vector[Int],
      fillings: Vector[Int]
  ): Vector[Int] =
    require(
      arguments.size == holes.size,
      s"${arguments.size} arguments for ${holes.size} holes"
    )
    val holeCount = holes.count {
      case Hole.Bound(_) => true
      case Hole.Ignored  => false
    }
    val (values, unread) =
      (0 until holeCount + fillings.size).foldLeft(
        (Vector.empty[Int], fillings.toList)
      ) { case ((read, remaining), slot) =>
        holes.indexOf(Hole.Bound(slot)) match
          case -1 =>
            remaining match
              case next :: rest => (read :+ next, rest)
              case Nil          =>
                throw IllegalArgumentException(
                  s"the fillings $fillings do not fill the slots of $holes"
                )
          case position => (read :+ arguments(position), remaining)
      }
    require(
      unread.isEmpty,
      s"the fillings $fillings are more than the slots of $holes"
    )
    values
