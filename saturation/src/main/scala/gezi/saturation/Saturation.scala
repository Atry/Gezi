package gezi.saturation

import gezi.egraph.EGraph
import gezi.egraph.InstanceKey
import gezi.egraph.Justification
import gezi.egraph.MadeNodes
import gezi.egraph.PendingBeta
import gezi.ematching.CompiledProgram
import gezi.ematching.Match
import gezi.ematching.Matching
import gezi.ematching.Program
import gezi.ematching.SeedKey
import gezi.ematching.SeedKind
import gezi.ir.BuiltInRule
import gezi.ir.Code
import gezi.ir.Direction
import gezi.ir.Instruction
import gezi.ir.Hole
import gezi.ir.Layer
import gezi.ir.Store
import scala.annotation.tailrec
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Thunk}

/** How a saturation ended, with the instances that changed the graph: no
  * delta left, the budget reached, or a stop requested by the caller's
  * signal (judge record 4.4) before a delta was taken.
  */
enum End:
  case FixedPoint(instances: Int)
  case BudgetExhausted(instances: Int)
  case Stopped(instances: Int)

/** A saturation's result: the graph, the node of each input, the nodes made
  * while the inputs were added, and how it ended.
  */
final case class Run(
    graph: EGraph,
    inputNodes: Vector[Int],
    inputNodesMade: Int,
    end: End
)

/** The fixed-point loop of the Prolog baseline (`fixpoint_egraph_run/3`),
  * over a program and its compiled form, whichever backend compiled it: the
  * deltas matched until none is left, the orientations that only unite
  * before the others; every match of a delta found on one graph and then
  * applied in order; unions and β steps worked after every instance.
  */
object Saturation:

  /** The run of the inputs: the initial graph of the pattern instructions, the
    * inputs added, the agenda worked and the deltas matched, with the
    * built-in rules the round enables; the graph records the terms made
    * when `explained` (a run whose proof is wanted).
    */
  def run(
      program: Program,
      compiled: CompiledProgram,
      rules: Set[BuiltInRule],
      store: Store,
      headArityBounds: Map[Instruction, Int],
      patternInstructions: Vector[Instruction],
      inputs: Vector[Instruction],
      budget: Int,
      explained: Boolean,
      stop: StopSignal
  ): Run =
    runFrom(program, compiled, rules, initialGraph(store, headArityBounds, patternInstructions, explained), inputs, budget, stop)

  /** The run of the inputs from the initial graph given, such as the graph
    * of the pattern instructions with a cost analysis (`EGraph.analysed`).
    */
  def runFrom(
      program: Program,
      compiled: CompiledProgram,
      rules: Set[BuiltInRule],
      initial: EGraph,
      inputs: Vector[Instruction],
      budget: Int,
      stop: StopSignal
  ): Run =
    val (withInputs, inputNodes) = inputsAdded(initial, inputs)
    val (graph, end) = saturated(program, compiled, rules, withInputs, budget, stop)
    Run(graph, inputNodes, withInputs.canonicalNodeCount - initial.canonicalNodeCount, end)

  /** The graph of the instructions the matched sides mention, in the order given
    * (the baseline's `pattern_handles/2`).
    */
  def initialGraph(
      store: Store,
      headArityBounds: Map[Instruction, Int],
      patternInstructions: Vector[Instruction],
      explained: Boolean
  ): EGraph =
    patternInstructions.foldLeft(EGraph.empty(store, headArityBounds, explained)) {
      (graph, instruction) =>
        val (added, _) = graph.instructionAdded(instruction)
        added
    }

  /** The graph with the inputs added in order, and the node of each. */
  def inputsAdded(graph: EGraph, inputs: Vector[Instruction]): (EGraph, Vector[Int]) =
    inputs.foldLeft((graph, Vector.empty[Int])) { case ((current, nodes), input) =>
      val (next, node) = current.instructionAdded(input)
      (next, nodes :+ node)
    }

  /** The graph saturated: the agenda worked, then the deltas matched until
    * none is left, the instances that changed the graph reach the budget,
    * or the signal asks for a stop, which is read before each delta.
    *
    * The budget counts the graph's instances from its start, so a graph
    * that a run left with `End.BudgetExhausted` or `End.Stopped` is
    * saturated further by passing it back with a budget above its
    * `instances`. Nothing is lost at the cut: a stop is read before a delta
    * is taken, and a delta the budget cut in the middle of its matches is
    * put back on its stack (`EGraph.mergeRestored`, `deltaRestored`), so
    * the resumed run matches it again; an instance of it already applied is
    * skipped by its key, or, its classes joined since, changes nothing and
    * is not counted. The graph the cut leaves is equal to the
    * inputs under the lemmas, as every graph of a run is, so its extraction
    * is sound.
    *
    * FIXME (2026-11-02): the signal is read between deltas only. The https://github.com/Atry/private-overlay/issues/1967
    * matches of one delta and their instances, and the agenda worked after
    * each (unions and β steps, which the budget does not count either, see
    * `agendaWorked`), run to their end once the delta is taken, so a call
    * stuck in one large delta or one long agenda still outlasts the judge's
    * cancel grace and is killed. Not
    * measured: no point of rounds 13 or 14 is known to spend a grace's
    * length in one delta. Candidate: read the signal in `matchesApplied`
    * before each match and in the agenda's loop, ending `End.Stopped` with
    * the graph as it is; every union made so far is an instance of a lemma
    * or a congruence, so the graph stays sound when cut there.
    */
  def saturated(
      program: Program,
      compiled: CompiledProgram,
      rules: Set[BuiltInRule],
      graph: EGraph,
      budget: Int,
      stop: StopSignal
  ): (EGraph, End) =
    require(budget >= 0, s"a budget is not negative: $budget")
    loop(program, compiled, rules, budget, stop, agendaWorked(program, compiled, rules, graph))

  /** The outcome of the matches of one delta: go on, or stop on the budget.
    */
  private enum Applied:
    case Continue(graph: EGraph)
    case BudgetSpent(graph: EGraph)

  /** The baseline's `saturation_loop/4`: the stack of the orientations that
    * only unite first; a duplicate taken is skipped.
    *
    * FIXME: the order of the deltas (the merges first, then the https://github.com/Atry/private-overlay/issues/2032
    * additions, each a stack) and of the agenda is fixed here, and it decides which instances a budget's cut keeps.
    * The order is to become an option of one interface chosen by configuration (entry data and `Defaults`).
    */
  @tailrec
  private def loop(
      program: Program,
      compiled: CompiledProgram,
      rules: Set[BuiltInRule],
      budget: Int,
      stop: StopSignal,
      graph: EGraph
  ): (EGraph, End) =
    val taken = graph.mergeTaken
      .map((node, rest) => (SeedKind.Merge, node, rest))
      .orElse(graph.deltaTaken.map((node, rest) => (SeedKind.Add, node, rest)))
    taken match
      case None => (graph, End.FixedPoint(graph.instances))
      case Some(_) if stop.stopRequested => (graph, End.Stopped(graph.instances))
      case Some((kind, node, rest)) =>
        val outcome =
          if rest.live(node) then deltaMatched(program, compiled, rules, kind, node, budget, rest)
          else Applied.Continue(rest)
        outcome match
          case Applied.Continue(next) =>
            loop(program, compiled, rules, budget, stop, agendaWorked(program, compiled, rules, next))
          case Applied.BudgetSpent(next) =>
            val restored = kind match
              case SeedKind.Merge => next.mergeRestored(node)
              case SeedKind.Add   => next.deltaRestored(node)
            (restored, End.BudgetExhausted(next.instances))

  /** The baseline's `delta_matched/6`: the matches of the delta under each
    * of its keys (an application's `Apply`, then its heads in filing
    * order), then under `Closure` when its class holds a closure state, then
    * for the orientations that add nodes under its first instruction; all found
    * on one graph, counted, then applied in order.
    */
  private def deltaMatched(
      program: Program,
      compiled: CompiledProgram,
      rules: Set[BuiltInRule],
      kind: SeedKind,
      node: Int,
      budget: Int,
      graph: EGraph
  ): Applied =
    val keyed = deltaKeys(graph, node).map(key =>
      compiled.matches(kind, key, graph, node)
    )
    val closure =
      if graph.hasClosure(graph.root(node)) then
        Vector(compiled.matches(kind, SeedKey.Closure, graph, node))
      else Vector.empty
    val instruction = kind match
      case SeedKind.Add =>
        graph
          .nodeInstruction(node)
          .fold(Vector.empty[Matching])(nodeInstruction =>
            Vector(compiled.matches(kind, SeedKey.InstructionNode(nodeInstruction), graph, node))
          )
      case SeedKind.Merge => Vector.empty
    val matchings = keyed ++ closure ++ instruction
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

  /** The baseline's `delta_keys/2`: a leaf has no key a seed is filed under. */
  private def deltaKeys(graph: EGraph, node: Int): Vector[SeedKey] =
    graph.layer(node) match
      case Apply(_, _) =>
        SeedKey.Apply +: graph.nodeHeads(node).map(SeedKey.Headed(_))
      case Parallel(_, _)           => Vector(SeedKey.Parallel)
      case Choice(_, _)             => Vector(SeedKey.Choice)
      case Thunk(code, holes, _)    => Vector(SeedKey.Thunk(code, holes))
      case NoinlineLeaf(_)                  => Vector.empty

  /** The baseline's `matches_applied/5`: each match's root and bindings read
    * as roots; its instance key made, which may make nodes; a key there
    * already skipped; otherwise the instance applied, and counted when it
    * made a node or joined two classes, the run stopping as soon as the
    * count reaches the budget.
    */
  @tailrec
  private def matchesApplied(
      program: Program,
      compiled: CompiledProgram,
      rules: Set[BuiltInRule],
      matches: Vector[Match],
      index: Int,
      budget: Int,
      graph: EGraph
  ): Applied =
    if index >= matches.size then Applied.Continue(graph)
    else
      val found = matches(index)
      val root = graph.root(found.root)
      val bindings = found.bindings.map(_.map(graph.root))
      val (keyed, key) =
        instanceKeyMade(program, compiled, found.orientation, root, bindings, graph)
      keyed.instanceKeyAdded(key) match
        case None =>
          matchesApplied(program, compiled, rules, matches, index + 1, budget, keyed)
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
              matchesApplied(program, compiled, rules, matches, index + 1, budget, counted)
          else
            matchesApplied(program, compiled, rules, matches, index + 1, budget, applied)

  /** The baseline's `instance_key_made/6`: the matched root, the essential
    * metavariables' roots and the classes of the shared subterms, which are
    * built (and may be made) in their order.
    */
  private def instanceKeyMade(
      program: Program,
      compiled: CompiledProgram,
      orientation: Int,
      root: Int,
      bindings: Vector[Option[Int]],
      graph: EGraph
  ): (EGraph, InstanceKey) =
    val plan = program.orientations(orientation)
    val (built, classes) =
      plan.shared.indices.foldLeft((graph, Vector.empty[Int])) {
        case ((current, roots), part) =>
          val (next, node) = compiled.shared(orientation, part, current, bindings)
          (next, roots :+ next.root(node))
      }
    (
      built,
      InstanceKey(orientation, root, plan.essential.map(bindings(_)), classes)
    )

  /** The baseline's `instance_applied/5`: the added side built and united
    * with the matched root, the lemma's left side first, and the agenda
    * worked.
    */
  private def instanceApplied(
      program: Program,
      compiled: CompiledProgram,
      rules: Set[BuiltInRule],
      orientation: Int,
      root: Int,
      bindings: Vector[Option[Int]],
      graph: EGraph
  ): EGraph =
    val plan = program.orientations(orientation)
    val (built, addedNode) = compiled.added(orientation, graph, bindings)
    val justification = Justification.Lemma(plan.lemma, bindings)
    // The added side is the instance's own node only when the graph did not
    // hold it before (`UnionRecord.made`): a hash-consed hit is an older node.
    val made = Option.when(addedNode >= graph.nodeCount)(MadeNodes(graph.nodeCount, addedNode))
    val united = plan.direction match
      case Direction.Forward  => built.unionWorked(root, addedNode, justification, made)
      case Direction.Backward => built.unionWorked(addedNode, root, justification, made)
    agendaWorked(program, compiled, rules, united)

  /** The baseline's `agenda_worked/2`: every pending union and β step
    * worked, the unions first, each queue in the order it was filled. In a
    * round that does not enable `BuiltInRule.Beta` a pending β step is taken
    * off its queue and dropped uncounted (`EGraph.betaDiscarded`), so the β
    * rule makes no union, no node and no closure state.
    */
  @tailrec
  def agendaWorked(program: Program, compiled: CompiledProgram, rules: Set[BuiltInRule], graph: EGraph): EGraph =
    graph.unionTaken match
      case Some((pending, rest)) =>
        agendaWorked(
          program,
          compiled,
          rules,
          rest.unionWorked(pending.first, pending.second, pending.justification, pending.made)
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
              agendaWorked(program, compiled, rules, betaWorked(program, compiled, pending, rest))
            case None => graph
        else
          graph.betaDiscarded match
            case Some(rest) => agendaWorked(program, compiled, rules, rest)
            case None       => graph

  /** The baseline's `beta_worked/4`: the application fills the next hole of
    * the closure state: a new state of its class while a hole is left; when
    * none is, the thunk's code read with its slots filled and united with the
    * application. Besides, an application that gives a thunk node its first
    * argument and leaves a hole is united with its residual thunk.
    *
    * The residual thunk (`residualThunk`) is one β step,
    * `(λk. λy. B) c = λy. B[k := c]`, a node the extraction can read; a
    * closure state is no node. It is needed by the curried contracts of
    * `prolog_backend_shapes`, whose right sides `(λk. λy. …) (contract_at g)`
    * are one thunk of two holes once a choice of one member is its member:
    * without the residual the steps of folds stayed
    * untyped (measured 2026-11-07: four tests of `NativeRouteCompilationTest`,
    * cons's native called 4 times instead of 8 on a fold of size 4).
    *
    * Only the first argument of a thunk node makes a residual, and a residual
    * never makes another: it is added without a closure state of its own
    * (`EGraph.residualAdded`), its class holding the application's extended
    * state, which carries the same arguments, so that the residual of a
    * further argument is never reached. A residual for every argument is
    * flat, the k-th of an n-hole thunk k fillings wide, n²/2 in all: the
    * graph's width grew quadratically on the tuple family (criterion 4,
    * production_reads 9447, 22919, 189767, 641607 at 64, 128, 512, 1024;
    * measured 2026-11-07). A residual with its own closure state beside the
    * extended one gave a class one closure state for each depth of partial
    * application: tuple-256's type check took 324 s against 7 s.
    *
    * FIXME (open; 2026-11-07): the residuals of later https://github.com/Atry/private-overlay/issues/2034
    * arguments are not nodes, an incompleteness of the β rule's reducts, not
    * an unsoundness. A lemma whose right side is a thunk applied to two or
    * more arguments before its closure is read, such as a contract that
    * needs k and f filled in `(λk. λf. λy. …) c d`, finds only k filled in a
    * node: the curried contracts need k only. Candidates: a residual whose
    * fillings share the previous residual's (not expressible as one flat
    * thunk layer), or residuals on demand by a strategy.
    */
  private def betaWorked(
      program: Program,
      compiled: CompiledProgram,
      pending: PendingBeta,
      graph: EGraph
  ): EGraph =
    graph.layer(pending.application) match
      case Apply(_, argument) =>
        val state = pending.state
        if state.left - 1 > 0 then
          val extended = graph.closureStateExtended(pending.application, state.applied(argument))
          if state.argumentsReversed.nonEmpty then extended
          else
            extended.layer(state.thunk) match
              case Thunk(code, holes, fillings) =>
                val (withResidual, residual) =
                  extended.residualAdded(residualThunk(code, holes, fillings, Vector(argument)))
                withResidual.unionQueued(
                  pending.application,
                  residual,
                  Justification.Beta(state.thunk),
                  Option.when(residual >= extended.nodeCount)(MadeNodes(extended.nodeCount, residual))
                )
              case other =>
                throw IllegalStateException(s"the closure state's node ${state.thunk} is no thunk: $other")
        else
          graph.layer(state.thunk) match
            case Thunk(code, holes, fillings) =>
              val values = slotValues(holes, state.argumentsWith(argument), fillings)
              // A code the program was not built with, such as one the graph made by respelling a thunk in the front
              // end's spelling (`EGraph.layerMade`), is read by the
              // reader of any code, which builds the nodes the compiled body would (children first, an inner thunk's
              // fillings read at the slots and its code kept).
              val (built, body) =
                if program.codes.contains(code) then compiled.body(code, graph, values)
                else HigherOrderMatching.bodyAdded(graph, code, values)
              built.unionQueued(
                pending.application,
                body,
                Justification.Beta(state.thunk),
                Option.when(body >= graph.nodeCount)(MadeNodes(graph.nodeCount, body))
              )
            case other =>
              throw IllegalStateException(
                s"the closure state's node ${state.thunk} is no thunk: $other"
              )
      case other =>
        throw IllegalStateException(
          s"the β step's node ${pending.application} is no application: $other"
        )

  /** The thunk applied to fewer arguments than it has holes: the same code,
    * the holes after the arguments', and each argument of a bound hole
    * among the fillings at its slot's place (the fillings are the values of
    * the slots that are no hole, in the order of their slots).
    */
  def residualThunk(code: Code, holes: Vector[Hole], fillings: Vector[Int], arguments: Vector[Int]): Layer[Int] =
    require(arguments.size < holes.size, s"${arguments.size} arguments leave no hole of $holes")
    val (residualHoles, residualFillings) = arguments.foldLeft((holes, fillings)) {
      case ((remaining, filled), supplied) =>
        val rest = remaining.tail
        remaining.head match
          case Hole.Bound(slot) =>
            val position = (0 until slot).count(candidate => !rest.contains(Hole.Bound(candidate)))
            (rest, filled.patch(position, Vector(supplied), 0))
          case Hole.Ignored => (rest, filled)
    }
    Thunk(code, residualHoles, residualFillings)

  /** What each slot of a thunk's code holds, by slot from 0: the slot of
    * the binder at position P of the holes holds the P-th argument, and every
    * other slot the next filling (the IR's `slot_values/4`).
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
              case Nil =>
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
