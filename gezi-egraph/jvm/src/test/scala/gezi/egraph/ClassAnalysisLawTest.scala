package gezi.egraph

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.ir.Layer
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.StateMachine
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Thunk}

/** A cost analysis of the law: a generated cost per label (each instruction's
  * leaf, and each other constructor), a node's cost its label's plus its
  * children's class costs, a class's the least of its nodes'. `None` is the
  * cost of a class with no node priced yet, the unit of the least.
  */
final case class LabelCostAnalysis(instructionCosts: Vector[Int], constructorCosts: Vector[Int])
    extends ClassAnalysis[Option[Int]]:

  def identity: Option[Int] = None

  def made(layer: Layer[Option[Int]]): Option[Int] =
    layer.children
      .foldLeft(Option(labelCost(layer)))((sum, child) => for total <- sum; cost <- child yield total + cost)

  def joined(left: Option[Int], right: Option[Int]): Option[Int] =
    (left ++ right).minOption

  private def labelCost(layer: Layer[Option[Int]]): Int = layer match
    case NoinlineLeaf(instruction) =>
      val position = GraphMachine.instructions.indexOf(instruction)
      require(position >= 0, s"a leaf of no instruction of the test: $instruction")
      instructionCosts(position)
    case Apply(_, _)     => constructorCosts(0)
    case Parallel(_, _)  => constructorCosts(1)
    case Choice(_, _)    => constructorCosts(2)
    case Thunk(_, _, _)  => constructorCosts(3)

/** The law of the e-graph's cost analysis slot, whose
  * purpose is to catch a cost the incremental repair fails to propagate: a
  * node added, a union, or a congruence the agenda works, after which some
  * class's kept cost differs from the least fixed point computed from
  * scratch on the same graph (`AnalysisSlot.computed`). The commands are the
  * e-graph's state machine test's (`GraphMachine`), from the empty graph
  * keeping the analysis; the agreement is checked after every command that
  * leaves the agenda empty. While a union waits, a class may keep the cost
  * of a node marked a duplicate, which the from-scratch values, over live
  * nodes, leave out until the union joins it with its twin's class.
  */
class ClassAnalysisLawTest extends GeneratedProperties:

  private final class Machine(analysis: LabelCostAnalysis)
      extends GraphMachine(GraphMachine.emptyGraph.analysed(analysis)):

    def agreement(model: GraphModel, system: GraphSystem, command: GraphCommand): Result =
      if system.graph.unionTaken.isDefined then Result.success
      else
        val kept = system.graph.analysis.map(_.values)
        val computed = AnalysisSlot.computed(system.graph, analysis).values
        if kept.contains(computed) then Result.success
        else Result.failure.log(s"kept costs $kept, computed from scratch $computed")

  private val cost = Gen.int(Range.constant(0, 5))

  private val analysisGenerator: Gen[LabelCostAnalysis] =
    for
      instructionCosts <- cost.list(Range.singleton(GraphMachine.instructions.size))
      constructorCosts <- cost.list(Range.singleton(4))
    yield LabelCostAnalysis(instructionCosts.toVector, constructorCosts.toVector)

  property("the kept costs are the least fixed point computed from scratch", _.copy(testLimit = 200)) {
    for
      analysis <- analysisGenerator.forAll
      machine = Machine(analysis)
      commands <- StateMachine
        .forAll(machine, 60)
        .cover(
          5,
          "a union of two classes of different costs",
          commands => unitesDifferentCosts(machine, commands)
        )
    yield StateMachine.run(machine, commands)
  }

  /** Whether some union of the commands unites two classes whose kept costs
    * differ before it, so that the joined cost changes one side and its
    * users are priced again.
    */
  private def unitesDifferentCosts(machine: Machine, commands: Vector[GraphCommand]): Boolean =
    commands
      .foldLeft((machine.initialSystem, false)) { case ((system, found), command) =>
        val differs = command match
          case GraphCommand.Union(first, second) =>
            val costs = system.graph.analysis.map(_.values)
            costs.map(_(system.graph.root(system.nodes(first)))) !=
              costs.map(_(system.graph.root(system.nodes(second))))
          case _ => false
        (machine.systemAfter(system, command), found || differs)
      }
      ._2
