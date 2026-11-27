package gezi.egraph

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.ir.LayerWith
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.StateMachine
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Thunk}

/** A cost analysis of the law: a generated cost per label (each instruction's
  * leaf, and each other constructor), a node's cost its label's plus its
  * children's class costs, a class's the least of its nodes'. `None` is the
  * cost of a class with no node priced yet, the unit of the least.
  */
final case class LabelCostAnalysis(
    instructionCosts: Vector[Int],
    constructorCosts: Vector[Int]
) extends ClassAnalysis[NoFacts.type, Option[Int]]:

  def identity: Option[Int] = None

  def made(
      layer: LayerWith[Option[Int], Configured[NoFacts.type]]
  ): Option[Int] =
    layer.children
      .foldLeft(Option(labelCost(layer)))((sum, child) =>
        for total <- sum; cost <- child yield total + cost
      )

  def joined(left: Option[Int], right: Option[Int]): Option[Int] =
    (left ++ right).minOption

  private def labelCost(
      layer: LayerWith[Option[Int], Configured[NoFacts.type]]
  ): Int = layer match
    case NoinlineLeaf(instruction) =>
      val position = GraphMachine.instructions.indexOf(instruction)
      require(
        position >= 0,
        s"a leaf of no instruction of the test: $instruction"
      )
      instructionCosts(position)
    case Apply(_, _)                  => constructorCosts(0)
    case Parallel(_, _)               => constructorCosts(1)
    case Choice(_, _)                 => constructorCosts(2)
    case Thunk(_, _, _)               => constructorCosts(3)
    case view: gezi.ir.StorageView[?] =>
      throw IllegalStateException(
        s"a node's layer is never a storage's view: $view"
      )

/** The law of the e-graph's product of analyses, whose purpose is to catch a
  * cost the incremental repair fails to propagate: a node added, a union, or a
  * congruence the agenda works, after which some class's kept cost differs from
  * the least fixed point computed from scratch on the same graph
  * (`AnalysisSlot.computed`), and two analyses kept together that are not kept
  * independently (one slot's repair writing the other's values, or one
  * replacing the other). The commands are the e-graph's state machine test's
  * (`GraphMachine`), from the empty graph keeping two generated analyses, each
  * checked against its own fixed point; the agreement is checked after every
  * command that leaves the agenda empty. While a union waits, a class may keep
  * the cost of a node marked a duplicate, which the from-scratch values, over
  * live nodes, leave out until the union joins it with its twin's class.
  */
class ClassAnalysisLawTest extends GeneratedProperties:

  /** The values the graph keeps for the analysis, when it keeps it. */
  private def kept(
      graph: Graph,
      analysis: ClassAnalysis[NoFacts.type, ?]
  ): Option[Map[Int, Any]] =
    graph.analyses.find(_.analysis eq analysis).map(_.values)

  private final class Machine(
      val analysis: LabelCostAnalysis,
      val other: LabelCostAnalysis
  ) extends GraphMachine(
        GraphMachine.emptyGraph.analysed(analysis).analysed(other)
      ):

    def agreement(
        model: GraphModel,
        system: GraphSystem,
        command: GraphCommand
    ): Result =
      if system.graph.unionTaken.isDefined then Result.success
      else
        Result.all(
          List(analysis, other).map(each =>
            val found = kept(system.graph, each)
            val computed = AnalysisSlot.computed(system.graph, each).values
            if found.contains(computed) then Result.success
            else
              Result.failure.log(
                s"kept costs $found, computed from scratch $computed"
              )
          ) :+ Result
            .diff(system.graph.analyses.size, 2)(_ == _)
            .log("the two analyses are not two slots")
        )

  private val cost = Gen.int(Range.constant(0, 5))

  private val analysisGenerator: Gen[LabelCostAnalysis] =
    for
      instructionCosts <- cost.list(
        Range.singleton(GraphMachine.instructions.size)
      )
      constructorCosts <- cost.list(Range.singleton(4))
    yield LabelCostAnalysis(
      instructionCosts.toVector,
      constructorCosts.toVector
    )

  /** The commands every sequence starts with: the first two instructions'
    * leaves, whose costs under the first analysis differ by construction
    * (`distinctLeaves`), united, and the agenda worked, so that every iteration
    * unites two classes of different costs and prices the joined class's users
    * again.
    */
  private val unionOfDifferentCosts: Vector[GraphCommand] =
    Vector(
      GraphCommand.AddInstruction(GraphMachine.instructions(0)),
      GraphCommand.AddInstruction(GraphMachine.instructions(1)),
      GraphCommand.Union(0, 1),
      GraphCommand.RunAgenda
    )

  /** An analysis whose first two instructions' leaves cost differently. */
  private val distinctLeaves: Gen[LabelCostAnalysis] =
    analysisGenerator.map(analysis =>
      analysis.copy(instructionCosts =
        analysis.instructionCosts
          .updated(1, (analysis.instructionCosts(0) + 1) % 6)
      )
    )

  property(
    "the kept costs are the least fixed point computed from scratch",
    _.copy(testLimit = 200)
  ) {
    for
      analysis <- distinctLeaves.forAll
      other <- analysisGenerator.forAll
      machine = Machine(analysis, other)
      commands <- StateMachine.forAll(machine, 60)
    yield StateMachine.run(machine, unionOfDifferentCosts ++ commands)
  }
