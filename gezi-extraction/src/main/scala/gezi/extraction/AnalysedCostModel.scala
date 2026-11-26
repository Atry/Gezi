package gezi.extraction

import gezi.egraph.ClassAnalysis
import gezi.egraph.EGraph

/** A cost model that also reads the cost of each child's class under a cost
  * analysis the graph keeps (`gezi.egraph.ClassAnalysis`): the cost of a production over its children's entries' costs
  * and their classes' analysed costs, in the order of `Shape.children`.
  * Only costs reach it: an analysis holds no fact about what a class holds
  * (`CONTRIBUTING.md`, "Types live only in the term").
  */
trait AnalysedCostModel[Cost, Value]:
  def cost(shape: Shape, childCosts: Vector[Cost], childValues: Vector[Value]): Cost
  def ordering: Ordering[Cost]

  /** As `CostModel.pricedChildren`. */
  def pricedChildren(shape: Shape): Vector[Boolean]

object AnalysedCostModel:

  /** The plain cost model of the extraction, reading the children's class
    * costs off the graph's slot of the analysis. Throws
    * `IllegalArgumentException` when the graph keeps no cost of that
    * analysis for a child's class.
    */
  def bound[Cost, Value](
      model: AnalysedCostModel[Cost, Value],
      graph: EGraph,
      analysis: ClassAnalysis[Value]
  ): CostModel[Cost] =
    new StatelessCostModel[Cost]:
      def cost(shape: Shape, childCosts: Vector[Cost]): Cost =
        model.cost(shape, childCosts, shape.children.map(child => analysedCost(graph, analysis, child)))
      def ordering: Ordering[Cost] = model.ordering
      def pricedChildren(shape: Shape): Vector[Boolean] = model.pricedChildren(shape)

  private def analysedCost[Value](graph: EGraph, analysis: ClassAnalysis[Value], child: Int): Value =
    graph.analysis
      .flatMap(_.valueOf(analysis, graph.root(child)))
      .getOrElse(throw IllegalArgumentException(s"the graph keeps no cost of the analysis for the class of $child"))
