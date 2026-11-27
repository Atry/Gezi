package com.yang_bo.gezi.extraction

import com.yang_bo.gezi.egraph.ClassAnalysis
import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** A cost model that also reads the cost of each child's class under a cost
  * analysis the graph keeps (`com.yang_bo.gezi.egraph.ClassAnalysis`): the cost of a
  * production over its children's entries' costs and their classes' analysed
  * costs, in the order of `Shape.children`. Only costs reach it: an analysis
  * holds no fact about what a class holds (`CONTRIBUTING.md`, "Types live only
  * in the term").
  */
trait AnalysedCostModel[C <: NativeSpecializer & Singleton, Cost, Value]:
  def cost(
      shape: Shape[C],
      childCosts: Vector[Cost],
      childValues: Vector[Value]
  ): Cost
  def ordering: Ordering[Cost]

  /** As `CostModel.pricedChildren`. */
  def pricedChildren(shape: Shape[C]): Vector[Boolean]

object AnalysedCostModel:

  /** The plain cost model of the extraction, reading the children's class costs
    * off the graph's slot of the analysis. Throws `IllegalArgumentException`
    * when the graph keeps no cost of that analysis for a child's class.
    */
  def bound[C <: NativeSpecializer & Singleton, Cost, Value](
      model: AnalysedCostModel[C, Cost, Value],
      graph: EGraph[C],
      analysis: ClassAnalysis[C, Value]
  )(using C): CostModel[C, Cost] =
    new StatelessCostModel[C, Cost]:
      def cost(shape: Shape[C], childCosts: Vector[Cost]): Cost =
        model.cost(
          shape,
          childCosts,
          shape.children.map(child => analysedCost(graph, analysis, child))
        )
      def ordering: Ordering[Cost] = model.ordering
      def pricedChildren(shape: Shape[C]): Vector[Boolean] =
        model.pricedChildren(shape)

  private def analysedCost[C <: NativeSpecializer & Singleton, Value](
      graph: EGraph[C],
      analysis: ClassAnalysis[C, Value],
      child: Int
  )(using
      C
  ): Value =
    graph
      .analysisValue(analysis, graph.root(child))
      .getOrElse(
        throw IllegalArgumentException(
          s"the graph keeps no cost of the analysis for the class of $child"
        )
      )
