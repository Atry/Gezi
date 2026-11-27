package com.yang_bo.gezi.backendcomparison

import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.ir.NativeSpecializer
import com.yang_bo.gezi.ir.Pattern
import com.yang_bo.gezi.ir.{Apply, Choice, Parallel, Thunk}

/** A naive matching that tries every pattern at every class, the oracle the
  * index's program and the saturation's fixed points are checked against.
  */
object NaiveMatching:

  /** The bindings of the metavariables, extending the given ones, under which
    * the class has the pattern: a metavariable is its class, a lambda pattern a
    * class with a closure state, an instruction the class of its node, and a
    * layer a live node of the class with that layer over classes that have the
    * children's patterns.
    */
  def matches[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      pattern: Pattern[C],
      root: Int,
      bindings: Map[Int, Int]
  ): Vector[Map[Int, Int]] =
    derivations(
      graph,
      pattern,
      root,
      Derivation(bindings, Set.empty, Set.empty)
    ).map(_.bindings)

  /** A way the pattern holds at a class: the bindings, the nodes it read (the
    * live node taken at each layer, the node of each instruction) and the
    * classes it read as holding a closure.
    */
  final case class Derivation(
      bindings: Map[Int, Int],
      nodesRead: Set[Int],
      closuresRead: Set[Int]
  )

  /** The derivations, extending the given one, by which the class has the
    * pattern, as `matches` reads it.
    */
  def derivations[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      pattern: Pattern[C],
      root: Int,
      sofar: Derivation
  ): Vector[Derivation] = pattern match
    case Pattern.Metavariable(index) =>
      sofar.bindings.get(index) match
        case Some(bound) =>
          if bound == root then Vector(sofar) else Vector.empty
        case None =>
          Vector(sofar.copy(bindings = sofar.bindings.updated(index, root)))
    case Pattern.Closure(index) =>
      if graph.hasClosure(root) then
        derivations(
          graph,
          Pattern.Metavariable(index),
          root,
          sofar.copy(closuresRead = sofar.closuresRead + root)
        )
      else Vector.empty
    case Pattern.InstructionReference(instruction) =>
      graph
        .instructionNode(instruction)
        .filter(graph.root(_) == root)
        .toVector
        .map(node => sofar.copy(nodesRead = sofar.nodesRead + node))
    case compound =>
      graph.liveNodes
        .filter(node => node.root == root && sameShape(compound, node.layer))
        .flatMap(node =>
          compound.children
            .zip(node.layer.children)
            .foldLeft(
              Vector(sofar.copy(nodesRead = sofar.nodesRead + node.node))
            ) { case (gathered, (child, childRoot)) =>
              gathered.flatMap(derivations(graph, child, childRoot, _))
            }
        )

  private def sameShape[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C],
      layer: com.yang_bo.gezi.ir.LayerWith[Int, com.yang_bo.gezi.ir.Configured[C]]
  ): Boolean =
    (pattern, layer) match
      case (Pattern.Apply(_, _), Apply(_, _))       => true
      case (Pattern.Parallel(_, _), Parallel(_, _)) => true
      case (Pattern.Choice(_, _), Choice(_, _))     => true
      case (
            Pattern.Thunk(code, holes, fillings),
            Thunk(layerCode, layerHoles, nodes)
          ) =>
        code == layerCode && holes == layerHoles && fillings.size == nodes.size
      case _ => false
