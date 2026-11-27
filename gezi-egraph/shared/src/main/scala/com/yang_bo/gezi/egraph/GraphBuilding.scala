package com.yang_bo.gezi.egraph

import com.yang_bo.gezi.ir.LayerWith
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** What a compiled program does to a graph when it builds nodes. Each operation
  * returns the graph after it; the graph it was called on is unchanged.
  */
trait GraphBuilding[C <: NativeSpecializer & Singleton, Graph <: GraphBuilding[
  C,
  Graph
]] extends GraphView[C]:

  /** The node of the instruction: found when the graph has the instruction,
    * otherwise its stored layer added (its children first, function before
    * argument, members and fillings in order), or a leaf when the instruction
    * is noinline.
    */
  def instructionAdded(instruction: Configured[C]): (Graph, Int)

  /** The node of a layer over nodes of any class, read over their roots: found
    * when a node has that signature, made otherwise.
    */
  def layerAdded(layer: LayerWith[Int, Configured[C]]): (Graph, Int)

  /** The application, which an added side built with a function metavariable or
    * a lambda at the head of its spine, is read by the β rule: it takes a β
    * step with every closure state of its function's class, now and when the
    * class gains one.
    */
  def applicationRead(node: Int): Graph
