package gezi.ematching.bytecode

import gezi.egraph.GraphBuilding
import gezi.egraph.GraphView
import gezi.ematching.Matching
import gezi.ir.NativeSpecializer

/** What the generated class implements: the entries of the program, each
  * named by a number the backend gave it, dispatched by a switch to the
  * class's static methods.
  */
trait GeneratedProgram:

  /** The matches of the entry's tree from the delta, grouped by seed in the
    * seeds' order, with the entries read.
    */
  def matches[C <: NativeSpecializer & Singleton](entry: Int, graph: GraphView[C], delta: Int): Matching

  /** The graph after building the orientation's added side, and its node. */
  def added(orientation: Int, graph: GraphBuilding[?, ?], values: Vector[Int]): (Any, Int)

  /** The graph after building the shared subterm of the number the backend
    * gave it, and its node.
    */
  def shared(part: Int, graph: GraphBuilding[?, ?], values: Vector[Int]): (Any, Int)

  /** The graph after building the body of the code of the number, and its
    * node.
    */
  def body(code: Int, graph: GraphBuilding[?, ?], values: Vector[Int]): (Any, Int)
