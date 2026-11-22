package gezi.ematching

import gezi.egraph.GraphBuilding
import gezi.egraph.GraphView
import gezi.ir.Code

/** A match of an orientation: the root of the class its matched side was
  * found in, and the node each metavariable was bound to, `None` for a
  * metavariable no side mentions.
  */
final case class Match(
    orientation: Int,
    root: Int,
    bindings: Vector[Option[Int]]
)

/** The matches of seeds, in the order found, and the entries their steps
  * read: one for each entry of a class's members, members of a head, users
  * or position users that a step went through, the measure of matching's
  * work. A step the seeds of a key share in their tree (`SeedTree`) reads
  * its entries once for all of them.
  */
final case class Matching(found: Vector[Match], entriesRead: Int):
  def read(count: Int): Matching = copy(entriesRead = entriesRead + count)

object Matching:
  val none: Matching = Matching(Vector.empty, 0)

/** A backend turns a whole program into an object that runs it. It is
  * given the program at once, so that a backend that compiles (to closures,
  * to TASTy through scala3-staging, to bytecode) pays its compiler once.
  * Every backend runs a program the same way: the same matches in the same
  * order, the same entries read, the same nodes built in the same order.
  */
trait Backend:
  def compiled(program: Program): CompiledProgram

/** A program as a backend runs it. */
trait CompiledProgram:

  /** The matches of the seeds filed under the kind and the key, from the
    * delta node, read off the graph by a run of their tree
    * (`Program.trees`): the seeds in their order, and each seed's matches in
    * the order of its steps' entries; with the entries the tree's steps
    * read.
    */
  def matches(
      kind: SeedKind,
      key: SeedKey,
      graph: GraphView,
      delta: Int
  ): Matching

  /** The node of the orientation's added side, built with the bindings. */
  def added[Graph <: GraphBuilding[Graph]](
      orientation: Int,
      graph: Graph,
      bindings: Vector[Option[Int]]
  ): (Graph, Int)

  /** The node of the orientation's shared subterm at the index, built with
    * the bindings.
    */
  def shared[Graph <: GraphBuilding[Graph]](
      orientation: Int,
      part: Int,
      graph: Graph,
      bindings: Vector[Option[Int]]
  ): (Graph, Int)

  /** The node of the code's body with its slots read as the given nodes. */
  def body[Graph <: GraphBuilding[Graph]](
      code: Code,
      graph: Graph,
      slotValues: Vector[Int]
  ): (Graph, Int)
