package gezi.egraph

import gezi.ir.Instruction
import gezi.ir.Layer

/** The head of an application's spine: an instruction and the number of arguments
  * applied to it; a class holding the instruction's node has the head of arity 0.
  */
final case class Head(instruction: Instruction, arity: Int)

/** The shapes a class files its members under. */
enum MemberShape:
  case Apply
  case Parallel
  case Choice
  case Thunk
  case Leaf

/** The roles a class files its users under: the nodes with the class as
  * their function, argument, left or right child.
  */
enum UserRole:
  case Function
  case Argument
  case Left
  case Right

/** The roles a class files its positional users under: the nodes with the
  * class as a member of their choice or a filling of their thunk.
  */
enum PositionRole:
  case Member
  case Filling

/** A user of a class at a position of its members or fillings. */
final case class PositionUser(position: Int, user: Int)

/** What a compiled program reads of a graph to match a delta. Nodes are
  * numbered by their creation; a class is named by the number of its root.
  *
  * The entries a class lists are every node ever filed there, in filing
  * order, the duplicates among them included: a reader skips a node for which
  * `live` is false. A list is a snapshot of the graph it was read from, so
  * that reading it while matching sees exactly the entries filed before.
  */
trait GraphView:

  /** The node's layer as it was made, over the nodes that were then the
    * roots of its children's classes.
    */
  def layer(node: Int): Layer[Int]

  /** The root of the node's class. */
  def root(node: Int): Int

  /** The node is not a duplicate: no union of congruence has made another
    * node stand for it.
    */
  def live(node: Int): Boolean

  def members(root: Int, shape: MemberShape): Vector[Int]

  def headMembers(root: Int, head: Head): Vector[Int]

  def users(root: Int, role: UserRole): Vector[Int]

  def positionUsers(root: Int, role: PositionRole): Vector[PositionUser]

  /** The node of the instruction, if the graph has added it. */
  def instructionNode(instruction: Instruction): Option[Int]

  /** The node of the layer, a layer over nodes of any class read over their
    * roots, when the graph has one of that signature.
    */
  def layerNode(layer: Layer[Int]): Option[Int]

  /** The class holds a closure state (a thunk with a hole left). */
  def hasClosure(root: Int): Boolean
