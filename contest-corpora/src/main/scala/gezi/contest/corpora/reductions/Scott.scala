package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemField

import gezi.weakhead.oldcorpora.ConstructorTree
import gezi.weakhead.oldcorpora.ScottDataType
import gezi.weakhead.oldcorpora.ScottDecoding
import gezi.frontend.Term
import gezi.ir.TailRecFolds
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** A constructor tree of a Scott data type, `constructor(Name, Subtrees)`
  * of `lambda_jit_scott_decoding`: the expected answer of a problem of the
  * reduction series, a tree with no ill-formed node.
  */
final case class ScottTree(name: String, subtrees: Vector[ScottTree]):

  /** The tree as the Scott decoder writes it (`ConstructorTree`),
    * trampolined, so that the deep trees of the large problems take no JVM
    * stack.
    */
  def decoded: ConstructorTree = ScottTree.decodedOf(this).result

/** The conversions of trees, trampolined. */
object ScottTree:

  private[reductions] def decodedOf(tree: ScottTree): TailRec[ConstructorTree] =
    Scott.traversed(tree.subtrees)(decodedOf).map(ConstructorTree.Constructor(tree.name, _))

/** The Scott data types the problems are read at, by the names the problems
  * state (`boolean`, `unary`, `binary`), and the canonical terms of their
  * trees: the Scott decoder of the problem corpora,
  * `gezi.weakhead.oldcorpora.ScottDecoding`, the port of
  * `old_corpora/scott_decoding.pl`, whose types are its `ScottDataType`.
  */
final case class Scott():

  /** The canonical closed term of a tree of the type
    * (`ScottDecoding.treeSurface`). Throws for a type with no such name or a
    * tree that is no value of the type.
    */
  def canonical(typeName: String, tree: ScottTree): Term =
    ScottDecoding.treeSurface(Scott.dataType(typeName), tree.decoded)

/** The trees of numbers, and the data types by name. */
object Scott:

  /** The data type the problems name `boolean`, `unary` or `binary`
    * (`scott_constructors/2`'s first argument). Throws for another name.
    */
  def dataType(typeName: String): ScottDataType = typeName match
    case "boolean" => ScottDataType.Booleans
    case "unary"   => ScottDataType.Unary
    case "binary"  => ScottDataType.Binary
    case other     => throw IllegalArgumentException(s"no Scott type $other")

  /** The constructor of no field. */
  def leaf(name: String): ScottTree = ScottTree(name, Vector.empty)

  /** The tree of a binary natural, least significant bit outermost:
    * zero, `even(h)` or `odd(h)` (`ScottDecoding.binaryTree`).
    */
  def binaryTree(number: BigInt): ScottTree = fromDecoded(ScottDecoding.binaryTree(number))

  /** The tree of a unary natural: zero, or `successor(p)`. */
  def unaryTree(number: Int): ScottTree =
    require(number >= 0, s"a unary natural is not negative: $number")
    (1 to number).foldLeft(leaf("zero"))((tree, _) => ScottTree("successor", Vector(tree)))

  /** The tree of a Boolean. */
  def booleanTree(value: Boolean): ScottTree = leaf(if value then "true" else "false")

  /** The decoded tree as a problem's tree. Throws for an ill-formed node,
    * which no expected answer holds.
    */
  def fromDecoded(tree: ConstructorTree): ScottTree = fromDecodedOf(tree).result

  private def fromDecodedOf(tree: ConstructorTree): TailRec[ScottTree] = tree match
    case ConstructorTree.Constructor(name, subtrees) => traversed(subtrees)(fromDecodedOf).map(ScottTree(name, _))
    case ConstructorTree.IllFormed => throw IllegalArgumentException("an ill-formed tree is no expected answer")

  /** The step on each item, in order, each a trampolined call. */
  private[reductions] def traversed[Item, Result](items: Vector[Item])(step: Item => TailRec[Result]): TailRec[Vector[Result]] =
    TailRecFolds.folded(items, Vector.empty[Result])((before, item) => step(item).map(before :+ _))

/** Reading trees from facts. */
object ScottTrees:

  /** The tree a datum writes, the plain pair `λtuple. tuple Name Subtrees`
    * of the constructor's name and the list of its subtrees, read as the one
    * alternative of one handler (`ProblemData.alternative`).
    */
  def treeOf(field: ProblemField): ScottTree = ProblemData.alternative(field, 1) match
    case (0, Vector(name, subtrees)) => ScottTree(ProblemData.text(name), ProblemData.list(subtrees).map(treeOf))
    case (position, fields) =>
      throw IllegalArgumentException(s"a tree is a pair of a name and subtrees, not alternative $position of ${fields.size}")
