package gezi.ematching.bytecode

import gezi.egraph.GraphBuilding
import gezi.ematching.Match
import gezi.ematching.Matching
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Layer
import gezi.ir.{Apply, Choice, Parallel, Thunk}

/** The matching of a tree's run so far: the matches found, by the number of the
  * seed that found them, each seed's in the order found; and the entries read.
  */
final case class Searched(bySeed: Vector[Vector[Match]], entriesRead: Int):
  def read(count: Int): Searched = copy(entriesRead = entriesRead + count)

  def found(seed: Int, matched: Match): Searched =
    copy(bySeed = bySeed.updated(seed, bySeed(seed) :+ matched))

/** The Scala values the generated code makes, through static methods (the
  * forwarders of this object) so that the class file does not spell out Scala's
  * encoding of options, tuples and enum cases. Each is a pure function.
  */
object GeneratedCodeSupport:

  val noBindings: Vector[Option[Int]] = Vector.empty

  def bound(bindings: Vector[Option[Int]], node: Int): Vector[Option[Int]] =
    bindings :+ Some(node)

  def unbound(bindings: Vector[Option[Int]]): Vector[Option[Int]] =
    bindings :+ None

  /** The matching of a tree of so many seeds before its run, a constant of the
    * generated class (its class data), made once when the program is compiled,
    * as the closure backend makes it once.
    */
  def searchStarted(seedCount: Int): Searched =
    Searched(Vector.fill(seedCount)(Vector.empty), 0)

  def found(
      searched: Searched,
      seed: Int,
      orientation: Int,
      root: Int,
      bindings: Vector[Option[Int]]
  ): Searched =
    searched.found(seed, Match(orientation, root, bindings))

  /** The matches of a tree's run grouped by seed, in the seeds' order. */
  def searchFinished(searched: Searched): Matching =
    Matching(searched.bySeed.flatten, searched.entriesRead)

  /** The value at the index, which is bound. */
  def value(values: Vector[Int], index: Int): Int =
    val node = values(index)
    require(node >= 0, s"the value at $index is unbound")
    node

  val noNodes: Vector[Int] = Vector.empty

  def appended(nodes: Vector[Int], node: Int): Vector[Int] = nodes :+ node

  def applyLayer(function: Int, argument: Int): Layer[Int] =
    Apply(function, argument)

  def parallelLayer(left: Int, right: Int): Layer[Int] = Parallel(left, right)

  def choiceLayer(left: Int, right: Int): Layer[Int] = Choice(left, right)

  def thunkLayer(
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[Int]
  ): Layer[Int] =
    Thunk(code, holes, fillings)

  def result(graph: GraphBuilding[?, ?], node: Int): (Any, Int) = (graph, node)

  /** A body that references a code the program lacks, thrown when it is built,
    * as the closure backend does.
    */
  def missingCode(code: Code): (Any, Int) =
    throw IllegalArgumentException(s"the program has no $code")

  /** The exception of a switch's default: the number names no entry. */
  def noEntry(kind: String, number: Int): RuntimeException =
    IllegalArgumentException(s"the generated program has no $kind $number")
