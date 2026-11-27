package com.yang_bo.gezi.backendcomparison

import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.saturation.End
import com.yang_bo.gezi.saturation.Saturation
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.LayerWith
import scala.annotation.tailrec
import scala.util.hashing.MurmurHash3
import com.yang_bo.gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Slot, Thunk}
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** A live node's layer with its children named by canonical class numbers: the
  * layer's kind, its constants (a leaf's instruction and a thunk's code by
  * their numbers in a `ConstantNumbers`; the slot of each hole, -1 for an
  * ignored one) and its children's numbers in layer order.
  */
final case class CanonicalNode(
    kind: Int,
    constants: Vector[Int],
    children: Vector[Int]
)

object CanonicalNode:
  /** Kind, then constants, then children, each vector compared element by
    * element and a prefix before a longer vector.
    */
  given Ordering[CanonicalNode] = (first, second) =>
    val byKind = Integer.compare(first.kind, second.kind)
    if byKind != 0 then byKind
    else
      val byConstants = compareNumbers(first.constants, second.constants)
      if byConstants != 0 then byConstants
      else compareNumbers(first.children, second.children)

  private def compareNumbers(first: Vector[Int], second: Vector[Int]): Int =
    first
      .lazyZip(second)
      .map(Integer.compare)
      .find(_ != 0)
      .getOrElse(Integer.compare(first.size, second.size))

/** The numbers a form names a leaf's instruction and a thunk's code by: the
  * exporter's numbers (`programfamilies`' `ExportedNumbering`, the Prolog
  * exporter's walk), with which `programfamilies`' snapshots of fixed points
  * are written, or the hash codes, which are the same in every process.
  */
final case class ConstantNumbers[C <: NativeSpecializer & Singleton](
    instruction: Configured[C] => Int,
    code: Code => Int
)

object ConstantNumbers:
  /** Each instruction and code by its hash code.
    *
    * FIXME (2026-11-02): a 32-bit hash code is not injective, so two
    * https://github.com/Atry/private-overlay/issues/1975 different leaf
    * instructions or codes with one hash code give one canonical constant, and
    * two different fixed points could share a form. Not observed (the forms
    * read this way are compared within one process). Candidate fixes: number
    * the constants by first occurrence in a deterministic walk of the
    * projection, or by a content digest.
    */
  def hashes[C <: NativeSpecializer & Singleton]: ConstantNumbers[C] =
    ConstantNumbers[C](_.hashCode, _.hashCode)

  /** Each instruction and code by its position in the exporter's numbering, and
    * after them each code of the projection's thunks that the numbering does
    * not hold, in the structural order of codes (`codeOrdering`), which is the
    * same in every process. Such a code is one the saturation made: a filling
    * respelled in the front end's spelling has a code no input or lemma side
    * spells. An instruction not among them is refused when the form reads it: a
    * leaf is a noinline instruction, which the saturation never makes.
    */
  def numbered[C <: NativeSpecializer & Singleton](
      instructions: Vector[Configured[C]],
      codes: Vector[Code],
      projection: Projection[C]
  )(using C): ConstantNumbers[C] =
    val exported = codes.toSet
    val made = projection.layers
      .collect { case Thunk(code, _, _) if !exported.contains(code) => code }
      .distinct
      .sorted(using codeOrdering)
    ConstantNumbers(
      instructions.zipWithIndex.toMap,
      (codes ++ made).zipWithIndex.toMap
    )

  /** Codes compared by their structure: the kind of the root layer, then its
    * slot or its holes, then its parts in order. Total on codes, and different
    * codes compare unequal, since an interned code is its structure.
    */
  val codeOrdering: Ordering[Code] = new Ordering[Code]:
    def compare(first: Code, second: Code): Int =
      if first eq second then 0
      else
        val byKind = Integer.compare(kind(first), kind(second))
        if byKind != 0 then byKind
        else
          (first.layer, second.layer) match
            case (Slot(firstIndex), Slot(secondIndex)) =>
              Integer.compare(firstIndex, secondIndex)
            case (
                  Thunk(firstCode, firstHoles, firstFillings),
                  Thunk(secondCode, secondHoles, secondFillings)
                ) =>
              val byHoles = Ordering.Implicits
                .seqOrdering[Vector, Int]
                .compare(
                  firstHoles.map(holeNumber),
                  secondHoles.map(holeNumber)
                )
              if byHoles != 0 then byHoles
              else
                partsCompared(
                  firstCode +: firstFillings,
                  secondCode +: secondFillings
                )
            case _ => partsCompared(parts(first), parts(second))

    private def partsCompared(first: Vector[Code], second: Vector[Code]): Int =
      first
        .lazyZip(second)
        .map(compare)
        .find(_ != 0)
        .getOrElse(Integer.compare(first.size, second.size))

  private def kind(code: Code): Int = code.layer match
    case Slot(_)        => 0
    case Apply(_, _)    => 1
    case Parallel(_, _) => 2
    case Choice(_, _)   => 3
    case Thunk(_, _, _) => 4

  private def parts(code: Code): Vector[Code] = code.layer match
    case Slot(_)                   => Vector.empty
    case Apply(function, argument) => Vector(function, argument)
    case Parallel(left, right)     => Vector(left, right)
    case Choice(left, right)       => Vector(left, right)
    case Thunk(inner, _, fillings) => inner +: fillings

  private def holeNumber(hole: Hole): Int = hole match
    case Hole.Bound(slot) => slot
    case Hole.Ignored     => -1

/** The fixed point a saturation reached, independent of the numbers of the
  * nodes and of the order of the unions: the live classes and nodes, and a
  * digest of every live node written as its class's canonical number and its
  * canonical layer, in sorted order. Two graphs with the same form have the
  * same classes holding the same layers over the same classes.
  */
final case class FixedPointForm(classes: Int, liveNodes: Int, digest: String)

/** What the form of a graph reads, with the live nodes and the classes numbered
  * densely in the graph's order: each live node's layer over the indexes of its
  * children's classes, and the index of its class.
  */
final case class Projection[C <: NativeSpecializer & Singleton](
    layers: Vector[LayerWith[Int, Configured[C]]],
    classes: Vector[Int]
):
  def classCount: Int = if classes.isEmpty then 0 else classes.max + 1

object Projection:
  def of[C <: NativeSpecializer & Singleton](graph: EGraph[C]): Projection[C] =
    val liveNodes = graph.nodes.indices.filter(graph.live).toVector
    val roots = liveNodes.map(graph.root).distinct
    val classIndex = roots.zipWithIndex.toMap
    Projection(
      liveNodes.map(node =>
        graph.layer(node).map(child => classIndex(graph.root(child)))
      ),
      liveNodes.map(node => classIndex(graph.root(node)))
    )

/** The canonical numbering of a graph's classes. A class is numbered at the
  * height of its lowest term, by its representative: among its nodes whose
  * children are all classes numbered at lower heights, the least canonical
  * layer. The classes numbered at one height take the next numbers in the order
  * of their representatives. Congruence makes representatives of different
  * classes differ (one layer over the same classes is one node), so the
  * numbering depends on the graph's structure alone; a tie is a graph not
  * closed under congruence, and is refused.
  */
object FixedPoint:

  /** One line of tab-separated values of a file of fixed points: the
    * configuration, the item, how the run ended (`fixed_point` or
    * `budget_exhausted`), and the form's classes, live nodes and digest. Two
    * runs of different algorithms reach the same fixed points when their files
    * are equal.
    */
  def line(
      configuration: String,
      item: String,
      end: End,
      fixedPoint: FixedPointForm
  ): String =
    val endName = end match
      case End.FixedPoint(_)      => "fixed_point"
      case End.BudgetExhausted(_) => "budget_exhausted"
      case End.Stopped(instances) =>
        throw IllegalStateException(
          s"a run never asked to stop ended stopped after $instances instances"
        )
    Vector(
      configuration,
      item,
      endName,
      fixedPoint.classes.toString,
      fixedPoint.liveNodes.toString,
      fixedPoint.digest
    ).mkString("\t")

  /** The compiled run's saturation projected, and how it ended: the graph of
    * the pattern instructions, the inputs added, saturated within the budget.
    * The graph is let go before the caller computes the form (kept, the two
    * exceeded a heap of 256 MB on the largest fixture, 215,140 nodes, measured
    * 2026-10-30).
    */
  def saturatedProjection[C <: NativeSpecializer & Singleton](
      item: Compiled[C]
  ): (Projection[C], End) =
    val input = item.input
    given C = input.store.construction.specializer
    val initial = Saturation.initialGraph(
      input.store,
      item.headArityBounds,
      input.patternInstructions,
      explained = false
    )
    val (withInputs, _) = Saturation.inputsAdded(initial, input.inputs)
    val (graph, end) =
      Saturation.saturated(
        item.program,
        item.compiled,
        BuiltInRule.beforeOptIn,
        withInputs,
        input.budget,
        StopSignal.NeverStopped
      )
    (Projection.of(graph), end)

  /** The form of a graph's fixed point, its constants by their hash codes. */
  def form[C <: NativeSpecializer & Singleton](
      graph: EGraph[C]
  ): FixedPointForm = form(Projection.of(graph), ConstantNumbers.hashes[C])

  /** The form of a graph's fixed point, from its projection, its constants by
    * their hash codes.
    */
  def form[C <: NativeSpecializer & Singleton](
      projection: Projection[C]
  ): FixedPointForm = form(projection, ConstantNumbers.hashes[C])

  /** The form of a graph's fixed point, from its projection, its constants by
    * the numbers.
    */
  def form[C <: NativeSpecializer & Singleton](
      projection: Projection[C],
      constants: ConstantNumbers[C]
  ): FixedPointForm =
    val nodeCount = projection.layers.size
    val classCount = projection.classCount
    val childClasses = projection.layers.map(_.children.distinct)
    val users = childClasses.zipWithIndex
      .flatMap((children, node) => children.map(child => child -> node))
      .groupMap(_._1)(_._2)
    val usersByClass =
      Vector.tabulate(classCount)(index => users.getOrElse(index, Vector.empty))
    val initial = Numbering(
      numbers = Vector.fill(classCount)(-1),
      numbered = 0,
      unsettledChildren = childClasses.map(_.size)
    )
    val ready =
      (0 until nodeCount).filter(node => childClasses(node).isEmpty).toVector
    val numbering =
      numbered(initial, ready, projection, usersByClass, constants)
    require(
      numbering.numbered == classCount,
      s"${classCount - numbering.numbered} classes have no finite term"
    )
    val canonical = (0 until nodeCount)
      .map(node =>
        (
          numbering.numbers(projection.classes(node)),
          canonicalNode(projection.layers(node), numbering.numbers, constants)
        )
      )
      .toVector
      .sortWith((first, second) =>
        first._1 < second._1 || (first._1 == second._1 &&
          summon[Ordering[CanonicalNode]].lt(first._2, second._2))
      )
    FixedPointForm(classCount, nodeCount, digest(canonical))

  /** The number of each class (-1 while it has none), how many are numbered,
    * and for each live node the number of its distinct children's classes not
    * numbered yet.
    */
  private final case class Numbering(
      numbers: Vector[Int],
      numbered: Int,
      unsettledChildren: Vector[Int]
  )

  /** One height after another: the classes of the ready nodes not numbered yet
    * are numbered in the order of their representatives, and the nodes whose
    * last unnumbered child was among them are ready at the next.
    */
  @tailrec
  private def numbered[C <: NativeSpecializer & Singleton](
      numbering: Numbering,
      ready: Vector[Int],
      projection: Projection[C],
      usersByClass: Vector[Vector[Int]],
      constants: ConstantNumbers[C]
  ): Numbering =
    val candidates =
      ready.filter(node => numbering.numbers(projection.classes(node)) < 0)
    if candidates.isEmpty then numbering
    else
      val representatives = candidates
        .groupBy(projection.classes)
        .toVector
        .map((classIndex, nodes) =>
          classIndex -> nodes
            .map(node =>
              canonicalNode(
                projection.layers(node),
                numbering.numbers,
                constants
              )
            )
            .min
        )
        .sortBy(_._2)
      representatives
        .zip(representatives.drop(1))
        .find((first, second) => first._2 == second._2)
        .foreach((first, second) =>
          throw IllegalStateException(
            s"classes ${first._1} and ${second._1} have one representative ${first._2}: the graph is not closed under congruence"
          )
        )
      val numbers = representatives.zipWithIndex.foldLeft(numbering.numbers) {
        case (current, ((classIndex, _), offset)) =>
          current.updated(classIndex, numbering.numbered + offset)
      }
      val (unsettledChildren, nextReady) =
        representatives.foldLeft(
          (numbering.unsettledChildren, Vector.empty[Int])
        ) { case ((counts, readyNext), (classIndex, _)) =>
          usersByClass(classIndex).foldLeft((counts, readyNext)) {
            case ((innerCounts, innerReady), user) =>
              val left = innerCounts(user) - 1
              (
                innerCounts.updated(user, left),
                if left == 0 then innerReady :+ user else innerReady
              )
          }
        }
      numbered(
        Numbering(
          numbers,
          numbering.numbered + representatives.size,
          unsettledChildren
        ),
        nextReady,
        projection,
        usersByClass,
        constants
      )

  private def canonicalNode[C <: NativeSpecializer & Singleton](
      layer: LayerWith[Int, Configured[C]],
      numbers: Vector[Int],
      constants: ConstantNumbers[C]
  ): CanonicalNode =
    layer match
      case Apply(function, argument) =>
        CanonicalNode(
          0,
          Vector.empty,
          Vector(numbers(function), numbers(argument))
        )
      case Parallel(left, right) =>
        CanonicalNode(1, Vector.empty, Vector(numbers(left), numbers(right)))
      case Choice(left, right) =>
        CanonicalNode(2, Vector.empty, Vector(numbers(left), numbers(right)))
      case Thunk(code, holes, fillings) =>
        CanonicalNode(
          3,
          constants.code(code) +: holes.map {
            case Hole.Bound(slot) => slot
            case Hole.Ignored     => -1
          },
          fillings.map(numbers)
        )
      case NoinlineLeaf(instruction) =>
        CanonicalNode(
          4,
          Vector(constants.instruction(instruction)),
          Vector.empty
        )
      case view: com.yang_bo.gezi.ir.StorageView[?] =>
        throw IllegalStateException(
          s"a node's layer is never a storage's view: $view"
        )

  /** Two 32-bit hashes of the sorted canonical nodes under different seeds, as
    * sixteen hexadecimal digits.
    */
  private def digest(canonical: Vector[(Int, CanonicalNode)]): String =
    val elements = canonical.map((number, node) =>
      (number, node.kind, node.constants, node.children)
    )
    val first = MurmurHash3.orderedHash(elements, 0x2b5f1e3d)
    val second = MurmurHash3.orderedHash(elements, 0x6c8e9cf7)
    f"$first%08x$second%08x"
