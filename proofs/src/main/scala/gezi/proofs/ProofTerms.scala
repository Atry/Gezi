package gezi.proofs

import scala.annotation.tailrec

import gezi.ir.Apply
import gezi.ir.Choice
import gezi.ir.Layer
import gezi.ir.LayerWith
import gezi.ir.NativeStorage
import gezi.ir.NoinlineLeaf
import gezi.ir.NotTerm
import gezi.ir.Opaque
import gezi.ir.Parallel
import gezi.ir.StorageAccess
import gezi.ir.StorageView
import gezi.ir.Thunk
import gezi.ir.UriNode
import gezi.ir.{Configured, NativeSpecializer}

/** A term an article writes, by its place among the terms of the article's `ProofTerms`: two terms of one article
  * are one term exactly when their places are one.
  */
final case class TermId(index: Int)

object TermId:
  /** A term of an article is no IR term: a layer over terms of an article is a layer of the article's. */
  given NotTerm[TermId] = NotTerm.granted

/** One term of an article, one layer down: an opaque term (an eigenvariable, a URI node), a leaf with no layer; a
  * native storage, a leaf of the IR that the article writes as its view `v ∥ T`, with the terms of the view's two
  * sides; or one layer of the IR (an application, a parallel, a choice or a thunk) over terms of the article.
  */
enum TermKey[+Term]:
  case Leaf(term: Term)
  case Stored(storage: Term, value: TermId, criterion: TermId)
  case Layered(layer: Layer[TermId])

/** The terms of one article, each once, in the order they were met: the term of each node of a proof
  * (`StrategyProof.layers`), read from its layer as it was made, and the term of each instruction the article reads
  * beside the nodes (a lemma's side, a constant of a lemma's pattern), read layer by layer. No IR term is built: a
  * term is its key, one layer over the places of the terms under it, so that two terms are one exactly when their
  * keys are one, as two instructions interned with no conversion were one (a node made as a storage's view `v ∥ T`
  * is the parallel over the view's two nodes, another term than the storage, which is a leaf). A storage is read
  * through its view, and each side of the view in turn, as a formatter of the term would: the article writes it so.
  *
  * @param keys
  *   each term's key, by its place
  * @param places
  *   each key's term
  * @param walked
  *   the term of each instruction read beside the nodes, and under them
  * @param nodeTerms
  *   each node's term, by the node's number
  * @param firstNodes
  *   each term of a node to the first node whose term it is
  */
final class ProofTerms[C <: NativeSpecializer & Singleton] private (
    keys: Vector[TermKey[Configured[C]]],
    places: Map[TermKey[Configured[C]], TermId],
    walked: Map[Configured[C], TermId],
    nodeTerms: Vector[TermId],
    firstNodes: Map[TermId, Int]
):

  /** The number of the article's terms: their places are 0 to one less. */
  def size: Int = keys.size

  /** The number of the proof's nodes. */
  def nodeCount: Int = nodeTerms.size

  /** The term of the node. */
  def nodeTerm(node: Int): TermId = nodeTerms(node)

  /** The first node whose term the term is; none for a term that is no node's (a term under a noinline leaf, a
    * lemma's constant the search never added).
    */
  def node(term: TermId): Option[Int] = firstNodes.get(term)

  /** The term's key. */
  def key(term: TermId): TermKey[Configured[C]] = keys(term.index)

  /** The term of an instruction the article reads (`ProofTerms.of`'s references, and every instruction under them
    * or under a node's leaf). Throws `IllegalArgumentException` for one it was not given.
    */
  def of(instruction: Configured[C]): TermId =
    walked.getOrElse(instruction, throw IllegalArgumentException(s"the article was not given the term $instruction"))

  /** Whether the term is opaque, a leaf with no layer. */
  def isLeaf(term: TermId): Boolean = key(term) match
    case TermKey.Leaf(_) => true
    case _               => false

  /** The term's one layer over terms of the article: a storage's its view `v ∥ T`. Throws `IllegalStateException`
    * for an opaque term, a URI node included, whose layer is no part of the IR.
    *
    * FIXME: a URI node is opaque, so any proof whose terms hold one has no article: the writer throws here, and the https://github.com/Atry/private-overlay/issues/1978
    * evaluation phase writes none for such a proof (`OpentheoryArticle.uriFree`, whose FIXME has the candidate).
    */
  def layer(term: TermId): Layer[TermId] = key(term) match
    case TermKey.Layered(layer)                 => layer
    case TermKey.Stored(_, value, criterion)    => StorageView(value, criterion)
    case TermKey.Leaf(leaf)                     => throw IllegalStateException(s"the $leaf has no layer")

  /** The term of the layer over terms of the article, when the article has it. */
  def existing(layer: Layer[TermId]): Option[TermId] = places.get(TermKey.Layered(layer))

  /** The name of the term variable that writes an opaque term that is no URI node, the opaque term's own name; none
    * for any other term. In an article such a term, which has no layer, can only be a variable.
    */
  def opaqueName(term: TermId)(using C): Option[String] = key(term) match
    case TermKey.Leaf(leaf) =>
      leaf.layer match
        case Opaque(name) => Some(name)
        case _            => None
    case _ => None

  /** Whether some term of the article is a URI node. */
  def holdsUri(using C): Boolean = keys.exists {
    case TermKey.Leaf(leaf) => leaf.uri.isDefined
    case _                  => false
  }

  /** Whether the term is a URI node or has one under it. */
  def holdsUriUnder(term: TermId)(using C): Boolean =
    @tailrec
    def searched(pending: List[TermId], visited: Set[TermId]): Boolean = pending match
      case Nil                                    => false
      case next :: rest if visited.contains(next) => searched(rest, visited)
      case next :: rest =>
        key(next) match
          case TermKey.Leaf(leaf)                   => leaf.uri.isDefined || searched(rest, visited + next)
          case TermKey.Stored(_, value, criterion)  => searched(value :: criterion :: rest, visited + next)
          case TermKey.Layered(layer)               => searched(layer.children.toList ++ rest, visited + next)
    searched(List(term), Set.empty)

object ProofTerms:

  /** The terms of the nodes of the layers, each a node's layer as it was made over nodes made before it, and of the
    * references, read with the capability to read a storage's view; with none, a storage met throws
    * `IllegalStateException`.
    */
  def of[C <: NativeSpecializer & Singleton](
      layers: Vector[LayerWith[Int, Configured[C]]],
      references: Iterable[Configured[C]],
      access: Option[StorageAccess]
  )(using C): ProofTerms[C] =
    val afterReferences = references.foldLeft(Building.empty[C])((building, reference) => walkedAll(List(Visit.Enter(reference)), building, access))
    val (building, nodeTerms) = layers.foldLeft((afterReferences, Vector.empty[TermId])) { case ((current, made), layer) =>
      layer match
        case NoinlineLeaf(instruction) =>
          val after = walkedAll(List(Visit.Enter(instruction)), current, access)
          (after, made :+ after.walked(instruction))
        // The node of a storage's view `v ∥ T` is that parallel over the view's two nodes, kept apart from the
        // storage's leaf.
        case StorageView(value, criterion) =>
          val (after, term) = current.placed(TermKey.Layered(Parallel(made(value), made(criterion))))
          (after, made :+ term)
        case other =>
          val (after, term) = current.placed(TermKey.Layered(other.map(made)))
          (after, made :+ term)
    }
    val firstNodes = nodeTerms.zipWithIndex.foldLeft(Map.empty[TermId, Int]) { case (found, (term, node)) =>
      if found.contains(term) then found else found.updated(term, node)
    }
    ProofTerms(building.keys, building.places, building.walked, nodeTerms, firstNodes)

  /** The terms placed so far. */
  private final case class Building[C <: NativeSpecializer & Singleton](
      keys: Vector[TermKey[Configured[C]]],
      places: Map[TermKey[Configured[C]], TermId],
      walked: Map[Configured[C], TermId]
  ):

    /** The term of the key, placed after the others if it has none. */
    def placed(key: TermKey[Configured[C]]): (Building[C], TermId) =
      places.get(key) match
        case Some(term) => (this, term)
        case None =>
          val term = TermId(keys.size)
          (copy(keys = keys :+ key, places = places.updated(key, term)), term)

  private object Building:
    def empty[C <: NativeSpecializer & Singleton]: Building[C] = Building(Vector.empty, Map.empty, Map.empty)

  /** A step of the walk of an instruction: entering it, or placing it once the terms under it are placed. */
  private enum Visit[C <: NativeSpecializer & Singleton]:
    case Enter(instruction: Configured[C])
    case Stored(storage: Configured[C], view: StorageView[Configured[C]])
    case Layered(instruction: Configured[C], layer: Layer[Configured[C]])

  /** The walk of the instructions pending, each placed after the terms under it: a loop over a stack of visits, since
    * an instruction may be as deep as a program.
    */
  @tailrec
  private def walkedAll[C <: NativeSpecializer & Singleton](
      pending: List[Visit[C]],
      building: Building[C],
      access: Option[StorageAccess]
  )(using specializer: C): Building[C] = pending match
    case Nil => building
    case Visit.Enter(instruction) :: rest =>
      if building.walked.contains(instruction) then walkedAll(rest, building, access)
      else
        instruction.layer match
          case storage: NativeStorage =>
            val view = (specializer: C).viewOf(storage)(using
              access.getOrElse(throw IllegalStateException(s"a storage in a term written with no capability to read it: $storage"))
            )
            walkedAll(Visit.Enter(view.value) :: Visit.Enter(view.criterion) :: Visit.Stored(instruction, view) :: rest, building, access)
          case UriNode(_) | Opaque(_) =>
            val (after, term) = building.placed(TermKey.Leaf(instruction))
            walkedAll(rest, after.copy(walked = after.walked.updated(instruction, term)), access)
          case application @ Apply(_, _) =>
            val layer: Layer[Configured[C]] = application
            walkedAll(
              layer.children.toList.map(child => Visit.Enter(child)) ::: Visit.Layered(instruction, layer) :: rest,
              building,
              access
            )
          case parallel @ Parallel(_, _) =>
            val layer: Layer[Configured[C]] = parallel
            walkedAll(
              layer.children.toList.map(child => Visit.Enter(child)) ::: Visit.Layered(instruction, layer) :: rest,
              building,
              access
            )
          case choice @ Choice(_, _) =>
            val layer: Layer[Configured[C]] = choice
            walkedAll(
              layer.children.toList.map(child => Visit.Enter(child)) ::: Visit.Layered(instruction, layer) :: rest,
              building,
              access
            )
          case thunk @ Thunk(_, _, _) =>
            val layer: Layer[Configured[C]] = thunk
            walkedAll(
              layer.children.toList.map(child => Visit.Enter(child)) ::: Visit.Layered(instruction, layer) :: rest,
              building,
              access
            )
    case Visit.Stored(storage, view) :: rest =>
      val (after, term) = building.placed(TermKey.Stored(storage, building.walked(view.value), building.walked(view.criterion)))
      walkedAll(rest, after.copy(walked = after.walked.updated(storage, term)), access)
    case Visit.Layered(instruction, layer) :: rest =>
      if building.walked.contains(instruction) then walkedAll(rest, building, access)
      else
        val (after, term) = building.placed(TermKey.Layered(layer.map(building.walked)))
        walkedAll(rest, after.copy(walked = after.walked.updated(instruction, term)), access)
