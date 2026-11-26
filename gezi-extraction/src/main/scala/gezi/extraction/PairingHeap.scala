package gezi.extraction

/** A persistent pairing heap with the order of SWI-Prolog's `library(heaps)`,
  * which the Prolog baseline's extraction reads its pending productions off:
  * the least key first, and among equal keys the order that library's melds
  * give, since the greedy fixed point of an extraction depends on the order
  * in which it reads equal keys. A meld keeps the left tree's root only when
  * its key is strictly less; `taken` pairs the subtrees of the root left to
  * right and melds the pairs from the right, as `pairing/2` does, here
  * without recursion on the JVM's stack.
  */
final case class PairingHeap[Key, Value](root: Option[PairingHeap.Tree[Key, Value]], size: Int)(
    using ordering: Ordering[Key]
):

  /** The heap with the value added under the key (`add_to_heap/4`). */
  def added(key: Key, value: Value): PairingHeap[Key, Value] =
    val single = PairingHeap.Tree(value, key, List.empty[PairingHeap.Tree[Key, Value]])
    PairingHeap(Some(root.fold(single)(PairingHeap.melded(_, single))), size + 1)

  /** The least key, its value and the heap without it; nothing for the empty
    * heap (`get_from_heap/4`).
    */
  def taken: Option[(Key, Value, PairingHeap[Key, Value])] =
    root.map(tree => (tree.key, tree.value, PairingHeap(PairingHeap.paired(tree.subtrees), size - 1)))

/** The trees of a pairing heap and its melds. */
object PairingHeap:

  /** A tree: the value and the key at its root, and its subtrees, the most
    * recently melded first.
    */
  final case class Tree[Key, Value](value: Value, key: Key, subtrees: List[Tree[Key, Value]])

  /** The heap of no value. */
  def empty[Key, Value](using ordering: Ordering[Key]): PairingHeap[Key, Value] =
    PairingHeap[Key, Value](None, 0)

  /** The heap of the pairs added in order (`list_to_heap/2`). */
  def of[Key, Value](pairs: Vector[(Key, Value)])(using ordering: Ordering[Key]): PairingHeap[Key, Value] =
    pairs.foldLeft(empty[Key, Value]) { case (heap, (key, value)) => heap.added(key, value) }

  /** `meld/3`: the left tree's root stays the root only when its key is
    * strictly less than the right tree's.
    */
  private def melded[Key, Value](left: Tree[Key, Value], right: Tree[Key, Value])(using
      ordering: Ordering[Key]
  ): Tree[Key, Value] =
    if ordering.lt(left.key, right.key) then left.copy(subtrees = right :: left.subtrees)
    else right.copy(subtrees = left :: right.subtrees)

  /** `pairing/2`: the trees melded in pairs from the left, the pairs then
    * melded from the right, an odd last tree the rightmost.
    */
  private def paired[Key, Value](trees: List[Tree[Key, Value]])(using
      ordering: Ordering[Key]
  ): Option[Tree[Key, Value]] =
    pairsReversed(trees, Nil) match
      case Nil => None
      case last :: before =>
        Some(before.foldLeft(last)((melds, pair) => melded(pair, melds)))

  /** The trees melded in pairs from the left, the last pair first. */
  @scala.annotation.tailrec
  private def pairsReversed[Key, Value](
      trees: List[Tree[Key, Value]],
      pairs: List[Tree[Key, Value]]
  )(using ordering: Ordering[Key]): List[Tree[Key, Value]] = trees match
    case first :: second :: rest => pairsReversed(rest, melded(first, second) :: pairs)
    case List(single)            => single :: pairs
    case Nil                     => pairs
