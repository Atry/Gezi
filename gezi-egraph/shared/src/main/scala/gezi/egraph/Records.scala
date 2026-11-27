package gezi.egraph

import gezi.ir.Layer
import gezi.ir.LayerWith
import gezi.ir.LemmaIdentifier
import gezi.ir.{Configured, NativeSpecializer}
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Thunk}

/** A closure state of a class: a thunk node with the arguments given to it so
  * far, in reverse lambda order, and the number of its holes left. A class
  * holding one is the function of applications that fill the next hole; a state
  * with no hole left is the thunk's code read with its slots filled.
  */
final case class ClosureState(
    thunk: Int,
    argumentsReversed: List[Int],
    left: Int
):
  /** The state after one more argument. */
  def applied(argument: Int): ClosureState =
    ClosureState(thunk, argument :: argumentsReversed, left - 1)

  /** The arguments given so far and the last one, in lambda order. */
  def argumentsWith(last: Int): Vector[Int] =
    (last :: argumentsReversed).reverse.toVector

/** Why two classes were united: an instance of an orientation of a lemma, with
  * the roots its metavariables were bound to (`None` for a metavariable no side
  * mentions); congruence, a user read again over the roots found with another
  * node's signature; the β rule, an application united with its body, one step,
  * the application first, with the thunk node of the closure state the step
  * took, so that the body's places can be walked back to the thunk's code (for
  * source locations only; nothing else reads it, and it changes no node, union
  * or order); β conversion, two terms equal by the β rule in more than one step
  * or through another spelling of a closure (the root case of the reverse β,
  * whose redex contracts to the term with its closures captured otherwise, and
  * the expansions and normalizations of `HigherOrderMatching`), with the node
  * of the two that the other reduces to, so that an article can state the
  * reduction in its direction (it changes no node, union or order, as `Beta`'s
  * thunk does not); or the abstraction rule, ξ, a closure united with the thunk
  * written back from its body opened at fresh eigenvariables and rewritten, the
  * eigenvariables' classes holding nothing else, with the eigenvariables' leaf
  * nodes in lambda order, the node of the body opened and the node of the
  * body's spelling that was abstracted, so that a trace can open the closure,
  * replay the body's unions from the body to the spelling and write it back
  * (like `Beta`'s thunk, the fields change no node, union or order).
  */
enum Justification:
  case Lemma(lemma: LemmaIdentifier, bindings: Vector[Option[Int]])
  case Congruence
  case Beta(thunk: Int)
  case BetaConversion(reduct: Int)
  case Abstraction(eigenvariables: Vector[Int], body: Int, spelling: Int)

  /** The pattern view of a native storage the graph keeps as a leaf united with
    * the leaf, `s ∥ T = s`: by the storage's definition s = v ∥ T, then (4),
    * `(v ∥ T) ∥ T = v ∥ (T ∥ T)`, and the idempotence of ∥, which (6) and (5)
    * give, `T ∥ T = T ∥ (T + (T ∥ T)) = T`.
    */
  case PatternView(leaf: Int)

  /** A native storage the graph keeps as a leaf united with the node of its
    * view, `s = v ∥ T`: the storage is the term its view spells, so the union
    * is the definition of the storage, the expansion direction of the built-in
    * rule "the storage's view" (`gezi.ir.BuiltInRule.StorageView`).
    */
  case StorageView(leaf: Int)

  /** An application united with the storage of the result of the native named
    * on the storages the classes `arguments` hold as leaves, its function's
    * class (the node `define`) holding a define bound to that native: the
    * application equals `define a1 … an` by the forest, its function and
    * arguments read in their classes, and that equals the result by the
    * native's obligation `native = define`, trusted as its binding states on
    * unfiltered values, with the unique spelling's pattern theorem at each
    * storage (`docs/design/gezi-set-equations-proofs.md`, section 23, under the
    * premise the fold requires).
    */
  case Folding(native: String, define: Int, arguments: Vector[Int])

  /** The η rule: the node `thunk`, a thunk of one hole whose code applies its
    * one filling to the hole (`λx. M x`, x not free in M), united with the node
    * of that filling, M.
    */
  case Eta(thunk: Int)

  /** A closure unit's compilation (`gezi.narrowblocks.ClosureUnits`): the unit
    * `function` united with the artifact its compilation gave, an equation that
    * compilation's own graph derives (its eigenvariables' openings, the
    * abstraction rule and the η rule); `function` is the unit's node.
    */
  case Compiled(function: Int)

/** A node that is not a duplicate, the root of its class and its layer over the
  * roots of its children's classes, as read at one time.
  */
final case class LiveNode[C <: NativeSpecializer & Singleton](
    node: Int,
    root: Int,
    layer: LayerWith[Int, Configured[C]]
)

/** The counts of a run: the nodes made, the unions that joined two classes, the
  * instances that changed the graph and the matches found.
  */
final case class Statistics(
    nodes: Int,
    unions: Int,
    instances: Int,
    matches: Int
)

/** The nodes one step of the graph made, from `first` to `last`: the nodes of a
  * lemma instance's added side, of a β step's body or residual, or of a body
  * written back, made one after another, children before the layers over them,
  * so that `last` is the root of what the step built.
  */
final case class MadeNodes(first: Int, last: Int)

/** A union that joined two classes, the two nodes as the union was asked, and
  * `made`: the nodes the union's own lemma instance, β step or written-back
  * body made, the last of them one of the two, or none, for a union whose two
  * nodes were both in the graph before it (a congruence, a merge, an instance
  * whose built side was already a node, an input's node). A log entry, as
  * `Justification.Beta`'s thunk is: nothing chooses by it, and emptying it
  * changes no answer. A trace reads it to tell a step that walks a union from
  * the node an instance matched to the node it built from one that walks it
  * back, and to find the step that made a node whose term a step backward
  * needs, and puts no type information in the host. Its memory is two Ints per
  * union that made nodes, and nothing per node: a node's maker is the union
  * whose range holds it.
  */
final case class UnionRecord(
    first: Int,
    second: Int,
    justification: Justification,
    made: Option[MadeNodes]
):

  /** The one of the two nodes the union's step made, the root of `made`. */
  def built: Option[Int] = made.map(_.last)

/** A union waiting in the agenda, with the nodes its step made, as
  * `UnionRecord` records them.
  */
final case class PendingUnion(
    first: Int,
    second: Int,
    justification: Justification,
    made: Option[MadeNodes]
)

/** A β step waiting in the agenda: the application fills the next hole of the
  * closure state.
  */
final case class PendingBeta(application: Int, state: ClosureState)

/** What tells two instances of an orientation apart: the matched root, the
  * roots of the essential metavariables (`None` when unbound) and the classes
  * of the shared subterms.
  */
final case class InstanceKey(
    orientation: Int,
    root: Int,
    values: Vector[Option[Int]],
    classes: Vector[Int]
)

/** One node: its layer over the nodes that were the roots of its children's
  * classes when it was made (its signature then, which matching and congruence
  * read); its parent in the union-find, itself while it is a root; its heads in
  * filing order; the first instruction filed onto it; whether it is a duplicate
  * and whether the β rule reads it; and `made`, its layer over the nodes its
  * maker passed, before any `root`. In a graph that records the terms made
  * (`EGraph.explained`), each node denotes exactly one term made, the term of
  * its `made` layer over its children's terms (explanation mode, after M.
  * Flatt, S. Coward, M. Willsey, Z. Tatlock and P. Panchekha, "Small Proofs
  * from Congruence Closure", FMCAD 2022: an id per distinct term made, a
  * hash-consing hit recorded as a congruence union); in one that does not,
  * `made` is the layer over roots itself.
  */
final case class NodeRecord[C <: NativeSpecializer & Singleton](
    layer: LayerWith[Int, Configured[C]],
    parent: Int,
    heads: Vector[Head[C]],
    instruction: Option[Configured[C]],
    duplicate: Boolean,
    readable: Boolean,
    made: LayerWith[Int, Configured[C]]
)

/** The entries of one collection of a class, every one ever filed in filing
  * order, the duplicates among them included until the collection is written
  * again without them, and the number of entries that became duplicates since
  * it was last written so.
  */
final case class Entries[Entry](items: Vector[Entry], dead: Int):
  def added(entry: Entry): Entries[Entry] = Entries(items :+ entry, dead)

  /** One more of the entries is a duplicate; once at least half of them are,
    * they are written again without the duplicates, so that reading them costs
    * at most twice the live ones. The entries a reader is given are a snapshot,
    * so writing them again changes no reading.
    */
  def oneDead(live: Entry => Boolean): Entries[Entry] =
    val deadCount = dead + 1
    if deadCount * 2 >= items.size then Entries(items.filter(live), 0)
    else Entries(items, deadCount)

object Entries:
  def empty[Entry]: Entries[Entry] = Entries(Vector.empty, 0)

/** The data of a class, kept in its root: its number of nodes; its members of
  * each shape; its applications by head; its heads in the order gained; its
  * users of each role; and its closure states, none until the class holds one,
  * a state dead when its thunk is a duplicate.
  */
final case class ClassData[C <: NativeSpecializer & Singleton](
    size: Int,
    applyMembers: Entries[Int],
    parallelMembers: Entries[Int],
    choiceMembers: Entries[Int],
    thunkMembers: Entries[Int],
    leafMembers: Entries[Int],
    headMembers: Map[Head[C], Entries[Int]],
    heads: Vector[Head[C]],
    functionUsers: Entries[Int],
    argumentUsers: Entries[Int],
    leftUsers: Entries[Int],
    rightUsers: Entries[Int],
    memberUsers: Entries[PositionUser],
    fillingUsers: Entries[PositionUser],
    closures: Option[Entries[ClosureState]]
):
  def members(shape: MemberShape): Entries[Int] = shape match
    case MemberShape.Apply    => applyMembers
    case MemberShape.Parallel => parallelMembers
    case MemberShape.Choice   => choiceMembers
    case MemberShape.Thunk    => thunkMembers
    case MemberShape.Leaf     => leafMembers

  def membersReplaced(shape: MemberShape, entries: Entries[Int]): ClassData[C] =
    shape match
      case MemberShape.Apply    => copy(applyMembers = entries)
      case MemberShape.Parallel => copy(parallelMembers = entries)
      case MemberShape.Choice   => copy(choiceMembers = entries)
      case MemberShape.Thunk    => copy(thunkMembers = entries)
      case MemberShape.Leaf     => copy(leafMembers = entries)

  def users(role: UserRole): Entries[Int] = role match
    case UserRole.Function => functionUsers
    case UserRole.Argument => argumentUsers
    case UserRole.Left     => leftUsers
    case UserRole.Right    => rightUsers

  def usersReplaced(role: UserRole, entries: Entries[Int]): ClassData[C] =
    role match
      case UserRole.Function => copy(functionUsers = entries)
      case UserRole.Argument => copy(argumentUsers = entries)
      case UserRole.Left     => copy(leftUsers = entries)
      case UserRole.Right    => copy(rightUsers = entries)

  def positionUsers(role: PositionRole): Entries[PositionUser] = role match
    case PositionRole.Member  => memberUsers
    case PositionRole.Filling => fillingUsers

  def positionUsersReplaced(
      role: PositionRole,
      entries: Entries[PositionUser]
  ): ClassData[C] = role match
    case PositionRole.Member  => copy(memberUsers = entries)
    case PositionRole.Filling => copy(fillingUsers = entries)

  def headEntries(head: Head[C]): Entries[Int] =
    headMembers.getOrElse(head, Entries.empty)

object ClassData:
  /** The data of a class of one node, before the node is filed in it. */
  def single[C <: NativeSpecializer & Singleton]: ClassData[C] = ClassData[C](
    size = 1,
    applyMembers = Entries.empty,
    parallelMembers = Entries.empty,
    choiceMembers = Entries.empty,
    thunkMembers = Entries.empty,
    leafMembers = Entries.empty,
    headMembers = Map.empty,
    heads = Vector.empty,
    functionUsers = Entries.empty,
    argumentUsers = Entries.empty,
    leftUsers = Entries.empty,
    rightUsers = Entries.empty,
    memberUsers = Entries.empty,
    fillingUsers = Entries.empty,
    closures = None
  )

  /** The data of a class that lost a union, let go: no reader reads the class
    * data of a node that is not a root.
    */
  def released[C <: NativeSpecializer & Singleton]: ClassData[C] =
    single[C].copy(size = 0)

/** The shape a node's layer is filed under. */
def shapeOf(layer: Layer[Any]): MemberShape = layer match
  case view: gezi.ir.StorageView[?] =>
    throw IllegalStateException(
      s"a node's layer is never a storage's view: $view"
    )
  case Apply(_, _)     => MemberShape.Apply
  case Parallel(_, _)  => MemberShape.Parallel
  case Choice(_, _)    => MemberShape.Choice
  case Thunk(_, _, _)  => MemberShape.Thunk
  case NoinlineLeaf(_) => MemberShape.Leaf
