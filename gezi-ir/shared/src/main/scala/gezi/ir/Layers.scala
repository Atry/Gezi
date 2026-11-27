package gezi.ir

/** The binder of one lambda of a thunk's chain: the slot it fills, or
  * nothing when the lambda ignores its argument.
  */
enum Hole:
  case Bound(slot: Int)
  case Ignored

  /** The same in every process: a singleton case's default hash code is its
    * identity's, which a constructor's hash code ([[ConstructorIdentity]])
    * must not read.
    */
  override def hashCode: Int = this match
    case Bound(slot) => slot + 1
    case Ignored     => 0

/** One layer of the IR over children of type `Child`: an application, a
  * parallel, a binary choice, a thunk (a lambda chain: its code, the hole of
  * each binder in lambda order, and the fillings of the code's other slots
  * in slot order), a URI node or an opaque term, the last two with no layer
  * of the IR under them. An [[Instruction]] is an interned term of these.
  *
  * The choice is binary, not a list: a binary choice is isomorphic to a
  * list, so no algorithm's complexity changes. A
  * chain of several members is right-nested, `a + (b + c)`, as a list's cells
  * nest ([[ChoiceSpine]]); a choice of one member is that member. Since the
  * choice is binary, there is no empty choice.
  */
// A native storage is a leaf of its term's layer: `layer` gives the storage itself, never its view, which only
// `StorageAccess` reads.
type IrLayer[+Child] = Apply[Child] | Parallel[Child] | Choice[Child] | Thunk[Child] | UriNode | Opaque | NativeStorage

/** One layer as the e-graph reads it, over children of type `Child`: an
  * application, a parallel, a binary choice, a thunk, or a noinline leaf, an
  * instruction whose term the e-graph never unfolds ([[Store.expanded]]).
  */
// A storage that is no leaf of the e-graph enters through its one-layer view, a `StorageView`, never a `Parallel` node
// over terms, which only a `NativeSpecializer` makes; the
// e-graph builds its node over classes from the view.
type LayerWith[+Child, +Leaf] =
  Apply[Child] | Parallel[Child] | Choice[Child] | Thunk[Child] | NoinlineLeaf[Leaf] | StorageView[Child]

/** A layer whose leaf's type does not matter to its reader (a pattern's, a code's, the dispatch's generic reads). */
type Layer[+Child] = LayerWith[Child, Any]

/** A code: one layer of a body over slots, its children other codes. An
  * inner thunk names its own code, and its fillings are codes read with the
  * enclosing code's slots. The choice is binary, as in [[IrLayer]].
  */
type CodeLayer[+Child] = Slot | Apply[Child] | Parallel[Child] | Choice[Child] | Thunk[Child]

/** A right-nested chain of binary choices read as its members, and members
  * nested into such a chain, over any representation of terms: a term that
  * is no choice is its only member, and `left + right` has `left` followed
  * by the members of `right`. A left member that is itself a choice stays one
  * member. The chain is isomorphic to a non-empty list, the choice's left
  * the head and its right the tail: `members(nested(found)) == found` for
  * every list `found` of one or more members whose last is no binary choice.
  * There is no empty choice, so a spine has at least one member.
  *
  * FIXME (2026-11-18, narrowed 2026-11-19): the two nestings of a chain are https://github.com/Atry/private-overlay/issues/1976
  * one term by equation (2), `(M + N) + P = M + (N + P)`, but the e-graph has
  * no lemma of associativity and matches by shape, so they saturate
  * differently. Measured by FixedWidthTypingLawTest under HEDGEHOG_SEED
  * 209486980499993 (int16_add on two 13-bit words): with the right sides of
  * hindley_milner_unions' decomposition lemmas read left-nested the run ends
  * at 791 unions with no clash and 1 β union; read right-nested, at 4,924
  * unions with the clash and 237 β unions. The front end nests every written
  * chain to the right, but a chain in parentheses after a `+` is a left
  * side of its own, so the text `a + (b + c)` is the left-nested
  * `(c + b) + a` and saturates as the other nesting does. Candidate fixes: a
  * lemma of associativity among the built-in rules (its cost: every chain's
  * nestings join one class), or one normal nesting of chains before
  * matching, in the orientations' patterns and in the inputs alike.
  */
object ChoiceSpine:

  /** The members of the right spine of the term, in order. */
  def members[Term](term: Term, choice: Term => Option[(Term, Term)]): Vector[Term] =
    @scala.annotation.tailrec
    def collected(current: Term, found: Vector[Term]): Vector[Term] =
      choice(current) match
        case Some((left, right)) => collected(right, found :+ left)
        case None                => found :+ current
    collected(term, Vector.empty)

  /** The members nested to the right: one is itself, several are
    * `m1 + (m2 + (... + mn))`. No member throws `IllegalArgumentException`:
    * the choice is binary and has no nullary case.
    */
  def nested[Term](members: Vector[Term], choice: (Term, Term) => Term): Term =
    members match
      case Vector()       => throw IllegalArgumentException("a choice of no member: the choice is binary, there is no empty choice")
      case Vector(single) => single
      case _              => members.init.foldRight(members.last)(choice)

/** A chain of parallels read as the set of its sides, for every kind of
  * term that has a parallel layer.
  */
object ParallelChain:

  /** The sides of a chain of parallels, left to right; the term itself when
    * it is no parallel.
    */
  def sides[Term](term: Term, parallel: Term => Option[(Term, Term)]): Vector[Term] =
    @scala.annotation.tailrec
    def from(pending: List[Term], found: Vector[Term]): Vector[Term] = pending match
      case Nil => found
      case current :: others =>
        parallel(current) match
          case Some((left, right)) => from(left :: right :: others, found)
          case None                => from(others, found :+ current)
    from(List(term), Vector.empty)

  /** The parallel of two terms as the chain of the distinct sides of both,
    * in the order first met, nested to the right: equal to their parallel by
    * the λ-lattice laws (∥ associative, commutative and idempotent), and no
    * longer than the number of distinct sides, so that a filter met again at
    * each call of a recursion over its value, `(t ∥ T) ∥ T`, stays `t ∥ T`.
    */
  def met[Term](first: Term, second: Term, parallel: Term => Option[(Term, Term)], make: (Term, Term) => Term): Term =
    if first == second then first
    else
      val distinct = (sides(first, parallel) ++ sides(second, parallel)).distinct
      distinct.init.foldRight(distinct.last)(make)

/** The IR as the e-graph reads it: the noinline instructions, which it never
  * expands. Every other instruction carries its layer, and every code
  * its code. And how the e-graph's write-back and the extraction's spelling
  * build the terms they intern (`construction`, through its configuration's native specializer), and with which capability
  * the graph reads a storage's view (the construction's).
  */
final case class Store[C <: NativeSpecializer & Singleton](noinline: Set[Configured[C]], construction: TermConstruction[C]):

  /** The capability the graph reads a storage's view with, its construction's. */
  def storageAccess: StorageAccess = construction.storageAccess

  /** The layer the e-graph makes for the instruction: a leaf when it is noinline
    * or a native storage kept as a leaf (`NativeStorage.leafInEGraph`), whose
    * view is not read; its layer otherwise, a storage that is no leaf giving its
    * one-layer view (a `StorageView`, read with the store's `StorageAccess`). A URI node is always a leaf: its layer is no part
    * of the IR, and the e-graph, which knows the IR only, does not read
    * files. Its δ equation, the node equal to its expansion, is the host's to
    * add as an instance, as a lemma's is, from the front end's expansion,
    * which is a function of the URI alone.
    *
    * FIXME (2026-11-12): no host driver adds the δ equation of a URI node https://github.com/Atry/private-overlay/issues/1977
    * yet, so a URI node in a term the e-graph reads stays a leaf of a class
    * of its own, and two files of one content at different URIs are not
    * related there. Under the corpora's convention (imports at a file's top)
    * no knowledge term holds a URI node, so nothing reads one today. The
    * driver must add the equation on demand, not for every URI node it
    * meets: the expansion of a captured directory holds its entries' URI
    * nodes, and expanding them in turn walks the file system from `file:///`.
    */
  def expanded(instruction: Configured[C]): LayerWith[Configured[C], Configured[C]] =
    if noinline.contains(instruction) || storedLeaf(instruction) then NoinlineLeaf(instruction)
    else
      instruction.layer match
        case UriNode(_)                 => NoinlineLeaf(instruction)
        case Opaque(_)                  => throw IllegalStateException(s"the $instruction has no layer")
        case application @ Apply(_, _)  => application
        case parallel @ Parallel(_, _)  => parallel
        case choice @ Choice(_, _)      => choice
        case thunk @ Thunk(_, _, _)     => thunk
        // A storage that is no leaf of the e-graph enters through its one-layer view, read by the graph's configuration.
        case storage: NativeStorage     => construction.specializer.viewOf(storage)(using storageAccess)

  def code(identifier: Code): CodeLayer[Code] = identifier.layer

  /** Whether the instruction is a native storage the e-graph keeps as a
    * leaf (`NativeStorage.leafInEGraph`): one class test, which reads no
    * layer, so the storage's view is never made.
    */
  private def storedLeaf(instruction: Configured[C]): Boolean = instruction.layer match
    case storage: NativeStorage => storage.leafInEGraph
    case _                      => false

/** The codes a computation over some terms may meet. */
object Reachability:

  /** Every code under the roots and the given codes: the code of each thunk
    * of a layer under a root (noinline instructions included, opaque ones having
    * no layer), and each code's subcodes, inner codes and fillings.
    */
  def codesUnder[C <: NativeSpecializer & Singleton](roots: Iterable[Configured[C]], codes: Iterable[Code])(using C): Set[Code] =
    val terms = instructionsUnder(roots)
    // A native storage's layer is the storage itself, never a thunk: its view is not read.
    val thunkCodes = terms.toVector.flatMap(term =>
      term.layer match
        case Thunk(code, _, _) => Vector(code)
        case _                 => Vector.empty
    )
    closed((thunkCodes ++ codes).toList, Set.empty)

  /** Every code under the given codes: each code's subcodes, inner codes and fillings. */
  def codesUnder(codes: Iterable[Code]): Set[Code] = closed(codes.toList, Set.empty)

  /** Every term under the roots, the roots included, opaque ones having no
    * layer and so nothing under them, and left out; under a native storage the
    * e-graph keeps as a leaf, only its criterion, which its pattern view adds.
    */
  def instructionsUnder[C <: NativeSpecializer & Singleton](roots: Iterable[Configured[C]])(using C): Set[Configured[C]] =
    instructionsClosed(roots.toList, Set.empty)

  @scala.annotation.tailrec
  private def instructionsClosed[C <: NativeSpecializer & Singleton](
      pending: List[Configured[C]],
      seen: Set[Configured[C]]
  )(using C): Set[Configured[C]] = pending match
    case Nil => seen
    case term :: rest =>
      if seen.contains(term) || term.opaque then instructionsClosed(rest, seen)
      else
        leafCriterion(term) match
          case Some(criterion) => instructionsClosed(criterion :: rest, seen + term)
          case None            => instructionsClosed(term.layer.children.toList ++ rest, seen + term)

  /** The criterion of a native storage the e-graph keeps as a leaf: the one
    * term under it the graph reads, through the leaf's pattern view, in the
    * term's configuration (`NativeSpecializer.criterionOf`); none for any other
    * term. A class test, the storage's view not read.
    */
  private def leafCriterion[C <: NativeSpecializer & Singleton](term: Configured[C])(using specializer: C): Option[Configured[C]] =
    term.layer match
      case storage: NativeStorage if storage.leafInEGraph => Some(specializer.criterionOf(storage))
      case _                                              => None

  @scala.annotation.tailrec
  private def closed(pending: List[Code], seen: Set[Code]): Set[Code] =
    pending match
      case Nil => seen
      case identifier :: rest =>
        if seen.contains(identifier) then closed(rest, seen)
        else closed(subcodes(identifier.layer).toList ++ rest, seen + identifier)

  /** The identifiers a code is over. */
  def subcodes(code: CodeLayer[Code]): Vector[Code] = code match
    case Slot(_)                   => Vector.empty
    case Apply(function, argument) => Vector(function, argument)
    case Parallel(left, right)     => Vector(left, right)
    case Choice(left, right)       => Vector(left, right)
    case Thunk(inner, _, fillings) => inner +: fillings
