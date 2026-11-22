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
type IrLayer[+Child] = Apply[Child] | Parallel[Child] | Choice[Child] | Thunk[Child] | UriNode | Opaque

/** One layer as the e-graph reads it, over children of type `Child`: an
  * application, a parallel, a binary choice, a thunk, or a noinline leaf, an
  * instruction whose term the e-graph never unfolds ([[Store.expanded]]).
  */
type Layer[+Child] = Apply[Child] | Parallel[Child] | Choice[Child] | Thunk[Child] | NoinlineLeaf[Instruction]

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

/** The IR as the e-graph reads it: the noinline instructions, which it never
  * expands. Every other instruction carries its layer, and every code
  * its code.
  */
final case class Store(noinline: Set[Instruction]):
  /** The layer the e-graph makes for the instruction: a leaf when it is noinline,
    * its layer otherwise. A URI node is always a leaf: its layer is no part
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
  def expanded(instruction: Instruction): Layer[Instruction] =
    if noinline.contains(instruction) then NoinlineLeaf(instruction)
    else
      instruction.layer match
        case UriNode(_)                 => NoinlineLeaf(instruction)
        case Opaque(_)                  => throw IllegalStateException(s"the $instruction has no layer")
        case application @ Apply(_, _)  => application
        case parallel @ Parallel(_, _)  => parallel
        case choice @ Choice(_, _)      => choice
        case thunk @ Thunk(_, _, _)     => thunk

  def code(identifier: Code): CodeLayer[Code] = identifier.layer

/** The codes a computation over some terms may meet. */
object Reachability:

  /** Every code under the roots and the given codes: the code of each thunk
    * of a layer under a root (noinline instructions included, opaque ones having
    * no layer), and each code's subcodes, inner codes and fillings.
    */
  def codesUnder(roots: Iterable[Instruction], codes: Iterable[Code]): Set[Code] =
    val instructions = instructionsUnder(roots)
    val thunkCodes = instructions.toVector.flatMap(instruction =>
      instruction.layer match
        case Thunk(code, _, _) => Vector(code)
        case _                       => Vector.empty
    )
    closed((thunkCodes ++ codes).toList, Set.empty)

  /** Every instruction under the roots, the roots included, opaque ones having no
    * layer and so nothing under them, and left out.
    */
  def instructionsUnder(roots: Iterable[Instruction]): Set[Instruction] = instructionsClosed(roots.toList, Set.empty)

  @scala.annotation.tailrec
  private def instructionsClosed(pending: List[Instruction], seen: Set[Instruction]): Set[Instruction] = pending match
    case Nil => seen
    case instruction :: rest =>
      if seen.contains(instruction) || instruction.opaque then instructionsClosed(rest, seen)
      else instructionsClosed(instruction.layer.children.toList ++ rest, seen + instruction)

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
