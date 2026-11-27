package gezi.ir

import gezi.ir.Interned.Interned
import scala.collection.immutable.BitSet

/** An instruction: one interned term of the IR ([[Interned]]), the canonical
  * object of its layer ([[IrLayer]]). `Instruction(layer)` returns the one live
  * instruction whose layer equals the given one, so that two instructions are
  * one term exactly when they are one object; an instruction no longer
  * reachable is garbage-collected (`Canonicalization`, on the JVM and under
  * Scala.js alike).
  *
  * An opaque instruction, `Instruction.opaque(name)`, stands for a term whose
  * layer is not known, named by a string: the noinline instructions of an
  * exported fixture, which the exporter wrote without their layers, and those
  * of generated stores. The store expands it to a leaf, never to its layer.
  *
  * A URI node, `Instruction.uri(uri)`, is a term named by an absolute URI
  * whose meaning the front end gives by an equation, a δ rule: the node
  * equals its expansion, a closed term the front end reads from the content
  * the URI locates, a function of the URI alone; the URI is absolute, and
  * how it maps to a path of mixins is its scheme's. Only the front end's directory sugar makes one;
  * the surface syntax has none. The node is data, its URI only. It is opaque:
  * its layer is no part of the IR. The evaluator expands it through the front
  * end and remembers the expansion in its reading state
  * (`gezi.weakhead.ReadingState`); the e-graph keeps it a leaf
  * (`Store.expanded`).
  *
  * REVIEW: a URI is an identity only. Strategies, backends, lemmas and
  * readers never look at any part of a URI: no name decides anything, and
  * everything is a pure function of structure (`CONTRIBUTING.md`, "Structure
  * only: no names, and every function a pure function of the term"); what a
  * URI node is, is its expansion. Only the front end's expansion dispatches
  * on the scheme.
  */
type Instruction = Interned[IrLayer]

object Instruction:

  // TODO: deleted: `Instruction.apply`, the canonical instruction of any layer. Wrong because it builds a term from children of any configuration, the untyped public
  // construction every term after the front end could be made by; issue https://github.com/Atry/private-overlay/issues/2261,
  // design v38, section 1. Read it back with `git show 7669694cc:gezi/ir/src/main/scala/gezi/ir/Identifiers.scala`.

  /** The canonical opaque instruction of the name. */
  def opaque(name: String): Instruction = Interned[IrLayer](gezi.ir.Opaque(name))

  /** The canonical URI node of the URI. Throws `IllegalArgumentException`
    * for a relative URI: the front end supports absolute URIs only.
    */
  def uri(uri: java.net.URI): Instruction = Interned[IrLayer](UriNode(uri))

  /** The canonical application, and its parts; an opaque instruction is none. */
  object Apply:
    // TODO: deleted: `Instruction.Apply.apply`. Wrong because it builds a term from children of any configuration, the untyped public
    // construction every term after the front end could be made by; issue https://github.com/Atry/private-overlay/issues/2261,
    // design v38, section 1. Read it back with `git show 7669694cc:gezi/ir/src/main/scala/gezi/ir/Identifiers.scala`.

    def unapply(instruction: Instruction): Option[(Instruction, Instruction)] = instruction.layer match
      case gezi.ir.Apply(function, argument) => Some((function, argument))
      case _                                     => None

  /** The canonical parallel of two sides, and its sides; an opaque
    * instruction is none.
    */
  object Parallel:

    def unapply(instruction: Instruction): Option[(Instruction, Instruction)] = instruction.layer match
      case gezi.ir.Parallel(left, right) => Some((left, right))
      case _                                 => None

  /** The canonical binary choice, and its two sides; an opaque instruction
    * is none.
    */
  object Choice:
    // TODO: deleted: `Instruction.Choice.apply`. Wrong because it builds a term from children of any configuration, the untyped public
    // construction every term after the front end could be made by; issue https://github.com/Atry/private-overlay/issues/2261,
    // design v38, section 1. Read it back with `git show 7669694cc:gezi/ir/src/main/scala/gezi/ir/Identifiers.scala`.

    def unapply(instruction: Instruction): Option[(Instruction, Instruction)] = instruction.layer match
      case gezi.ir.Choice(left, right) => Some((left, right))
      case _                               => None


  /** The members of an instruction's right `+` spine ([[ChoiceSpine.members]]):
    * the instruction itself for one that is no choice, an opaque one
    * included. Matches every instruction.
    */
  object ChoiceMembers:
    def unapply(instruction: Instruction): Some[Vector[Instruction]] =
      Some(ChoiceSpine.members[Instruction](instruction, Choice.unapply))

  /** The canonical thunk of a code, the hole of each binder in lambda order
    * and the fillings of the code's other slots in slot order, and its parts;
    * an opaque instruction is none.
    */
  object Thunk:
    // TODO: deleted: `Instruction.Thunk.apply`, which also built thunks with no holes. Wrong because it builds a term from children of any configuration, the untyped public
    // construction every term after the front end could be made by; issue https://github.com/Atry/private-overlay/issues/2261,
    // design v38, section 1. Read it back with `git show 7669694cc:gezi/ir/src/main/scala/gezi/ir/Identifiers.scala`.

    def unapply(instruction: Instruction): Option[(Code, Vector[Hole], Vector[Instruction])] = instruction.layer match
      case gezi.ir.Thunk(code, holes, fillings) => Some((code, holes, fillings))
      case _                                        => None

/** A code: one interned body over slots ([[Interned]] over [[CodeLayer]]), the
  * canonical object of its layer, made and compared as an [[Instruction]] is.
  */
type Code = Interned[CodeLayer]

/** What a code reads, computed once per distinct code: the root constructor
  * of the code holds it (`codeFacts` of `Slot`, `Apply`, `Parallel`,
  * `Choice` and `Thunk`), as a code used to hold its own lazy fields before
  * every code was a shared constructor.
  *
  * Slots are small integers and every code's facts are the union of its
  * parts', so they are bit sets, whose union allocates a word per 64 slots.
  *
  * @param slotsRead
  *   the slots the code reads
  * @param slotsReadMoreThanOnce
  *   the slots the code may read more than once: those with two or more
  *   occurrences in the code written out as a tree, and those with an
  *   occurrence in the fillings of an inner thunk that has holes, a lambda
  *   that may be applied any number of times
  * @param slotsReadOutsideParallelRightOperands
  *   the slots the code reads at a position that is not the right operand of
  *   a parallel: its own slots, and the slots read so by those fillings of its
  *   inner thunks whose slot the inner code reads so; an inner thunk's code
  *   reads the inner thunk's slots, not these
  */
final case class CodeFacts(slotsRead: BitSet, slotsReadMoreThanOnce: BitSet, slotsReadOutsideParallelRightOperands: BitSet):

  /** The facts of a code that reads this code's slots and the other's, each
    * occurrence counted, the slots read outside right operands being `outside`.
    */
  private[ir] def joined(other: CodeFacts, outside: BitSet): CodeFacts =
    CodeFacts(
      slotsRead | other.slotsRead,
      slotsReadMoreThanOnce | other.slotsReadMoreThanOnce | (slotsRead & other.slotsRead),
      outside
    )

/** How a code hands its result to the continuation in one of its slots:
  * the slot occurs
  * in the code only in tail position, each time applied to `arity`
  * arguments that do not read it. A tail position is
  *   - the head of the code's spine, `Slot(s) M1 … Mn`;
  *   - both sides of a choice or a parallel, at one arity, by equations (8)
  *     and (9) of the formal definition, `(M + N) k = M k + N k` and
  *     `(M ∥ N) k = M k ∥ N k`;
  *   - a step `Apply(H, Thunk(inner, holes, fillings))` that does not read
  *     the slot in `H` and passes it on as one bare filling of the
  *     continuation thunk, in whose code the slot that filling fills is in
  *     tail position at the same arity.
  * `steps` says whether the plan passes through at least one step, that is,
  * whether there is work before the continuation is used that a reader may
  * share. The plan is syntax only: whether each step's function in turn
  * calls its continuation in tail position is known only when the step is
  * reduced, and the reader checks it there.
  */
final case class TailPlan(arity: Int, steps: Boolean)

object Code:

  /** The slots of the code that are in tail position only, each with its
    * plan ([[TailPlan]]), computed once per code.
    */
  def tailPlans(code: Code): Map[Int, TailPlan] = code.layer match
    case slot @ gezi.ir.Slot(_)              => slot.codeTailPlans
    case application @ gezi.ir.Apply(_, _)   => application.codeTailPlans
    case parallel @ gezi.ir.Parallel(_, _)   => parallel.codeTailPlans
    case choice @ gezi.ir.Choice(_, _)       => choice.codeTailPlans
    case thunk @ gezi.ir.Thunk(_, _, _)      => thunk.codeTailPlans

  /** The slot of the thunk's code that the filling of the index fills: the
    * code's slots no hole binds, in ascending order, as the evaluator places
    * the fillings.
    */
  def filledSlot(code: Code, holes: Vector[Hole], fillingCount: Int, fillingIndex: Int): Int =
    val bound = holes.collect { case Hole.Bound(slot) => slot }.toSet
    (0 until bound.size + fillingCount).filterNot(bound.contains)(fillingIndex)

  /** The index of the one filling of the continuation that passes the slot
    * on bare, when no other filling reads it: the step of a tail plan
    * (`TailPlan`).
    */
  def passedFilling(fillings: Vector[Code], slot: Int): Option[Int] =
    val bare = fillings.indices.filter(index => fillings(index).layer == gezi.ir.Slot(slot))
    val reading = fillings.indices.filter(index => facts(fillings(index)).slotsRead(slot))
    bare match
      case Seq(index) if reading == Seq(index) => Some(index)
      case _                                   => None

  /** The tail plans of the code computed over the codes it is made of, each
    * visited once with no recursion on the JVM stack, as `computedFacts`
    * does: a chain of continuations nested n deep is n codes deep.
    */
  private[ir] def computedTailPlans(root: Code): Map[Int, TailPlan] =
    def reads(code: Code, slot: Int): Boolean = facts(code).slotsRead(slot)
    @scala.annotation.tailrec
    def spine(current: Code, arguments: List[Code]): (Code, List[Code]) = current.layer match
      case gezi.ir.Apply(function, argument) => spine(function, argument :: arguments)
      case _                                 => (current, arguments)
    def parts(code: Code): List[Code] = code.layer match
      case gezi.ir.Apply(_, argument) =>
        argument.layer match
          case gezi.ir.Thunk(inner, holes, _) if holes.nonEmpty => List(inner)
          case _                                                 => Nil
      case gezi.ir.Parallel(left, right) => List(left, right)
      case gezi.ir.Choice(left, right)   => List(left, right)
      case _                             => Nil
    def both(left: Map[Int, TailPlan], right: Map[Int, TailPlan]): Map[Int, TailPlan] =
      left.flatMap((slot, leftPlan) =>
        right.get(slot).filter(_.arity == leftPlan.arity).map(rightPlan => slot -> TailPlan(leftPlan.arity, leftPlan.steps || rightPlan.steps))
      )
    def plansOf(code: Code, found: Map[Code, Map[Int, TailPlan]]): Map[Int, TailPlan] = code.layer match
      case gezi.ir.Slot(index) => Map(index -> TailPlan(0, steps = false))
      case gezi.ir.Apply(function, argument) =>
        val headed = spine(code, Nil) match
          case (head, arguments) =>
            head.layer match
              case gezi.ir.Slot(index) if !arguments.exists(reads(_, index)) => Map(index -> TailPlan(arguments.size, steps = false))
              case _                                                         => Map.empty[Int, TailPlan]
        val passed = argument.layer match
          case gezi.ir.Thunk(inner, holes, fillings) if holes.nonEmpty =>
            facts(argument).slotsRead.toVector.filterNot(reads(function, _)).flatMap(slot =>
              passedFilling(fillings, slot).flatMap(index =>
                found(inner).get(filledSlot(inner, holes, fillings.size, index)).map(plan => slot -> TailPlan(plan.arity, steps = true))
              )
            ).toMap
          case _ => Map.empty[Int, TailPlan]
        headed ++ passed
      case gezi.ir.Parallel(left, right) => both(found(left), found(right))
      case gezi.ir.Choice(left, right)   => both(found(left), found(right))
      case gezi.ir.Thunk(_, _, _)        => Map.empty
    @scala.annotation.tailrec
    def computed(pending: List[(Code, Boolean)], found: Map[Code, Map[Int, TailPlan]]): Map[Code, Map[Int, TailPlan]] =
      pending match
        case Nil                                       => found
        case (code, _) :: rest if found.contains(code) => computed(rest, found)
        case (code, false) :: rest                     => computed(parts(code).map((_, false)) ::: (code, true) :: rest, found)
        case (code, true) :: rest                      => computed(rest, found.updated(code, plansOf(code, found)))
    computed(List((root, false)), Map.empty)(root)

  /** Whether the code reads each filling of a thunk of the code and holes at
    * a position that is not the right operand of a parallel
    * (`CodeFacts.slotsReadOutsideParallelRightOperands`). The fillings fill
    * the slots that no hole binds, in ascending order.
    */
  def fillingsReadOutsideParallelRightOperands(code: Code, holes: Vector[Hole], fillingCount: Int): Vector[Boolean] =
    val bound = holes.collect { case Hole.Bound(slot) => slot }.toSet
    val slots = (0 until bound.size + fillingCount).filterNot(bound.contains).toVector
    val read = facts(code).slotsReadOutsideParallelRightOperands
    slots.map(read.contains)

  /** The number of fillings a well-formed thunk of the code and holes has:
    * the code's slots, 0 to the highest it reads, that no hole binds. None
    * when the holes bind a slot twice or a slot above the highest the code
    * reads, which no thunk of the code can do.
    */
  def fillingCount(code: Code, holes: Vector[Hole]): Option[Int] =
    val bound = holes.collect { case Hole.Bound(slot) => slot }
    val slotCount = facts(code).slotsRead.lastOption.fold(0)(_ + 1)
    Option.when(bound.distinct.size == bound.size && bound.forall(_ < slotCount))(slotCount - bound.size)

  /** The slots the code may read more than once
    * (`CodeFacts.slotsReadMoreThanOnce`), computed once per code.
    */
  def slotsReadMoreThanOnce(code: Code): Set[Int] = facts(code).slotsReadMoreThanOnce

  /** The facts of the code, held by its root constructor and computed once. */
  def facts(code: Code): CodeFacts = code.layer match
    case slot @ gezi.ir.Slot(_)              => slot.codeFacts
    case application @ gezi.ir.Apply(_, _)   => application.codeFacts
    case parallel @ gezi.ir.Parallel(_, _)   => parallel.codeFacts
    case choice @ gezi.ir.Choice(_, _)       => choice.codeFacts
    case thunk @ gezi.ir.Thunk(_, _, _)      => thunk.codeFacts

  /** The facts of the code computed over its subcodes, each visited once with
    * no recursion on the JVM stack (an inner thunk's code, another code, is
    * asked for its own held facts, which `apply` computed when it built the
    * thunk, so that asking them recurses no deeper: read lazily, a chain of
    * thunks nested n deep, which a text in the multi-line CPS layout makes,
    * computed its facts n frames deep and overflowed the stack on
    * `hidden_37_courses_large`). A slot's facts are the ones its interned
    * constructor holds, so a slot takes no entry of the walk.
    */
  private[ir] def computedFacts(root: Code): CodeFacts =
    def isSlot(code: Code): Boolean = code.layer match
      case gezi.ir.Slot(_) => true
      case _               => false
    def parts(code: Code): List[Code] = (code.layer match
      case gezi.ir.Slot(_)                   => Nil
      case gezi.ir.Apply(function, argument) => List(function, argument)
      case gezi.ir.Parallel(left, right)     => List(left, right)
      case gezi.ir.Choice(left, right)       => List(left, right)
      case gezi.ir.Thunk(_, _, fillings)     => fillings.toList
    ).filterNot(isSlot)
    def factsIn(code: Code, found: Map[Code, CodeFacts]): CodeFacts =
      if isSlot(code) then facts(code) else found(code)
    def factsOf(code: Code, found: Map[Code, CodeFacts]): CodeFacts = code.layer match
      case gezi.ir.Slot(index) =>
        val read = BitSet(index)
        CodeFacts(read, BitSet.empty, read)
      case gezi.ir.Apply(function, argument) =>
        val (functionFacts, argumentFacts) = (factsIn(function, found), factsIn(argument, found))
        functionFacts.joined(argumentFacts, functionFacts.slotsReadOutsideParallelRightOperands | argumentFacts.slotsReadOutsideParallelRightOperands)
      case gezi.ir.Parallel(left, right) =>
        val (leftFacts, rightFacts) = (factsIn(left, found), factsIn(right, found))
        leftFacts.joined(rightFacts, leftFacts.slotsReadOutsideParallelRightOperands)
      case gezi.ir.Choice(left, right) =>
        val (leftFacts, rightFacts) = (factsIn(left, found), factsIn(right, found))
        leftFacts.joined(rightFacts, leftFacts.slotsReadOutsideParallelRightOperands | rightFacts.slotsReadOutsideParallelRightOperands)
      case gezi.ir.Thunk(inner, holes, fillings) =>
        val fillingFacts = fillings.map(factsIn(_, found))
        val outside = fillingFacts
          .lazyZip(fillingsReadOutsideParallelRightOperands(inner, holes, fillings.size))
          .foldLeft(BitSet.empty) { case (read, (filling, readOutside)) =>
            if readOutside then read | filling.slotsReadOutsideParallelRightOperands else read
          }
        val counted = fillingFacts.foldLeft(CodeFacts(BitSet.empty, BitSet.empty, BitSet.empty))((total, filling) => total.joined(filling, outside))
        if holes.nonEmpty then counted.copy(slotsReadMoreThanOnce = counted.slotsRead) else counted
    @scala.annotation.tailrec
    def computed(pending: List[(Code, Boolean)], found: Map[Code, CodeFacts]): Map[Code, CodeFacts] =
      pending match
        case Nil                                       => found
        case (code, _) :: rest if found.contains(code) => computed(rest, found)
        case (code, false) :: rest                     => computed(parts(code).map((_, false)) ::: (code, true) :: rest, found)
        case (code, true) :: rest                      => computed(rest, found.updated(code, factsOf(code, found)))
    computed(List((root, false)), Map.empty)(root)

  /** The canonical code of the layer. The facts of a thunk's inner code are
    * computed here (`computedFacts`), before the thunk exists, so that a
    * chain of nested thunks has each level's facts computed from the one
    * below it, already known. Only an inner code is forced: the facts of
    * every other code stay computed when first asked, since forcing every
    * code as it is built merged the slots' counts at every node of a deep
    * code (measured 2026-11-19: frontend's DeepTermsTest and ten other suites
    * over their deadlines).
    */
  def apply(layer: CodeLayer[Code]): Code =
    layer match
      case gezi.ir.Thunk(inner, _, _) =>
        facts(inner) match
          case CodeFacts(_, _, _) => Interned[CodeLayer](layer)
      case _ => Interned[CodeLayer](layer)

  /** The canonical reference to the slot of the index, and its index. */
  object Slot:
    def apply(index: Int): Code = Code(gezi.ir.Slot(index))

    def unapply(code: Code): Option[Int] = code.layer match
      case gezi.ir.Slot(index) => Some(index)
      case _                        => None

  /** The canonical application, and its parts. */
  object Apply:
    def apply(function: Code, argument: Code): Code = Code(gezi.ir.Apply(function, argument))

    def unapply(code: Code): Option[(Code, Code)] = code.layer match
      case gezi.ir.Apply(function, argument) => Some((function, argument))
      case _                                     => None

  /** The canonical parallel of two sides, and its sides. */
  object Parallel:
    def apply(left: Code, right: Code): Code = Code(gezi.ir.Parallel(left, right))

    def unapply(code: Code): Option[(Code, Code)] = code.layer match
      case gezi.ir.Parallel(left, right) => Some((left, right))
      case _                                 => None

  /** The canonical binary choice, and its two sides. */
  object Choice:
    def apply(left: Code, right: Code): Code = Code(gezi.ir.Choice(left, right))

    def unapply(code: Code): Option[(Code, Code)] = code.layer match
      case gezi.ir.Choice(left, right) => Some((left, right))
      case _                               => None

    /** The members nested to the right ([[ChoiceSpine.nested]]): one is
      * itself; none throws.
      */
    def nested(members: Vector[Code]): Code =
      ChoiceSpine.nested[Code](members, Choice(_, _))

  /** The members of a code's right `+` spine ([[ChoiceSpine.members]]).
    * Matches every code.
    */
  object ChoiceMembers:
    def unapply(code: Code): Some[Vector[Code]] =
      Some(ChoiceSpine.members[Code](code, Choice.unapply))

  /** The canonical inner thunk that reads slots of the enclosing code: its
    * code, the hole of each binder, and its fillings, codes read with the
    * enclosing code's slots; and its parts.
    */
  object Thunk:
    def apply(code: Code, holes: Vector[Hole], fillings: Vector[Code]): Code =
      Code(gezi.ir.Thunk(code, holes, fillings))

    def unapply(code: Code): Option[(Code, Vector[Hole], Vector[Code])] =
      code.layer match
        case gezi.ir.Thunk(inner, holes, fillings) => Some((inner, holes, fillings))
        case _                                         => None

/** A lemma, named by the number the exporter gave it; the justification of a
  * union that an instance of one of its orientations made.
  */
opaque type LemmaIdentifier = Int

object LemmaIdentifier:
  def apply(number: Int): LemmaIdentifier =
    require(number >= 0, s"a lemma's number is not negative: $number")
    number

  extension (lemma: LemmaIdentifier) def number: Int = lemma
