package gezi.frontend

import scala.annotation.tailrec
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Instruction
import gezi.ir.Spine

/** Whether a program is a pure λ term: built of variables, abstractions and
  * applications only, with no choice, no parallel and no constant (a constant's body is not seen here, so it may
  * hide any of them). A program that writes top, the term that stands for no
  * answer, is not pure: top holds a parallel.
  *
  * The judge's points writer gives a point traps (candidates that are not
  * normal forms of its program) only when its program is pure (`pure`) and
  * the reference reading (contest-corpora's `Reduction.answeredNormalForms`)
  * reads exactly one normal form N0. The reading proves only that T ⊑_O N
  * for each normal form N it reads, never that nothing else is; for a pure
  * program T read to the one normal form N0, the reading applies the η rule
  * at abstraction, so T =βη N0, inside ⊢_{λ-lattice-unit-η}, and
  * NF◇(T) = {N0} by Böhm's separation of distinct βη normal forms: no other closed βη normal form N has T ⊑_O N. For a
  * program with a choice or a parallel no such proof
  * exists yet.
  *
  * A variable arguments partial function applied to the bits of its own
  * literal, `(λL. M) L`, is contracted before it is looked at: each bit, the
  * abstraction `λx. x K top` applied to `λt. λf. t` (or `λx. x top K` to
  * `λt. λf. f`), is K by three β steps, so the term is β-equal to one with M
  * in its place, and the two are ≃_O, with the same answers. Its misses,
  * the top of each bit, are then no part of the term looked at. A marker of
  * the library spelled as a tag,
  * `λx. (λ"$k". λv. v) "$k" x`, is such a redex, so a program that uses
  * the library stays pure (measured 2026-11-19: with the top of every marker
  * looked at, the trap law's points that write a trap fell to 16% of its
  * inputs, below the 20% it asks for).
  */
object ProgramPurity:

  /** Whether the term is pure. Walks a stack of subterms, so a deep program
    * does not overflow the JVM's stack.
    */
  def pure(term: DeBruijnTerm): Boolean =
    @tailrec
    def walked(pending: List[DeBruijnTerm]): Boolean = pending match
      case Nil                                            => true
      case DeBruijnTerm.Variable(_) :: rest               => walked(rest)
      case DeBruijnTerm.Lambda(body) :: rest              => walked(body :: rest)
      case (application @ DeBruijnTerm.Apply(function, argument)) :: rest =>
        literalContracted(application) match
          case Some(contracted) => walked(contracted :: rest)
          case None             => walked(function :: argument :: rest)
      case (DeBruijnTerm.Choice(_, _) | DeBruijnTerm.Parallel(_, _) | DeBruijnTerm.Constant(_) |
          DeBruijnTerm.Free(_)) :: _ =>
        false
      case other :: _ =>
        throw IllegalStateException(
          s"a de Bruijn term is a variable, an abstraction, an application, a constant, a free name, a choice or a parallel, not ${other.layer}"
        )
    walked(List(term))

  /** The application with its head contracted when the head is a variable
    * arguments partial function applied to the bits of its literal, one bit
    * at a time as long as the argument is the bit the abstraction expects,
    * the body after those bits reading none of their binders; none when no
    * bit is contracted.
    */
  private def literalContracted(application: DeBruijnTerm): Option[DeBruijnTerm] =
    @tailrec
    def peeled(function: DeBruijnTerm, arguments: List[DeBruijnTerm], count: Int): (DeBruijnTerm, List[DeBruijnTerm], Int) =
      (function, arguments) match
        case (DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), matched), missed)), argument :: later)
            if missed == Literals.top && argument == Literals.one =>
          peeled(matched, later, count + 1)
        case (DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), missed), matched)), argument :: later)
            if missed == Literals.top && argument == Literals.zero =>
          peeled(matched, later, count + 1)
        case _ => (function, arguments, count)
    val (head, arguments) = Spine.of(application)
    val (under, later, count) = peeled(head, arguments.toList, 0)
    Option.when(count > 0 && !DeBruijnTerm.readsBelow(under, count))(
      later.foldLeft(DeBruijnTerm.shiftedDown(under, count))(DeBruijnTerm.Apply(_, _))
    )

  /** `pure` of the instruction's readback (`Defunctionalization.instructionTerm`), decided on the IR at the size of its
    * graph: the readback writes a closed instruction out at every occurrence, a tree that can be exponentially larger
    * than the graph, while here each closed instruction is walked once, alone, which is the same walk wherever it
    * occurs: its redexes lie inside it. A variable arguments partial function applied to the bits of its literal is
    * contracted as `pure` contracts it, one bit at a time, where the abstraction `λx. x K top` (or `λx. x top K`), a
    * thunk of one hole whose branches do not read it, is the head of an application spine whose next argument is the
    * bit it expects. A thunk's fillings and an inner thunk's codes are walked where their slots are read, as the
    * readback puts them there; a code is walked at each such read, the codes the front end writes being trees.
    *
    * Purpose: the judge's trap writer decides purity for every program of a points file;
    * the readback took about 16% of TrapJudgmentsLawTest's samples
    * (JFR, 2026-11-19).
    */
  def pureInstruction(instruction: Instruction): Boolean =
    @tailrec
    def walked(pending: List[Value], visited: Set[Instruction]): Boolean = pending match
      case Nil => true
      case value :: rest =>
        resolved(value) match
          case Value.Bound                                         => walked(rest, visited)
          case Value.Closed(closed) if visited.contains(closed)    => walked(rest, visited)
          case current =>
            val seen = current match
              case Value.Closed(closed) => visited + closed
              case _                    => visited
            spine(current) match
              case (head, arguments @ (_ :: _)) =>
                selected(head, arguments) match
                  case Some(contracted) => walked(contracted :: rest, seen)
                  case None             => walked(head :: arguments ::: rest, seen)
              // A contracted head applied to no argument: the head, looked at as any other value.
              case (head, Nil) if head ne current => walked(head :: rest, seen)
              case (head, Nil) =>
                opened(head) match
                  case Some((code, _, slots)) => walked(Value.Open(code, slots) :: rest, seen)
                  case None                   => false
    walked(List(Value.Closed(instruction)), Set.empty)

  /** A term the IR walk looks at: a variable bound by a thunk's hole, a closed instruction, a code read with the
    * values of its slots, or a term applied to arguments.
    */
  private enum Value:
    case Bound
    case Closed(instruction: Instruction)
    case Open(code: Code, slots: Vector[Value])
    case Applied(function: Value, arguments: List[Value])

  /** The value with its slot reads followed to what they read. */
  @tailrec
  private def resolved(value: Value): Value = value match
    case Value.Open(Code.Slot(index), slots) =>
      if index >= 0 && index < slots.size then resolved(slots(index))
      else throw IllegalStateException(s"a code reads slot $index of a thunk of ${slots.size} slots")
    case other => other

  /** The head of the value's application spine and its arguments, in order. */
  private def spine(value: Value): (Value, List[Value]) =
    @tailrec
    def collected(current: Value, arguments: List[Value]): (Value, List[Value]) = resolved(current) match
      case Value.Closed(Instruction.Apply(function, argument)) => collected(Value.Closed(function), Value.Closed(argument) :: arguments)
      case Value.Open(Code.Apply(function, argument), slots)   => collected(Value.Open(function, slots), Value.Open(argument, slots) :: arguments)
      case Value.Applied(function, applied)                    => collected(function, applied ::: arguments)
      case head                                                => (head, arguments)
    collected(value, Nil)

  /** The body of a thunk with the values of its slots, its holes bound; none for any other value. */
  private def opened(value: Value): Option[(Code, Vector[Hole], Vector[Value])] = resolved(value) match
    case Value.Closed(Instruction.Thunk(code, holes, fillings)) =>
      Some((code, holes, Defunctionalization.slotValues(holes, holes.map(_ => Value.Bound), fillings.map(Value.Closed(_)))))
    case Value.Open(Code.Thunk(inner, holes, fillings), slots) =>
      Some((inner, holes, Defunctionalization.slotValues(holes, holes.map(_ => Value.Bound), fillings.map(Value.Open(_, slots)))))
    case _ => None

  /** The spine with its head contracted where the head is the abstraction of a bit applied to that bit: the branch
    * the bit selects, applied to the arguments after it; none when the first argument is no such bit.
    */
  private def selected(head: Value, arguments: List[Value]): Option[Value] =
    arguments match
      case argument :: later =>
        opened(head).flatMap {
          case (Code.Apply(Code.Apply(Code.Slot(read), first), second), Vector(Hole.Bound(bound)), slots)
              if read == bound && !Code.facts(first).occurrences.contains(bound) && !Code.facts(second).occurrences.contains(bound) =>
            if missing(Value.Open(second, slots)) && isBit(argument, oneInstruction) then Some(Value.Applied(Value.Open(first, slots), later))
            else if missing(Value.Open(first, slots)) && isBit(argument, zeroInstruction) then
              Some(Value.Applied(Value.Open(second, slots), later))
            else None
          case _ => None
        }
      case Nil => None

  private val topInstruction: Instruction = Defunctionalization.thunkInstruction(Literals.top)

  private val oneInstruction: Instruction = Defunctionalization.thunkInstruction(Literals.one)

  private val zeroInstruction: Instruction = Defunctionalization.thunkInstruction(Literals.zero)

  /** Whether the value is top, the miss of a bit. */
  private def missing(value: Value): Boolean = resolved(value) match
    case Value.Closed(instruction) => instruction == topInstruction
    case _                         => false

  /** Whether the value is the bit, as a closed instruction or as an inner thunk of the same code. */
  private def isBit(value: Value, bit: Instruction): Boolean = (resolved(value), bit) match
    case (Value.Closed(instruction), _) => instruction == bit
    case (Value.Open(Code.Thunk(inner, holes, Vector()), _), Instruction.Thunk(code, bitHoles, Vector())) =>
      inner == code && holes == bitHoles
    case _ => false
