package gezi.weakhead

import gezi.ir.Code
import gezi.ir.ConstructorIdentity
import gezi.ir.Instruction
import gezi.ir.Interned
import gezi.ir.Interned.Interned
import gezi.ir.Hole
import scala.annotation.tailrec
import gezi.weakhead.Trampoline
import gezi.weakhead.Trampoline.done
import gezi.weakhead.Trampoline.tailcall

/** The variable of the binder a normal-form reading opened at the depth, the
  * Prolog reader's `bound(Depth)`: the number of binders opened above it.
  *
  * A neutral value, a free variable (`CONTRIBUTING.md`, "Types live only in the term"), kept as an exception argued here
  * (a neutral value is not used by default; a use needs a reason it cannot
  * do without):
  * Böhm's reading of a normal form under a lambda reads the lambda's body,
  * an open term, and an open body has no reading without something standing
  * for its variable. A closed argument in its place would let the body
  * inspect it, so the read form would be the body's at that argument, not
  * the body's. The variable is the read term's own binder, opened and closed
  * again: every normal form the reader returns abstracts it back into a hole
  * and is closed, and no text names it.
  */
final case class BoundVariable(level: Int) extends NeutralVariable

/** One layer of an open normal form: an application, a thunk, or the
  * variable of an opened binder, a neutral value of no argument whose
  * variable is a `BoundVariable` (the constructions of `OpenNormalForm` make
  * no other).
  */
type NormalFormLayer[+Child] = gezi.ir.Apply[Child] | gezi.ir.Thunk[Child] | Neutral[Child]

/** An open normal form (normal_forms.pl, AN OPEN NORMAL FORM): what a reading
  * under some opened binders builds, an instruction of the thunk IR whose
  * free variables are leaves, an interned term and so a value as it is. Two
  * open normal forms read at one depth stand for α-equivalent terms exactly
  * when they are one object, since a variable is named by the absolute depth
  * of its binder and a thunk is canonical.
  */
type OpenNormalForm = Interned[NormalFormLayer]

/** The constructions and the parts of open normal forms, each made through
  * the pool.
  */
object OpenNormalForm:

  private def of(layer: NormalFormLayer[OpenNormalForm]): OpenNormalForm = Interned[NormalFormLayer](layer)

  /** The variable of the binder opened at the level, the Prolog reader's
    * `neutral(bound(Level), [])`.
    */
  object Leaf:
    def apply(level: Int): OpenNormalForm = of(Neutral(BoundVariable(level), Vector.empty))

    def unapply(form: OpenNormalForm): Option[Int] = form.layer match
      case Neutral(BoundVariable(level), arguments) if arguments.isEmpty => Some(level)
      case _                                                             => None

  /** A leaf or an application applied to an open normal form. */
  object Apply:
    def apply(function: OpenNormalForm, argument: OpenNormalForm): OpenNormalForm =
      of(gezi.ir.Apply(function, argument))

    def unapply(form: OpenNormalForm): Option[(OpenNormalForm, OpenNormalForm)] = form.layer match
      case gezi.ir.Apply(function, argument) => Some((function, argument))
      case _                                     => None

  /** An abstraction in the canonical form, each filling a closed open normal
    * form (a canonical thunk) or a leaf.
    */
  object Thunk:
    def apply(code: Code, holes: Vector[Hole], fillings: Vector[OpenNormalForm]): OpenNormalForm =
      of(gezi.ir.Thunk(code, holes, fillings))

    def unapply(form: OpenNormalForm): Option[(Code, Vector[Hole], Vector[OpenNormalForm])] = form.layer match
      case gezi.ir.Thunk(code, holes, fillings) => Some((code, holes, fillings))
      case _                                        => None

/** How a normal-form reading reads a parallel set of several heads. */
enum ReadOut:

  /** Each normal form every head reads, each head read whole
    * (normal_forms.pl, THE PARALLEL'S READ-OUT).
    */
  case Whole

  /** Each normal form of the first head, in order, that every other head
    * reads too, decided for each by descending into the head and the normal
    * form together (`headReads`), not by enumerating the head's reads
    * (THE READ-OUT BY MEMBERSHIP), under every mode: it decides membership
    * by reading the head down the target's shape, never by enumerating the
    * head's normal forms, so a table that completes a head's reading does
    * not stop it.
    */
  case Membership

/** The βη normal forms of a closed term, read on the weak-head evaluator: the
  * port of `gezi/prolog/gezi/normal_forms.pl`, whose
  * module comment the definitions here follow; each normal form an
  * instruction of the thunk IR in the canonical form of
  * `Defunctionalization.thunkInstruction` (D1 of `lean/README.md`, "Design decisions").
  *
  * THE READING is Böhm's (Barendregt, chapter 10), on `WeakHead`, building
  * the normal form on the IR as it reads. The parallel sets of the term are
  * taken, and each is read by its heads: a lambda is applied to a fresh
  * neutral value of `BoundVariable(depth)`, its body read one binder deeper,
  * and the fresh variable abstracted into a hole; a neutral value of a bound
  * variable reads as the application of its leaf to its arguments, each read
  * at the same depth; a parallel set of several heads is read out
  * (`ReadOut`).
  *
  * THE ABSTRACTION of the variable of level Depth over an open normal form
  * Body read one binder deeper gives what `thunkInstruction` gives for the
  * abstraction of the term Body stands for: Function when Body is Function
  * applied to the leaf of Depth and Function holds no leaf of Depth (the η
  * rule); when Body is a thunk, the chain one binder longer, the leaf of
  * Depth among its fillings its first hole, ignored when absent, every slot
  * keeping its number; otherwise a chain of one binder, whose slots are
  * Body's leaves, its closed thunks and the fillings of its inner thunks
  * that are not closed, numbered by first occurrence in preorder, equal
  * closed thunks sharing a slot.
  *
  * AN ANSWER N OF Term SATISFIES Term ⊑_O N: the reader answers
  * N for T only when T ⊑ N, which holds up to ⊑_O as every derivation of ⊢
  * does, by the derivations of the Prolog
  * module comment: a parallel set P of T has T ⊑ P (`WeakHead`); a lambda H
  * with H x ⊑ B has H ⊑ λx. B by the congruence under λ and the η rule; a
  * spine by (10) and (8); a parallel L ∥ R ⊑ N when L ⊑ N and R ⊑ N, by the
  * λ-lattice laws (1) and (3) to (6). A head with no read gives no answer: a
  * false negative, which a sound approximation allows.
  *
  * A normal form reads as many times as its reading finds it; `normalForms`
  * keeps each once. A term whose Böhm tree is infinite is read as long as
  * its reading goes; the budget bounds it.
  */
object NormalForms:

  /** The distinct normal forms read of the closed term under the mode, in
    * the order first read, with the whole read-out. A normal form read again
    * is dropped as it is read: a term whose reading finds one normal form
    * many times, such as a list of R choices whose members are equal, which
    * the reading takes 2^R times, holds that one normal form, not 2^R
    * copies of it.
    */
  def normalForms(mode: Mode, term: Value): Computation[ReadingState, Vector[Instruction]] =
    normalForm(mode, ReadOut.Whole, term).distinctCollected

  /** The normal forms read of the closed term under the mode, one at a time
    * (normal_form/4). Throws `EvaluationError` with `OpenNormalForm` should a
    * normal form read at depth 0 not be a closed thunk.
    */
  def normalForm(mode: Mode, readOut: ReadOut, term: Value): Answers[ReadingState, Instruction] =
    termRead(mode, readOut, 0, term).map(read =>
      if closed(read) then closedInstruction(read).result
      else throw EvaluationError(EvaluationErrorReason.OpenNormalForm)
    )

  private def termRead(
      mode: Mode,
      readOut: ReadOut,
      depth: Int,
      term: Value
  ): Answers[ReadingState, OpenNormalForm] =
    WeakHead.heads(mode, term).flatMap(setRead(mode, readOut, depth, _))

  /** The reads of a parallel set: of its head when it has one; the reads
    * every one of its heads reads when it has several (`ReadOut`), since
    * H1 ⊑ N and H2 ⊑ N give H1 ∥ H2 ⊑ N.
    *
    * The first head is read first, and when its reading has finished with no
    * read, the set has none and the other heads are not read. A reading the
    * limit stops is no finished ∅: the stop ends the whole reading.
    * FIXME (known incompleteness): the rule is asymmetric. A set whose head https://github.com/Atry/private-overlay/issues/2037
    * with no read is a later one still reads the heads before it to the end,
    * and does not finish when one of them does not; candidates: interleave
    * the heads' reads, or read the cheaper head first by a measure.
    *
    * A set that holds a closed head beside a head that is the variable of an
    * opened binder, applied to arguments or to none, reads ∅ with no head
    * read (`closedBesideOpenedVariable`): every read of the closed head is a
    * closed open normal form, and every read of the other holds that
    * variable's leaf, so the two reads have no member in common, which is
    * what both read-outs would give had both readings finished. The rule
    * answers nothing the reads of the heads would not: it only spares reading
    * them, and with it top = Y (λz. λx. z ∥ x), whose body is top ∥ x under its
    * opened binder, reads ∅ under the plain evaluator too, as `top` stands
    * where the empty choice stood.
    *
    * FIXME (known incompleteness, 2026-11-11): the empty parallel set, which https://github.com/Atry/private-overlay/issues/1946
    * only an evaluation that knows a least term answers
    * (`KnownExtremes`), reads nothing here. Every normal form is an answer
    * of a least term, and this reader, which gives its answers one at a
    * time, has no way to give them all; a caller that asks whether one
    * normal form is an answer can be answered yes, as `Reading`'s witness
    * reading is.
    */
  private def setRead(
      mode: Mode,
      readOut: ReadOut,
      depth: Int,
      set: ParallelSet
  ): Answers[ReadingState, OpenNormalForm] =
    set.heads match
      case Vector()       => Answers.empty
      case Vector(single) => headRead(mode, readOut, depth, single)
      case heads @ (first +: others) =>
        Answers
          .computed(Computation.pure(Vector(closedBesideOpenedVariable(depth, heads))))
          .flatMap(disjoint =>
            if disjoint then Answers.empty
            else
              readOut match
                case ReadOut.Whole =>
                  Answers.computed(
                    headRead(mode, readOut, depth, first).distinctCollected.flatMap(firstReads =>
                      Computation.folded(others, firstReads)((reads, head) =>
                        if reads.isEmpty then Computation.pure(reads)
                        else
                          headRead(mode, readOut, depth, head).distinctCollected.map(headReads =>
                            val readSet = headReads.toSet
                            reads.filter(readSet.contains)
                          )
                      )
                    )
                  )
                case ReadOut.Membership =>
                  others.foldLeft(headRead(mode, readOut, depth, first))((reads, head) =>
                    reads.filtered(read => headReads(mode, depth, head, openValue(read)))
                  )
          )
      case heads =>
        throw IllegalStateException(s"a vector of heads that is not empty has a first head, but ${heads.size} heads matched none")

  // ---- whether a head reads a given normal form ----

  /** Whether the closed term has one parallel set of one head, and that head
    * reads the normal form `target` (`headReads`): the term is the target up
    * to ≃_O, not only a term with the target among its normal forms, whose
    * other parallel sets or heads would be more. The heads are read by the
    * mode; the target's binders are opened as `headReads` opens them, by the
    * fresh variables of `BoundVariable`, the reader's own.
    */
  def soleHeadReads(mode: Mode, term: Value, target: Value): Computation[ReadingState, Boolean] =
    WeakHead.heads(mode, term).collected.flatMap {
      case Vector(set) =>
        set.heads match
          case Vector(head) => headReads(mode, 0, head, target)
          case _            => Computation.pure(false)
      case _ => Computation.pure(false)
    }

  /** Whether the head reads the normal form `target`, a value whose one
    * head is that normal form's: the head and the target are read together,
    * down the target's shape. Where either is a lambda, both are applied to
    * the fresh variable of the depth (the η rule, so that an η-reduced target
    * meets its expansion); where both are variables applied to arguments, the
    * variables and the numbers of arguments are compared, then each pair of
    * arguments in order. The test answers false at the first difference, so
    * it finishes wherever the head and the target differ at a finite depth,
    * where enumerating the head's reads and comparing each to the target
    * finishes only when the head has finitely many: `zero ∥ nat_type`'s
    * parallel set {zero, successor N} reads zero's normal form against
    * successor N, which differs at its head variable, two binders down,
    * while successor N has a read for every natural.
    *
    * It answers true only where some read of the head is the target, and
    * false where the enumeration would find none: two βη normal forms are
    * equal as canonical thunks exactly when they agree under this descent,
    * and the head's reads are taken set by set, every head of a set reading
    * the target, as `setRead` reads them. A set that `setRead` reads as ∅
    * (no head, or a closed head beside an opened variable) reads no target
    * here either.
    */
  private def headReads(mode: Mode, depth: Int, head: Head, target: Value): Computation[ReadingState, Boolean] =
    normalFormHead(mode, target).flatMap(targetHead => headsAgree(mode, depth, head, targetHead))

  /** Whether some parallel set of the value has every head reading the
    * target's head.
    */
  private def valueReads(mode: Mode, depth: Int, value: Value, target: Value): Computation[ReadingState, Boolean] =
    normalFormHead(mode, target).flatMap(targetHead =>
      WeakHead.heads(mode, value).exists(set =>
        if set.heads.isEmpty then Computation.pure(false)
        else
          Computation.state[ReadingState].flatMap(_ =>
            if set.heads.size > 1 && closedBesideOpenedVariable(depth, set.heads) then Computation.pure(false)
            else
              Computation.folded(set.heads, true)((agreed, head) =>
                if !agreed then Computation.pure(false) else headsAgree(mode, depth, head, targetHead)
              )
          )
      )
    )

  /** The one head of a normal form read as a value. Throws
    * `IllegalStateException` when the value has another number of parallel
    * sets or heads, which no normal form has.
    */
  private def normalFormHead(mode: Mode, target: Value): Computation[ReadingState, Head] =
    WeakHead.heads(mode, target).collected.map {
      case Vector(set) =>
        set.heads match
          case Vector(head) => head
          case heads        => throw IllegalStateException(s"a normal form read as a value has a parallel set of ${heads.size} heads")
      case sets => throw IllegalStateException(s"a normal form read as a value has ${sets.size} parallel sets")
    }

  private def headsAgree(mode: Mode, depth: Int, head: Head, targetHead: Head): Computation[ReadingState, Boolean] =
    (head, targetHead) match
      case (Head.Lambda(_, _, _), _) | (_, Head.Lambda(_, _, _)) =>
        val fresh = Value.Neutral(BoundVariable(depth), Vector.empty)
        valueReads(mode, depth + 1, Value.Apply(head.value, fresh), Value.Apply(targetHead.value, fresh))
      case (Head.Neutral(BoundVariable(level), arguments), Head.Neutral(BoundVariable(targetLevel), targetArguments))
          if level >= 0 && level < depth =>
        if level != targetLevel || arguments.size != targetArguments.size then Computation.pure(false)
        else
          Computation.folded(arguments.zip(targetArguments), true) { case (agreed, (argument, targetArgument)) =>
            if !agreed then Computation.pure(false) else valueReads(mode, depth, argument, targetArgument)
          }
      case (Head.Neutral(variable, _), _) =>
        throw EvaluationError(EvaluationErrorReason.NeutralValueNotOpened(variable, depth))
      case (other, _) => throw IllegalStateException(s"a head is a thunk or a neutral value, not $other")

  /** The open normal form as a value: its leaves the fresh variables of
    * their levels, its thunks with their fillings as values.
    */
  private def openValue(form: OpenNormalForm): Value = form match
    case OpenNormalForm.Leaf(level)              => Value.Neutral(BoundVariable(level), Vector.empty)
    case OpenNormalForm.Apply(function, argument) => Value.Apply(openValue(function), openValue(argument))
    case OpenNormalForm.Thunk(code, holes, fillings) => Value.Thunk(code, holes, fillings.map(openValue))

  /** The node of a normal form, one step charged for building it. The
    * readback builds a node of each answer at each level it reads: the k-th
    * natural of `nat_type`, its levels shared with the answers before it,
    * takes a bounded number of reduction steps but k nodes, and uncharged its
    * readback took time quadratic in the steps.
    */
  private def nodeBuilt(node: OpenNormalForm): Answers[ReadingState, OpenNormalForm] =
    Answers(WeakHead.stepTaken.map(_ => Some((node, Answers.empty))))

  private def headRead(
      mode: Mode,
      readOut: ReadOut,
      depth: Int,
      head: Head
  ): Answers[ReadingState, OpenNormalForm] = head match
    case Head.Lambda(_, _, _) =>
      termRead(mode, readOut, depth + 1, Value.Apply(head.value, Value.Neutral(BoundVariable(depth), Vector.empty)))
        .flatMap(body => nodeBuilt(abstracted(body, depth)))
    case Head.Neutral(BoundVariable(level), arguments) if level >= 0 && level < depth =>
      argumentsRead(mode, readOut, depth, arguments, 0, OpenNormalForm.Leaf(level))
    case Head.Neutral(variable, _) =>
      throw EvaluationError(EvaluationErrorReason.NeutralValueNotOpened(variable, depth))
    case other => throw IllegalStateException(s"a head is a thunk or a neutral value, not $other")

  /** The most values `closedValue` walks before it answers that the value is
    * not known to be closed. A choice, not a measurement: a value is a tree
    * that shares its parts on the heap, so its walk may be far longer than
    * the heap it takes, and the walk is paid at a parallel set before any
    * head is read. top's head is a handful of values. Past the limit the
    * set is read as it was without the rule.
    */
  private val closedWalkLimit: Int = 4096

  /** Whether one head of the set is the variable of a binder opened above
    * the depth, applied to arguments or to none, and another is closed. The
    * variable's head is looked for first, and the walk of the others is
    * taken only when there is one.
    */
  private def closedBesideOpenedVariable(depth: Int, heads: Vector[Head]): Boolean =
    heads.exists {
      case Head.Neutral(BoundVariable(level), _) => level >= 0 && level < depth
      case _                                     => false
    } && heads.exists {
      case Head.Neutral(_, _) => false
      case closedCandidate    => closedValue(List(closedCandidate.value), Set.empty, closedWalkLimit)
    }

  /** Whether no neutral value occurs in the pending values, other than a
    * leaf whose variable stands for a closed term (`NeutralVariable.closedLeaf`,
    * such as a value the JIT carries), each interned value visited once,
    * within `remaining` values: such a value stands for a closed term, and
    * every read of it is closed. An instruction ends the walk at once, being a
    * closed term of the IR (`ConstructorIdentity.isInstruction`, one field
    * read), as an instruction did before every value was interned. False when the
    * walk meets any other neutral value or spends `remaining`.
    */
  @tailrec
  private def closedValue(pending: List[Value], visited: Set[Value], remaining: Int): Boolean =
    pending match
      case Nil                                      => true
      case _ if remaining <= 0                      => false
      case value :: rest if visited.contains(value) => closedValue(rest, visited, remaining - 1)
      case value :: rest if ConstructorIdentity.isInstruction(value) => closedValue(rest, visited, remaining - 1)
      case value :: rest =>
        value match
          case Value.Neutral(variable, arguments) =>
            if arguments.isEmpty && variable.closedLeaf then closedValue(rest, visited + value, remaining - 1)
            else false
          case Value.Apply(function, argument) => closedValue(function :: argument :: rest, visited + value, remaining - 1)
          case Value.Parallel(left, right)     => closedValue(left :: right :: rest, visited + value, remaining - 1)
          case Value.Choice(left, right)       => closedValue(left :: right :: rest, visited + value, remaining - 1)
          case Value.Thunk(_, _, fillings)     => closedValue(fillings.toList ::: rest, visited + value, remaining - 1)
          case _                               => closedValue(rest, visited + value, remaining - 1)

  /** The function applied to the open normal form of each argument from the
    * index on, in turn; a later argument is read for each read of the
    * earlier ones, as Prolog's backtracking reads it.
    */
  private def argumentsRead(
      mode: Mode,
      readOut: ReadOut,
      depth: Int,
      arguments: Vector[Value],
      index: Int,
      function: OpenNormalForm
  ): Answers[ReadingState, OpenNormalForm] =
    if index >= arguments.size then Answers.single(function)
    else
      termRead(mode, readOut, depth, arguments(index)).flatMap(argumentRead =>
        nodeBuilt(OpenNormalForm.Apply(function, argumentRead)).flatMap(applied =>
          argumentsRead(mode, readOut, depth, arguments, index + 1, applied)
        )
      )

  // ---- the abstraction of a fresh neutral value into a hole ----

  /** Where a slot of a chain of one binder reads from. */
  private enum SlotSource:
    case Bound
    case Free(level: Int)
    case Closed(term: OpenNormalForm)

  /** The abstraction of the variable of level `depth` over the body, the η
    * contraction `λx. F x = F` taken when F holds no leaf of the level.
    */
  private def abstracted(body: OpenNormalForm, depth: Int): OpenNormalForm = body match
    case OpenNormalForm.Apply(function, OpenNormalForm.Leaf(level))
        if level == depth && !levelOccurs(List(function), depth) =>
      function
    case OpenNormalForm.Thunk(code, holes, fillings) =>
      fillings.indexOf(OpenNormalForm.Leaf(depth)) match
        case -1 => OpenNormalForm.Thunk(code, Hole.Ignored +: holes, fillings)
        case position =>
          OpenNormalForm.Thunk(
            code,
            Hole.Bound(filledSlot(position, holes, 0)) +: holes,
            fillings.patch(position, Vector.empty, 1)
          )
    case _ =>
      val (code, slots) = bodyCode(body, depth, Vector.empty).result
      val hole = slots.indexOf(SlotSource.Bound) match
        case -1    => Hole.Ignored
        case index => Hole.Bound(index)
      val fillings = slots.collect {
        case SlotSource.Closed(closedTerm) => closedTerm
        case SlotSource.Free(level)        => OpenNormalForm.Leaf(level)
      }
      OpenNormalForm.Thunk(code, Vector(hole), fillings)

  /** The slot of the filling at the position, the fillings being the values
    * of the slots that are no hole, in slot order.
    */
  @tailrec
  private def filledSlot(position: Int, holes: Vector[Hole], slot: Int): Int =
    if holes.contains(Hole.Bound(slot)) then filledSlot(position, holes, slot + 1)
    else if position == 0 then slot
    else filledSlot(position - 1, holes, slot + 1)

  /** The code of an open normal form in the body of a chain of the one
    * binder of the level, and what each slot reads, each source once in order
    * of first occurrence.
    */
  private def bodyCode(
      term: OpenNormalForm,
      depth: Int,
      slots: Vector[SlotSource]
  ): Trampoline[(Code, Vector[SlotSource])] =
    if closed(term) then
      val (index, after) = slotOf(SlotSource.Closed(term), slots)
      done((Code.Slot(index), after))
    else
      term match
        case OpenNormalForm.Leaf(level) =>
          val (index, after) = slotOf(leafSource(level, depth), slots)
          done((Code.Slot(index), after))
        case OpenNormalForm.Apply(function, argument) =>
          for
            (functionCode, afterFunction) <- tailcall(bodyCode(function, depth, slots))
            (argumentCode, afterArgument) <- tailcall(bodyCode(argument, depth, afterFunction))
          yield (Code.Apply(functionCode, argumentCode), afterArgument)
        case OpenNormalForm.Thunk(code, holes, fillings) =>
          val (references, after) = fillings.foldLeft((Vector.empty[Code], slots)) {
            case ((referencesSoFar, current), filling) =>
              val source = filling match
                case OpenNormalForm.Leaf(level)          => leafSource(level, depth)
                case closedFilling if closed(closedFilling) => SlotSource.Closed(closedFilling)
                case _ =>
                  throw EvaluationError(EvaluationErrorReason.NotAnOpenNormalFormFilling)
              val (index, next) = slotOf(source, current)
              (referencesSoFar :+ Code.Slot(index), next)
          }
          done((Code.Thunk(code, holes, references), after))

  private def leafSource(level: Int, depth: Int): SlotSource =
    if level == depth then SlotSource.Bound else SlotSource.Free(level)

  /** The slot of the source, appended when new. */
  private def slotOf(source: SlotSource, slots: Vector[SlotSource]): (Int, Vector[SlotSource]) =
    slots.indexOf(source) match
      case -1    => (slots.size, slots :+ source)
      case index => (index, slots)

  /** The term is closed: a thunk with no leaf among its fillings, a closed
    * canonical thunk (its other fillings are closed already). An application
    * has a leaf at its head.
    */
  private def closed(term: OpenNormalForm): Boolean = allClosed(List(term))

  @tailrec
  private def allClosed(pending: List[OpenNormalForm]): Boolean = pending match
    case Nil => true
    case OpenNormalForm.Thunk(_, _, fillings) :: rest =>
      !fillings.exists {
        case OpenNormalForm.Leaf(_) => true
        case _                      => false
      } && allClosed(rest)
    case (OpenNormalForm.Leaf(_) | OpenNormalForm.Apply(_, _)) :: _ => false
    case other :: _ =>
      throw IllegalStateException(
        s"an open normal form is a leaf, an application or a thunk (the constructions of OpenNormalForm make no other), not ${other.layer}"
      )

  /** The leaf of the level occurs in one of the open normal forms; in a
    * thunk it can only be a filling.
    */
  @tailrec
  private def levelOccurs(pending: List[OpenNormalForm], level: Int): Boolean = pending match
    case Nil => false
    case OpenNormalForm.Leaf(found) :: rest =>
      found == level || levelOccurs(rest, level)
    case OpenNormalForm.Apply(function, argument) :: rest =>
      levelOccurs(function :: argument :: rest, level)
    case OpenNormalForm.Thunk(_, _, fillings) :: rest =>
      fillings.contains(OpenNormalForm.Leaf(level)) || levelOccurs(rest, level)
    case other :: _ =>
      throw IllegalStateException(
        s"an open normal form is a leaf, an application or a thunk (the constructions of OpenNormalForm make no other), not ${other.layer}"
      )

  /** The instruction of a closed open normal form: a canonical thunk, its
    * fillings closed.
    */
  private def closedInstruction(term: OpenNormalForm): Trampoline[Instruction] = term match
    case OpenNormalForm.Thunk(code, holes, fillings) =>
      allClosedInstructions(fillings).map(Instruction.Thunk(code, holes, _))
    case _                              => throw EvaluationError(EvaluationErrorReason.OpenNormalForm)

  private def allClosedInstructions(terms: Vector[OpenNormalForm]): Trampoline[Vector[Instruction]] =
    def from(index: Int, instructions: Vector[Instruction]): Trampoline[Vector[Instruction]] =
      if index >= terms.size then done(instructions)
      else
        tailcall(closedInstruction(terms(index))).flatMap(instruction =>
          from(index + 1, instructions :+ instruction)
        )
    from(0, Vector.empty)
