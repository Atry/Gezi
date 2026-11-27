package com.yang_bo.gezi.weakhead

import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Hole
import scala.annotation.tailrec
import com.yang_bo.gezi.weakhead.Trampoline
import com.yang_bo.gezi.weakhead.Trampoline.done
import com.yang_bo.gezi.weakhead.Trampoline.tailcall
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer, Value}

/** The variable of the binder a normal-form reading opened at the depth, the
  * Prolog reader's `bound(Depth)`: the number of binders opened above it.
  *
  * A neutral value, a free variable (`CONTRIBUTING.md`, "Types live only in the
  * term"), kept as an exception argued here (a neutral value is not used by
  * default; a use needs a reason it cannot do without): Böhm's reading of a
  * normal form under a lambda reads the lambda's body, an open term, and an
  * open body has no reading without something standing for its variable. A
  * closed argument in its place would let the body inspect it, so the read form
  * would be the body's at that argument, not the body's. The variable is the
  * read term's own binder, opened and closed again: every normal form the
  * reader returns abstracts it back into a hole and is closed, and no text
  * names it.
  */
final case class BoundVariable(level: Int) extends NeutralVariable

/** An open normal form (normal_forms.pl, AN OPEN NORMAL FORM): what a reading
  * under some opened binders builds, a value of the configuration `C` made of
  * applications, thunks, storages handed over whole (`Stored`) and the
  * variables of the opened binders, neutral values of no argument whose
  * variable is a `BoundVariable` (the constructions of `OpenNormalForm` make no
  * other). Two open normal forms read at one depth stand for α-equivalent terms
  * exactly when they are one object, since a variable is named by the absolute
  * depth of its binder and a thunk is canonical. The configuration is the
  * type's, so the open normal forms of two configurations are never mixed.
  */
opaque type OpenNormalForm[C <: NativeSpecializer & Singleton] = Value[C]

/** The constructions and the parts of open normal forms, each made through the
  * specializer in scope.
  */
object OpenNormalForm:

  /** The open normal form as a value: the same object. */
  def value[C <: NativeSpecializer & Singleton](
      form: OpenNormalForm[C]
  ): Value[C] = form

  /** Whether the two open normal forms of one configuration are one object. */
  def same[C <: NativeSpecializer & Singleton](
      left: OpenNormalForm[C],
      right: OpenNormalForm[C]
  )(using C): Boolean =
    Value.same(left, right)

  /** The variable of the binder opened at the level, the Prolog reader's
    * `neutral(bound(Level), [])`.
    */
  object Leaf:
    def apply[C <: NativeSpecializer & Singleton](level: Int)(using
        C
    ): OpenNormalForm[C] =
      NeutralValue(BoundVariable(level), Vector.empty)

    def unapply[C <: NativeSpecializer & Singleton](form: OpenNormalForm[C])(
        using C
    ): Option[Int] =
      NeutralValue.unapply(form: Value[C]) match
        case Some((BoundVariable(level), arguments)) if arguments.isEmpty =>
          Some(level)
        case _ => None

  /** A storage that may be handed over whole as a Scott ADT value
    * (`NativeStorage.handedOverWhole`), kept in the normal form as it is, a
    * closed leaf: its native data is the value, so the reading neither
    * eliminates it through its view nor reads its fields.
    */
  object Stored:
    def apply[C <: NativeSpecializer & Singleton](term: Configured[C])(using
        C
    ): OpenNormalForm[C] = Value.of(term)

    def unapply[C <: NativeSpecializer & Singleton](form: OpenNormalForm[C])(
        using C
    ): Option[Configured[C]] =
      storedWhole(form)

  /** The term the value is when it is a storage handed over whole (`Stored`).
    */
  private[weakhead] def storedWhole[C <: NativeSpecializer & Singleton](
      value: Value[C]
  )(using C): Option[Configured[C]] =
    com.yang_bo.gezi.ir.Closed
      .configured(value)
      .filter(term =>
        (term.representation: AnyRef) match
          case storage: com.yang_bo.gezi.ir.NativeStorage => storage.handedOverWhole
          case _                              => false
      )

  /** A leaf or an application applied to an open normal form. */
  object Apply:
    def apply[C <: NativeSpecializer & Singleton](
        function: OpenNormalForm[C],
        argument: OpenNormalForm[C]
    )(using C): OpenNormalForm[C] =
      Value.Apply(function, argument)

    def unapply[C <: NativeSpecializer & Singleton](form: OpenNormalForm[C])(
        using C
    ): Option[(OpenNormalForm[C], OpenNormalForm[C])] =
      Value.Apply.unapply(form: Value[C])

  /** An abstraction in the canonical form, each filling a closed open normal
    * form (a canonical thunk) or a leaf. A thunk of no hole is no open normal
    * form: its construction throws.
    */
  object Thunk:
    def apply[C <: NativeSpecializer & Singleton](
        code: Code,
        holes: Vector[Hole],
        fillings: Vector[OpenNormalForm[C]]
    )(using C): OpenNormalForm[C] =
      Value.Thunk(code, holes, fillings)

    def unapply[C <: NativeSpecializer & Singleton](form: OpenNormalForm[C])(
        using C
    ): Option[(Code, Vector[Hole], Vector[OpenNormalForm[C]])] =
      Value.Thunk.unapply(form: Value[C])

/** How a normal-form reading reads a parallel set of several heads. */
enum ParallelSetReading:

  /** Each normal form every head reads: one head read to its end (the first
    * that ends within its share of steps, the heads tried in order, else the
    * first head, `firstEnded`), and its reads, each given once, tested together
    * in one descent of each other head (`headReadsAll`): the answers of reading
    * every head whole and intersecting, at most the heads' shares more than
    * reading the first head whole and the others once, and an end where a head
    * that ends within its share differs from the others at a finite depth (`(λa b.
    * a) ∥ (λz s. s nat_type)` reads ∅, `nat_type ∥ (λa b. a)` reads `λa b. a`).
    * Unlike `Membership`, which streams the first head's reads and tests each
    * alone, it collects them before it tests any.
    */
  case Whole

  /** Each normal form of the first head, in order, that every other head reads
    * too, decided for each by descending into the head and the normal form
    * together (`headReads`), not by enumerating the head's reads (THE READ-OUT
    * BY MEMBERSHIP), under every mode: it decides membership by reading the
    * head down the target's shape, never by enumerating the head's normal
    * forms, so a table that completes a head's reading does not stop it.
    */
  case Membership

/** The βη normal forms of a closed term, read on the weak-head evaluator: the
  * port of `gezi/prolog/gezi/normal_forms.pl`, whose module comment the
  * definitions here follow but for the whole read-out of a parallel set
  * (`ParallelSetReading.Whole`); each normal form an instruction of the thunk
  * IR in the canonical form of `Defunctionalization.thunkInstruction` (D1 of
  * `lean/README.md`, "Design decisions").
  *
  * THE READING is Böhm's (Barendregt, chapter 10), on `WeakHead`, building the
  * normal form on the IR as it reads. The parallel sets of the term are taken,
  * and each is read by its heads: a lambda is applied to a fresh neutral value
  * of `BoundVariable(depth)`, its body read one binder deeper, and the fresh
  * variable abstracted into a hole; a neutral value of a bound variable reads
  * as the application of its leaf to its arguments, each read at the same
  * depth; a parallel set of several heads is read out (`ParallelSetReading`).
  *
  * THE ABSTRACTION of the variable of level Depth over an open normal form Body
  * read one binder deeper gives what `thunkInstruction` gives for the
  * abstraction of the term Body stands for: Function when Body is Function
  * applied to the leaf of Depth and Function holds no leaf of Depth (the η
  * rule); when Body is a thunk, the chain one binder longer, the leaf of Depth
  * among its fillings its first hole, ignored when absent, every slot keeping
  * its number; otherwise a chain of one binder, whose slots are Body's leaves,
  * its closed thunks and the fillings of its inner thunks that are not closed,
  * numbered by first occurrence in preorder, equal closed thunks sharing a
  * slot.
  *
  * AN ANSWER N OF Term SATISFIES Term ⊑_O N: the reader answers N for T only
  * when T ⊑ N, which holds up to ⊑_O as every derivation of ⊢ does, by the
  * derivations of the Prolog module comment: a parallel set P of T has T ⊑ P
  * (`WeakHead`); a lambda H with H x ⊑ B has H ⊑ λx. B by the congruence under
  * λ and the η rule; a spine by (10) and (8); a parallel L ∥ R ⊑ N when L ⊑ N
  * and R ⊑ N, by the λ-lattice laws (1) and (3) to (6). A head with no read
  * gives no answer: a false negative, which a sound approximation allows.
  *
  * A normal form reads as many times as its reading finds it; `normalForms`
  * keeps each once. A term whose Böhm tree is infinite is read as long as its
  * reading goes; the budget bounds it.
  */
object NormalForms:

  /** The distinct normal forms read of the closed term under the mode, in the
    * order first read, with the whole read-out. A normal form read again is
    * dropped as it is read: a term whose reading finds one normal form many
    * times, such as a list of R choices whose members are equal, which the
    * reading takes 2^R times, holds that one normal form, not 2^R copies of it.
    */
  def normalForms[C <: NativeSpecializer & Singleton](
      mode: Mode,
      term: Value[C]
  )(using C): Computation[ReadingState[C], Vector[Configured[C]]] =
    normalForm(mode, ParallelSetReading.Whole, term).distinctCollected

  /** The normal forms read of the closed term under the mode, one at a time
    * (normal_form/4). Throws `EvaluationError` with `OpenNormalForm` should a
    * normal form read at depth 0 not be a closed thunk.
    */
  def normalForm[C <: NativeSpecializer & Singleton](
      mode: Mode,
      parallelSetReading: ParallelSetReading,
      term: Value[C]
  )(using C): Answers[ReadingState[C], Configured[C]] =
    termRead(mode, parallelSetReading, 0, term).map(read =>
      if closed(read) then closedInstruction(read)
      else throw EvaluationError(EvaluationErrorReason.OpenNormalForm)
    )

  private def termRead[C <: NativeSpecializer & Singleton](
      mode: Mode,
      parallelSetReading: ParallelSetReading,
      depth: Int,
      term: Value[C]
  )(using C): Answers[ReadingState[C], OpenNormalForm[C]] =
    // A storage handed over whole is its own normal form, its view not read: computing normal forms leaves a storage in
    // place, and only the terms a storage holds as written are read further.
    OpenNormalForm.storedWhole(term) match
      case Some(stored) => Answers.single(OpenNormalForm.Stored(stored))
      case None         =>
        WeakHead
          .heads(mode, term)
          .flatMap(setRead(mode, parallelSetReading, depth, _))

  /** The reads of a parallel set: of its head when it has one; the reads every
    * one of its heads reads when it has several (`ParallelSetReading`), since
    * H1 ⊑ N and H2 ⊑ N give H1 ∥ H2 ⊑ N.
    *
    * Under the whole read-out each head is first tried within a share of steps,
    * in order, and the first to end has its reads tested on the others; when
    * none ends within its share, the first head is read to its end
    * (`firstEnded`): `nat_type ∥ (λa b. a)` reads `(λa b. a)` as its swap does.
    * A reading the limit stops is no finished ∅: the stop ends the whole
    * reading.
    *
    * A set that holds a closed head beside a head that is the variable of an
    * opened binder, applied to arguments or to none, reads ∅ with no head read
    * (`closedBesideOpenedVariable`): every read of the closed head is a closed
    * open normal form, and every read of the other holds that variable's leaf,
    * so the two reads have no member in common, which is what both read-outs
    * would give had both readings finished. The rule answers nothing the reads
    * of the heads would not: it only spares reading them, and with it top = Y
    * (λz. λx. z ∥ x), whose body is top ∥ x under its opened binder, reads ∅
    * under the plain evaluator too, as `top` stands where the empty choice
    * stood.
    *
    * FIXME (known incompleteness, 2026-11-11): the empty parallel set, which
    * https://github.com/Atry/private-overlay/issues/1946 only an evaluation
    * that knows a least term answers (`KnownExtremes`), reads nothing here.
    * Every normal form is an answer of a least term, and this reader, which
    * gives its answers one at a time, has no way to give them all; a caller
    * that asks whether one normal form is an answer can be answered yes, as
    * `Reading`'s witness reading is.
    */
  private def setRead[C <: NativeSpecializer & Singleton](
      mode: Mode,
      parallelSetReading: ParallelSetReading,
      depth: Int,
      set: ParallelSet[C]
  )(using C): Answers[ReadingState[C], OpenNormalForm[C]] =
    set.heads match
      case Vector()       => Answers.empty
      case Vector(single) => headRead(mode, parallelSetReading, depth, single)
      case heads @ (first +: others) =>
        Answers
          .computed(
            Computation.pure(Vector(closedBesideOpenedVariable(depth, heads)))
          )
          .flatMap(disjoint =>
            if disjoint then Answers.empty
            else
              parallelSetReading match
                // The reads of the head the set is read from (`firstEnded`), kept where every other head reads them,
                // all tested in one descent of each (`headReadsAll`).
                case ParallelSetReading.Whole =>
                  Answers.computed(
                    firstEnded(
                      heads,
                      headRead(mode, parallelSetReading, depth, _)
                    ).flatMap((finished, finishedReads) =>
                      Computation.folded(
                        heads.zipWithIndex.collect {
                          case (head, index) if index != finished => head
                        },
                        finishedReads
                      )((reads, head) =>
                        if reads.isEmpty then Computation.pure(reads)
                        else
                          headReadsAll(
                            mode,
                            depth,
                            head,
                            reads.map(OpenNormalForm.value[C])
                          ).map(kept =>
                            reads.zipWithIndex.collect {
                              case (read, index) if kept.contains(index) => read
                            }
                          )
                      )
                    )
                  )
                case ParallelSetReading.Membership =>
                  others.foldLeft(
                    headRead(mode, parallelSetReading, depth, first)
                  )((reads, head) =>
                    reads.filtered(read =>
                      headReads(mode, depth, head, OpenNormalForm.value(read))
                    )
                  )
          )
      case heads =>
        throw IllegalStateException(
          s"a vector of heads that is not empty has a first head, but ${heads.size} heads matched none"
        )

  /** The steps each head of a set is first given to read to its end
    * (`firstEnded`).
    */
  private val headShare: Long = 4096

  /** The position of the head whose reads the set is read from, and those
    * reads, each once: the first head that ends within its share of `headShare`
    * steps, the heads tried in order; and when none does, the first head read
    * to its end, as the heads were read before shares, so that a set costs at
    * most its heads' shares more than that reading and a nested set's shares
    * add up and never multiply (each set is read in full once). An attempt that
    * runs out of its share is given up, its steps kept spent and its state
    * dropped (`withinShare`).
    *
    * FIXME: the order of the heads still decides whether some sets end: a
    * https://github.com/Atry/private-overlay/issues/2037 head with finitely
    * many reads that needs more than its share, behind a first head with
    * infinitely many; the descents of the other heads, taken in their order,
    * one of which need not end (`(λa b. a) ∥ (λa b. Ω) ∥ (λa b. b)` reads ∅ in
    * another order); and `ParallelSetReading.Membership`, which streams the
    * first head.
    */
  private def firstEnded[C <: NativeSpecializer & Singleton](
      heads: Vector[Head[C]],
      reads: Head[C] => Answers[ReadingState[C], OpenNormalForm[C]]
  )(using C): Computation[ReadingState[C], (Int, Vector[OpenNormalForm[C]])] =
    def tried(
        position: Int
    ): Computation[ReadingState[C], (Int, Vector[OpenNormalForm[C]])] =
      if position == heads.size then
        reads(heads(0)).distinctCollected.map((0, _))
      else
        withinShare(reads(heads(position)).distinctCollected, headShare)
          .flatMap {
            case Some(found) => Computation.pure((position, found))
            case None        => tried(position + 1)
          }
    tried(0)

  /** The computation under a ceiling of the share more steps (`Budget.ceiling`,
    * the reading's limit left as it is): its value, or none when it ran out of
    * that ceiling below the bound it was tried under, its steps then kept spent
    * and its state dropped, as if it had not been made: its tables and the
    * JIT's state memoize deterministic functions, so dropping them changes no
    * answer, and its cost records (`codeApplications`, `nativeCalls`, the JIT's
    * wasted block steps) go with them though its steps stay spent. A stop at
    * the bound it was tried under, a requested stop or an exhausted resource is
    * the stop.
    */
  private def withinShare[C <: NativeSpecializer & Singleton, Result](
      computation: Computation[ReadingState[C], Result],
      share: Long
  )(using C): Computation[ReadingState[C], Option[Result]] =
    ReadingState.attempted(computation, share, speculative = false).map {
      case Attempt.Finished(value) => Some(value)
      case Attempt.OutOfSteps(_)   => None
    }

  // ---- whether a head reads a given normal form ----

  /** Whether the closed term has one parallel set of one head, and that head
    * reads the normal form `target` (`headReads`): the term is the target up to
    * ≃_O, not only a term with the target among its normal forms, whose other
    * parallel sets or heads would be more. The heads are read by the mode; the
    * target's binders are opened as `headReads` opens them, by the fresh
    * variables of `BoundVariable`, the reader's own.
    */
  def soleHeadReads[C <: NativeSpecializer & Singleton](
      mode: Mode,
      term: Value[C],
      target: Value[C]
  )(using C): Computation[ReadingState[C], Boolean] =
    WeakHead.heads(mode, term).collected.flatMap {
      case Vector(set) =>
        set.heads match
          case Vector(head) => headReads(mode, 0, head, target)
          case _            => Computation.pure(false)
      case _ => Computation.pure(false)
    }

  /** Whether the head reads the normal form `target`, a value whose one head is
    * that normal form's: the head and the target are read together, down the
    * target's shape. Where either is a lambda, both are applied to the fresh
    * variable of the depth (the η rule, so that an η-reduced target meets its
    * expansion); where both are variables applied to arguments, the variables
    * and the numbers of arguments are compared, then each pair of arguments in
    * order. The test answers false at the first difference, so it finishes
    * wherever the head and the target differ at a finite depth, where
    * enumerating the head's reads and comparing each to the target finishes
    * only when the head has finitely many: `zero ∥ nat_type`'s parallel set
    * {zero, successor N} reads zero's normal form against successor N, which
    * differs at its head variable, two binders down, while successor N has a
    * read for every natural.
    *
    * It answers true only where some read of the head is the target, and false
    * where the enumeration would find none: two βη normal forms are equal as
    * canonical thunks exactly when they agree under this descent, and the
    * head's reads are taken set by set, every head of a set reading the target,
    * as `setRead` reads them. A set that `setRead` reads as ∅ (no head, or a
    * closed head beside an opened variable) reads no target here either.
    */
  private def headReads[C <: NativeSpecializer & Singleton](
      mode: Mode,
      depth: Int,
      head: Head[C],
      target: Value[C]
  )(using C): Computation[ReadingState[C], Boolean] =
    headReadsAll(mode, depth, head, Vector(target)).map(_.nonEmpty)

  /** A target normal form expanded once, so that testing it costs no step: an
    * abstraction, its body under the fresh variable of the depth it was opened
    * at, or a variable applied to the expanded arguments.
    */
  private enum TargetShape:
    case Abstraction(body: TargetShape)
    case Spine(level: Int, arguments: Vector[TargetShape])

  /** The shape of a normal form read as a value at the depth. */
  private def targetShape[C <: NativeSpecializer & Singleton](
      mode: Mode,
      depth: Int,
      target: Value[C]
  )(using C): Computation[ReadingState[C], TargetShape] =
    normalFormHead(mode, target).flatMap {
      case Head.Lambda(_, _, _) =>
        targetShape(
          mode,
          depth + 1,
          Value.Apply(target, NeutralValue(BoundVariable(depth), Vector.empty))
        ).map(TargetShape.Abstraction(_))
      case Head.Neutral(BoundVariable(level), arguments) =>
        Computation
          .traversed(arguments)(targetShape(mode, depth, _))
          .map(TargetShape.Spine(level, _))
      case other =>
        throw IllegalStateException(
          s"a normal form's head is an abstraction or a bound variable, not $other"
        )
    }

  /** The target applied to the fresh variable of the depth, as the descent
    * applies both sides where either is an abstraction (the η rule).
    */
  private def underFresh(target: TargetShape, depth: Int): TargetShape =
    target match
      case TargetShape.Abstraction(body)       => body
      case TargetShape.Spine(level, arguments) =>
        TargetShape.Spine(
          level,
          arguments :+ TargetShape.Spine(depth, Vector.empty)
        )

  /** The indices of the targets, normal forms read as values, that the head
    * reads, as `headReads` states it, decided for all in one descent of the
    * head. The targets are expanded once (`targetShape`), and the head's
    * subterms are evaluated once for the targets still alive where they are
    * reached, a neutral head's arguments once more for each level of
    * abstraction a target meets it with (the η rule), so that the steps are at
    * most those of reading the head's normal forms whole, times that depth,
    * plus the targets' expansion.
    */
  private def headReadsAll[C <: NativeSpecializer & Singleton](
      mode: Mode,
      depth: Int,
      head: Head[C],
      targets: Vector[Value[C]]
  )(using C): Computation[ReadingState[C], Set[Int]] =
    Computation
      .traversed(targets)(targetShape(mode, depth, _))
      .flatMap(shapes => headsAgreeAll(mode, depth, head, shapes.zipWithIndex))

  /** The indices of the targets the head agrees with, by the descent
    * `headReads` states.
    */
  private def headsAgreeAll[C <: NativeSpecializer & Singleton](
      mode: Mode,
      depth: Int,
      head: Head[C],
      targets: Vector[(TargetShape, Int)]
  )(using C): Computation[ReadingState[C], Set[Int]] =
    def applied(
        group: Vector[(TargetShape, Int)]
    ): Computation[ReadingState[C], Set[Int]] =
      if group.isEmpty then Computation.pure(Set.empty)
      else
        val fresh = NeutralValue[C](BoundVariable(depth), Vector.empty)
        valueReadsAll(
          mode,
          depth + 1,
          Value.Apply(head.value, fresh),
          group.map((target, index) => (underFresh(target, depth), index))
        )
    if targets.isEmpty then Computation.pure(Set.empty)
    else
      head match
        case Head.Lambda(_, _, _) => applied(targets)
        case Head.Neutral(BoundVariable(level), arguments)
            if level >= 0 && level < depth =>
          val abstractions = targets.filter {
            case (TargetShape.Abstraction(_), _) => true
            case _                               => false
          }
          val matching = targets.collect {
            case (TargetShape.Spine(targetLevel, targetArguments), index)
                if targetLevel == level && targetArguments.size == arguments.size =>
              (targetArguments, index)
          }
          val byArguments: Computation[ReadingState[C], Set[Int]] =
            if matching.isEmpty then Computation.pure(Set.empty)
            else
              Computation.folded(
                arguments.indices.toVector,
                matching.map(_._2).toSet
              )((alive, position) =>
                if alive.isEmpty then Computation.pure(alive)
                else
                  valueReadsAll(
                    mode,
                    depth,
                    arguments(position),
                    matching.collect {
                      case (targetArguments, index) if alive.contains(index) =>
                        (targetArguments(position), index)
                    }
                  ).map(alive.intersect)
              )
          applied(abstractions).flatMap(throughEta =>
            byArguments.map(throughEta ++ _)
          )
        case Head.Neutral(variable, _) =>
          throw EvaluationError(
            EvaluationErrorReason.NeutralValueNotOpened(variable, depth)
          )
        case other =>
          throw IllegalStateException(
            s"a head is a thunk or a neutral value, not $other"
          )

  /** The indices of the targets some parallel set of the value reads, every
    * head of the set agreeing with the target, the sets taken in order until
    * every target has one.
    */
  private def valueReadsAll[C <: NativeSpecializer & Singleton](
      mode: Mode,
      depth: Int,
      value: Value[C],
      targets: Vector[(TargetShape, Int)]
  )(using C): Computation[ReadingState[C], Set[Int]] =
    def over(
        sets: Answers[ReadingState[C], ParallelSet[C]],
        remaining: Vector[(TargetShape, Int)],
        found: Set[Int]
    ): Computation[ReadingState[C], Set[Int]] =
      if remaining.isEmpty then Computation.pure(found)
      else
        sets.pull.flatMap {
          case None              => Computation.pure(found)
          case Some((set, rest)) =>
            val agreed: Computation[ReadingState[C], Set[Int]] =
              if set.heads.isEmpty || (set.heads.size > 1 && closedBesideOpenedVariable(
                  depth,
                  set.heads
                ))
              then Computation.pure(Set.empty)
              else
                Computation.folded(set.heads, remaining.map(_._2).toSet)(
                  (alive, head) =>
                    if alive.isEmpty then Computation.pure(alive)
                    else
                      headsAgreeAll(
                        mode,
                        depth,
                        head,
                        remaining.filter(target => alive.contains(target._2))
                      ).map(alive.intersect)
                )
            agreed.flatMap(newly =>
              over(
                rest,
                remaining.filterNot(target => newly.contains(target._2)),
                found ++ newly
              )
            )
        }
    if targets.isEmpty then Computation.pure(Set.empty)
    else over(WeakHead.heads(mode, value), targets, Set.empty)

  /** The one head of a normal form read as a value. Throws
    * `IllegalStateException` when the value has another number of parallel sets
    * or heads, which no normal form has.
    */
  private def normalFormHead[C <: NativeSpecializer & Singleton](
      mode: Mode,
      target: Value[C]
  )(using C): Computation[ReadingState[C], Head[C]] =
    WeakHead.heads(mode, target).collected.map {
      case Vector(set) =>
        set.heads match
          case Vector(head) => head
          case heads        =>
            throw IllegalStateException(
              s"a normal form read as a value has a parallel set of ${heads.size} heads"
            )
      case sets =>
        throw IllegalStateException(
          s"a normal form read as a value has ${sets.size} parallel sets"
        )
    }

  /** The node of a normal form, one step charged for building it. The readback
    * builds a node of each answer at each level it reads: the k-th natural of
    * `nat_type`, its levels shared with the answers before it, takes a bounded
    * number of reduction steps but k nodes, and uncharged its readback took
    * time quadratic in the steps.
    */
  private def nodeBuilt[C <: NativeSpecializer & Singleton](
      node: OpenNormalForm[C]
  )(using C): Answers[ReadingState[C], OpenNormalForm[C]] =
    Answers(WeakHead.stepTaken[C].map(_ => Some((node, Answers.empty))))

  private def headRead[C <: NativeSpecializer & Singleton](
      mode: Mode,
      parallelSetReading: ParallelSetReading,
      depth: Int,
      head: Head[C]
  )(using C): Answers[ReadingState[C], OpenNormalForm[C]] = head match
    case Head.Lambda(_, _, _) =>
      termRead(
        mode,
        parallelSetReading,
        depth + 1,
        Value.Apply(
          head.value,
          NeutralValue(BoundVariable(depth), Vector.empty)
        )
      )
        .flatMap(body => nodeBuilt(abstracted(body, depth)))
    case Head.Neutral(BoundVariable(level), arguments)
        if level >= 0 && level < depth =>
      argumentsRead(
        mode,
        parallelSetReading,
        depth,
        arguments,
        0,
        OpenNormalForm.Leaf[C](level)
      )
    case Head.Neutral(variable, _) =>
      throw EvaluationError(
        EvaluationErrorReason.NeutralValueNotOpened(variable, depth)
      )
    case other =>
      throw IllegalStateException(
        s"a head is a thunk or a neutral value, not $other"
      )

  /** The most values `closedValue` walks before it answers that the value is
    * not known to be closed. A choice, not a measurement: a value is a tree
    * that shares its parts on the heap, so its walk may be far longer than the
    * heap it takes, and the walk is paid at a parallel set before any head is
    * read. top's head is a handful of values. Past the limit the set is read as
    * it was without the rule.
    */
  private val closedWalkLimit: Int = 4096

  /** Whether one head of the set is the variable of a binder opened above the
    * depth, applied to arguments or to none, and another is closed. The
    * variable's head is looked for first, and the walk of the others is taken
    * only when there is one.
    */
  private def closedBesideOpenedVariable[C <: NativeSpecializer & Singleton](
      depth: Int,
      heads: Vector[Head[C]]
  )(using C): Boolean =
    heads.exists {
      case Head.Neutral(BoundVariable(level), _) => level >= 0 && level < depth
      case _                                     => false
    } && heads.exists {
      case Head.Neutral(_, _) => false
      case closedCandidate    =>
        closedValue(List(closedCandidate.value), Set.empty, closedWalkLimit)
    }

  /** Whether no neutral value occurs in the pending values, other than a leaf
    * whose variable stands for a closed term (`NeutralVariable.closedLeaf`,
    * such as a value the JIT carries), each interned value visited once, within
    * `remaining` values: such a value stands for a closed term, and every read
    * of it is closed. An instruction ends the walk at once, being a closed term
    * of the IR (`com.yang_bo.gezi.ir.Closed.configured`, one field read), as an instruction
    * did before every value was interned. False when the walk meets any other
    * neutral value or spends `remaining`.
    */
  @tailrec
  private def closedValue[C <: NativeSpecializer & Singleton](
      pending: List[Value[C]],
      visited: Set[Value[C]],
      remaining: Int
  )(using C): Boolean =
    pending match
      case Nil                                      => true
      case _ if remaining <= 0                      => false
      case value :: rest if visited.contains(value) =>
        closedValue(rest, visited, remaining - 1)
      case value :: rest if com.yang_bo.gezi.ir.Closed.configured(value).isDefined =>
        closedValue(rest, visited, remaining - 1)
      case value :: rest =>
        value match
          case NeutralValue(variable, arguments) =>
            if arguments.isEmpty && variable.closedLeaf then
              closedValue(rest, visited + value, remaining - 1)
            else false
          case Value.Apply(function, argument) =>
            closedValue(
              function :: argument :: rest,
              visited + value,
              remaining - 1
            )
          case Value.Parallel(left, right) =>
            closedValue(left :: right :: rest, visited + value, remaining - 1)
          case Value.Choice(left, right) =>
            closedValue(left :: right :: rest, visited + value, remaining - 1)
          case Value.Thunk(_, _, fillings) =>
            closedValue(
              fillings.toList ::: rest,
              visited + value,
              remaining - 1
            )
          case _ => closedValue(rest, visited + value, remaining - 1)

  /** The function applied to the open normal form of each argument from the
    * index on, in turn; a later argument is read for each read of the earlier
    * ones, as Prolog's backtracking reads it.
    */
  private def argumentsRead[C <: NativeSpecializer & Singleton](
      mode: Mode,
      parallelSetReading: ParallelSetReading,
      depth: Int,
      arguments: Vector[Value[C]],
      index: Int,
      function: OpenNormalForm[C]
  )(using C): Answers[ReadingState[C], OpenNormalForm[C]] =
    if index >= arguments.size then Answers.single(function)
    else
      termRead(mode, parallelSetReading, depth, arguments(index)).flatMap(
        argumentRead =>
          nodeBuilt(OpenNormalForm.Apply(function, argumentRead)).flatMap(
            applied =>
              argumentsRead(
                mode,
                parallelSetReading,
                depth,
                arguments,
                index + 1,
                applied
              )
          )
      )

  // ---- the abstraction of a fresh neutral value into a hole ----

  /** Where a slot of a chain of one binder reads from. */
  private enum SlotSource[C <: NativeSpecializer & Singleton]:
    case Bound()
    case Free(level: Int)
    case Closed(term: OpenNormalForm[C])

  /** Whether the two sources are one: a closed term is compared as an object
    * (`OpenNormalForm.same`).
    */
  private def sameSource[C <: NativeSpecializer & Singleton](
      left: SlotSource[C],
      right: SlotSource[C]
  )(using C): Boolean =
    (left, right) match
      case (SlotSource.Bound(), SlotSource.Bound())          => true
      case (SlotSource.Free(first), SlotSource.Free(second)) => first == second
      case (SlotSource.Closed(first), SlotSource.Closed(second)) =>
        OpenNormalForm.same(first, second)
      case _ => false

  /** Whether the open normal form is the leaf of the level. */
  private def isLeaf[C <: NativeSpecializer & Singleton](
      form: OpenNormalForm[C],
      level: Int
  )(using C): Boolean = form match
    case OpenNormalForm.Leaf(found) => found == level
    case _                          => false

  /** The abstraction of the variable of level `depth` over the body, the η
    * contraction `λx. F x = F` taken when F holds no leaf of the level.
    */
  private def abstracted[C <: NativeSpecializer & Singleton](
      body: OpenNormalForm[C],
      depth: Int
  )(using C): OpenNormalForm[C] = body match
    case OpenNormalForm.Apply(function, OpenNormalForm.Leaf(level))
        if level == depth && !levelOccurs(List(function), depth) =>
      function
    case OpenNormalForm.Thunk(code, holes, fillings) =>
      fillings.indexWhere(isLeaf(_, depth)) match
        case -1 => OpenNormalForm.Thunk(code, Hole.Ignored +: holes, fillings)
        case position =>
          OpenNormalForm.Thunk(
            code,
            Hole.Bound(filledSlot(position, holes, 0)) +: holes,
            fillings.patch(position, Vector.empty, 1)
          )
    case _ =>
      val (code, slots) = bodyCode(body, depth, Vector.empty).result
      val hole = slots.indexWhere {
        case SlotSource.Bound() => true
        case _                  => false
      } match
        case -1    => Hole.Ignored
        case index => Hole.Bound(index)
      val fillings = slots.collect {
        case SlotSource.Closed(closedTerm) => closedTerm
        case SlotSource.Free(level)        => OpenNormalForm.Leaf[C](level)
      }
      OpenNormalForm.Thunk(code, Vector(hole), fillings)

  /** The slot of the filling at the position, the fillings being the values of
    * the slots that are no hole, in slot order.
    */
  @tailrec
  private def filledSlot(position: Int, holes: Vector[Hole], slot: Int): Int =
    if holes.contains(Hole.Bound(slot)) then
      filledSlot(position, holes, slot + 1)
    else if position == 0 then slot
    else filledSlot(position - 1, holes, slot + 1)

  /** The code of an open normal form in the body of a chain of the one binder
    * of the level, and what each slot reads, each source once in order of first
    * occurrence.
    */
  private def bodyCode[C <: NativeSpecializer & Singleton](
      term: OpenNormalForm[C],
      depth: Int,
      slots: Vector[SlotSource[C]]
  )(using C): Trampoline[(Code, Vector[SlotSource[C]])] =
    if closed(term) then
      val (index, after) = slotOf(SlotSource.Closed(term), slots)
      done((Code.Slot(index), after))
    else
      term match
        case OpenNormalForm.Leaf(level) =>
          val (index, after) = slotOf(leafSource[C](level, depth), slots)
          done((Code.Slot(index), after))
        case OpenNormalForm.Apply(function, argument) =>
          for
            (functionCode, afterFunction) <- tailcall(
              bodyCode(function, depth, slots)
            )
            (argumentCode, afterArgument) <- tailcall(
              bodyCode(argument, depth, afterFunction)
            )
          yield (Code.Apply(functionCode, argumentCode), afterArgument)
        case OpenNormalForm.Thunk(code, holes, fillings) =>
          val (references, after) =
            fillings.foldLeft((Vector.empty[Code], slots)) {
              case ((referencesSoFar, current), filling) =>
                val source = filling match
                  case OpenNormalForm.Leaf(level) => leafSource[C](level, depth)
                  case closedFilling if closed(closedFilling) =>
                    SlotSource.Closed(closedFilling)
                  case _ =>
                    throw EvaluationError(
                      EvaluationErrorReason.NotAnOpenNormalFormFilling
                    )
                val (index, next) = slotOf(source, current)
                (referencesSoFar :+ Code.Slot(index), next)
            }
          done((Code.Thunk(code, holes, references), after))
        case _ =>
          throw IllegalStateException(
            "an open normal form is a leaf, an application, a thunk or a stored leaf (the constructions of OpenNormalForm make no other)"
          )

  private def leafSource[C <: NativeSpecializer & Singleton](
      level: Int,
      depth: Int
  ): SlotSource[C] =
    if level == depth then SlotSource.Bound() else SlotSource.Free(level)

  /** The slot of the source, appended when new. */
  private def slotOf[C <: NativeSpecializer & Singleton](
      source: SlotSource[C],
      slots: Vector[SlotSource[C]]
  )(using C): (Int, Vector[SlotSource[C]]) =
    slots.indexWhere(sameSource(_, source)) match
      case -1    => (slots.size, slots :+ source)
      case index => (index, slots)

  /** The term is closed: a thunk with no leaf among its fillings, a closed
    * canonical thunk (its other fillings are closed already). An application
    * has a leaf at its head.
    */
  private def closed[C <: NativeSpecializer & Singleton](
      term: OpenNormalForm[C]
  )(using C): Boolean = allClosed(List(term))

  @tailrec
  private def allClosed[C <: NativeSpecializer & Singleton](
      pending: List[OpenNormalForm[C]]
  )(using C): Boolean = pending match
    case Nil                                          => true
    case OpenNormalForm.Stored(_) :: rest             => allClosed(rest)
    case OpenNormalForm.Thunk(_, _, fillings) :: rest =>
      !fillings.exists {
        case OpenNormalForm.Leaf(_) => true
        case _                      => false
      } && allClosed(rest)
    case (OpenNormalForm.Leaf(_) | OpenNormalForm.Apply(_, _)) :: _ => false
    case _                                                          =>
      throw IllegalStateException(
        "an open normal form is a leaf, an application, a thunk or a stored leaf (the constructions of OpenNormalForm make no other)"
      )

  /** The leaf of the level occurs in one of the open normal forms; in a thunk
    * it can only be a filling.
    */
  @tailrec
  private def levelOccurs[C <: NativeSpecializer & Singleton](
      pending: List[OpenNormalForm[C]],
      level: Int
  )(using C): Boolean = pending match
    case Nil                                => false
    case OpenNormalForm.Stored(_) :: rest   => levelOccurs(rest, level)
    case OpenNormalForm.Leaf(found) :: rest =>
      found == level || levelOccurs(rest, level)
    case OpenNormalForm.Apply(function, argument) :: rest =>
      levelOccurs(function :: argument :: rest, level)
    case OpenNormalForm.Thunk(_, _, fillings) :: rest =>
      fillings.exists(isLeaf(_, level)) || levelOccurs(rest, level)
    case _ =>
      throw IllegalStateException(
        "an open normal form is a leaf, an application, a thunk or a stored leaf (the constructions of OpenNormalForm make no other)"
      )

  /** The term of a closed open normal form, a canonical thunk with closed
    * fillings: the same object, a value that holds no neutral value and no
    * suspension, which `com.yang_bo.gezi.ir.Closed.configured` reads off by two fields.
    */
  private def closedInstruction[C <: NativeSpecializer & Singleton](
      term: OpenNormalForm[C]
  )(using C): Configured[C] =
    com.yang_bo.gezi.ir.Closed
      .configured(OpenNormalForm.value(term))
      .getOrElse(throw EvaluationError(EvaluationErrorReason.OpenNormalForm))
