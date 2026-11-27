package gezi.weakhead

import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Spine
import gezi.weakhead.Trampoline
import gezi.weakhead.Trampoline.done
import gezi.weakhead.Trampoline.tailcall
import gezi.ir.{Apply, Choice, Parallel, Slot, Thunk}
import gezi.ir.{Configured, NativeSpecializer, Value}

/** The weak-head evaluator on the thunk IR, the port of
  * `gezi/prolog/gezi/weak_head.pl`: the reference interpreter.
  * `heads(mode, term)` gives the value of the closed term
  * (`Value`) as a set of parallel sets (`ParallelSet`) of heads (`Head`): a
  * disjunctive normal form, the choice of its members, each member the
  * parallel of its heads; a choice inside a parallel needs the distributive
  * law.
  *
  * THE RULES, the parallel sets of each layer by the defunctionalized beta
  * rule of D2 of `lean/README.md`, "Design decisions"; no delta,
  * and no index is read. `S ⊗ T` is the set of the parallels p ∥ q, p of S
  * and q of T:
  *   - a thunk with a hole is one parallel set of one head, itself;
  *   - a thunk with no hole is the instance of its code under its fillings,
  *     whose parallel sets are its own;
  *   - `apply(F, A)`: for each parallel set p of F, the ⊗ of what each head
  *     of p gives applied to A, by equations (8) and (9),
  *     `(M + N) P = M P + N P` and `(M ∥ N) P = M P ∥ N P`: a thunk takes A
  *     at its first hole (an ignored hole drops A) and gives the result's
  *     parallel sets; a neutral value takes A as its last argument; the empty
  *     parallel set gives itself;
  *   - `choice(Left, Right)`: the parallel sets of each member of its right
  *     spine;
  *   - `parallel(Left, Right)`: those of Left ⊗ those of Right, both sides
  *     evaluated. A side with no parallel set leaves the parallel with none;
  *   - a neutral value is one parallel set of one head, itself.
  * The heads of a parallel set are not combined: the parallel of two
  * abstractions stays two heads.
  *
  * KNOWN EXTREMES, the variant (`KnownExtremes`, a part of the reading's
  * state). Before a term is evaluated it is compared with the listed
  * spellings of greatest and of least terms of ⊑_O, by reference: every
  * value is interned, so two spellings of one term are one object. A
  * listed top has no parallel set, whatever it is applied to; a listed
  * bottom has the empty parallel set, whatever it is applied to. The rules
  * of the two then are the set operations above, and nothing more is
  * executed for them:
  *   - top + M = M: no parallel set joins the others;
  *   - top ∥ M = top: ⊗ with no parallel set gives none;
  *   - top M = top: no parallel set to apply;
  *   - bottom ∥ M = M: ⊗ with the empty parallel set leaves the other;
  *   - bottom M = bottom: the empty parallel set applied gives itself;
  *   - bottom + M = bottom: the answers hold the empty parallel set beside
  *     M's. By absorption, equation (6), a set that holds the empty parallel
  *     set stands for bottom whatever else it holds; the evaluator leaves
  *     the others in, each still an answer, and `bottomAbsorbed` drops them.
  * Each of the six holds up to ≃_O of a top and of a bottom; for top the
  * three are Lean's `contextualEquivalenceTopChoice`,
  * `contextualEquivalenceTopParallel` and `contextualEquivalenceTopApplication`
  * (`lean/LambdaJit/ContextualPreorderTop.lean`), and for Ω
  * `omegaParallelContextualEquivalence`,
  * `omegaApplicationContextualEquivalence` and
  * `omegaChoiceContextualEquivalence`, with `omegaContextualPreorder`, Ω ⊑_O M
  * for every M (`lean/LambdaJit/ContextualPreorderUnconditional.lean`).
  * A term that has no head and is not listed is not recognised: under
  * tabling(weak_head) its table completes with no parallel set, which reads
  * as a top's does. That loses answers and adds none.
  *
  * WHY A PARALLEL SET IS AN ANSWER'S STEP. Read every term back to the
  * calculus (the readback of D3 of `lean/README.md`, "Design decisions", a neutral value read as its variable
  * applied to its arguments, an open term of the calculus), and a parallel
  * set as the parallel of its heads. For every parallel set P of T,
  * ⊢_{λ-lattice-unit-η} T + P = T, that is T ⊑ P
  * (the formal definition of the calculus (`CONTRIBUTING.md`, "Terms"); ⊢ is a congruence on
  * open terms too): the two beta clauses of D2 are derivations on readbacks
  * (Readback.readbackSound in gezi/lean, for IR terms); a member Mi of
  * M1 + ... + Mn with Mi ⊑ P gives M1 + ... + Mn ⊑ P by equations (1) and
  * (2); F ⊑ P gives F A ⊑ P A by (8); (9) is an equation; L ⊑ P and R ⊑ Q
  * give L ∥ R ⊑ P ∥ Q, the parallel being the least upper bound by (3) to
  * (6); ⊑ is transitive by (2). Taking one member of a choice inside a
  * parallel is that last step: M ∥ (N + P) ⊑ (M ∥ N) + (M ∥ P) holds in
  * every lattice. Soundness needs no more. The converse, the distributive
  * law, is not among the ten equations but holds up to ≃_O
  * (`parallelChoiceDistributiveContextualEquivalence`,
  * `lean/LambdaJit/ContextualPreorderDistributive.lean`), so the rule of a
  * parallel loses no answer: M ∥ (N + P) and the choice of the parallels it
  * gives, (M ∥ N) + (M ∥ P), have the same answers. Elsewhere the evaluator
  * may lose answers, as a sound approximation may. A
  * reader that answers a βη normal form N of a closed T only when T ⊑ N
  * answers only N with T ⊑_O N, since T + N = T is then derivable and every
  * equation ⊢ derives holds up to ≃_O. Under known extremes the
  * steps for a listed term hold up to ≃_O, which contains ⊢ and is a
  * congruence, so T ⊑_O P ⊑_O N, and N is an answer by the primary
  * definition.
  *
  * FIXME (2026-10-10, carried from weak_head.pl:79): Readback.readbackSound https://github.com/Atry/private-overlay/issues/1949
  * is proved for the IR, whose finite terms have no free variable, and a
  * neutral value is no IR term. That a beta clause applied to a thunk
  * holding a neutral value in a slot reads back to a β step of the open
  * term, the neutral value read as its variable, is the same substitution
  * with a free variable in place of a closed term; it is argued here on
  * paper and not stated in Lean. Candidate fix: a variable leaf in Lean's
  * FiniteTerm (one of the routes listed under D3 of `lean/README.md`) and readbackSound
  * restated over it.
  *
  * ANSWERS ARE A SET; their order is a function of the term under weak_head:
  * each choice's members left to right, depth first, and for a parallel
  * each parallel set of its left side with each of its right side, the same
  * in every run (the calculus does not see that order, A + B = B + A by (1),
  * but every parallel set found is an answer, so a caller may stop at the
  * first one that answers its question, and the witness reading of
  * `Reading` does). Under tabling(weak_head) the parallel sets of a
  * completed table come in the order they were first found, a function of
  * the computation, which a caller does not stop on either.
  *
  * STEPS. Every evaluation is bounded by a budget of steps (`Budget`), a
  * count that is the same on every run: the evaluator is a pure function of
  * the term and the state. A STEP is:
  *   - under weak_head: one layer of a term read and dispatched by its
  *     constructor, or one head applied to one argument;
  *   - under tabling(weak_head): one call of the tabled function, answered
  *     from its table or evaluated, one head applied to one argument, or one
  *     parallel of two parallel sets made (a parallel of two sides that have
  *     m and n parallel sets is m times n steps, taken before any is made:
  *     MEASURED 2026-11-11, with no step for it a tabled reading of
  *     `ParallelSetLawTest` within 20,000 steps ran out of a 256 MB heap
  *     after 75 s, in the products of two large answer sets).
  * Building an instance takes no step of its own: it happens once per step
  * and costs at most the size of a code of the program. A step is taken before the
  * work it counts; a computation whose next step would pass the limit stops
  * there (`Computed.Stopped`). Under tabling(weak_head) a reading also
  * stops when a new table would pass its table limit
  * (`ReadingState.tableLimit`), the state then naming the resource
  * (`ReadingState.exhausted`).
  *
  * APPLICATIONS COUNTED. A reading asked to count them
  * (`ReadingState.codeApplications`, which `ReadingExecutor` sets when its
  * budget says `countedUnits`) counts one application of a code each time
  * the machine enters an instance of it: a thunk of the code whose holes are
  * all filled is replaced by the code's body under its fillings. Under
  * weak_head that is a thunk with no hole evaluated. Under tabling(weak_head)
  * it is a thunk with no hole read as a key's body, a head applied to its last
  * argument (the instance it gives is the thunk's body at once), and under
  * `ContinuationReading.Packed` a head walked applied to its pack, a fallback
  * taken (`BodyGoal.FallbackChecked`) and a step's continuation walked with
  * its fields. A pack (`pack`), a closed term the reader makes under
  * `Packed`, is counted under its code like any thunk when a program applies
  * its tuple to the last argument; its code is a body over slots like any
  * other, so the count joins that of any code of the term spelled alike. An
  * instance answered from a table afterwards is counted all
  * the same, since the table is looked up by the body; a thunk answered from
  * its own table is not replaced, and so not counted. The counts are costs, a
  * part of what this approximation does, and never decide anything here: a
  * reading counts or not and takes the same steps, tables and answers.
  *
  * MODES (9.2). weak_head evaluates with no table, by a machine whose state
  * is a stack of goals and choice points (lists on the heap): a goal is a
  * term with the arguments its heads are still to be applied to, so a run
  * that re-enters the same term, as Omega's does, grows nothing, and a run
  * whose function positions nest grows the list of arguments; a parallel is
  * a goal that holds the goals of its left side, and for each parallel set
  * of that side a goal that holds the goals of its right side. A parallel
  * one of whose sides is a run without end does not end. tabling(weak_head)
  * tables every evaluation of a term (`Tabling`), keyed by the term, an
  * interned value: an evaluation that
  * re-enters a term under evaluation reads that term's table, so a term
  * whose evaluation only re-enters itself has no head and the evaluation
  * completes (Omega), and a cyclic program whose evaluations reach finitely
  * many terms completes. The tables are the evaluator's alone.
  *
  * Departures from the Prolog evaluator: the tables are values in the reading's state, not
  * SWI-Prolog's tables, so there is nothing to drop; the reading's store of
  * the Prolog evaluator has no counterpart, every value being interned in the
  * process's pool (2026-11-15); a thunk's code is always a code; a Prolog
  * term of no constructor of the IR has no counterpart, the values being
  * typed.
  */
object WeakHead:

  // ---- the heads of a term ----

  /** The parallel sets of the closed term under the mode, one at a time, in
    * the mode's order: under weak_head the term's own order, each parallel
    * set as found (one may be found more than once); under
    * tabling(weak_head) those of the term's table, each once, in the same
    * order, each as soon as it is found and before the table completes
    * (`Tabling`); under jit the JIT's. The evaluation knows the extremes of the reading's
    * state (KNOWN EXTREMES).
    */
  def heads[C <: NativeSpecializer & Singleton](mode: Mode, term: Value[C])(using C): Answers[ReadingState[C], ParallelSet[C]] = mode match
    case Mode.WeakHead => untabledHeads(term)
    case Mode.TablingWeakHead => called(term, tabling.answers)
    case Mode.Jit =>
      Answers.computed(Computation.state[ReadingState[C]].map(state => Vector(state.configuration.jit))).flatMap {
        case Some(evaluator) => evaluator.heads(term)
        case None            => throw IllegalStateException("a reading under the JIT whose configuration holds no JIT")
      }

  /** The answers reduced by the rule bottom + M = bottom (KNOWN EXTREMES):
    * the empty parallel set alone when the answers hold it, the answers as
    * they are otherwise. For a caller that states a finished evaluation's
    * value; a caller that reads answers out keeps the others, each of which
    * is an answer.
    */
  def bottomAbsorbed[C <: NativeSpecializer & Singleton](heads: Vector[ParallelSet[C]])(using C): Vector[ParallelSet[C]] =
    if heads.exists(_.isBottom) then Vector(ParallelSet.bottom[C]) else heads

  // ---- known extremes ----

  /** A greatest or a least term of ⊑_O. */
  private enum Extreme:
    case Top
    case Bottom

  /** Whether the term is a listed top or a listed bottom of the state's
    * known extremes: nothing when none is listed, or when the term is
    * neither. A term spells a listed one exactly when it equals it. Every
    * value is interned and the extremes are held by the state, so they stay
    * reachable and canonical for the whole reading, and `==` ends at `eq` or
    * at a differing hash code, whatever the term's size.
    */
  private def knownExtreme[C <: NativeSpecializer & Singleton](term: Value[C], state: ReadingState[C])(using C): Option[Extreme] =
    val extremes = state.extremes
    if extremes.isEmpty then None
    else if extremes.top(term) then Some(Extreme.Top)
    else if extremes.bottom(term) then Some(Extreme.Bottom)
    else None

  /** Under `ApplicationReading.BySpine`, the listed top or bottom that is
    * the longest proper prefix of a spine of at least one argument: the
    * spine's head applied to its first k arguments, k at least one and less
    * than their number, found by comparing the listed term's own head and
    * arguments with the spine's. The whole spine and its head are compared
    * where each is evaluated (`knownExtreme`), so with the prefixes compared
    * here the extremes are met in the order `ApplicationReading.ByLayer`
    * meets them, a top before a bottom of the same length.
    */
  private def knownPrefix[C <: NativeSpecializer & Singleton](head: Value[C], arguments: Vector[Value[C]], state: ReadingState[C])(using C): Option[Extreme] =
    val extremes = state.extremes
    if extremes.isEmpty then None
    else
      // The length of the proper prefix the listed term spells, 0 for none; a loop over indices, so that a
      // spine read allocates nothing when no listed term is a prefix of it, as `knownExtreme`'s `contains`
      // allocates nothing (the collections this replaced cost 97,000 to 205,000 B/op of the untabled knowledge
      // reading, measured 2026-11-20).
      // A listed term is pure, one object under every configuration: its arguments are compared with the spine's as
      // objects.
      def prefixLength(listed: gezi.ir.Pure): Int = listed.representation.layer match
        case application @ gezi.ir.Apply(_, _) =>
          val listedArguments = application.spineArguments
          @scala.annotation.tailrec
          def matched(index: Int): Boolean =
            index == listedArguments.size || ((listedArguments(index): AnyRef) eq arguments(index).representation) && matched(index + 1)
          if listedArguments.size < arguments.size && matched(0) then listedArguments.size else 0
        case _ => 0
      @scala.annotation.tailrec
      def longest(listed: Vector[gezi.ir.Pure], index: Int, found: Int): Int =
        if index == listed.size then found else longest(listed, index + 1, found.max(prefixLength(listed(index))))
      val top = longest(extremes.tops, 0, 0)
      val bottom = longest(extremes.bottoms, 0, 0)
      if top == 0 && bottom == 0 then None
      else if top >= bottom then Some(Extreme.Top)
      else Some(Extreme.Bottom)

  // ---- weak_head: the untabled evaluation ----

  /** A goal of the untabled machine:
    *   - the parallel sets of a term applied to the arguments in order;
    *   - those of the members of the right spine of a choice's right side,
    *     each applied to the arguments, the choice point: the spine is taken
    *     apart one choice at a time as the goal runs, never collected, so a
    *     reading that leaves a long choice early pays for the members it
    *     reached and not for the rest;
    *   - the parallel of each parallel set the left goals give with each one
    *     of the right term applied to the arguments: the arguments go to both
    *     sides of a parallel, by equation (9), so a parallel set found is
    *     applied to nothing more;
    *   - the parallel of one parallel set with each one the right goals give.
    */
  private enum Goal[C <: NativeSpecializer & Singleton]:
    case Evaluation(term: Value[C], arguments: List[Value[C]])
    case RemainingMembers(remaining: Value[C], arguments: List[Value[C]])
    case ParallelLeft(left: List[Goal[C]], right: Value[C], arguments: List[Value[C]])
    case ParallelRight(leftSet: ParallelSet[C], right: List[Goal[C]])

  /** The untabled machine: the goals still to be run, the next first. */
  private final case class HeadMachine[C <: NativeSpecializer & Singleton](goals: List[Goal[C]])

  /** What the machine run to its next parallel set gives: the set and the
    * machine after it, or nothing when no goal is left.
    */
  private type Pulled[C <: NativeSpecializer & Singleton] = Computed[ReadingState[C], Option[(ParallelSet[C], HeadMachine[C])]]

  /** The parallel sets of the term, the term's own order: each choice's
    * members left to right, and for a parallel each parallel set of its
    * left side with each of its right side, the right side evaluated again
    * for each.
    */
  private def untabledHeads[C <: NativeSpecializer & Singleton](term: Value[C])(using C): Answers[ReadingState[C], ParallelSet[C]] =
    machineHeads(HeadMachine(List(Goal.Evaluation(term, Nil))))

  private def machineHeads[C <: NativeSpecializer & Singleton](machine: HeadMachine[C])(using C): Answers[ReadingState[C], ParallelSet[C]] =
    Answers(Computation(state =>
      nextHead(machine.goals, state).map {
        case Computed.Done(Some((set, rest)), after) =>
          Computed.Done(Some((set, machineHeads(rest))), after)
        case Computed.Done(None, after) => Computed.Done(None, after)
        case Computed.Stopped(stopped)  => Computed.Stopped(stopped)
      }
    ))

  /** The machine run to its next parallel set. A run that only re-enters
    * terms, as Omega's does, is a loop of the trampoline and grows nothing;
    * a run whose function positions nest grows the list of arguments; a
    * choice leaves a goal for the members after the one taken, and none
    * after its last.
    */
  private def nextHead[C <: NativeSpecializer & Singleton](goals: List[Goal[C]], state: ReadingState[C])(using C): Trampoline[Pulled[C]] = goals match
    case Nil => done(Computed.Done(None, state))
    case Goal.RemainingMembers(remaining, arguments) :: rest =>
      remaining match
        case Value.Choice(member, later) =>
          tailcall(nextHead(Goal.Evaluation(member, arguments) :: Goal.RemainingMembers(later, arguments) :: rest, state))
        case last => tailcall(nextHead(Goal.Evaluation(last, arguments) :: rest, state))
    case Goal.ParallelLeft(left, right, arguments) :: rest =>
      tailcall(nextHead(left, state)).flatMap {
        case Computed.Stopped(stopped)  => done(Computed.Stopped(stopped))
        case Computed.Done(None, after) => tailcall(nextHead(rest, after))
        case Computed.Done(Some((leftSet, leftRest)), after) =>
          val remaining =
            if leftRest.goals.isEmpty then rest
            else Goal.ParallelLeft(leftRest.goals, right, arguments) :: rest
          tailcall(
            nextHead(Goal.ParallelRight(leftSet, List(Goal.Evaluation(right, arguments))) :: remaining, after)
          )
      }
    case Goal.ParallelRight(leftSet, right) :: rest =>
      tailcall(nextHead(right, state)).flatMap {
        case Computed.Stopped(stopped)  => done(Computed.Stopped(stopped))
        case Computed.Done(None, after) => tailcall(nextHead(rest, after))
        case Computed.Done(Some((rightSet, rightRest)), after) =>
          val remaining =
            if rightRest.goals.isEmpty then rest
            else Goal.ParallelRight(leftSet, rightRest.goals) :: rest
          done(Computed.Done(Some((leftSet.parallel(rightSet), HeadMachine(remaining))), after))
      }
    case Goal.Evaluation(goalTerm, arguments) :: rest =>
      state.budget.charged match
        case None => done(Computed.Stopped(state))
        case Some(charged) =>
          val (term, stepped) = uriExpanded(goalTerm, state.copy(budget = charged))
          knownExtreme(term, stepped) match
            case Some(Extreme.Top) => tailcall(nextHead(rest, stepped))
            case Some(Extreme.Bottom) =>
              done(Computed.Done(Some((ParallelSet.bottom, HeadMachine(rest))), stepped))
            case None =>
              nativeResult(term, stepped) match
                case Some((result, called)) => tailcall(nextHead(Goal.Evaluation(result, arguments) :: rest, called))
                case None =>
                  storageEliminated(term, stepped) match
                    case Value.Thunk(code, holes, fillings) if holes.nonEmpty =>
                      arguments match
                        case Nil =>
                          done(
                            Computed.Done(
                              Some((ParallelSet.single(Head.Lambda(code, holes, fillings)), HeadMachine(rest))),
                              stepped
                            )
                          )
                        case argument :: later =>
                          argumentTaken(
                            thunkOrSuspension(code, holes.tail, holeFilled(holes.head, holes.tail, fillings, argument)),
                            later,
                            rest,
                            stepped
                          )
                    case SuspensionValue(code, fillings) =>
                      tailcall(nextHead(Goal.Evaluation(instanceTerm(code, fillings, stepped.specializer), arguments) :: rest, stepped.entered(code)))
                    case Value.Apply(function, argument) =>
                      stepped.applications match
                        case ApplicationReading.ByLayer =>
                          tailcall(nextHead(Goal.Evaluation(function, argument :: arguments) :: rest, stepped))
                        case ApplicationReading.BySpine | ApplicationReading.BySharedPrefix =>
                          val (head, spineArguments) = Value.Spine.of(term)
                          knownPrefix(head, spineArguments, stepped) match
                            case Some(Extreme.Top) => tailcall(nextHead(rest, stepped))
                            case Some(Extreme.Bottom) =>
                              done(Computed.Done(Some((ParallelSet.bottom, HeadMachine(rest))), stepped))
                            case None =>
                              tailcall(nextHead(Goal.Evaluation(head, spineArguments.foldRight(arguments)(_ :: _)) :: rest, stepped))
                    case Value.Choice(member, later) =>
                      tailcall(nextHead(Goal.Evaluation(member, arguments) :: Goal.RemainingMembers(later, arguments) :: rest, stepped))
                    case Value.Parallel(left, right) =>
                      tailcall(
                        nextHead(
                          Goal.ParallelLeft(List(Goal.Evaluation(left, arguments)), right, arguments) :: rest,
                          stepped
                        )
                      )
                    case NeutralValue(variable, neutralArguments) =>
                      arguments match
                        case Nil =>
                          done(
                            Computed.Done(
                              Some((ParallelSet.single(Head.Neutral(variable, neutralArguments)), HeadMachine(rest))),
                              stepped
                            )
                          )
                        case argument :: later =>
                          argumentTaken(NeutralValue(variable, neutralArguments :+ argument), later, rest, stepped)
                    case opaque =>
                      throw IllegalStateException(s"the opaque $opaque has no layer")

  /** A head applied to its first argument, one step: the result applied to
    * the arguments after it is the next goal.
    */
  private def argumentTaken[C <: NativeSpecializer & Singleton](
      result: Value[C],
      later: List[Value[C]],
      rest: List[Goal[C]],
      state: ReadingState[C]
  )(using C): Trampoline[Pulled[C]] =
    state.budget.charged match
      case None          => done(Computed.Stopped(state))
      case Some(charged) => tailcall(nextHead(Goal.Evaluation(result, later) :: rest, state.copy(budget = charged)))

  // ---- tabling(weak_head) ----

  /** The tabled function, as the body sees it. */
  private type TabledCall[C <: NativeSpecializer & Singleton] = Value[C] => Answers[ReadingState[C], ParallelSet[C]]

  private def tabling[C <: NativeSpecializer & Singleton](using C): Tabling[ReadingState[C], Value[C], ParallelSet[C]] =
    Tabling(_.tables, (state, tables) => state.copy(tables = tables), state => state.sharing.completedTables(state), tabledBody[C])

  /** The parallel sets of the value's table, each as it is found: one step,
    * then the tabled function called on the value, an interned term and so
    * a key of fixed cost.
    */
  private def called[C <: NativeSpecializer & Singleton](value: Value[C], call: TabledCall[C])(using C): Answers[ReadingState[C], ParallelSet[C]] =
    bodyAnswers(List(BodyGoal.Called(value, Nil)), call)

  /** Whether the reading may hold one more table for the key: it holds one
    * already, or fewer than its table limit.
    */
  private def tableAllowed[C <: NativeSpecializer & Singleton](key: Value[C], state: ReadingState[C])(using C): Boolean =
    val tables = state.tables
    tables.complete.contains(key) || tables.open.contains(key) ||
      tables.complete.size + tables.open.size < state.tableLimit

  /** The parallel sets of the layer of an identifier (THE RULES and KNOWN
    * EXTREMES), each evaluation of a part a call of the tabled function, in
    * the term's own order, each as it is found. The body is monotone, as
    * `Tabling` asks: a union, or a ⊗, of what larger answer sets give is
    * larger.
    */
  private def tabledBody[C <: NativeSpecializer & Singleton](key: Value[C], call: TabledCall[C])(using C): Answers[ReadingState[C], ParallelSet[C]] =
    Answers(Computation.state[ReadingState[C]].flatMap(found =>
      val (term, state) = uriExpanded(key, found)
      Computation.replaced(state).flatMap(_ => bodyAnswers(List(BodyGoal.Read(term, Nil)), call).pull)
    ))

  /** A goal of a tabled body's machine: the body is a stack of goals, the first run first, and what is to be done with the
    * parallel set a goal gives is a list of frames, the first applied first, in place of the closures
    * that `Answers.flatMap` built, one per answer and layer. The steps, the table limit's checks and
    * the order of the answers are those the combinators gave: each goal and frame below is one of
    * them, named in its Scaladoc.
    */
  private enum BodyGoal[C <: NativeSpecializer & Singleton]:

    /** The body of the key read as the term, a URI node expanded already:
      * a choice's members left to right; an application's function's
      * parallel sets, each applied to the argument; a parallel's left
      * side's parallel sets, each with every parallel set of its right side,
      * the right side called again for each, as the untabled machine
      * evaluates it again.
      */
    case Read(term: Value[C], after: List[BodyFrame[C]])

    /** The value's table: one step, the table limit checked, then the
      * tabled function called on the value.
      */
    case Called(value: Value[C], after: List[BodyFrame[C]])

    /** Each member of the right spine of a choice's right side called, as
      * `Called` calls it, left to right: the spine is taken apart one choice
      * at a time as the goal runs, with no step of its own, never collected,
      * so a reading that leaves a long choice early pays for the members it
      * reached and not for the rest.
      */
    case RemainingMembers(remaining: Value[C], after: List[BodyFrame[C]])

    /** The answers of a call still to be taken, each given to the frames. */
    case Consumed(answers: Answers[ReadingState[C], ParallelSet[C]], after: List[BodyFrame[C]])

    /** The answers of a complete table from the index on, each given to the
      * frames, read by index: what `Tabling.consumed` gives for a complete
      * table, the answers in their order and nothing else, without the stream
      * it builds, a closure for each answer (JFR, 2026-11-19).
      */
    case Listed(answers: Vector[ParallelSet[C]], index: Int, after: List[BodyFrame[C]])

    /** A parallel set given to the frames. */
    case Delivered(set: ParallelSet[C], after: List[BodyFrame[C]])

    /** The ⊗ of what each of the heads, at least one, gives applied to the
      * argument, the first head's parallel sets outermost.
      */
    case HeadsApplied(heads: Vector[Head[C]], argument: Value[C], after: List[BodyFrame[C]])

    /** The parallel sets of a head applied to the argument, one step. */
    case HeadApplied(head: Head[C], argument: Value[C], after: List[BodyFrame[C]])

    /** The parallel sets of the code under the fillings, the slot's filling
      * the pack of the code's tail plan (`ContinuationReading.Packed`),
      * read by walking the plan: a tail `pack M1 … Mn` evaluated as it is;
      * both sides of a choice or a parallel walked; a step's function
      * called and checked (`BodyFrame.StepFunction`). `head` is the head
      * whose shared table this is, marked unverified when a branch is
      * dropped.
      */
    case Walked(code: Code, fillings: Vector[Value[C]], slot: Int, head: Value[C], after: List[BodyFrame[C]])

    /** After a consumer has taken the shared answers of its head applied to
      * the pack: the head applied to the continuation by the β rule as well,
      * when the head has been marked unverified (`ReadingState.unverified`).
      */
    case FallbackChecked(head: Value[C], code: Code, filled: Vector[Value[C]], after: List[BodyFrame[C]])

  /** What is done with a parallel set a goal gives. */
  private enum BodyFrame[C <: NativeSpecializer & Singleton]:

    /** A function's parallel set applied to the argument: the ⊗ of what each
      * of its heads gives, by equation (9); the empty parallel set gives
      * itself, the ⊗ of nothing.
      */
    case SetApplied(argument: Value[C])

    /** A parallel's left side's parallel set: the right side called, each of
      * its parallel sets in parallel with this one.
      */
    case RightCalled(right: Value[C])

    /** A parallel set in parallel with the left one, one step for each
      * parallel made (STEPS).
      */
    case Paralleled(left: ParallelSet[C])

    /** The first head's parallel set: the other heads' parallel sets, each
      * in parallel with it.
      */
    case OthersApplied(others: Vector[Head[C]], argument: Value[C])

    /** A walked parallel's left side's parallel set: the right side walked,
      * each of its parallel sets in parallel with this one.
      */
    case RightWalked(code: Code, fillings: Vector[Value[C]], slot: Int, head: Value[C])

    /** A parallel set of a walked step's function: when it is one head
      * `λc'. S'` whose tail plan has the continuation's arity, the shared
      * table of that head applied to its pack is called, its answers given
      * to `StepFields`; the empty parallel set gives itself; any other set
      * drops the branch and marks the walked head unverified.
      */
    case StepFunction(continuation: Continuation[C], head: Value[C])

    /** A parallel set of a checked step's function applied to its pack: a
      * pack's tuple, whose fields the continuation takes, its code then
      * walked; the empty parallel set gives itself; any other set drops the
      * branch and marks the walked head unverified.
      */
    case StepFields(continuation: Continuation[C], head: Value[C])

  /** The continuation of a walked step, `λx1 … xm. R`: its code, holes and
    * fillings, and the slot of its code that holds the pack passed on.
    */
  private final case class Continuation[C <: NativeSpecializer & Singleton](code: Code, holes: Vector[Hole], fillings: Vector[Value[C]], slot: Int)

  private type BodyPulled[C <: NativeSpecializer & Singleton] =
    Trampoline[Computed[ReadingState[C], Option[(ParallelSet[C], Answers[ReadingState[C], ParallelSet[C]])]]]

  /** The parallel sets the goals give, each as it is found. */
  private def bodyAnswers[C <: NativeSpecializer & Singleton](goals: List[BodyGoal[C]], call: TabledCall[C])(using C): Answers[ReadingState[C], ParallelSet[C]] =
    Answers(Computation(state => bodyPulled(goals, state, call)))

  /** The goals run to their next parallel set, the goals left after it, or to
    * their end. A loop of the trampoline: a goal pushes the goals it leads to
    * on the stack.
    */
  private def bodyPulled[C <: NativeSpecializer & Singleton](goals: List[BodyGoal[C]], state: ReadingState[C], call: TabledCall[C])(using C): BodyPulled[C] = goals match
    case Nil => done(Computed.Done(None, state))
    case goal :: rest =>
      goal match
        case BodyGoal.Delivered(set, Nil) => done(Computed.Done(Some((set, bodyAnswers(rest, call))), state))
        case BodyGoal.Delivered(set, frame :: after) =>
          frame match
            case BodyFrame.SetApplied(argument) =>
              set.heads match
                case Vector() => tailcall(bodyPulled(BodyGoal.Delivered(ParallelSet.bottom, after) :: rest, state, call))
                case heads    => tailcall(bodyPulled(BodyGoal.HeadsApplied(heads, argument, after) :: rest, state, call))
            case BodyFrame.RightCalled(right) =>
              tailcall(bodyPulled(BodyGoal.Called(right, BodyFrame.Paralleled(set) :: after) :: rest, state, call))
            case BodyFrame.Paralleled(left) =>
              state.budget.charged match
                case None => done(Computed.Stopped(state))
                case Some(charged) =>
                  val stepped = state.copy(budget = charged)
                  state.parallels match
                    case ParallelReading.BothSides =>
                      tailcall(bodyPulled(BodyGoal.Delivered(left.parallel(set), after) :: rest, stepped, call))
                    case ParallelReading.HeadsMet =>
                      headsMet(left.parallel(set), state.specializer) match
                        case Some(met) => tailcall(bodyPulled(BodyGoal.Delivered(met, after) :: rest, stepped, call))
                        case None      => tailcall(bodyPulled(rest, stepped, call))
            case BodyFrame.OthersApplied(others, argument) =>
              tailcall(bodyPulled(BodyGoal.HeadsApplied(others, argument, BodyFrame.Paralleled(set) :: after) :: rest, state, call))
            case BodyFrame.RightWalked(code, fillings, slot, head) =>
              tailcall(bodyPulled(BodyGoal.Walked(code, fillings, slot, head, BodyFrame.Paralleled(set) :: after) :: rest, state, call))
            case BodyFrame.StepFunction(continuation, head) =>
              val arity = continuation.holes.size
              set.heads match
                case Vector() => tailcall(bodyPulled(BodyGoal.Delivered(ParallelSet.bottom, after) :: rest, state, call))
                case Vector(Head.Lambda(stepCode, stepHoles @ Vector(Hole.Bound(stepSlot)), stepFillings))
                    if Code.tailPlans(stepCode).get(stepSlot).exists(_.arity == arity) &&
                      !state.unverified.contains(Value.Thunk(stepCode, stepHoles, stepFillings)) =>
                  val shared = Value.Apply(Value.Thunk(stepCode, stepHoles, stepFillings), pack(arity))
                  tailcall(bodyPulled(BodyGoal.Called(shared, BodyFrame.StepFields(continuation, head) :: after) :: rest, state, call))
                case _ => tailcall(bodyPulled(rest, state.copy(unverified = state.unverified + head), call))
            case BodyFrame.StepFields(continuation, head) =>
              val arity = continuation.holes.size
              set.heads match
                case Vector() => tailcall(bodyPulled(BodyGoal.Delivered(ParallelSet.bottom, after) :: rest, state, call))
                case Vector(tuple) =>
                  packFields(tuple, arity) match
                    case Some(fields) =>
                      chargedTimes(state.budget, arity) match
                        case None => done(Computed.Stopped(state))
                        case Some(budget) =>
                          val (_, filled) = fields.foldLeft((continuation.holes, continuation.fillings)) { case ((holes, fillings), field) =>
                            (holes.tail, holeFilled(holes.head, holes.tail, fillings, field))
                          }
                          val walked = BodyGoal.Walked(continuation.code, filled, continuation.slot, head, after)
                          tailcall(bodyPulled(walked :: rest, state.copy(budget = budget).entered(continuation.code), call))
                    case None => tailcall(bodyPulled(rest, state.copy(unverified = state.unverified + head), call))
                case _ => tailcall(bodyPulled(rest, state.copy(unverified = state.unverified + head), call))
        case BodyGoal.RemainingMembers(remaining, after) =>
          remaining match
            case Value.Choice(member, later) =>
              tailcall(bodyPulled(BodyGoal.Called(member, after) :: BodyGoal.RemainingMembers(later, after) :: rest, state, call))
            case last => tailcall(bodyPulled(BodyGoal.Called(last, after) :: rest, state, call))
        case BodyGoal.Called(value, after) =>
          state.budget.charged match
            case None => done(Computed.Stopped(state))
            case Some(charged) =>
              val stepped = state.copy(budget = charged)
              if !tableAllowed(value, stepped) then done(Computed.Stopped(stepped.copy(exhausted = Some(Resource.Tables))))
              else
                stepped.tables.complete.get(value) match
                  case Some(complete) => tailcall(bodyPulled(BodyGoal.Listed(complete.ordered, 0, after) :: rest, stepped, call))
                  case None           => tailcall(bodyPulled(BodyGoal.Consumed(call(value), after) :: rest, stepped, call))
        case BodyGoal.Listed(answers, index, after) =>
          if index >= answers.size then tailcall(bodyPulled(rest, state, call))
          else tailcall(bodyPulled(BodyGoal.Delivered(answers(index), after) :: BodyGoal.Listed(answers, index + 1, after) :: rest, state, call))
        case BodyGoal.Consumed(answers, after) =>
          tailcall(answers.pull.run(state)).flatMap {
            case Computed.Stopped(stopped) => done(Computed.Stopped(stopped))
            case Computed.Done(None, pulledState) => tailcall(bodyPulled(rest, pulledState, call))
            case Computed.Done(Some((set, more)), pulledState) =>
              tailcall(bodyPulled(BodyGoal.Delivered(set, after) :: BodyGoal.Consumed(more, after) :: rest, pulledState, call))
          }
        case BodyGoal.HeadsApplied(heads, argument, after) =>
          heads match
            case Vector(single) => tailcall(bodyPulled(BodyGoal.HeadApplied(single, argument, after) :: rest, state, call))
            case first +: others =>
              tailcall(bodyPulled(BodyGoal.HeadApplied(first, argument, BodyFrame.OthersApplied(others, argument) :: after) :: rest, state, call))
            case _ => throw IllegalStateException("no head to apply")
        case BodyGoal.HeadApplied(head, argument, after) =>
          state.budget.charged match
            case None => done(Computed.Stopped(state))
            case Some(charged) =>
              val stepped = state.copy(budget = charged)
              head match
                case Head.Lambda(code, holes, fillings) =>
                  val filled = holeFilled(holes.head, holes.tail, fillings, argument)
                  if holes.tail.nonEmpty then
                    tailcall(bodyPulled(BodyGoal.Delivered(ParallelSet.single(Head.Lambda(code, holes.tail, filled)), after) :: rest, stepped, call))
                  else
                    val goals = lastApplied(code, holes, fillings, filled, argument, after, stepped)
                    tailcall(bodyPulled(goals ::: rest, lastEntered(code, goals, stepped), call))
                case Head.Neutral(variable, arguments) =>
                  tailcall(bodyPulled(BodyGoal.Delivered(ParallelSet.single(Head.Neutral(variable, arguments :+ argument)), after) :: rest, stepped, call))
                case other => throw IllegalStateException(s"a head is a thunk or a neutral value, not $other")
        case BodyGoal.Walked(code, fillings, slot, head, after) =>
          val next = code.layer match
            case gezi.ir.Choice(left, right) =>
              List(BodyGoal.Walked(left, fillings, slot, head, after), BodyGoal.Walked(right, fillings, slot, head, after))
            case gezi.ir.Parallel(left, right) =>
              List(BodyGoal.Walked(left, fillings, slot, head, BodyFrame.RightWalked(right, fillings, slot, head) :: after))
            case gezi.ir.Apply(function, argument) if spineHead(code).layer != gezi.ir.Slot(slot) =>
              argument.layer match
                case gezi.ir.Thunk(inner, holes, innerFillings) =>
                  val index = Code
                    .passedFilling(innerFillings, slot)
                    .getOrElse(throw IllegalStateException(s"a walked step passes no bare slot $slot on"))
                  val continuation =
                    Continuation(inner, holes, innerFillings.map(instanceTerm(_, fillings, state.specializer)), Code.filledSlot(inner, holes, innerFillings.size, index))
                  List(BodyGoal.Called(instanceTerm(function, fillings, state.specializer), BodyFrame.StepFunction(continuation, head) :: after))
                case other => throw IllegalStateException(s"a walked step's argument is a thunk, not $other")
            case _ => List(BodyGoal.Called(instanceTerm(code, fillings, state.specializer), after))
          tailcall(bodyPulled(next ::: rest, state, call))
        case BodyGoal.FallbackChecked(head, code, filled, after) =>
          if state.unverified.contains(head) then
            tailcall(bodyPulled(BodyGoal.Called(instanceTerm(code, filled, state.specializer), after) :: rest, state.entered(code), call))
          else tailcall(bodyPulled(rest, state, call))
        case BodyGoal.Read(term, after) =>
          knownExtreme(term, state) match
            case Some(Extreme.Top)    => tailcall(bodyPulled(rest, state, call))
            case Some(Extreme.Bottom) => tailcall(bodyPulled(BodyGoal.Delivered(ParallelSet.bottom, after) :: rest, state, call))
            case None =>
              nativeResult(term, state) match
                case Some((result, called)) => tailcall(bodyPulled(BodyGoal.Read(result, after) :: rest, called, call))
                case None =>
                  storageEliminated(term, state) match
                    case Value.Thunk(code, holes, fillings) if holes.nonEmpty =>
                      tailcall(bodyPulled(BodyGoal.Delivered(ParallelSet.single(Head.Lambda(code, holes, fillings)), after) :: rest, state, call))
                    case Value.Thunk(code, _, fillings) =>
                      tailcall(bodyPulled(BodyGoal.Called(instanceTerm(code, fillings, state.specializer), after) :: rest, state.entered(code), call))
                    case Value.Apply(function, argument) =>
                      state.applications match
                        case ApplicationReading.ByLayer =>
                          tailcall(bodyPulled(BodyGoal.Called(function, BodyFrame.SetApplied(argument) :: after) :: rest, state, call))
                        case ApplicationReading.BySpine =>
                          val (head, spineArguments) = Value.Spine.of(term)
                          knownPrefix(head, spineArguments, state) match
                            case Some(Extreme.Top) => tailcall(bodyPulled(rest, state, call))
                            case Some(Extreme.Bottom) =>
                              tailcall(bodyPulled(BodyGoal.Delivered(ParallelSet.bottom, after) :: rest, state, call))
                            case None =>
                              val frames = spineArguments.foldRight(after)((spineArgument, later) => BodyFrame.SetApplied(spineArgument) :: later)
                              tailcall(bodyPulled(BodyGoal.Called(head, frames) :: rest, state, call))
                        case ApplicationReading.BySharedPrefix =>
                          val (head, spineArguments) = Value.Spine.of(term)
                          knownPrefix(head, spineArguments, state) match
                            case Some(Extreme.Top) => tailcall(bodyPulled(rest, state, call))
                            case Some(Extreme.Bottom) =>
                              tailcall(bodyPulled(BodyGoal.Delivered(ParallelSet.bottom, after) :: rest, state, call))
                            case None =>
                              val (length, prefix, spinePrefixes) = sharedPrefix(term, head, spineArguments.size, state)
                              val frames =
                                spineArguments.drop(length).foldRight(after)((spineArgument, later) => BodyFrame.SetApplied(spineArgument) :: later)
                              tailcall(bodyPulled(BodyGoal.Called(prefix, frames) :: rest, state.copy(spinePrefixes = spinePrefixes), call))
                    case Value.Choice(member, later) =>
                      tailcall(bodyPulled(BodyGoal.Called(member, after) :: BodyGoal.RemainingMembers(later, after) :: rest, state, call))
                    case Value.Parallel(left, right) =>
                      tailcall(bodyPulled(BodyGoal.Called(left, BodyFrame.RightCalled(right) :: after) :: rest, state, call))
                    case NeutralValue(variable, arguments) =>
                      tailcall(bodyPulled(BodyGoal.Delivered(ParallelSet.single(Head.Neutral(variable, arguments)), after) :: rest, state, call))
                    case opaque => throw IllegalStateException(s"the opaque $opaque has no layer")

  /** The parallel set met head by head (`ParallelReading.HeadsMet`): the
    * lambda heads of one code and one list of holes merged into one, whose
    * fillings are the parallels of theirs, a filling the heads share kept as
    * it is; and nothing, the set dropped, when two of its lambda heads have
    * as many holes and their codes' bodies are applications of two different
    * of their binders. Neutral heads are kept as they are.
    */
  private def headsMet[C <: NativeSpecializer & Singleton](set: ParallelSet[C], specializer: C)(using C): Option[ParallelSet[C]] =
    val merged = set.heads.foldLeft(Vector.empty[Head[C]])((kept, head) =>
      head match
        case Head.Lambda(code, holes, fillings) =>
          kept.indexWhere {
            case Head.Lambda(keptCode, keptHoles, _) => keptCode == code && keptHoles == holes
            case _                                   => false
          } match
            case -1 => kept :+ head
            case index =>
              kept(index) match
                case Head.Lambda(_, _, keptFillings) =>
                  require(keptFillings.size == fillings.size, s"two thunks of one code and one list of holes have as many fillings")
                  val metFillings = keptFillings.zip(fillings).map(fillingsMet(_, _, specializer))
                  kept.updated(index, Head.Lambda(code, holes, metFillings))
                case other => throw IllegalStateException(s"the index found a lambda head, not $other")
        case _ => kept :+ head
    )
    val applied = merged.collect { case Head.Lambda(code, holes, _) => (holes.size, appliedBinder(code, holes)) }
    val clash = applied.exists { case (holeCount, binder) =>
      binder.nonEmpty && applied.exists { case (otherCount, otherBinder) =>
        otherCount == holeCount && otherBinder.nonEmpty && otherBinder != binder
      }
    }
    if clash then None else Some(ParallelSet.of(merged))

  /** The parallel of two fillings as the chain of the distinct sides of both,
    * in the order first met, nested to the right: equal to their parallel by
    * the λ-lattice laws (∥ associative, commutative and idempotent), and no
    * longer than the number of distinct sides. A filter met again at each
    * call of a recursion over its value, `(t ∥ LT) ∥ LT`, stays `t ∥ LT`
    * instead of growing by a side at each call (MEASURED 2026-11-21: with
    * the plain parallel, the filtered parity fold of
    * `ParallelReadingLawTest` took 3,166 steps at 32 elements and 10,187 at
    * 64).
    */
  private def fillingsMet[C <: NativeSpecializer & Singleton](first: Value[C], second: Value[C], specializer: C)(using C): Value[C] =
    // A storage is a leaf of its term's layer, so `Value.Parallel.unapply` never takes its view apart; a parallel is
    // built by the reading's specializer, so that meeting a storage with its own criterion keeps the storage.
    gezi.ir.ParallelChain.met[Value[C]](first, second, Value.Parallel.unapply, Value.Parallel(_, _))

  /** The binder, by its position among the holes, that the code's body is an
    * application of, or none when the spine's head is no binder of the
    * thunk (a filling, an abstraction, a choice or a parallel).
    */
  private def appliedBinder(code: Code, holes: Vector[Hole]): Option[Int] =
    spineHead(code).layer match
      case gezi.ir.Slot(slot) =>
        holes.indexOf(Hole.Bound(slot)) match
          case -1       => None
          case position => Some(position)
      case _ => None

  /** Under `ApplicationReading.BySharedPrefix`, the prefix of the spine, a key
    * read with `argumentCount` arguments after its head, that the key's body
    * calls through its table: its length k, the prefix `head a1 … ak`, and the
    * index of the keys' spines with the prefixes walked to find it. The
    * proper prefixes are walked from the longest down, each the function of
    * the one before, and the first that holds a table, complete or in
    * progress, or that an earlier key's spine went on from with another
    * argument, is the one; every prefix walked that the index does not hold
    * is entered with the argument this spine goes on with. The head, k = 0,
    * when none is. A walk of at most `argumentCount - 1` prefixes, the
    * applications `ByLayer` would take apart one by one, each a table look-up
    * and an index look-up of interned terms, so of fixed cost.
    */
  private def sharedPrefix[C <: NativeSpecializer & Singleton](term: Value[C], head: Value[C], argumentCount: Int, state: ReadingState[C])(using C): (Int, Value[C], Map[Value[C], Value[C]]) =
    val tables = state.tables
    @scala.annotation.tailrec
    def walked(longer: Value[C], length: Int, spinePrefixes: Map[Value[C], Value[C]]): (Int, Value[C], Map[Value[C], Value[C]]) =
      if length == 0 then (0, head, spinePrefixes)
      else
        longer.layer match
          case gezi.ir.Apply(prefix, next) =>
            if tables.complete.contains(prefix) || tables.open.contains(prefix) then
              (length, prefix, if spinePrefixes.contains(prefix) then spinePrefixes else spinePrefixes.updated(prefix, next))
            else
              spinePrefixes.get(prefix) match
                case Some(seen) if seen != next => (length, prefix, spinePrefixes)
                case Some(_)                    => walked(prefix, length - 1, spinePrefixes)
                case None                       => walked(prefix, length - 1, spinePrefixes.updated(prefix, next))
          case other => throw IllegalStateException(s"a spine of ${length + 1} more arguments is an application, not $other")
    walked(term, argumentCount - 1, state.spinePrefixes)

  /** The goals of a head with one hole left applied to its last argument
    * (`ContinuationReading`): under `Substituted`, or when the code has no
    * tail plan for the hole's slot through a step, the instance of the code
    * under the fillings. Under `Packed`, a head applied to the pack of its
    * plan's arity is walked (`BodyGoal.Walked`), the body of the shared
    * table; a head applied to any other continuation calls the shared
    * table, `head pack`, and gives each of its answers the continuation,
    * then checks whether the head was marked unverified
    * (`BodyGoal.FallbackChecked`). A head with no step in its plan has no
    * work before its continuation to share, and is read as under
    * `Substituted`, so that a Scott value applied to its cases costs no
    * table more.
    *
    */
  private def lastApplied[C <: NativeSpecializer & Singleton](
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[Value[C]],
      filled: Vector[Value[C]],
      argument: Value[C],
      after: List[BodyFrame[C]],
      state: ReadingState[C]
  )(using C): List[BodyGoal[C]] =
    val substituted = List(BodyGoal.Called(instanceTerm(code, filled, state.specializer), after))
    state.continuations match
      case ContinuationReading.Substituted => substituted
      case ContinuationReading.Packed =>
        holes match
          case Vector(Hole.Bound(slot)) =>
            Code.tailPlans(code).get(slot).filter(_.arity >= 1) match
              case Some(plan) =>
                val head = Value.Thunk(code, holes, fillings)
                if Value.same(argument, pack(plan.arity)) then List(BodyGoal.Walked(code, filled, slot, head, after))
                else if plan.steps && !state.unverified.contains(head) then
                  List(
                    BodyGoal.Called(Value.Apply(head, pack(plan.arity)), BodyFrame.SetApplied(argument) :: after),
                    BodyGoal.FallbackChecked(head, code, filled, after)
                  )
                else substituted
              case None => substituted
          case _ => substituted

  /** The state after a head of the code took its last argument and gave the
    * goals (`lastApplied`), with the code's application counted where the
    * goals enter its instance (APPLICATIONS COUNTED): the instance, and the
    * walk of a head applied to the pack; not the call of the shared table,
    * the goals that end with `BodyGoal.FallbackChecked`, whose walk is
    * counted where it is read and whose fallback where that goal takes it.
    * A function of the goals' shape, so that `lastApplied` builds no pair on
    * this hot path, counting or not (the review of
    * https://github.com/Atry/private-overlay/pull/1828).
    */
  private def lastEntered[C <: NativeSpecializer & Singleton](code: Code, goals: List[BodyGoal[C]], state: ReadingState[C])(using C): ReadingState[C] =
    goals match
      case _ :: BodyGoal.FallbackChecked(_, _, _, _) :: Nil => state
      case _                                                => state.entered(code)

  /** The head of the code's spine: the code itself unless it is an
    * application.
    */
  @scala.annotation.tailrec
  private def spineHead(code: Code): Code = code.layer match
    case Apply(function, _) => spineHead(function)
    case _                  => code

  /** The budget with `count` steps taken, or None when it runs out first. */
  @scala.annotation.tailrec
  private def chargedTimes(budget: Budget, count: Int): Option[Budget] =
    if count == 0 then Some(budget)
    else
      budget.charged match
        case None       => None
        case Some(once) => chargedTimes(once, count - 1)

  /** The largest arity whose pack is made once and kept. */
  private[weakhead] val keptPackArity: Int = 16

  /** `pack_n`, `λm1 … mn. λt. t m1 … mn`, a closed term
    * (`ContinuationReading.Packed`): one interned object for each arity.
    */
  private def packMade(arity: Int): gezi.ir.Pure =
    val tuple = (1 to arity).foldLeft(DeBruijnTerm.Variable(0))((applied, position) =>
      DeBruijnTerm.Apply(applied, DeBruijnTerm.Variable(arity + 1 - position))
    )
    Defunctionalization.pure((0 to arity).foldLeft(tuple)((body, _) => DeBruijnTerm.Lambda(body)))

  private val packs: Vector[gezi.ir.Pure] = Vector.tabulate(keptPackArity + 1)(packMade)

  /** The pack of the arity (`packMade`). */
  private[weakhead] def pack[C <: NativeSpecializer & Singleton](arity: Int)(using specializer: C): Value[C] =
    Value.of(Configured.fromPure(specializer)(if arity <= keptPackArity then packs(arity) else packMade(arity)))

  /** The fields of a pack's tuple, `λt. t m1 … mn` with its fields filled:
    * the head of the pack's own code with one hole left, each field the
    * value of the slot the code's spine applies `t` to. None for any other
    * head.
    */
  private def packFields[C <: NativeSpecializer & Singleton](head: Head[C], arity: Int)(using C): Option[Vector[Value[C]]] = (head, pack(arity)) match
    case (Head.Lambda(code, holes, fillings), Value.Thunk(packCode, _, _)) if (code eq packCode) && holes.size == 1 =>
      @scala.annotation.tailrec
      def arguments(current: Code, found: List[Code]): List[Code] = current.layer match
        case Apply(function, argument) => arguments(function, argument :: found)
        case _                         => found
      val filledSlots = (0 until holes.size + fillings.size).filterNot(holes.collect { case Hole.Bound(slot) => slot }.contains)
      Some(arguments(code, Nil).toVector.map(argument =>
        argument.layer match
          case Slot(index) => fillings(filledSlots.indexOf(index))
          case other       => throw IllegalStateException(s"a pack's tuple applies its slot to slots, not to $other")
      ))
    case _ => None

  /** One step taken, or a stop when the budget is spent: a reduction's
    * step, and a node of a normal form a reading builds
    * (`NormalForms.nodeBuilt`).
    */
  private[weakhead] def stepTaken[C <: NativeSpecializer & Singleton](using C): Computation[ReadingState[C], Unit] =
    Computation(state =>
      done(state.budget.charged match
        case Some(charged) => Computed.Done((), state.copy(budget = charged))
        case None          => Computed.Stopped(state))
    )

  /** A URI node replaced by its expansion, the δ step: the expansion the
    * state remembers, or the front end's (`DirectoryTree.expansion`, a
    * first-order call of the front end, which defines the URI's equation),
    * remembered from now on; any other value as it is. The front end defines
    * the equation between a URI node and the IR, and the expansion of a
    * `file:` URL is remembered, a memo. An expansion is no URI node, so one step
    * reaches a layer. Taking it costs no evaluator step.
    */
  private def uriExpanded[C <: NativeSpecializer & Singleton](value: Value[C], state: ReadingState[C])(using C): (Value[C], ReadingState[C]) =
    gezi.ir.Closed.configured(value).filter(term =>
      term.layer match
        case gezi.ir.UriNode(_) => true
        case _                  => false
    ) match
      case Some(node) =>
        val (expansion, expansions) = state.expansions.expanded(node, state.specializer)
        (Value.of(expansion), state.copy(expansions = expansions))
      case None => (value, state)

  // ---- shared with the JIT ----

  /** The fillings after the first hole takes the argument (weak_head.pl's
    * hole_filled/5; D1 of `lean/README.md`, the first beta clause of D2), `remaining` the
    * holes after it: the argument goes in at its slot's position among the
    * filled slots, after the fillings when they are fewer (Lean's `fill`,
    * take and drop), and an ignored hole drops it.
    */
  def holeFilled[C <: NativeSpecializer & Singleton](
      hole: Hole,
      remaining: Vector[Hole],
      fillings: Vector[Value[C]],
      argument: Value[C]
  )(using C): Vector[Value[C]] = hole match
    case Hole.Ignored => fillings
    case Hole.Bound(slot) =>
      val position = Defunctionalization.fillingPosition(remaining, slot).min(fillings.size)
      fillings.patch(position, Vector(argument), 0)

  /** The instance of the code under the fillings, the values of its slots in
    * slot order (weak_head.pl's instance_term/3; D2 of `lean/README.md`, the second beta
    * clause): a slot reads its value, and a nested thunk keeps its code and
    * holes while its fillings, codes over the enclosing slots, are
    * instantiated, each parallel built by the reading's specializer
    * (`NativeSpecializer.parallelOfValues`), so that a unique spelling becomes
    * its storage and nothing is built as written where it has one. Throws
    * `EvaluationError` with `SlotWithoutValue` for a slot the fillings do not
    * reach.
    */
  def instanceTerm[C <: NativeSpecializer & Singleton](code: Code, fillings: Vector[Value[C]], specializer: C)(using C): Value[C] =
    codeInstance(code, fillings, specializer).result

  /** The result of the native the term is an exact application of, under
    * the reading's storage option (`StorageReading.called`), each native
    * called charged a step of the budget and counted (`nativeCalls`), with
    * the state charged; none when the reading takes no option, the term is no
    * such application, or the budget cannot pay for the calls, the term then
    * read as it is. The option calls no native unless every argument has a
    * value, so no call's result is dropped.
    */
  private def nativeResult[C <: NativeSpecializer & Singleton](term: Value[C], state: ReadingState[C])(using C): Option[(Value[C], ReadingState[C])] =
    state.storages.flatMap(reading =>
      val (result, calls) = reading.called(term)
      // A budget that cannot pay for the calls leaves the term to be read as
      // it is, the natives' computation then uncharged (a cost, never an answer).
      if calls == 0 then None
      else
        state.budget.chargedTimes(calls).flatMap(charged =>
          result.map((_, state.copy(budget = charged, nativeCalls = state.nativeCalls + calls)))
        )
    )

  /** The term read at a head: a storage, a leaf of its term's layer, is read as the value `C ȳ` of its one-layer view
    * `C ȳ ∥ T`, read with the reading's `StorageAccess`: `C ȳ ∥ T ≃_O C ȳ` by the unique spelling's pattern theorem
    * (`docs/design/gezi-set-equations-proofs.md`, section 23), whose premise is the backend's obligation; any other term
    * as it is.
    */
  private def storageEliminated[C <: NativeSpecializer & Singleton](term: Value[C], state: ReadingState[C])(using
      C
  ): Value[C] = (term.representation: AnyRef) match
    // The view is the reading's configuration's: one layer, read by its native specializer with its capability.
    case storage: gezi.ir.NativeStorage => Value.of(state.specializer.viewOf(storage)(using state.storageAccess).value)
    case _                              => term

  /** The thunk value of a code with holes still to fill, or its suspension when every hole is filled: a code whose
    * holes are all filled is a delayed instance, no thunk.
    */
  private def thunkOrSuspension[C <: NativeSpecializer & Singleton](code: Code, holes: Vector[Hole], fillings: Vector[Value[C]])(
      using C
  ): Value[C] =
    if holes.isEmpty then SuspensionValue(code, fillings) else Value.Thunk(code, holes, fillings)

  private def codeInstance[C <: NativeSpecializer & Singleton](
      code: Code,
      fillings: Vector[Value[C]],
      specializer: C
  )(using C): Trampoline[Value[C]] = code.layer match
    case Slot(index) =>
      if index < fillings.size then done(fillings(index))
      else throw EvaluationError(EvaluationErrorReason.SlotWithoutValue(index, fillings.size))
    case Apply(function, argument) =>
      for
        functionInstance <- tailcall(codeInstance(function, fillings, specializer))
        argumentInstance <- tailcall(codeInstance(argument, fillings, specializer))
      yield Value.Apply(functionInstance, argumentInstance)
    case Parallel(left, right) =>
      for
        leftInstance <- tailcall(codeInstance(left, fillings, specializer))
        rightInstance <- tailcall(codeInstance(right, fillings, specializer))
      yield Value.Parallel(leftInstance, rightInstance)
    case Choice(left, right) =>
      for
        leftInstance <- tailcall(codeInstance(left, fillings, specializer))
        rightInstance <- tailcall(codeInstance(right, fillings, specializer))
      yield Value.Choice(leftInstance, rightInstance)
    case Thunk(inner, holes, innerFillings) =>
      allInstances(innerFillings, fillings, specializer).map(thunkOrSuspension(inner, holes, _))

  private def allInstances[C <: NativeSpecializer & Singleton](
      codes: Vector[Code],
      fillings: Vector[Value[C]],
      specializer: C
  )(using C): Trampoline[Vector[Value[C]]] =
    def from(index: Int, instances: Vector[Value[C]]): Trampoline[Vector[Value[C]]] =
      if index >= codes.size then done(instances)
      else
        tailcall(codeInstance(codes(index), fillings, specializer)).flatMap(instance =>
          from(index + 1, instances :+ instance)
        )
    from(0, Vector.empty)

