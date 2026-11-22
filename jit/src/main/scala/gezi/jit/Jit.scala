package gezi.jit

import gezi.weakhead.Answers
import gezi.weakhead.Computation
import gezi.weakhead.CompletedTables
import gezi.weakhead.Computed
import gezi.weakhead.Decoding
import gezi.weakhead.Head
import gezi.weakhead.JitEvaluator
import gezi.weakhead.ListCase
import gezi.weakhead.ListCodec
import gezi.weakhead.ListConstructor
import gezi.weakhead.ListElementField
import gezi.weakhead.ListRepresentation
import gezi.weakhead.ListTail
import gezi.weakhead.ParallelSet
import gezi.weakhead.ReadingState
import gezi.weakhead.SharedCompletedTables
import gezi.weakhead.TableSharing
import gezi.weakhead.Tabling
import gezi.weakhead.Value
import gezi.weakhead.Values
import gezi.weakhead.WeakHead
import gezi.strategies.DispatchDecision
import gezi.ir.CodeLayer
import gezi.ir.Code
import gezi.ir.Instruction
import gezi.ir.Hole
import gezi.ir.Layer
import gezi.weakhead.Trampoline
import gezi.weakhead.Trampoline.done
import gezi.weakhead.Trampoline.tailcall
import gezi.ir.{Apply, Choice, Opaque, Parallel, Slot, Thunk, UriNode}

/** What the JIT evaluates under, chosen when the program is compiled: the
  * library's backend facts, which carry the natives and data families the
  * JIT runs (`BackendFacts.nativeBackend`, the one place the JIT reads them
  * from), the compilation budget (the number of codes a
  * reading's cache may hold compiled, beyond which an instance is
  * interpreted), the generation strategy, the compilation backend, and the
  * dispatch mode, and whether instances are tabled (`instanceTable`).
  * Built once and passed on: a reading's JIT state belongs to the
  * configuration it was built under (`JitRunState.of`).
  *
  * @param instanceTable
  *   whether instances are tabled: an instance's heads are the least fixed
  *   point of the tabled function whose body is its reading, kept by its code
  *   and fillings (`TabledInstance`, `JitRunState.instanceTables`), so that the
  *   next instance with the same key takes them from the table instead of
  *   running the code again. No default: every caller states its choice,
  *   since tabling is the default and not tabling the speculation: tabling
  *   costs at most a constant factor over not tabling, while not tabling can
  *   cost exponentially more, and an entry's
  *   choice comes from its data. The table gives every head the untabled reading gives, each
  *   as it is found (`Tabling`), and decides instances whose untabled
  *   reading has no end, an instance met again within its own reading being
  *   answered by its approximation. An instance missed while a fallback
  *   point's check is in progress (`JitRunState.readingPath` not empty) is
  *   run untabled, since a cut's heads are the check's, not the instance's
  *   anywhere else
  * @param instanceTableTrial
  *   the fewest entries of a code the table judges the code's cost on
  *   (`TableCost.unprofitable`), `TableCost.trial` by default; a test lowers
  *   it so that the cutoff fires on small terms
  * @param nativeBlocks
  *   the native block mechanism (`NativeBlockMechanism`): which instances
  *   enter a block when an application fills a code's last hole, what the
  *   block runs, and when a code is retired; `NoNativeBlocks` by default,
  *   the only implementation (the FIXME on `NativeBlockMechanism`)
  * @param instanceRetention
  *   how the state keeps the instance table's complete tables
  *   (`InstanceRetention`); two generations of
  *   `JitConfiguration.defaultInstanceTableGeneration` entries by default
  * @param instanceCheckpoints
  *   which instances the table looks up and records (`InstanceCheckpoints`),
  *   from costs only; `ProfitableCheckpoints` by default,
  *   the table as it was before checkpoint policies
  * @param instanceLookahead
  *   how far a missed instance's reading is pulled beyond the heads its
  *   consumers ask for (`InstanceLookahead`); `Lazy` by default, the table
  *   as it was before lookaheads
  */
final class JitConfiguration(
    val facts: BackendFacts,
    val budget: Int,
    val strategy: GenerationStrategy,
    val backend: CompilationBackend,
    val dispatch: DispatchMode,
    val instanceTable: Boolean,
    val instanceTableTrial: Long = TableCost.trial,
    val instanceRetention: InstanceRetention = InstanceRetention.Generations(JitConfiguration.defaultInstanceTableGeneration),
    val nativeBlocks: NativeBlockMechanism = NoNativeBlocks,
    val instanceCheckpoints: InstanceCheckpoints = ProfitableCheckpoints,
    val instanceLookahead: InstanceLookahead = InstanceLookahead.Lazy
):
  require(budget >= 0, s"a compilation budget is not negative: $budget")
  require(instanceTableTrial >= 0, s"a table's trial is not negative: $instanceTableTrial")
  instanceRetention match
    case InstanceRetention.Generations(size) => require(size >= 1, s"a generation of the instance table holds an entry at least: $size")
    case InstanceRetention.NeverDropped      => ()
  instanceLookahead match
    case InstanceLookahead.WithinSteps(steps) => require(steps >= 1, s"a lookahead pulls a step at least: $steps")
    case InstanceLookahead.Lazy               => ()

/** The configurations a test or a program builds. */
object JitConfiguration:

  /** The default budget, the Prolog JIT's flag `lambda_jit_compilation_budget`. */
  val defaultBudget: Int = 10000

  /** The young generation's default size (`InstanceRetention.Generations`).
    *
    * Measured 2026-11-02 on d702a2487 with this change, `contest-entries-solo`, one
    * reading each, CPUs 4 and 5, -Xmx3g SerialGC as the judge runs it (the
    * table without a bound held 2,084,612 entries after the
    * calls_10000 respelled point of a published points file). calls_10000
    * respelled then direct in one JVM, seconds: no
    * bound 25.3 and 31.2; 2^18 51.6 and 30.6 (the point's working set
    * exceeds a generation, so it reads its instances again); 2^20 28.3 and
    * 28.2; 2^21 26.7 and 27.2. That file's whole pass (seed 3417947893, 291
    * rows): no bound 559.4 s, 2^20 529.6 s, every row with the same
    * outcome but edit_distances/direct/repetitions_1, stopped with no bound
    * and no_answer under 2^20. A choice among these readings, not an
    * optimum: one reading each.
    */
  val defaultInstanceTableGeneration: Int = 1 << 20

  /** The facts, the default budget, the strategy `predicate_per_code`, the
    * closure backend, no dispatch strategy, and the instance table as the
    * caller states (`instanceTable`).
    */
  def of(facts: BackendFacts, instanceTable: Boolean): JitConfiguration =
    JitConfiguration(facts, defaultBudget, PredicatePerCode, ClosureBackend, DispatchMode.NoDispatch, instanceTable)

/** The emission a strategy gave a code has another slot count than the code
  * (the Prolog JIT's `domain_error(Name/Arity, StubIndicator)`): the code's
  * slot count and the emission's.
  */
final case class EmissionSlotCount(code: Code, codeSlots: Int, emissionSlots: Int)
    extends RuntimeException:
  override def getMessage: String =
    s"the emission of code $code reads $emissionSlots slots, the code has $codeSlots"

/** An instance with fewer fillings than its code's slots, reached through a
  * compiled code (the Prolog JIT's `fillings_fewer_than_slots(Count,
  * Fillings)`).
  */
final case class FillingsFewerThanSlots(slots: Int, fillings: Int) extends RuntimeException:
  override def getMessage: String = s"fillings_fewer_than_slots($slots, $fillings)"

/** The JIT evaluator, the port of `gezi/prolog/gezi/jit.pl`,
  * whose module comment the rules here follow section by section (AN
  * EVALUATOR OVER THE REFERENCE'S VALUES, THE UNIT IS A CODE, THE BUDGET,
  * THE GENERATION STRATEGY, THE BACKEND'S REPRESENTATIONS, ONLY A
  * TYPE-FILTERED CONSTRUCTOR ENTERS A REPRESENTATION, A DECODE POINT, A
  * SLOT STEP, A NATIVE, A PARALLEL STEP, A FALLBACK POINT, A BLOCK, AN
  * ELIMINATION, WHY THE ANSWERS STAY ANSWERS, THE CHECK HAS NO COUNT OF ITS
  * OWN, DISPATCH STRATEGIES, THE CHECK'S EVALUATION IS PASSED ON, THE COST
  * OF A COPY, THE READING OF AN INFINITE VALUE). It answers the heads the
  * reference (`gezi.weakhead.WeakHead` under weak_head) answers, in
  * the same order, except at the backend's representations.
  *
  * THE UNIT IS A CODE, COMPILED AT ITS FIRST INSTANCE. An instance of a code
  * (a thunk with no hole left) is evaluated by the code's compiled closure
  * (`CompiledCode`, from the strategy's emission by the backend); a code is
  * compiled at its first instance in the evaluation order, a function of the
  * term, and kept in the reading's state (`JitRunState`), from one reading of
  * a suite to the next as the Prolog JIT kept it in the process. Beyond the
  * budget an instance is interpreted: its term built as the reference
  * builds it and its heads taken by these rules, so a term's answers depend
  * neither on the budget nor on what was compiled before.
  *
  * THE MACHINE. As the reference's untabled machine, the evaluation is a
  * stack of goals on the heap: a term with the arguments its heads are
  * still to be applied to, the remaining members of a choice, the remaining
  * clauses of a compiled code, or a stream of heads computed by a rule (a
  * decode point's, a native's, an elimination's), so that a run that
  * re-enters the same term, as Omega's does, grows nothing. Reading one
  * layer of a term, and applying one head to one argument, is one step of
  * the reading's budget, as in the reference.
  *
  * APPLICATIONS COUNTED. A reading asked to count them
  * (`ReadingState.codeApplications`, `gezi.hotspot.Budget.countedUnits`)
  * counts one application of a code each time the JIT enters an instance of
  * it: where it meets a thunk of the code with no hole, in a term read or as
  * a compiled clause's start (`ClauseStart.Instance`, a code whose holes the
  * clause filled when it was compiled), and where it fills the last hole of a
  * head of the code. The instance is counted when it is entered, whatever
  * gives its heads then: the instance table, the native block, the compiled
  * clauses or the interpreter. A cell (`JitRules.cellCode`), the JIT's own
  * sharing of an argument and no code of the term, is not counted. A step of
  * the budget is not taken for each count: a clause that starts with an
  * instance enters it within the step that entered its own code, so the
  * counts of a JIT reading may exceed its steps. Counting changes no step,
  * table or head.
  *
  * Departures from the Prolog JIT:
  * the cache, the counts, the decodings' numbers and the readings' path are
  * a value in the reading's state, not in the process and the thread, so
  * there is no drop, no thread and no transaction, and a stopped reading
  * leaves its compiled codes whole (each code is compiled before it runs);
  * the inner instance a clause holds looks its code up in the cache where
  * the Prolog clause called the code's predicate by its literal name (one
  * map lookup, no compilation once the code is compiled); a code is always a
  * code identifier; the decode point's intersection of a parallel's two
  * sides keeps the left side's order where the Prolog JIT sorted it; the
  * backend's constants are read by the reference evaluator
  * (`BackendFacts.constants`).
  *
  * FIXME (carried from jit.pl:598): a natural whose nested readings never https://github.com/Atry/private-overlay/issues/1930
  * repeat in spelling has a check without end, so the cooperative answer is
  * lost: `((fixpoint (\f. \n. successor (f (successor n)))) zero) zero
  * (\_. zero)`, whose value is the rational `fixpoint successor` with an
  * argument that grows, which HM types and the reference reads as zero, gave
  * no normal form within the Prolog reading's 10,000,000 inferences
  * (measured 2026-10-30): the check needs the whole natural, a big integer,
  * before either path. A list's spine has no such check since its cells
  * keep their tails unread, but an item that is a fallback point is still
  * checked when its cell is built (the FIXME at `itemOutcome`). Candidate: a
  * natural whose successors are not read until a consumer reads them, which
  * a big integer is not; not designed.
  *
  * FIXME (carried from jit.pl:612, decided for steps): the comparison https://github.com/Atry/private-overlay/issues/1931
  * of `ReadingPath.extended` costs no step beyond the
  * reading that calls it, while its time grows with what the two readings
  * share: the comparison is the structural equality of two operands, which
  * walks them where they agree. Operands that share a long prefix still
  * compare it: in the Prolog JIT the successors of a natural a closure
  * builds, each nested reading's operand one successor shorter, took 138,
  * 140 and 170 microseconds a successor at k = 256, 512 and 900 for the run
  * of (\y. successor^k y) zero (measured on main a4c6c432e), close to
  * linear at those sizes, quadratic beyond. Steps count the evaluator's
  * goals, as inferences counted SWI-Prolog's calls, and neither counts the
  * cells a comparison walks, so the defect is the same under steps.
  * Candidate: a comparison in constant time, which needs a key of the
  * reading that does not walk its operand; not designed.
  *
  * FIXME (carried from jit.pl:623): the readers read a normal form under a https://github.com/Atry/private-overlay/issues/1932
  * binder by applying a head to a neutral value, and a fallback point over
  * a term that holds one does not hold, so a strategy whose decision is
  * `rejected` throws where the reading reaches one, an error of the reading
  * and of no input (derived from the rules, not measured). Candidate: a
  * reader's neutral, which is no input of the program, takes the untyped
  * path under every strategy; not designed.
  *
  * FIXME (carried from jit.pl:640): the JIT decides a cycle only through the https://github.com/Atry/private-overlay/issues/1933
  * instance table. A tabled instance met again within its own reading is
  * answered by its approximation and read again to its fixed point
  * (`tabledInstance`), so
  * Omega and the rings of problems/merge_graph end with no head where the
  * cycle runs through tabled instances. A cycle still runs to the budget
  * where an instance on it runs untabled: under `instanceTable` false,
  * which every caller states; inside a
  * fallback point's check (`JitRunState.readingPath` not empty); where the
  * checkpoint policy only looks the instance up (`CheckpointDecision.LookupOnly`);
  * and for a code `TableCost.unprofitable` cut off. The reference reads such
  * programs under tabling(weak_head).
  *
  * The FIXME of jit.pl:145 is closed by the port:
  * the Prolog JIT's predicates outlived a thread that ended without a drop.
  * Here the compiled codes are a value of the reading's state, which nothing
  * keeps once the reading lets it go, and no thread or process holds a
  * cache; the defect has no counterpart.
  */
final case class Jit(configuration: JitConfiguration) extends JitEvaluator:

  private val rules = JitRules(configuration)

  def heads(term: Value): Answers[ReadingState, ParallelSet] =
    rules.heads(JitValues.fromValue(term)).flatMap(rules.observed)

  def encoded(heads: Vector[ParallelSet]): Vector[ParallelSet] =
    heads.map(set => ParallelSet.of(set.heads.map(rules.headEncoded)))

  /** The values of a representation the term's heads are: the values a term
    * `x ∥ C` decodes into, C a decoding criterion, with no normal form read;
    * none for a head that is no value of a representation.
    */
  def representedHeads(term: JitValue): Answers[ReadingState, NativeValue] =
    rules.heads(term).flatMap {
      case JitHead.Represented(_, value) => Answers.single(value)
      case _                             => Answers.empty
    }

  /** The representation the decoding criterion names, if it names one. */
  def representationOf(criterion: Instruction): Option[Representation] =
    rules.decodingCriterion(JitValues.fromValue(criterion))

  /** The closed term the run-time value stands for, its represented values
    * encoded. Throws `IllegalArgumentException` for a value that holds a
    * neutral value.
    */
  def closedTerm(value: JitValue): Instruction =
    Values.instruction(JitValues.plain(JitValues.encoded(value, configuration.facts)))

/** A result of the JIT's reads of syntax (its rules that read terms by their
  * layers, the section "reading terms by their layers" of `JitRules`), with
  * the count of the layers they read. A reading adds the
  * count to `JitCounts.syntaxReads`; the count is returned, never kept in
  * global state. The decoding criteria the reads read by an instruction, not yet
  * known to the reading (`KnownCriteria`), come back with the result
  * (`learned`), and the reading keeps them in its state
  * (`JitRunState.criteria`).
  */
private final case class SyntaxRead[+Result](
    result: Result,
    reads: Long,
    learned: Map[Instruction, Option[Representation]] = Map.empty
):

  def map[Next](change: Result => Next): SyntaxRead[Next] = SyntaxRead(change(result), reads, learned)

  def flatMap[Next](continuation: Result => SyntaxRead[Next]): SyntaxRead[Next] =
    val next = continuation(result)
    SyntaxRead(next.result, reads + next.reads, if next.learned.isEmpty then learned else learned ++ next.learned)

  /** The same result with the reads and the criteria learned by another
    * read added.
    */
  def joined(other: SyntaxRead[Any]): SyntaxRead[Result] =
    SyntaxRead(result, reads + other.reads, if other.learned.isEmpty then learned else learned ++ other.learned)

  /** The same result with `more` reads counted. */
  def counted(more: Long): SyntaxRead[Result] = copy(reads = reads + more)

private object SyntaxRead:

  /** A result read with no read of syntax. */
  def pure[Result](result: Result): SyntaxRead[Result] = SyntaxRead(result, 0)

  /** The continuation's result on the first read's, if there is one; none
    * otherwise, and then the continuation reads nothing.
    */
  def chained[First, Next](first: SyntaxRead[Option[First]])(
      continuation: First => SyntaxRead[Option[Next]]
  ): SyntaxRead[Option[Next]] =
    first.flatMap {
      case Some(found) => continuation(found)
      case None        => pure(None)
    }

/** The decoding criteria a reading has already read, by the criterion's
  * instruction (`JitRunState.criteria`): the representation each names, or none.
  * `JitRules.decodingCriterionRead` is a pure function of the instruction, the
  * layers under it, which never change, and the
  * backend's facts, which the configuration fixes, so a criterion read once
  * is taken from here by every later read of the reading. A criterion is the
  * syntax of the filter written in the term; what is kept is which backend
  * representation that syntax names, never a fact about a value.
  */
private final case class KnownCriteria(byInstruction: Map[Instruction, Option[Representation]])

private object KnownCriteria:

  /** No criterion read: the refinement's reads, outside a reading. */
  val none: KnownCriteria = KnownCriteria(Map.empty)

/** The outcome of a fallback point's check, or of an argument's reading
  * (jit.pl's `typed(Values)` and `untyped(Untyped)`): the values at the
  * place, or the run-time value that carries the operand's heads.
  */
enum Outcome:
  case Typed(values: Vector[NativeArgument])
  case Untyped(value: JitValue)

/** The place of a native's parameter once the list's element filter is
  * known: a representation, a list's item in the representation of the
  * element filter, or a list's tail in the list's representation.
  */
enum Place:
  case In(representation: Representation)
  case ItemOf(element: JitValue)
  case TailOf(element: JitValue)

/** An argument of a native given its last argument (arguments_valued/3):
  * its values, its untyped outcome, or the argument to read when the native
  * is called.
  */
private enum Valued:
  case Values(values: Vector[NativeArgument])
  case Unvalued(value: JitValue)
  case Lazy(argument: JitValue, place: Place)

/** The bounds of the rules. */
object JitRules:

  /** The steps a native block's entry may spend reading a filling to its
    * head to find the self filling (`JitRules.selfFound`): a choice, not a
    * measurement; Turing's fixed point combinator, the library's
    * `fixpoint`, reaches its function's lambda in a few steps.
    */
  val selfReadingSteps: Long = 64

  /** Whether two values spell one term: equal, or applications whose parts
    * spell one term, an instruction read through its application layer
    * (`JitRules.selfFound`). It reads syntax only, and decides whether a
    * filling holds itself, never what a value is.
    */
  def spelledAlike(left: JitValue, right: JitValue): Boolean =
    (left eq right) || left == right || ((applicationOf(left), applicationOf(right)) match
      case (Some((leftFunction, leftArgument)), Some((rightFunction, rightArgument))) =>
        spelledAlike(leftFunction, rightFunction) && spelledAlike(leftArgument, rightArgument)
      case _ => false)

  private def applicationOf(value: JitValue): Option[(JitValue, JitValue)] = value match
    case JitValue.Apply(function, argument) => Some((function, argument))
    case _ => None

  /** The code of a cell (`JitRules.shared`): slot 0, whose instance under
    * the fillings `[v]` is v.
    */
  val cellCode: Code = Code.Slot(0)

/** The rules of the JIT under one configuration (`Jit`'s comment). */
final case class JitRules(configuration: JitConfiguration):

  private val facts = configuration.facts

  private val nativeBackend = facts.nativeBackend

  /** The families whose positions hold a term as written
    * (`DataFamily.heldAsWritten`), read once, so that the decoding's hot path
    * asks a set and not the backend's table.
    */
  private val familiesHeldAsWritten: Set[FamilyIdentity] =
    nativeBackend.families.filter(_.heldAsWritten).map(_.identity).toSet

  private def heldAsWritten(representation: Representation): Boolean =
    familiesHeldAsWritten.contains(representation.familyIdentity)

  private type Stream = Answers[ReadingState, JitHead]

  // ---- the machine ----

  private enum Goal:
    case Evaluation(term: JitValue, arguments: List[JitValue])
    /** A layer already read, dispatched by its constructor alone, never to a
      * native: the generic reading of a native-bound library file's term,
      * whose layer is that term itself now that an instruction is its own
      * layer (`genericApplied`).
      */
    case LayerEvaluation(layer: JitValue, arguments: List[JitValue])
    case Members(members: Vector[JitValue], from: Int, arguments: List[JitValue])
    case Clauses(code: CompiledCode, fillings: Vector[JitValue], from: Int, arguments: List[JitValue])
    case Heads(heads: Stream, arguments: List[JitValue])
    case Untabled(code: Code, fillings: Vector[JitValue])

  private final case class Machine(goals: List[Goal])

  /** The heads of the closed term, one at a time, in the reference's order
    * (jit_head/2).
    */
  def heads(term: JitValue): Stream = headsApplied(term, Nil)

  /** The heads of the term applied to the arguments in turn. */
  private def headsApplied(term: JitValue, arguments: List[JitValue]): Stream =
    running(Machine(List(Goal.Evaluation(term, arguments))))

  /** The heads of the head applied to the arguments in turn
    * (heads_applied/3).
    */
  private def headApplied(head: JitHead, arguments: List[JitValue]): Stream =
    running(Machine(List(Goal.Heads(Answers.single(head), arguments))))

  /** The heads the machine reads, its goals run in turn on the reading's
    * state.
    *
    * FIXME (2026-11-07): a reading can still run out of https://github.com/Atry/private-overlay/issues/1934
    * memory here. The hot ladder's `calls_100000_hot` direct, read as written
    * with the instance table on (CPUs 2 and 3), ran out of memory with a
    * 2 GB heap after 120 s and with a 1 GB heap after 58 s, after the
    * trampoline and the miss's continuation removed the retention of run and reading
    * states. At the last JFR object count the heap held `JitValue.Apply`
    * (157 MB) and pending `Trampoline` continuations and `JitRules` lambdas
    * (about 320 MB). The cause is not localized. An unverified guess: a
    * by-need reading of iterate's state builds a chain of applications as
    * long as the calls. Candidates, not designed: find what holds the
    * applications (JFR old object samples with paths to the roots), then
    * force a goal's state where the reading's semantics allows it, or bound
    * the pending goals.
    */
  private def running(machine: Machine): Stream =
    Answers(Computation(state =>
      nextHead(machine.goals, state).map {
        case Computed.Done(Some((head, rest)), after) => Computed.Done(Some((head, running(rest))), after)
        case Computed.Done(None, after)               => Computed.Done(None, after)
        case Computed.Stopped(stopped)                => Computed.Stopped(stopped)
      }
    ))

  private type Next = Trampoline[Computed[ReadingState, Option[(JitHead, Machine)]]]

  private def nextHead(goals: List[Goal], state: ReadingState): Next = goals match
    case Nil => done(Computed.Done(None, state))
    case Goal.Untabled(code, fillings) :: rest => untabledInstance(code, fillings, Nil, rest, state)
    case Goal.Members(members, from, arguments) :: rest =>
      val remaining =
        if from + 1 < members.size then Goal.Members(members, from + 1, arguments) :: rest else rest
      tailcall(nextHead(Goal.Evaluation(members(from), arguments) :: remaining, state))
    case Goal.Clauses(code, fillings, from, arguments) :: rest =>
      val remaining =
        if from + 1 < code.emission.clauses.size then Goal.Clauses(code, fillings, from + 1, arguments) :: rest
        else rest
      code.clause(from, fillings) match
        case ClauseStart.Evaluation(term, clauseArguments) =>
          tailcall(nextHead(Goal.Evaluation(term, clauseArguments.toList ++ arguments) :: remaining, state))
        case ClauseStart.Answer(head) => applied(head, arguments, remaining, state)
        case ClauseStart.Instance(inner, innerFillings, clauseArguments) =>
          instance(inner, innerFillings, clauseArguments.toList ++ arguments, remaining, state.entered(inner))
        case ClauseStart.ParallelHead(left, right, clauseArguments) =>
          tailcall(nextHead(Goal.Evaluation(JitValue.Parallel(left, right), clauseArguments.toList ++ arguments) :: remaining, state))
    case Goal.Heads(stream, arguments) :: rest =>
      tailcall(stream.pull.run(state)).flatMap {
        case Computed.Done(None, after) => tailcall(nextHead(rest, after))
        case Computed.Done(Some((head, more)), after) =>
          applied(head, arguments, Goal.Heads(more, arguments) :: rest, after)
        case Computed.Stopped(stopped) => done(Computed.Stopped(stopped))
      }
    case Goal.Evaluation(term, arguments) :: rest =>
      state.budget.charged match
        case None => done(Computed.Stopped(state))
        case Some(charged) =>
          val stepped = state.copy(budget = charged)
          // A listed extreme of ⊑_O is not evaluated, whatever it is applied
          // to, as under the weak head's machines (`WeakHead.knownExtreme`):
          // a
          // greatest term gives no head, a least term the empty parallel set.
          // One pool interns values and instructions, so a listed extreme and
          // the JIT's value of the same term are one object.
          val extremes = stepped.extremes
          if !extremes.isEmpty && extremes.tops.exists(_ == term) then tailcall(nextHead(rest, stepped))
          else if !extremes.isEmpty && extremes.bottoms.exists(_ == term) then
            done(Computed.Done(Some((EmptyParallel, Machine(rest))), stepped))
          else evaluated(term, arguments, rest, stepped)
    case Goal.LayerEvaluation(layer, arguments) :: rest =>
      state.budget.charged match
        case None          => done(Computed.Stopped(state))
        case Some(charged) => layerEvaluated(layer, arguments, rest, state.copy(budget = charged))

  /** One layer of the term read and dispatched by its constructor (jit_head/2). */
  private def evaluated(term: JitValue, arguments: List[JitValue], rest: List[Goal], state: ReadingState): Next =
    term match
      case JitValue.Represented(representation, value) =>
        applied(JitHead.Represented(representation, value), arguments, rest, state)
      case JitValue.Evaluated(written, mode, found) =>
        if mode == configuration.dispatch then
          tailcall(nextHead(Goal.Heads(Answers.of(found), arguments) :: rest, state))
        else tailcall(nextHead(Goal.Evaluation(written, arguments) :: rest, state))
      // A URI node is its expansion, the δ step, as under the weak head
      // (`WeakHead.uriExpanded`): the expansion the state remembers, or the
      // front end's (`DirectoryTree.expansion`), remembered from now on; no
      // evaluator step. A cell reads the directory tree off its state through
      // its root's URI node.
      case JitValue.Instruction(instruction) if instruction.uri.isDefined =>
        val expansion = state.expansions.get(instruction).getOrElse(gezi.directorysugar.DirectoryTree.expansion(instruction))
        tailcall(
          nextHead(Goal.Evaluation(expansion, arguments) :: rest, state.copy(expansions = state.expansions.updated(instruction, expansion)))
        )
      case JitValue.Instruction(instruction) if facts.nativeOfParameters(instruction).isDefined =>
        val native = facts.nativeOfParameters(instruction).get
        applied(JitHead.NativeApplication(instruction, native, native.parameterCount, Vector.empty), arguments, rest, state)
      case _ =>
        val read = layer(term)
        layerEvaluated(read.result, arguments, rest, syntaxCounted(state, read))

  private def layerEvaluated(layer: JitValue, arguments: List[JitValue], rest: List[Goal], state: ReadingState): Next =
    layer match
      case JitValue.Thunk(code, holes, fillings) =>
        if holes.nonEmpty then applied(JitHead.Lambda(code, holes, fillings), arguments, rest, state)
        else instance(code, fillings, arguments, rest, state.entered(code))
      case JitValue.Cell(inner) => instance(JitRules.cellCode, Vector(inner), arguments, rest, state)
      case JitValue.Apply(function, argument) =>
        tailcall(nextHead(Goal.Evaluation(function, argument :: arguments) :: rest, state))
      case JitValue.Choice(members) =>
        given KnownCriteria = known(state)
        val read = fallbackMembers(members)
        val counted = syntaxCounted(state, read)
        read.result match
          case Some((operand, representation)) =>
            tailcall(nextHead(Goal.Heads(fallbackPointHeads(representation, operand), arguments) :: rest, counted))
          case None =>
            if members.isEmpty then tailcall(nextHead(rest, counted))
            else tailcall(nextHead(Goal.Members(members, 0, arguments) :: rest, counted))
      case JitValue.Parallel(left, right) =>
        given KnownCriteria = known(state)
        val read = decodingRepresentation(right)
        val counted = syntaxCounted(state, read)
        read.result match
          case Some(representation) =>
            tailcall(nextHead(Goal.Heads(decodePointHeads(representation, left), arguments) :: rest, counted))
          // FIXME: the https://github.com/Atry/private-overlay/issues/2038
          // JIT does not read `ReadingState.parallels`; a parallel head is
          // applied with both sides as under `ParallelReading.BothSides`,
          // so `HeadsMet` does not reach an entry's reading.
          case None => applied(JitHead.Parallel(left, right), arguments, rest, counted)
      case JitValue.Neutral(variable, neutralArguments) =>
        applied(JitHead.Neutral(variable, neutralArguments), arguments, rest, state)
      case other => throw IllegalStateException(s"a layer read is no layer: ${other.layer.productPrefix}")

  /** The instance of the code under the fillings applied to the arguments
    * (jit_instance_head/3). Under `instanceTable`, the instance's heads come from the table when its
    * key is complete there; otherwise they are the instance's tabled heads
    * (`tabledInstance`), each applied to the arguments as it comes. A reading
    * the budget stops while it reads them completes nothing in the table. An
    * instance whose code the table does not pay for (`TableCost`), a cell's
    * excepted (`shared`), is run as it is, without the table. An
    * instance is keyed by its code and its fillings (`TabledInstance`), all
    * interned. A lookup is charged as steps what its key costs to hash and
    * compare, the number of its fillings: a hit takes an instance's heads
    * for no other step, so without the charge a budget of steps bought more
    * work under the table than without it.
    *
    * MEASURED (2026-11-01 06:18 UTC, a probe that is not committed, CPUs 0
    * and 1, `contest-entries-osprey` with the table on, before lookups were charged and
    * codes cut off): the longest common subsequence written by definition
    * (the published repeated_library_longest_common_subsequences, one site,
    * binary naturals) is read correctly at n = 10 to 320 in 10,912 to
    * 45,520,688 steps, 0.35 to 30.4 s, with 9 to 13 table entries a cell of
    * the (n + 1)^2; without the table it is exponential in n.
    *
    * MEASURED (2026-11-01 20:51 UTC, the same kind of probe over
    * 208 published points in the pass's order, CPUs 0 and 1, `contest-entries-osprey`
    * with the table on, lookups charged and codes cut off by `TableCost`):
    * every outcome the same as without the table (196 correct, 8 stopped, 4
    * member judgments unproved), 287 s against 388 s in all;
    * repeated_reduction_problems_grids 1.1 s against 5.5 s,
    * repeated_library_billboards 22.0 s against 28.9 s,
    * repeated_library_unshared_doublings 11.1 s against 14.6 s,
    * repeated_set_free_scope_judgments 56.4 s against 49.1 s. Before the
    * charge and the cutoff the same probe took 520 s, the points that read
    * to their budget up to three times as long as without the table.
    *
    * MEASURED (2026-11-02, a probe that is not committed, CPUs 2 and 3, the
    * plain JIT with no dispatch and the table on, the longest common
    * subsequence's direct site of two random strings of n characters below
    * 4): when an instance whose fillings exceeded 64 nodes ran untabled, the
    * steps a cell were 250, 1,099, 1,523 and 112,826 at n = 2, 4, 6 and 8
    * and grew with n beyond; keyed by the
    * identity of their fillings, those instances are tabled, and the steps
    * a cell are 193, 169, 183, 159 and 157 at n = 8, 24, 50, 100 and 200
    * (6,331,399 steps and 2.2 s at n = 200). At the nominal n = 3000 that
    * is still about 1.4 * 10^9 steps and 9 * 10^6 entries.
    */
  private def instance(
      code: Code,
      fillings: Vector[JitValue],
      arguments: List[JitValue],
      rest: List[Goal],
      state: ReadingState
  ): Next =
    if !configuration.instanceTable then untabledInstance(code, fillings, arguments, rest, state)
    else
      val run = JitRunState.of(state, configuration)
      val cost = run.tableCosts.getOrElse(code, TableCost.none)
      val decision =
        if code == JitRules.cellCode then CheckpointDecision.Tabled
        else configuration.instanceCheckpoints.decided(cost, run.stepsSinceCheckpoint(state.budget.spent), configuration.instanceTableTrial)
      if decision == CheckpointDecision.Untabled then untabledInstance(code, fillings, arguments, rest, state)
      else
        val key = TabledInstance(code, fillings)
        val charged = fillings.size
        val lookup = state.budget.spent + charged
        if lookup > state.budget.limit then done(Computed.Stopped(state))
        else
          tabledInstance(
            code,
            fillings,
            arguments,
            rest,
            state.copy(budget = state.budget.copy(spent = lookup)),
            run,
            cost,
            key,
            charged,
            decision == CheckpointDecision.Tabled
          )

  /** The instance under the table with its key, the checkpoint strategy
    * having chosen to look it up (`instance`), each case charged the key's
    * lookup: a complete table's heads, counted as a hit in the code's cost;
    * otherwise, when `recording` (`CheckpointDecision.Tabled`) and outside a
    * fallback point's check, the instance's tabled heads (`instanceTabling`),
    * each as it is found, its reading's steps entered in the code's cost when
    * its table completes, a checkpoint (`JitRunState.lastCheckpointSpent`);
    * and the instance run untabled, with nothing recorded, otherwise
    * (`CheckpointDecision.LookupOnly`, or inside a check). An instance met
    * again within its own reading is answered by its approximation, and its
    * component read again until its reads grow no more (`Tabling`): the
    * table decides an instance whose untabled reading has no end, Omega's
    * among them, where
    * running such a re-entry untabled read it to the budget.
    *
    * A hit is also charged one step for each head it replays, as the
    * untabled machine spends at least a step on each head it reads: a
    * reading's heads are then bounded by its budget. Charged the lookup
    * alone, a hit replayed any number of heads for free, and an instance
    * whose body reads a tabled instance in several branches of a choice
    * multiplied its heads at every nesting. MEASURED 2026-11-03:
    * `InstanceTableClearingLawTest` drew the term
    * `randomLatticeApplication(26, SplitMix(272145737283953041))`, whose
    * reading under the table hit one instance with 2,187 heads at step 102
    * and with 1,594,323 heads at step 168, three times as many every 11
    * steps, and ran out of a 512 MB heap within a budget of 2,000 steps;
    * untabled, it spent its 20,000 steps in 20 MB.
    *
    * Inside a fallback point's check (`JitRunState.readingPath` not empty) a
    * miss is run untabled: a cut there answers `Untyped` because the reading
    * recurred among the readings around it, which another context does not
    * have, so the heads read inside a check are the check's and are kept out
    * of the table. A complete table is still read there.
    *
    * The state keeps the complete tables as the configuration's
    * `instanceRetention` says: under `InstanceRetention.Generations` the
    * complete tables of `instanceTables` are the young generation, and when
    * it holds `size` of them it becomes the old generation
    * (`JitRunState.olderInstances`); under `NeverDropped` nothing is dropped.
    * A table found in the old generation, or in the cache service when the
    * reading shares its complete tables (`sharedInstances`, the second
    * level), is completed in the young one again and charged as a hit.
    */
  private def tabledInstance(
      code: Code,
      fillings: Vector[JitValue],
      arguments: List[JitValue],
      rest: List[Goal],
      state: ReadingState,
      run: JitRunState,
      cost: TableCost,
      key: TabledInstance,
      lookupNodes: Int,
      recording: Boolean
  ): Next =
    val tables = run.instanceTables
    val rolled = configuration.instanceRetention match
      case InstanceRetention.Generations(size) if tables.complete.size >= size && !tables.complete.contains(key) =>
        run.copy(instanceTables = tables.copy(complete = Map.empty), olderInstances = tables.complete)
      case InstanceRetention.Generations(_) | InstanceRetention.NeverDropped => run
    rolled.instanceTables.complete
      .get(key)
      .orElse(rolled.olderInstances.get(key))
      .orElse(sharedInstances(state).found(key).map(_._1)) match
      case Some(heads) =>
        val replayed = state.budget.spent + heads.ordered.size
        if replayed > state.budget.limit then done(Computed.Stopped(state))
        else
          val young = rolled.instanceTables
          val kept = if young.complete.contains(key) then rolled else rolled.copy(instanceTables = young.copy(complete = young.complete.updated(key, heads)))
          val counted = state.copy(
            budget = state.budget.copy(spent = replayed),
            jitState = kept.copy(tableCosts = run.tableCosts.updated(code, cost.hit(lookupNodes)))
          )
          tailcall(nextHead(Goal.Heads(Answers.of(heads.ordered), arguments) :: rest, counted))
      case None if !recording || run.readingPath != ReadingPath.Empty => untabledInstance(code, fillings, arguments, rest, state)
      case None =>
        val heads =
          instanceTabling.answers(key)
        val missed = rolled.tableCosts.getOrElse(code, TableCost.none).missOpened
        val opened = rolled.copy(tableCosts = rolled.tableCosts.updated(code, missed))
        val stream = configuration.instanceLookahead match
          case InstanceLookahead.Lazy               => entered(heads, key, lookupNodes, 0)
          case InstanceLookahead.WithinSteps(steps) => InstanceLookahead.lookedAhead(entered(heads, key, lookupNodes, 0), steps)
        tailcall(nextHead(Goal.Heads(stream, arguments) :: rest, state.copy(jitState = opened)))

  /** The instance table: the tabled function whose body is an instance's own
    * reading, a machine of its own (`Goal.Untabled`), within which the
    * instances it meets are again looked up in the table (`instance`); its
    * tables are `JitRunState.instanceTables`.
    */
  private val instanceTabling: Tabling[ReadingState, TabledInstance, JitHead] =
    Tabling(
      state => JitRunState.of(state, configuration).instanceTables,
      (state, tables) => state.copy(jitState = JitRunState.of(state, configuration).copy(instanceTables = tables)),
      // The complete tables are also kept in the cache service when the reading shares its complete tables; the
      // instances in progress, which the cycle check marks, stay in the state.
      sharedInstances,
      (key, _) => running(Machine(List(Goal.Untabled(key.code, key.fillings))))
    )

  /** Where a reading keeps the instance table's complete tables beside the
    * JIT's state, as its `ReadingState.sharing` says: nowhere under `Local`;
    * under `Shared`, the cache service's namespace of this configuration and
    * of the state's extremes, application reading and expansion source,
    * read off the state at each call (`CompletedInstanceNamespace`).
    */
  private def sharedInstances(state: ReadingState): CompletedTables[ReadingState, TabledInstance, JitHead] =
    state.sharing match
      case TableSharing.Local => CompletedTables.unshared
      case TableSharing.Shared(cache, retention, source) =>
        SharedCompletedTables(cache, CompletedInstanceNamespace(configuration, state.extremes, state.applications, source, retention))

  /** The heads of the instance's table as they come, and, when they end with
    * the instance's table complete, the steps their pulls spent entered in
    * the code's cost (`TableCost.entered`), a checkpoint. The steps are
    * counted over the pulls alone: what the caller does with a head between
    * them is no part of the instance's reading.
    */
  private def entered(heads: Stream, key: TabledInstance, lookupNodes: Int, steps: Long): Stream =
    Answers(Computation(state =>
      val spentBefore = state.budget.spent
      tailcall(heads.pull.run(state)).map {
        case Computed.Done(Some((head, more)), after) =>
          Computed.Done(Some((head, entered(more, key, lookupNodes, steps + (after.budget.spent - spentBefore)))), after)
        case Computed.Done(None, after) =>
          val run = JitRunState.of(after, configuration)
          if !run.instanceTables.complete.contains(key) then Computed.Done(None, after)
          else
            val cost = run.tableCosts.getOrElse(key.code, TableCost.none)
            val spent = steps + (after.budget.spent - spentBefore)
            Computed.Done(
              None,
              after.copy(jitState =
                run.copy(lastCheckpointSpent = after.budget.spent, tableCosts = run.tableCosts.updated(key.code, cost.entered(lookupNodes, spent)))
              )
            )
        case Computed.Stopped(stopped) => Computed.Stopped(stopped)
      }
    ))

  /** An instance of the code with the fillings applied to the arguments, by
    * the code's compiled clauses, taken into the state at its first instance
    * (`sharedCode`), or interpreted beyond the budget.
    */
  private def untabledInstance(
      code: Code,
      fillings: Vector[JitValue],
      arguments: List[JitValue],
      rest: List[Goal],
      state: ReadingState
  ): Next =
    val run = JitRunState.of(state, configuration)
    run.compiled.get(code) match
      case Some(compiled) => clausesCalled(compiled, fillings, arguments, rest, state)
      // A requested stop (the reading's signal) leaves the code uncompiled: the case below reads it as it is.
      case None if run.compiled.size < configuration.budget && !state.budget.stop.stopRequested =>
        val compiled = sharedCode(code, state)
        val after = state.copy(jitState =
          run.copy(compiled = run.compiled.updated(code, compiled), compilationOrder = run.compilationOrder :+ code)
        )
        clausesCalled(compiled, fillings, arguments, rest, after)
      case None =>
        tailcall(nextHead(Goal.Evaluation(CodeReading.instance(code, fillings), arguments) :: rest, state))

  /** The code's compiled form for a state that holds none: compiled here when
    * the reading keeps its memos in its state alone; otherwise the one the
    * cache service holds under the code and this JIT's configuration
    * (`CompiledCodes`, of the reading's retention), compiled and written
    * there when it holds none.
    * A compiled form is a pure function of the code's syntax under the
    * configuration, so a form found there is the one compiled here, and
    * clearing the service changes only cost.
    */
  private def sharedCode(code: Code, state: ReadingState): CompiledCode =
    state.sharing match
      case TableSharing.Local => compiledCode(code)
      case TableSharing.Shared(cache, retention, _) =>
        cache.locked(CompiledCodes(configuration, retention))(_.getOrElseUpdate(code, compiledCode(code)))

  private def clausesCalled(
      compiled: CompiledCode,
      fillings: Vector[JitValue],
      arguments: List[JitValue],
      rest: List[Goal],
      state: ReadingState
  ): Next =
    if fillings.size < compiled.emission.slotCount then
      throw FillingsFewerThanSlots(compiled.emission.slotCount, fillings.size)
    if compiled.emission.clauses.isEmpty then tailcall(nextHead(rest, state))
    else tailcall(nextHead(Goal.Clauses(compiled, fillings, 0, arguments) :: rest, state))

  /** The code compiled by the configuration's strategy and backend
    * (code_compiled/2): the emission's slot count is the code's, or the
    * strategy broke its contract and the compilation throws.
    */
  def compiledCode(code: Code): CompiledCode =
    val emission = configuration.strategy.emission(code)
    val slots = CodeReading.slotCount(code)
    if emission.slotCount != slots then throw EmissionSlotCount(code, slots, emission.slotCount)
    configuration.backend.compiled(code, emission)

  /** A head applied to the arguments: the head itself when there is none;
    * otherwise one step, the head applied to the first (jit_applied/3), and
    * the rest applied to its heads.
    */
  private def applied(head: JitHead, arguments: List[JitValue], rest: List[Goal], state: ReadingState): Next =
    arguments match
      case Nil => done(Computed.Done(Some((head, Machine(rest))), state))
      // The empty parallel set applied to anything is itself (a least term
      // of ⊑_O applied to anything is one).
      case _ if head == EmptyParallel => done(Computed.Done(Some((head, Machine(rest))), state))
      case argument :: later =>
        state.budget.charged match
          case None => done(Computed.Stopped(state))
          case Some(charged) => appliedTo(head, argument, later, rest, state.copy(budget = charged))

  private def appliedTo(
      head: JitHead,
      argument: JitValue,
      later: List[JitValue],
      rest: List[Goal],
      state: ReadingState
  ): Next = head match
    case EmptyParallel => done(Computed.Done(Some((EmptyParallel, Machine(rest))), state))
    case gezi.ir.Thunk(code, holes, fillings) =>
      val filled = CodeReading.holeFilled(holes.head, holes.tail, fillings, shared(code, holes.head, argument))
      if holes.tail.nonEmpty then applied(JitHead.Lambda(code, holes.tail, filled), later, rest, state)
      else
        val entry = BlockEntry(code, holes.head, fillings, written(argument))
        val entered = state.entered(code)
        if configuration.nativeBlocks.entered(entry, JitRunState.of(entered, configuration).blockRecord) then
          blockEntered(entry, filled, later, rest, entered)
        else instance(code, filled, later, rest, entered)
    case gezi.weakhead.Neutral(variable, neutralArguments) =>
      applied(JitHead.Neutral(variable, neutralArguments :+ argument), later, rest, state)
    case gezi.ir.Parallel(left, right) =>
      tailcall(nextHead(Goal.Evaluation(JitValue.Parallel(JitValue.Apply(left, argument), JitValue.Apply(right, argument)), later) :: rest, state))
    case gezi.jit.Represented(representation, value) =>
      if facts.shapeChecked(representation.familyIdentity) then eliminationExtended(representation, value, Vector.empty, argument, later, rest, state)
      else tailcall(nextHead(Goal.Heads(eliminationEncoded(representation, value, Vector(argument)), later) :: rest, state))
    case gezi.jit.Elimination(representation, value, cases) =>
      eliminationExtended(representation, value, cases, argument, later, rest, state)
    case gezi.jit.NativeApplication(instruction, native, missing, nativeArguments) =>
      val extended = nativeArguments :+ argument
      if missing - 1 > 0 then applied(JitHead.NativeApplication(instruction, native, missing - 1, extended), later, rest, state)
      else tailcall(nextHead(Goal.Heads(nativeAppliedHeads(instruction, native, extended), later) :: rest, state))

  /** The argument as it fills the hole of the code: under `instanceTable`,
    * when the hole's slot is one the code may read more than once
    * (`Code.slotsReadMoreThanOnce`) and reading the argument may cost more
    * than one layer, a cell over it (`JitValue.Cell`), which stands for the
    * closed thunk of `JitRules.cellCode` with the argument as its one
    * filling; otherwise the argument itself. A
    * cell's instance is always tabled (`instance` skips its `TableCost`), so
    * the slot's reads after the first take its heads from the table: the
    * value is shared as call by need shares it, whatever the costs counted
    * on the codes the argument's reading runs. Reads of syntax look through
    * a cell (`layerOf`). Its purpose (the defect of 2026-11-02): a code
    * judged unprofitable in a hot loop, and so no longer tabled, took the
    * sharing away from a later loop over the same code that read each value
    * twice, which then took steps exponential in its length; the law test
    * `TableSharingLawTest` reproduces it. Which slots are read twice is
    * syntax, a count of occurrences, and no type.
    *
    * MEASURED (2026-11-02, a scratch probe of `TableSharingLawTest`'s
    * programs, the trial 4, after a hot loop of 64 calls of `iterate` and of
    * the function that reads its argument twice): without cells, the steps
    * at k = 8, 12 and 16 were 11,510, 184,310 and 2,949,110, those of the
    * JIT with no table, against 1,221, 2,005 and 2,949 from an empty table.
    */
  private def shared(code: Code, hole: Hole, argument: JitValue): JitValue = hole match
    case Hole.Bound(slot)
        if configuration.instanceTable && Code.slotsReadMoreThanOnce(code).contains(slot) && readingCosts(argument) =>
      JitValue.Cell(argument)
    case _ => argument

  /** Whether reading the value to its heads may cost more than one layer:
    * not for a value that is its own head (represented, `Evaluated`,
    * neutral), a lambda, a cell, an opaque instruction or an instruction of a lambda.
    */
  private def readingCosts(value: JitValue): Boolean = value match
    case JitValue.Represented(_, _) | JitValue.Evaluated(_, _, _) | JitValue.Neutral(_, _) | JitValue.Cell(_) => false
    case JitValue.Instruction(instruction) if instruction.opaque                                     => false
    case JitValue.Thunk(_, holes, _)                                                        => holes.isEmpty
    case JitValue.Apply(_, _) | JitValue.Choice(_) | JitValue.Parallel(_, _) => true

  /** The instance at the entry, its last hole filled, run as a native block
    * of the configuration's mechanism (`NativeBlockMechanism`): the fillings
    * that may be the self filling read to their heads first, each within
    * `JitRules.selfReadingSteps` steps (`selfFound`); the block run with the
    * artifact kept for the code (`JitRunState.blockArtifacts`); its outcome
    * recorded (`JitRunState.blockRecord`, costs, never a type) and the
    * artifact it returns kept; the block's value then taken as the
    * instance's head or evaluated by the machine, its steps and native calls
    * counted. A block that falls back leaves the instance to the machine from
    * its entry.
    */
  private def blockEntered(
      entry: BlockEntry,
      filled: Vector[JitValue],
      later: List[JitValue],
      rest: List[Goal],
      state: ReadingState
  ): Next =
    val candidates = entry.fillings.toList.filter {
      case JitValue.Instruction(_) | JitValue.Represented(_, _) => false
      case _                                                   => true
    }
    tailcall(selfFound(candidates, state)).flatMap { (self, afterSelf) =>
      val budget = afterSelf.budget
      val run = JitRunState.of(afterSelf, configuration)
      val result = configuration.nativeBlocks.run(
        this,
        entry,
        self,
        run.blockArtifacts.get(entry.code),
        budget.limit - budget.spent,
        budget.spent,
        budget.stop
      )
      val recorded = run.copy(
        blockRecord = run.blockRecord.recorded(entry.code, result.outcome),
        blockArtifacts = result.artifact.fold(run.blockArtifacts)(run.blockArtifacts.updated(entry.code, _))
      )
      result.outcome match
        case BlockOutcome.FellBack(_) =>
          instance(entry.code, filled, later, rest, afterSelf.copy(jitState = recorded))
        case BlockOutcome.Finished(value, costs) =>
          val counts = costs.callsByNative.foldLeft(recorded.counts)((current, call) =>
            current.copy(
              nativeCalls = current.nativeCalls + call._2,
              callsByNative = current.callsByNative.updated(call._1, current.callsOf(call._1) + call._2)
            )
          )
          val counted = afterSelf.copy(budget = budget.copy(spent = budget.spent + costs.steps), jitState = recorded.copy(counts = counts))
          value match
            case JitValue.Represented(representation, native) => applied(JitHead.Represented(representation, native), later, rest, counted)
            case other => tailcall(nextHead(Goal.Evaluation(other, later) :: rest, counted))
    }

  /** The first of the fillings whose only head, read within
    * `JitRules.selfReadingSteps` steps, is a lambda that holds the filling
    * itself among its fillings, spelled alike (the recursion of a fixed
    * point combinator: reading the self gives a lambda over the self), with
    * that head; and the state after the reads. A read that stops at that
    * bound reads no head, and the reading's own limit is kept.
    */
  private def selfFound(
      pending: List[JitValue],
      state: ReadingState
  ): Trampoline[(Option[SelfFilling], ReadingState)] =
    pending match
      case Nil => done((None, state))
      case candidate :: others =>
        val limit = state.budget.limit
        val capped = state.copy(budget = state.budget.copy(limit = math.min(limit, state.budget.spent + JitRules.selfReadingSteps)))
        tailcall(heads(candidate).pull.run(capped)).flatMap {
          case Computed.Done(Some((JitHead.Lambda(foundCode, foundHoles, foundFillings), more)), after)
              if foundFillings.exists(JitRules.spelledAlike(_, candidate)) =>
            tailcall(more.pull.run(after)).flatMap { computed =>
              val (only, afterMore) = computed match
                case Computed.Done(None, found) => (true, found)
                case Computed.Done(_, found)    => (false, found)
                case Computed.Stopped(found)    => (false, found)
              val restored = afterMore.copy(budget = afterMore.budget.copy(limit = limit))
              if only then done((Some(SelfFilling(candidate, foundCode, foundHoles, foundFillings)), restored))
              else tailcall(selfFound(others, restored))
            }
          case Computed.Done(_, after) =>
            tailcall(selfFound(others, after.copy(budget = after.budget.copy(limit = limit))))
          case Computed.Stopped(after) =>
            tailcall(selfFound(others, after.copy(budget = after.budget.copy(limit = limit))))
        }

  /** The represented value applied to the cases and then to the argument
    * (elimination_extended/5): an elimination head while the codec's count
    * of cases is not reached; then the chosen case's heads applied to its
    * fields.
    */
  private def eliminationExtended(
      representation: Representation,
      value: NativeValue,
      cases: Vector[JitValue],
      argument: JitValue,
      later: List[JitValue],
      rest: List[Goal],
      state: ReadingState
  ): Next =
    val extended = cases :+ argument
    val (count, branch, fields) = codecBranch(representation, value)
    if count - extended.size > 0 then applied(JitHead.Elimination(representation, value, extended), later, rest, state)
    else tailcall(nextHead(Goal.Evaluation(extended(branch - 1), fields.toList ++ later) :: rest, state))

  /** The codec's reading of the value as the branch-th of its count of
    * cases, over the run-time values of the fields (codec_branch/5).
    */
  def codecBranch(representation: Representation, value: NativeValue): (Int, Int, Vector[JitValue]) =
    (representation, value) match
      case (Representation.Data(familyIdentity, parameter), _) =>
        val family = dataFamily(familyIdentity)
        val DataLayer(constructor, fields) = family.layer(parameter, value)
        (family.constructors(parameter).size, constructor + 1, fieldValues(family, parameter, constructor, fields))
      case (Representation.ListOf(element), NativeValue.Listed(list)) =>
        val (count, branch, fields) = ListCodec.eliminatedBranch(element, list)
        (count, branch, fields.map(fieldValue))
      case _ => throw IllegalStateException(s"a value of another representation than ${representation.familyIdentity.shown}")

  /** The data family of the identity, which a representation of the JIT names
    * only when the backend has it.
    */
  private def dataFamily(identity: FamilyIdentity): DataFamily =
    nativeBackend.family(identity).getOrElse(throw IllegalStateException(s"no data family ${identity.shown} in the backend"))

  /** The run-time values of a layer's fields at the parameter, each
    * represented in its field's family at its field's parameter.
    */
  private def fieldValues(
      family: DataFamily,
      parameter: Option[NativeValue],
      constructor: Int,
      fields: Vector[NativeValue]
  ): Vector[JitValue] =
    family.constructors(parameter)(constructor).fields.zip(fields).map((field, value) =>
      JitValues.fieldTerm(field.representation(parameter), value)
    )

  /** The run-time value of a field a list hands out. */
  private def fieldValue(field: ListElementField[JitValue]): JitValue = field match
    case ListElementField.Filtered(item, element) => JitValue.Parallel(item, element)
    case ListElementField.Represented(element, list) =>
      JitValue.Represented(Representation.ListOf(element), NativeValue.Listed(list))
    case ListElementField.Term(term) => term

  // ---- reading terms by their layers ----

  /** The term as written (written_term/2): an `Evaluated` value's written
    * operand, any other value itself.
    */
  private def written(value: JitValue): JitValue = value match
    case JitValue.Evaluated(found, _, _) => found
    case other                           => other

  /** The value read one layer (term_layer/2). Every value is its own layer;
    * reading a value that is an instruction (the program's syntax, or a
    * value the JIT built that equals an instruction, one object in the pool)
    * is one read of syntax (`JitCounts.syntaxReads`), and any other value is
    * read without one. An opaque instruction has no layer.
    */
  private def layer(value: JitValue): SyntaxRead[JitValue] = value match
    case JitValue.Instruction(instruction) =>
      if instruction.opaque then throw IllegalStateException(s"the $instruction has no layer")
      SyntaxRead(value, 1)
    case other => SyntaxRead.pure(other)

  /** The value's layer when it has one: a represented value and an
    * `Evaluated` value have none.
    */
  private def layerOf(value: JitValue): SyntaxRead[Option[JitValue]] = value match
    case JitValue.Represented(_, _) | JitValue.Evaluated(_, _, _) => SyntaxRead.pure(None)
    case JitValue.Cell(inner)                                    => layerOf(inner)
    case other                                                    => layer(other).map(Some(_))

  /** The representation whose decoding criterion the term is
    * (jit_decoding_criterion/2): the instruction of a define that names a data
    * family of the backend that takes no parameter
    * (`BackendFacts.criterionFamily`: a declared family's criterion, or a
    * define whose first `native_specialization` names a codec); the
    * application of a define that names a family taking a criterion
    * parameter to as many criteria; the application of a define whose first
    * `native_specialization` names a family that takes one, F, to a term P
    * that decodes by its syntax in the parameter's family, the
    * representation of F at that value; or the application of a define with
    * `native_specialization(list)` to an element filter E, the
    * representation list(E). The reads of syntax are not counted: the
    * refinement asks it while it compiles, outside a reading.
    */
  def decodingCriterion(criterion: JitValue): Option[Representation] =
    decodingCriterionRead(criterion)(using KnownCriteria.none).result

  /** `decodingCriterion`, with its reads of syntax: an instruction's criterion is
    * taken from the criteria the reading already read, and otherwise read
    * and returned as learned (`KnownCriteria`).
    */
  private def decodingCriterionRead(criterion: JitValue)(using
      known: KnownCriteria
  ): SyntaxRead[Option[Representation]] =
    criterion match
      case JitValue.Instruction(instruction) =>
        known.byInstruction.get(instruction) match
          case Some(found) => SyntaxRead.pure(found)
          case None =>
            val read = criterionRead(criterion)
            read.copy(learned = read.learned.updated(instruction, read.result))
      case _ => criterionRead(criterion)

  /** The representation whose decoding criterion the term is, read from its
    * syntax (`decodingCriterion`).
    */
  private def criterionRead(criterion: JitValue)(using KnownCriteria): SyntaxRead[Option[Representation]] =
    criterion match
      case JitValue.Instruction(instruction) if facts.criterionFamily.contains(instruction) =>
        SyntaxRead.pure(
          nativeBackend
            .family(facts.criterionFamily(instruction))
            .filter(family => family.parameterFamily.isEmpty && family.criterionArity == 0)
            .map(family => Representation.Data(family.identity, None))
        )
      case _ =>
        criterionSpine(criterion, Vector.empty).flatMap {
          case Some((function, arguments)) =>
            criterionFamily(function, arguments.size) match
              case Some(family) =>
                arguments
                  .foldLeft(SyntaxRead.pure(Option(Vector.empty[Representation])))((found, argument) =>
                    SyntaxRead.chained(found)(sofar => decodingCriterionRead(argument).map(_.map(sofar :+ _)))
                  )
                  .map(_.map(criteria => Representation.Data(family.identity, Some(NativeValue.CriterionParameters(criteria)))))
              case None => valueParameterCriterionRead(criterion)
          case None => valueParameterCriterionRead(criterion)
        }

  /** The family of criterion parameters whose criterion is the instruction,
    * applied to as many criteria as the family takes (`criterionArity`),
    * at least one.
    */
  private def criterionFamily(function: Instruction, arguments: Int): Option[DataFamily] =
    facts.criterionFamily
      .get(function)
      .flatMap(nativeBackend.family)
      .filter(family => arguments > 0 && family.criterionArity == arguments)

  /** The term as an instruction that names a family (`BackendFacts.criterionFamily`)
    * applied to arguments, read along its spine of applications, through the layers of
    * the instructions and thunks it meets: a filter writes a family's criterion
    * applied to its parameters, `C @ P1 @ … @ Pk`, and the parameters are
    * read from it as written, never from a value.
    */
  private def criterionSpine(term: JitValue, arguments: Vector[JitValue]): SyntaxRead[Option[(Instruction, Vector[JitValue])]] =
    term match
      case JitValue.Instruction(instruction) if facts.criterionFamily.contains(instruction) => SyntaxRead.pure(Some((instruction, arguments)))
      case JitValue.Apply(function, argument) => criterionSpine(function, argument +: arguments)
      case _ =>
        layerOf(term).flatMap {
          case Some(JitValue.Apply(function, argument)) => criterionSpine(function, argument +: arguments)
          case _                                        => SyntaxRead.pure(None)
        }

  /** The representation whose decoding criterion the term is, a list's or
    * a family's at a value parameter (`decodingCriterion`).
    */
  private def valueParameterCriterionRead(criterion: JitValue)(using KnownCriteria): SyntaxRead[Option[Representation]] =
        layerOf(criterion).flatMap {
          case Some(JitValue.Apply(JitValue.Instruction(function), element))
              if facts.criterionFamily.get(function).contains(Representation.listFamily) =>
            SyntaxRead.pure(Some(Representation.ListOf(element)))
          case Some(JitValue.Apply(JitValue.Instruction(function), parameterTerm)) =>
            facts.criterionFamily.get(function).flatMap(nativeBackend.family) match
              case Some(family) =>
                family.parameterFamily match
                  case Some(parameterFamily) =>
                    syntaxDecoded(parameterFamily, None, parameterTerm).map(
                      _.map(parameter => Representation.Data(family.identity, Some(parameter)))
                    )
                  case None => SyntaxRead.pure(None)
              case None => SyntaxRead.pure(None)
          case _ => SyntaxRead.pure(None)
        }

  /** The value of the family at the parameter that the term spells by its
    * syntax alone, read layer by layer: an application, along its spine, of
    * the define bound to one of the family's constructors at the parameter to
    * as many arguments as the constructor has fields, each argument the
    * spelling of a value of its field's family at its field's parameter;
    * `None` for any other term. A term that is a fallback point
    * `x + (x ∥ T')` (`fallbackPoint`), as the refinement writes at every
    * level of a literal, is read through to its operand x, decoded at the
    * same family and parameter: the choice equals x whatever T' names, by
    * equation (6) of the formal definition, M + (M ∥ N) = M, so T' need not
    * name the field's representation. It evaluates nothing: a parameter is
    * read from the decoding criterion the term carries (`x ∥ word_type W`, W
    * a numeral written out), never from a value.
    */
  private def syntaxDecoded(
      familyIdentity: FamilyIdentity,
      parameter: Option[NativeValue],
      term: JitValue,
  )(using KnownCriteria): SyntaxRead[Option[NativeValue]] =
    nativeBackend.family(familyIdentity) match
      case None => SyntaxRead.pure(None)
      case Some(family) =>
        val constructors = family.constructors(parameter)
        val defines = constructors.map(constructor => facts.boundDefine(constructor.native))
        spineRead(term, Vector.empty).flatMap {
          case Some((JitValue.Instruction(head), arguments)) =>
            defines.indexOf(Some(head)) match
              case -1 => SyntaxRead.pure(None)
              case index if family.excluded(parameter, index) || constructors(index).fields.size != arguments.size =>
                SyntaxRead.pure(None)
              case index =>
                constructors(index).fields
                  .zip(arguments)
                  .foldLeft(SyntaxRead.pure(Option(Vector.empty[NativeValue]))) { case (decoded, (field, argument)) =>
                    SyntaxRead.chained(decoded)(values =>
                      field.representation(parameter) match
                        case Representation.Data(fieldFamily, fieldParameter) =>
                          syntaxDecoded(fieldFamily, fieldParameter, argument).map(_.map(values :+ _))
                        case Representation.ListOf(_) => SyntaxRead.pure(None)
                    )
                  }
                  .map(_.map(fields => family.built(parameter, DataLayer(index, fields))))
          case Some(_) => SyntaxRead.pure(None)
          case None =>
            SyntaxRead.chained(fallbackPoint(term)) { case (operand, _) =>
              syntaxDecoded(familyIdentity, parameter, operand)
            }
        }

  /** The head and the arguments of the term's spine of applications, read
    * layer by layer until an instruction that is the define bound to a native, or
    * a layer that is no application; `None` when the head is not an instruction.
    */
  private def spineRead(
      term: JitValue,
      arguments: Vector[JitValue],
  ): SyntaxRead[Option[(JitValue, Vector[JitValue])]] =
    term match
      case JitValue.Instruction(instruction) if facts.isBoundToNative(instruction) => SyntaxRead.pure(Some((term, arguments)))
      case JitValue.Apply(function, argument) => spineRead(function, argument +: arguments)
      case _ =>
        layerOf(term).flatMap {
          case Some(JitValue.Apply(function, argument)) => spineRead(function, argument +: arguments)
          case _                                        => SyntaxRead.pure(None)
        }

  /** The criterion the value reaches by slot steps (criterion_reached/2):
    * itself when it is a decoding criterion, or the instance of a thunk of
    * one hole whose code is a slot, applied to an argument, when that
    * reaches one.
    */
  private def criterionReached(value: JitValue)(using KnownCriteria): SyntaxRead[Option[JitValue]] =
    val term = written(value)
    decodingCriterionRead(term).flatMap(criterion =>
      if criterion.isDefined then SyntaxRead.pure(Some(term))
      else
        SyntaxRead.chained(SyntaxRead.chained(layerOf(term))(lastHoleStep(slotSteps = true, _)))(
          criterionReached(_)
        )
    )

  /** The representation of the decode point whose criterion side the value
    * is, if it is one.
    */
  private def decodingRepresentation(criterionSide: JitValue)(using KnownCriteria): SyntaxRead[Option[Representation]] =
    SyntaxRead.chained(criterionReached(criterionSide))(decodingCriterionRead(_))

  /** The β step's instance when the layer applies a thunk to the last of its
    * holes and the thunk's code is a slot, or with `slotSteps` false also a
    * parallel (last_hole_step/3).
    */
  private def lastHoleStep(slotSteps: Boolean, layer: JitValue): SyntaxRead[Option[JitValue]] =
    layer match
      case JitValue.Apply(function, argument) =>
        lastHoleThunk(function).map(_.flatMap {
          case (code, Vector(hole), fillings) =>
            val admitted = code.layer match
              case Slot(_)        => true
              case Parallel(_, _) => !slotSteps
              case _                   => false
            if admitted then
              Some(CodeReading.instance(code, CodeReading.holeFilled(hole, Vector.empty, fillings, argument)))
            else None
          case _ => None
        })
      case _ => SyntaxRead.pure(None)

  /** The value is a thunk with holes, or one applied to fewer arguments than
    * its holes, and the thunk with those arguments filled in
    * (last_hole_thunk/2).
    */
  private def lastHoleThunk(value: JitValue): SyntaxRead[Option[(Code, Vector[Hole], Vector[JitValue])]] =
    layerOf(written(value)).flatMap {
      case Some(JitValue.Thunk(code, holes, fillings)) if holes.nonEmpty => SyntaxRead.pure(Some((code, holes, fillings)))
      case Some(JitValue.Apply(inner, argument)) =>
        lastHoleThunk(inner).map(_.flatMap { (code, holes, fillings) =>
          if holes.size >= 2 then Some((code, holes.tail, CodeReading.holeFilled(holes.head, holes.tail, fillings, argument)))
          else None
        })
      case _ => SyntaxRead.pure(None)
    }

  /** The members are a fallback point's (fallback_members/3): an operand
    * and its parallel, compared by spelling (every value interned, one
    * spelling is one object, compared by reference), whose criterion reaches
    * a decoding criterion; the operand and the representation.
    */
  private def fallbackMembers(members: Vector[JitValue])(using KnownCriteria): SyntaxRead[Option[(JitValue, Representation)]] =
    members match
      case Vector(operand, filtered) =>
        layerOf(written(filtered)).flatMap {
          case Some(JitValue.Parallel(filteredOperand, criterion)) if filteredOperand == operand =>
            decodingRepresentation(criterion).map(_.map((operand, _)))
          case _ => SyntaxRead.pure(None)
        }
      case _ => SyntaxRead.pure(None)

  /** The value, read as written, is a fallback point (fallback_point/3). */
  private def fallbackPoint(value: JitValue)(using KnownCriteria): SyntaxRead[Option[(JitValue, Representation)]] =
    val term = written(value)
    term match
      case JitValue.Instruction(instruction) if facts.bound(instruction) => SyntaxRead.pure(None)
      case _ =>
        layerOf(term).flatMap {
          case Some(JitValue.Choice(members)) => fallbackMembers(members)
          case _                              => SyntaxRead.pure(None)
        }

  /** The value is a decode point, or reaches one by slot steps and parallel
    * steps (decode_point_reached/3): its operand and representation.
    */
  private def decodePointReached(value: JitValue)(using KnownCriteria): SyntaxRead[Option[(JitValue, Representation)]] =
    SyntaxRead.chained(layerOf(written(value))) {
      case JitValue.Parallel(operand, criterion) => decodingRepresentation(criterion).map(_.map((operand, _)))
      case other =>
        SyntaxRead.chained(lastHoleStep(slotSteps = false, other))(decodePointReached(_))
    }

  /** The representation the value is ready in for a native (native_ready/2
    * read for its representation): a represented value's, a decode point's
    * or a fallback point's.
    */
  private def readyRepresentation(value: JitValue)(using KnownCriteria): SyntaxRead[Option[Representation]] =
    written(value) match
      case JitValue.Represented(found, _) => SyntaxRead.pure(Some(found))
      case term =>
        decodePointReached(term).flatMap {
          case Some((_, representation)) => SyntaxRead.pure(Some(representation))
          case None                      => fallbackPoint(term).map(_.map(_._2))
        }

  /** The value is ready in the place (native_ready/2). */
  private def nativeReady(value: JitValue, place: Place)(using KnownCriteria): SyntaxRead[Boolean] = place match
    case Place.In(representation) => readyRepresentation(value).map(_.contains(representation))
    case Place.ItemOf(element) =>
      decodingCriterionRead(element).flatMap {
        case Some(representation) => nativeReady(value, Place.In(representation))
        case None                 => SyntaxRead.pure(false)
      }
    case Place.TailOf(element) => nativeReady(value, Place.In(Representation.ListOf(element)))

  /** The places of the native's parameters when its result is in the
    * representation, if it can be (representation_matched/2). A result at
    * the call's parameter (`NativePlace.Parameter`) takes the parameter of
    * the representation, which a decoding criterion written in the term
    * named, where the native admits it (`Native.parameterAdmitted`).
    */
  private def placesFor(native: NativeName, representation: Representation): Option[Vector[Place]] =
    val representations = nativeBackend.natives(native)
    val bound: Option[(Option[JitValue], Option[NativeValue])] = (representations.result, representation) match
      case (NativePlace.Fixed(found), _) if found == representation => Some((None, None))
      case (NativePlace.AnyList, Representation.ListOf(found))      => Some((Some(found), None))
      case (NativePlace.Parameter(family), Representation.Data(found, parameter))
          if found == family && representations.parameterAdmitted(parameter) =>
        Some((None, parameter))
      case _ => None
    bound
      .filterNot(_ => representations.takesNaturalList)
      .map((element, parameter) => representations.parameters.map(place(_, element, parameter)))

  /** The place of a native's parameter under the call's list element filter
    * and family parameter.
    */
  private def place(native: NativePlace, element: Option[JitValue], parameter: Option[NativeValue]): Place =
    (native, element) match
      case (NativePlace.Fixed(representation), _)   => Place.In(representation)
      case (NativePlace.Parameter(family), _)       => Place.In(Representation.Data(family, parameter))
      case (NativePlace.OfParameter(of), _)         => Place.In(of(parameter))
      case (NativePlace.AnyList, Some(found))       => Place.In(Representation.ListOf(found))
      case (NativePlace.Item, Some(found))          => Place.ItemOf(found)
      case (NativePlace.Tail, Some(found))          => Place.TailOf(found)
      case _ => throw IllegalStateException(s"a list's place with no element filter: $native")

  /** The spine of applications read through the layers (spine_listed/4): its
    * head and the arguments in order; a native's instruction and a represented
    * value are heads.
    */
  private def spineListed(value: JitValue): SyntaxRead[(JitValue, Vector[JitValue])] =
    @scala.annotation.tailrec
    def listed(current: JitValue, arguments: List[JitValue], reads: Long): SyntaxRead[(JitValue, Vector[JitValue])] =
      written(current) match
        case term @ JitValue.Represented(_, _) => SyntaxRead((term, arguments.toVector), reads)
        case term @ JitValue.Instruction(instruction) if facts.bound(instruction) => SyntaxRead((term, arguments.toVector), reads)
        case term =>
          val found = layerOf(term)
          found.result match
            case Some(JitValue.Apply(function, argument)) => listed(function, argument :: arguments, reads + found.reads)
            case _                                        => SyntaxRead((term, arguments.toVector), reads + found.reads)
    listed(value, Nil, 0)

  /** The natives bound to the spine's head, in the index's order. */
  private def headNatives(head: JitValue): Vector[BoundNative] = head match
    case JitValue.Instruction(instruction) => facts.natives.getOrElse(instruction, Vector.empty)
    case _                          => Vector.empty

  /** The value is a type-filtered constructor of the representation, whose
    * native has the count of parameters (filtered_constructor_parameters/3).
    */
  private def filteredConstructorParameters(value: JitValue, representation: Representation)(using KnownCriteria): SyntaxRead[Option[Int]] =
    filteredCount(value, representation).result

  /** The count of `filteredConstructorParameters`, trampolined: a chain of
    * type-filtered constructors, a list of a thousand conses among them, is
    * read down its arguments on the heap.
    */
  private def filteredCount(value: JitValue, representation: Representation)(using
      KnownCriteria
  ): Trampoline[SyntaxRead[Option[Int]]] =
    written(value) match
      case JitValue.Represented(_, _) => done(SyntaxRead.pure(None))
      case term =>
        val spine = spineListed(term)
        val (head, arguments) = spine.result
        def first(natives: List[BoundNative], sofar: SyntaxRead[Unit]): Trampoline[SyntaxRead[Option[Int]]] = natives match
          case Nil => done(SyntaxRead.pure(None).joined(sofar))
          case native :: rest =>
            placesFor(native.name, representation) match
              case Some(places) if native.parameterCount == arguments.size =>
                tailcall(filteredArguments(arguments.zip(places).toList)).flatMap(filtered =>
                  if filtered.result then done(SyntaxRead.pure(Some(native.parameterCount)).joined(sofar).joined(filtered))
                  else first(rest, sofar.joined(filtered))
                )
              case _ => tailcall(first(rest, sofar))
        first(headNatives(head).toList, spine.map(_ => ()))

  private def filteredArguments(pairs: List[(JitValue, Place)])(using
      KnownCriteria
  ): Trampoline[SyntaxRead[Boolean]] = pairs match
    case Nil => done(SyntaxRead.pure(true))
    case (argument, place) :: rest =>
      val ready = nativeReady(argument, place)
      if ready.result then tailcall(filteredArguments(rest)).map(_.joined(ready))
      else
        val constructed = place match
          case Place.TailOf(element)    => Some(Representation.ListOf(element))
          case Place.In(representation) => Some(representation)
          case Place.ItemOf(_)          => None
        constructed match
          case None => done(ready)
          case Some(found) =>
            tailcall(filteredCount(argument, found)).flatMap(count =>
              if count.result.exists(_ > 0) then
                filteredArguments(rest).map(_.joined(ready).joined(count))
              else done(SyntaxRead.pure(false).joined(ready).joined(count))
            )

  private def filteredConstructor(value: JitValue, representation: Representation)(using KnownCriteria): SyntaxRead[Boolean] =
    filteredConstructorParameters(value, representation).map(_.isDefined)

  // ---- state ----

  /** The state with the reads of syntax counted (`JitCounts.syntaxReads`)
    * and the criteria they learned kept (`JitRunState.criteria`).
    */
  private def syntaxCounted(state: ReadingState, read: SyntaxRead[Any]): ReadingState =
    if read.reads == 0 && read.learned.isEmpty then state
    else
      val current = JitRunState.of(state, configuration)
      state.copy(jitState =
        current.copy(
          counts = current.counts.copy(syntaxReads = current.counts.syntaxReads + read.reads),
          criteria = if read.learned.isEmpty then current.criteria else current.criteria ++ read.learned
        )
      )

  /** The criteria the reading has already read (`KnownCriteria`). */
  private def known(state: ReadingState): KnownCriteria = KnownCriteria(JitRunState.of(state, configuration).criteria)

  /** The result of the reads of syntax, the reads counted and the criteria
    * learned kept in the state.
    */
  private def syntaxResult[Result](read: SyntaxRead[Result]): Computation[ReadingState, Result] =
    Computation.modified[ReadingState](syntaxCounted(_, read)).map(_ => read.result)

  /** The result of the reads of syntax under the reading's known criteria,
    * the reads counted and the criteria learned kept in the state.
    */
  private def syntaxRead[Result](reading: KnownCriteria ?=> SyntaxRead[Result]): Computation[ReadingState, Result] =
    Computation.state[ReadingState].flatMap(state => syntaxResult(reading(using known(state))))

  /** The reading's known criteria. */
  private def syntaxContext: Computation[ReadingState, KnownCriteria] =
    Computation.state[ReadingState].map(known)

  private def run: Computation[ReadingState, JitRunState] =
    Computation.state[ReadingState].map(JitRunState.of(_, configuration))

  private def runModified(change: JitRunState => JitRunState): Computation[ReadingState, Unit] =
    Computation.modified[ReadingState](state => state.copy(jitState = change(JitRunState.of(state, configuration))))

  private def countsModified(change: JitCounts => JitCounts): Computation[ReadingState, Unit] =
    runModified(found => found.copy(counts = change(found.counts)))

  private def computedStream(computation: Computation[ReadingState, Stream]): Stream =
    computedAnswers(computation)

  // ---- natives ----

  /** The native applied to the values, its result in the representation;
    * the call counted (native_called/3).
    */
  private def nativeCalled(native: NativeName, values: Vector[NativeArgument], representation: Representation): Computation[ReadingState, NativeValue] =
    countsModified(counts =>
      counts.copy(
        nativeCalls = counts.nativeCalls + 1,
        callsByNative = counts.callsByNative.updated(native, counts.callsOf(native) + 1)
      )
    ).map(_ => nativeBackend.natives(native).implementation(values))

  /** The heads of the define at the instruction, bound to the native, given its
    * last argument (jit_applied/3 on a native application): the native's
    * result on each combination of its arguments' values when every
    * argument is ready (for a data family's constructor, when every
    * argument is written represented, below); otherwise the define's own
    * heads applied to the arguments.
    *
    * What licenses forcing the operands of a native other than a
    * constructor: a ready argument (written
    * represented, or under a decode point or a fallback point of the
    * place's criterion) is read to its values (`argumentsValued`,
    * `nativeValue`) before the native is called, so an operand with no head
    * gives the application no head. That equals the define only where the
    * `native` declaration's equivalence, native = define, also covers an
    * operand with no head: the define applied to such an operand at that
    * place has no head either, that is, the define is strict in the place.
    * The host chooses nothing here: the `native` declaration and the
    * criterion written in the term decide, and the equivalence is the
    * declaration's proof obligation.
    *
    * A data family's constructor (`NativeBackend.constructorNatives`, a
    * backend fact) is not strict in its fields: its define answers a lambda
    * without reading them (`successor` is λn.λz.λs. s n). So its native is
    * called only when every argument is already written represented, which
    * forces nothing; otherwise the define's heads are taken, the fields
    * left as the term writes them, decode points included, until a strict
    * native or a decoding reads them.
    *
    * FIXME: the strictness of the natives of the corpus modules is not yet https://github.com/Atry/private-overlay/issues/1935
    * audited (`natural_plus` and the unary comparisons, the binary and twin
    * arithmetic, `fixpoint` by derivation, `every_assignment`,
    * `billboard_go`, `concatenation_fit`, `workers_place`, the `wren_binary_*`
    * operations): a native whose define is not strict in a place it forces
    * loses answers as `successor` did. Candidate: a native is called eagerly
    * only where the term spells a proved strictness property at the call
    * (the whole-block proof structure of the interface review of
    * 2026-11-03).
    */
  private def nativeAppliedHeads(instruction: Instruction, native: BoundNative, arguments: Vector[JitValue]): Stream =
    computedStream(syntaxRead(argumentsReady(native.name, arguments)).flatMap {
        case None => Computation.pure(genericApplied(instruction, arguments))
        case Some(_) if nativeBackend.constructorNatives.contains(native.name) && !arguments.forall(written(_).layer.isInstanceOf[Represented]) =>
          Computation.pure(genericApplied(instruction, arguments))
        case Some((places, result)) =>
          argumentsValued(arguments, places).map(valued =>
            if valued.exists(_.isInstanceOf[Valued.Unvalued]) then
              genericApplied(instruction, valuedTerms(valued, places))
            else
              valuedCombinations(valued).flatMap(values =>
                Answers.computed(nativeCalled(native.name, values, result).map(found => Vector(JitHead.Represented(result, found))))
              )
          )
    })

  /** Every argument is ready at its place, the list's element filter taken
    * from the tail before the items are read (native_arguments_ready/2):
    * the places and the result's representation. A native whose result is
    * at the call's parameter is ready only on arguments already written
    * represented (`parameterisedReady`).
    */
  private def argumentsReady(native: NativeName, arguments: Vector[JitValue])(using KnownCriteria): SyntaxRead[Option[(Vector[Place], Representation)]] =
    val representations = nativeBackend.natives(native)
    representations.result match
      case NativePlace.Parameter(family) => SyntaxRead.pure(parameterisedReady(representations, family, arguments))
      case _                             => listedOrFixedReady(representations, arguments)

  /** The places and the result's representation of a native whose result
    * is at the call's parameter, when every argument is written represented
    * and in its place at the parameter the native computes from their
    * values (`Native.resultParameter`, applied to represented values only);
    * otherwise none, and the application is read generically.
    *
    * FIXME (the interface review of 2026-11-03): https://github.com/Atry/private-overlay/issues/1936
    * this bottom-up route derives the result's
    * parameter in Scala from the operands' values. The review moves it into
    * lemmas: type-preservation lemmas write the result's criterion into the
    * term (for example `word_cell @ b @ (w ∥ word_type n) = (…) ∥ word_type
    * (successor n)`), and a native's place is read only from the criterion
    * written at its node. Then this route and `Native.resultParameter` go.
    */
  private def parameterisedReady(
      representations: Native,
      family: FamilyIdentity,
      arguments: Vector[JitValue]
  ): Option[(Vector[Place], Representation)] =
    val represented = arguments.map(written).collect { case JitValue.Represented(found, value) => (found, value) }
    if represented.size != arguments.size then None
    else
      representations.resultParameter(represented.map(_._2)).flatMap(parameter =>
        val places = representations.parameters.map(place(_, None, parameter))
        val fitting = places.zip(represented).forall {
          case (Place.In(expected), (found, _)) => expected == found
          case _                                => false
        }
        Option.when(fitting)((places, Representation.Data(family, parameter)))
      )

  /** `argumentsReady` of a native whose result is in a fixed
    * representation or a list.
    */
  private def listedOrFixedReady(representations: Native, arguments: Vector[JitValue])(using KnownCriteria): SyntaxRead[Option[(Vector[Place], Representation)]] =
    val pairs = representations.parameters.zip(arguments)
    val element = pairs.foldLeft(SyntaxRead.pure(Option(Option.empty[JitValue]))) { (sofar, pair) =>
      SyntaxRead.chained(sofar)(bound =>
        pair match
          case (NativePlace.Fixed(representation), argument) =>
            nativeReady(argument, Place.In(representation)).map(ready => if ready then Some(bound) else None)
          case (NativePlace.Tail | NativePlace.AnyList, argument) =>
            readyRepresentation(argument).map {
              case Some(Representation.ListOf(found)) if bound.forall(_ == found) => Some(Some(found))
              case _                                                             => None
            }
          case (NativePlace.Item, _)        => SyntaxRead.pure(Some(bound))
          case (NativePlace.NaturalList(_), _) => SyntaxRead.pure(None)
          case (NativePlace.Parameter(_) | NativePlace.OfParameter(_), _) =>
            throw IllegalStateException(s"a place at the call's parameter in a native whose result is not: ${representations.result}")
      )
    }
    SyntaxRead.chained(element)(bound =>
      val itemsReady = pairs.foldLeft(SyntaxRead.pure(true)) { (sofar, pair) =>
        sofar.flatMap(ready =>
          if !ready then SyntaxRead.pure(false)
          else
            pair match
              case (NativePlace.Item, argument) =>
                bound match
                  case Some(found) => nativeReady(argument, Place.ItemOf(found))
                  case None        => SyntaxRead.pure(false)
              case _ => SyntaxRead.pure(true)
        )
      }
      val result = representations.result match
        case NativePlace.Fixed(representation) => Some(representation)
        case NativePlace.AnyList               => bound.map(Representation.ListOf(_))
        case _                                 => None
      itemsReady.map(ready =>
        if ready then result.map(found => (representations.parameters.map(place(_, bound, None)), found)) else None
      )
    )

  /** For each ready argument, its outcome taken once (arguments_valued/3). */
  private def argumentsValued(arguments: Vector[JitValue], places: Vector[Place]): Computation[ReadingState, Vector[Valued]] =
    Computation.traversed(arguments.zip(places)) { (argument, place) =>
      place match
        case Place.ItemOf(element) => itemOutcome(argument, element).map(outcomeValued)
        case Place.TailOf(element) => tailOutcome(argument, element).map(outcomeValued)
        case Place.In(representation) =>
          syntaxRead(fallbackPoint(argument)).flatMap {
            case Some((operand, _)) => fallbackOutcome(representation, operand).map(outcomeValued)
            case None               => Computation.pure(Valued.Lazy(argument, place))
          }
    }

  private def outcomeValued(outcome: Outcome): Valued = outcome match
    case Outcome.Typed(values)  => Valued.Values(values)
    case Outcome.Untyped(value) => Valued.Unvalued(value)

  /** Each combination of the arguments' values, in order (valued_values/2). */
  private def valuedCombinations(valued: Vector[Valued]): Answers[ReadingState, Vector[NativeArgument]] =
    valued.foldLeft(Answers.single[ReadingState, Vector[NativeArgument]](Vector.empty)) { (combinations, argument) =>
      combinations.flatMap(found =>
        (argument match
          case Valued.Values(values)         => Answers.of[ReadingState, NativeArgument](values)
          case Valued.Lazy(argument, place)  => nativeValue(argument, place)
          case Valued.Unvalued(_)            => Answers.empty[ReadingState, NativeArgument]
        ).map(found :+ _)
      )
    }

  /** The arguments the define takes when the native falls back to it
    * (valued_terms/3).
    */
  private def valuedTerms(valued: Vector[Valued], places: Vector[Place]): Vector[JitValue] =
    valued.zip(places).map {
      case (Valued.Values(values), place) => outcomeTerm(Outcome.Typed(values), place)
      case (Valued.Unvalued(value), _)    => value
      case (Valued.Lazy(argument, _), _)  => argument
    }

  /** The heads of the native-bound library file's term at the instruction, from
    * its own layer, applied to the arguments (generic_applied/3). The layer
    * is dispatched by its constructor alone (`Goal.LayerEvaluation`): it is
    * the term itself, which evaluated again would be dispatched to its
    * native, the very native this reading stands in for.
    */
  private def genericApplied(instruction: Instruction, arguments: Vector[JitValue]): Stream =
    computedStream(
      syntaxRead(layer(instruction)).map(found => running(Machine(List(Goal.LayerEvaluation(found, arguments.toList)))))
    )

  // ---- fallback points ----

  /** The heads of a fallback point of the representation over the operand
    * (fallback_point_head/3).
    *
    * FIXME (carried from jit.pl:768; a fallback point is taken when the https://github.com/Atry/private-overlay/issues/1937
    * input cannot be proved in the domain, and the check should be fast): the check of
    * a fallback point reads all of the operand's heads before either path
    * (`valueRead`), so an operand whose heads do not all end proves nothing
    * and runs neither path: [zero, Ω] as an operand gives no head where the
    * reference gives zero's first (derived from the rules, not measured).
    * The same holds of `argumentsValued` for a native's argument.
    * Candidate: take the untyped path's heads beside a reading that has not
    * ended, interleaved fairly, which is not designed.
    */
  private def fallbackPointHeads(representation: Representation, operand: JitValue): Stream =
    if heldAsWritten(representation) then heads(operand) // x + (x ∥ C) is x for a least term C
    else
      computedStream(fallbackOutcome(representation, operand).map {
        case Outcome.Typed(values) => Answers.of(values.map(headOfValue(representation, _)))
        case Outcome.Untyped(untyped) => heads(untyped)
      })

  private def headOfValue(representation: Representation, value: NativeArgument): JitHead = value match
    case NativeArgument.Represented(found) => JitHead.Represented(representation, found)
    case other => throw IllegalStateException(s"a value of a representation is no ${other.productPrefix}")

  /** The reading of a fallback point, taken once (fallback_outcome/3). */
  private def fallbackOutcome(representation: Representation, operand: JitValue): Computation[ReadingState, Outcome] =
    val read = syntaxRead(
      constructorOutcome(operand, representation).flatMap {
        case found @ Some(_) => SyntaxRead.pure(found)
        case None            => codecLiteralOutcome(operand, representation).map(_.map(Computation.pure(_)))
      }
    ).flatMap {
      case Some(outcome) => outcome
      case None =>
        syntaxRead(fallbackPoint(operand)).flatMap {
          case Some((inner, innerRepresentation)) =>
            fallbackOutcome(innerRepresentation, inner).flatMap(innerOutcome =>
              if innerRepresentation == representation then Computation.pure(innerOutcome)
              else valueRead(representation, outcomeTerm(innerOutcome, Place.In(innerRepresentation)))
            )
          case None => valueRead(representation, operand)
        }
    }
    read.map {
      case Outcome.Untyped(_) if configuration.dispatch.outsideDecided == DispatchDecision.Rejected =>
        throw TypedVersionDomain(representation, written(operand))
      case outcome => outcome
    }

  /** The reading of a type-filtered constructor, each argument read once
    * (constructor_outcome/3).
    */
  private def constructorOutcome(
      operand: JitValue,
      representation: Representation,
  )(using KnownCriteria): SyntaxRead[Option[Computation[ReadingState, Outcome]]] =
    filteredConstructor(operand, representation).flatMap(filtered =>
      if !filtered then SyntaxRead.pure(None)
      else spineListed(operand).map(constructorArgumentsOutcome(representation, _))
    )

  /** Whether the native's result is at the call's parameter
    * (`NativePlace.Parameter`).
    */
  private def parameterised(native: NativeName): Boolean = nativeBackend.natives(native).result match
    case NativePlace.Parameter(_) => true
    case _                        => false

  /** The reading of a literal of a data family that has a codec and whose
    * spine's head has no constructor native of a fixed place at the
    * representation (the words and the binary naturals, whose constructors'
    * natives are at the family's parameter): the value the operand
    * spells by its syntax alone at the representation's parameter
    * (`syntaxDecoded`), typed; `None` when the representation is no data
    * family with a codec, when the head has a constructor native of a fixed
    * place there (`constructorOutcome` reads such a literal), or when the
    * syntax does not decode, and the operand is then read as before. A
    * constructor native at the family's parameter does not stop the decoding:
    * `constructorOutcome` reads a literal only when it is type-filtered, so a
    * literal under a decode point reads as it did before those natives
    * existed. The decision rests on the criterion written in the fallback
    * point, which named the representation, and on the operand's syntax;
    * nothing is evaluated and no value is guessed.
    */
  private def codecLiteralOutcome(
      operand: JitValue,
      representation: Representation,
  )(using KnownCriteria): SyntaxRead[Option[Outcome]] =
    representation match
      case Representation.Data(familyIdentity, parameter) if nativeBackend.family(familyIdentity).isDefined =>
        val term = written(operand)
        spineRead(term, Vector.empty).flatMap {
          case Some((head, _))
              if headNatives(head).exists(native =>
                !parameterised(native.name) && placesFor(native.name, representation).isDefined
              ) =>
            SyntaxRead.pure(None)
          case Some(_) =>
            syntaxDecoded(familyIdentity, parameter, term).map(
              _.map(value => Outcome.Typed(Vector(NativeArgument.Represented(value))))
            )
          case None => SyntaxRead.pure(None)
        }
      case _ => SyntaxRead.pure(None)

  /** The reading of a type-filtered constructor of the representation whose
    * spine is the head and the arguments (`constructorOutcome`).
    */
  private def constructorArgumentsOutcome(
      representation: Representation,
      spine: (JitValue, Vector[JitValue])
  ): Option[Computation[ReadingState, Outcome]] =
    val (head, arguments) = spine
    val instruction = head match
      case JitValue.Instruction(found) => found
      case other => throw IllegalStateException(s"a type-filtered constructor's head is a ${other.layer.productPrefix}")
    headNatives(head)
      .find(native => native.parameterCount == arguments.size && placesFor(native.name, representation).isDefined)
      .map(native =>
        val places = placesFor(native.name, representation).get
        Computation.traversed(arguments.zip(places))(argumentOutcome).flatMap(outcomes =>
          val typed = outcomes.collect { case Outcome.Typed(values) => values }
          val combinations =
            if typed.size == outcomes.size then
              typed.foldLeft(Vector(Vector.empty[NativeArgument]))((found, values) => found.flatMap(prefix => values.map(prefix :+ _)))
            else Vector.empty
          Computation.traversed(combinations)(values => nativeCalled(native.name, values, representation)).map(results =>
            if typed.size == outcomes.size && results.nonEmpty then Outcome.Typed(results.map(NativeArgument.Represented(_)))
            else
              val terms = outcomes.zip(places).map((outcome, place) => outcomeTerm(outcome, place))
              Outcome.Untyped(terms.foldLeft(instruction: JitValue)(JitValue.Apply(_, _)))
          )
        )
      )

  /** The reading of an argument of a type-filtered constructor, taken once
    * (argument_outcome/3).
    */
  private def argumentOutcome(argument: JitValue, place: Place): Computation[ReadingState, Outcome] =
    place match
      case Place.ItemOf(element) => itemOutcome(argument, element)
      case Place.TailOf(element) => tailOutcome(argument, element)
      case Place.In(representation) =>
        syntaxRead(fallbackPoint(argument)).flatMap {
          case Some((operand, _)) => fallbackOutcome(representation, operand)
          case None =>
            syntaxRead(
              nativeReady(argument, place).flatMap(ready =>
                if ready then SyntaxRead.pure(None) else constructorOutcome(argument, representation)
              )
            ).flatMap(notReadyConstructor =>
              notReadyConstructor.getOrElse(
                written(argument) match
                  case JitValue.Represented(found, value) if found == representation =>
                    Computation.pure(Outcome.Typed(Vector(NativeArgument.Represented(value))))
                  case _ =>
                    nativeValue(argument, place).collected.map(values =>
                      if values.isEmpty then Outcome.Untyped(argument) else Outcome.Typed(values)
                    )
              )
            )
        }

  /** The reading of a list's item (item_outcome/3).
    *
    * FIXME (carried from jit.pl:1096, the re-check of the lists' https://github.com/Atry/private-overlay/issues/1938
    * representation, 2026-10-29): the check of a fallback point runs when
    * its cell is built, so a list holding one is less lazy than the define,
    * which leaves the item unread until a consumer reads it; in a compiled
    * run every item cons's native receives is such a point. Where the check
    * does not end, a reading of the list's spine loses its answer: measured
    * 2026-10-29 in the Prolog JIT, list_fold zero (\h. \a. successor a)
    * (cons [Ω, Ω ∥ nat_type] (nil ∥ list_type nat_type)), Ω = (\x. x x)
    * (\y. y y), runs past 2,000,000 inferences, while the same term with the
    * tail nil reads successor zero. This is the check that does not end of
    * the FIXME at `fallbackPointHeads` (jit.pl's fallback_point_head/3),
    * met here where the item is never read. Candidate: keep such an
    * item unread in the cell, marked as not filtered by the element, hand it
    * out as it is, and filter the marked items at a strict decode point over
    * the list; not designed.
    */
  private def itemOutcome(argument: JitValue, element: JitValue): Computation[ReadingState, Outcome] =
    syntaxRead(fallbackPoint(argument)).flatMap {
      case Some((operand, _)) =>
        syntaxRead(decodingCriterionRead(element)).flatMap(criterion =>
          val representation = criterion.getOrElse(
            throw IllegalStateException("a list's item read in a list whose element filter is no decoding criterion")
          )
          fallbackOutcome(representation, operand).map {
            case Outcome.Typed(values) =>
              Outcome.Typed(values.map(value => NativeArgument.Item(headOfValue(representation, value).asValue)))
            case untyped => untyped
          }
        )
      case None => Computation.pure(Outcome.Typed(Vector(NativeArgument.Item(argument))))
    }

  /** The reading of a list's tail (tail_outcome/3): a represented list by
    * its value, any other tail unread.
    */
  private def tailOutcome(argument: JitValue, element: JitValue): Computation[ReadingState, Outcome] =
    Computation.pure(written(argument) match
      case JitValue.Represented(Representation.ListOf(found), NativeValue.Listed(list)) if found == element =>
        Outcome.Typed(Vector(NativeArgument.Tail(ListTail.Listed(list))))
      case _ => Outcome.Typed(Vector(NativeArgument.Tail(ListTail.Unread(argument))))
    )

  /** An outcome as a term (outcome_term/3). */
  private def outcomeTerm(outcome: Outcome, place: Place): JitValue = (outcome, place) match
    case (Outcome.Untyped(untyped), _) => untyped
    case (Outcome.Typed(values), Place.ItemOf(_)) =>
      oneOrChoice(values.map {
        case NativeArgument.Item(item) => item
        case other => throw IllegalStateException(s"an item's outcome holds a ${other.productPrefix}")
      })
    case (Outcome.Typed(values), Place.TailOf(element)) =>
      oneOrChoice(values.map {
        case NativeArgument.Tail(tail) => fieldValue(ListCodec.tailField(element, tail))
        case other => throw IllegalStateException(s"a tail's outcome holds a ${other.productPrefix}")
      })
    case (Outcome.Typed(values), Place.In(representation)) =>
      oneOrChoice(values.map(value => headOfValue(representation, value).asValue))

  private def oneOrChoice(values: Vector[JitValue]): JitValue = values match
    case Vector(one) => one
    case several     => JitValue.Choice(several)

  /** The reading of an operand that is neither a type-filtered constructor
    * nor a fallback point (value_read/3): its heads read once, typed when
    * every one stands for a value of the representation, otherwise the
    * `Evaluated` value that carries them; a reading that recurs among the
    * readings around it stands for no value.
    */
  private def valueRead(representation: Representation, value: JitValue): Computation[ReadingState, Outcome] =
    value match
      case JitValue.Evaluated(_, mode, found) if mode == configuration.dispatch =>
        headsValues(representation, found).map {
          case Some(values) => Outcome.Typed(values)
          case None         => Outcome.Untyped(value)
        }
      case _ =>
        run.flatMap(current =>
          current.readingPath.extended(OperandReading(representation, value)) match
            case None => runModified(cut => cut.copy(cuts = cut.cuts + 1)).map(_ => Outcome.Untyped(value))
            case Some(extended) =>
              for
                _ <- runModified(_.copy(readingPath = extended))
                found <- heads(value).collected
                _ <- runModified(_.copy(readingPath = current.readingPath))
                values <- headsValues(representation, found)
              yield values match
                case Some(typed) => Outcome.Typed(typed)
                case None => Outcome.Untyped(JitValue.Evaluated(JitValues.writtenThroughout(value), configuration.dispatch, found))
        )

  /** Every head, one at least, stands for a value of the representation
    * (heads_values/3), the values in order.
    */
  private def headsValues(representation: Representation, found: Vector[JitHead]): Computation[ReadingState, Option[Vector[NativeArgument]]] =
    if found.isEmpty then Computation.pure(None)
    else
      Computation.folded(found, Option(Vector.empty[NativeArgument])) {
        case (None, _) => Computation.pure(None)
        case (Some(values), head) => headValue(representation, head).map(_.map(values :+ NativeArgument.Represented(_)))
      }

  /** The value of the representation the head stands for (head_value/3): a
    * value of it; a value of another representation whose encoding of one
    * layer stands for one; or the head of a define bound to a native of no
    * parameter whose result is in the representation.
    */
  private def headValue(representation: Representation, head: JitHead): Computation[ReadingState, Option[NativeValue]] =
    head match
      case JitHead.Represented(found, value) =>
        if found == representation then Computation.pure(Some(value))
        else firstHeadValue(representation, encodedHeads(found, value))
      case JitHead.Lambda(code, holes, fillings) if fillings.isEmpty =>
        Computation.pure(
          facts.constants.collectFirst {
            case BackendConstant(`code`, `holes`, value, place) if placeHolds(place, representation) => value
          }
        )
      case _ => Computation.pure(None)

  /** Whether a native's result at the place is in the representation. */
  private def placeHolds(place: NativePlace, representation: Representation): Boolean = (place, representation) match
    case (NativePlace.Fixed(found), _)                    => found == representation
    case (NativePlace.AnyList, Representation.ListOf(_))  => true
    case _                                                => false

  private def firstHeadValue(representation: Representation, stream: Stream): Computation[ReadingState, Option[NativeValue]] =
    stream.pull.flatMap {
      case None => Computation.pure(None)
      case Some((head, rest)) =>
        headValue(representation, head).flatMap {
          case found @ Some(_) => Computation.pure(found)
          case None            => firstHeadValue(representation, rest)
        }
    }

  // ---- decode points ----

  /** The heads of a decode point of the representation over the value
    * (decode_point_head/3).
    */
  private def decodePointHeads(representation: Representation, value: JitValue): Stream =
    if heldAsWritten(representation) then heads(value) // x ∥ C is x for a least term C
    else
      computedStream(syntaxRead(filteredConstructor(value, representation)).map(filtered =>
        if filtered then
          nativeValue(value, Place.In(representation)).flatMap {
            case NativeArgument.Represented(result) =>
              Answers.computed(
                syntaxRead(decodePointValue(representation, result)).map(found => Vector(JitHead.Represented(representation, found)))
              )
            case other => throw IllegalStateException(s"a decode point's value is a ${other.productPrefix}")
          }
        else decodedHeads(representation, value)
      ))

  /** The value a decode point of the representation takes for a value
    * (decode_point_value/3): a list's cell with its tail filtered by the
    * list's criterion, unless that tail is already such a decode point.
    */
  private def decodePointValue(representation: Representation, value: NativeValue)(using KnownCriteria): SyntaxRead[NativeValue] =
    (representation, value) match
      case (Representation.ListOf(element), NativeValue.Listed(ListRepresentation.Cell(item, tail))) =>
        tailFiltered(tail, representation).map(filtered =>
          if filtered then value
          else
            val field = fieldValue(ListCodec.tailField(element, tail))
            NativeValue.Listed(
              ListRepresentation.Cell(item, ListTail.Unread(JitValue.Parallel(field, JitValue.Apply(facts.listType, element))))
            )
        )
      case _ => SyntaxRead.pure(value)

  private def tailFiltered(tail: ListTail[JitValue], representation: Representation)(using KnownCriteria): SyntaxRead[Boolean] = tail match
    case ListTail.Unread(term) => decodePointReached(term).map(_.exists(_._2 == representation))
    case ListTail.Listed(_)    => SyntaxRead.pure(false)

  /** The values of the place the term, ready in it or a type-filtered
    * constructor of it, evaluates to by the natives and the codecs
    * (native_value/3).
    */
  private def nativeValue(operand: JitValue, place: Place): Answers[ReadingState, NativeArgument] =
    Answers(syntaxContext.flatMap(knownCriteria =>
      given KnownCriteria = knownCriteria
      (place match
        case Place.ItemOf(element) =>
          Answers.computed(itemOutcome(operand, element).map {
            case Outcome.Typed(items)    => items
            case Outcome.Untyped(value)  => Vector(NativeArgument.Item(value))
          })
        case Place.TailOf(element) =>
          written(operand) match
            case JitValue.Represented(Representation.ListOf(found), NativeValue.Listed(list)) if found == element =>
              Answers.single(NativeArgument.Tail(ListTail.Listed(list)))
            case _ =>
              computedAnswers(syntaxResult(nativeReady(operand, Place.In(Representation.ListOf(element)))).map(ready =>
                if ready then Answers.single(NativeArgument.Tail(ListTail.Unread(operand)))
                else
                  nativeValue(operand, Place.In(Representation.ListOf(element))).map {
                    case NativeArgument.Represented(NativeValue.Listed(list)) => NativeArgument.Tail(ListTail.Listed(list))
                    case other => throw IllegalStateException(s"a list's value is a ${other.productPrefix}")
                  }
              ))
        case Place.In(representation) => representedValues(operand, representation)
      ).pull
    ))

  private def representedValues(operand: JitValue, representation: Representation)(using
      KnownCriteria
  ): Answers[ReadingState, NativeArgument] =
    val term = written(operand)
    operand match
      case _ if heldAsWritten(representation) =>
        computedAnswers(unreadField(operand).map(found => Answers.of(found.toVector.map(NativeArgument.Represented(_)))))
      case JitValue.Evaluated(_, mode, _) if mode == configuration.dispatch =>
        decodedHeads(representation, operand).map(representedArgument)
      case _ =>
        term match
          case JitValue.Represented(found, value) =>
            if found == representation then Answers.single(NativeArgument.Represented(value))
            else throw IllegalStateException(s"a ${found.familyIdentity.shown} value read as ${representation.familyIdentity.shown}")
          case _ =>
            computedAnswers(syntaxResult(decodePointReached(term)).flatMap {
              case Some((filtered, _)) => Computation.pure(decodePointHeads(representation, filtered).map(representedArgument))
              case None =>
                syntaxResult(fallbackPoint(term)).flatMap {
                  case Some((fallbackOperand, _)) =>
                    Computation.pure(computedAnswers(fallbackOutcome(representation, fallbackOperand).map {
                      case Outcome.Typed(values)    => Answers.of(values)
                      case Outcome.Untyped(untyped) => decodedHeads(representation, untyped).map(representedArgument)
                    }))
                  case None =>
                    syntaxResult(spineListed(term)).map((head, arguments) =>
                      Answers.of[ReadingState, BoundNative](headNatives(head)).flatMap(native =>
                        placesFor(native.name, representation) match
                          case None => Answers.empty
                          case Some(places) =>
                            if places.size != arguments.size then Answers.empty
                            else
                              nativeValues(arguments, places).flatMap(values =>
                                Answers.computed(nativeCalled(native.name, values, representation).map(found =>
                                  Vector(NativeArgument.Represented(found))
                                ))
                              )
                      )
                    )
                }
            })

  private def computedAnswers[Answer](computation: Computation[ReadingState, Answers[ReadingState, Answer]]): Answers[ReadingState, Answer] =
    Answers(computation.flatMap(_.pull))

  private def representedArgument(head: JitHead): NativeArgument = head match
    case JitHead.Represented(_, value) => NativeArgument.Represented(value)
    case other => throw IllegalStateException(s"a decoded head is a ${other.productPrefix}")

  /** Each combination of the arguments' values at their places
    * (native_values/3).
    */
  private def nativeValues(arguments: Vector[JitValue], places: Vector[Place]): Answers[ReadingState, Vector[NativeArgument]] =
    arguments.zip(places).foldLeft(Answers.single[ReadingState, Vector[NativeArgument]](Vector.empty)) {
      case (combinations, (argument, place)) =>
        combinations.flatMap(found => nativeValue(argument, place).map(found :+ _))
    }

  // ---- the codecs ----

  /** The heads `Represented(R, V)` of the values V the value decodes into by
    * the representation's codec (decoded_head/3).
    *
    * TODO (carried from jit.pl:287): a decoding that meets a constructor of R's
    * codec applied to its fields, untyped, at the top or at a field, reads
    * the fields and calls the native, and a codec constructor given a field
    * not ready keeps its fields for such a read (`git show
    * 675d169e4:lambda_jit/prolog/lambda_jit/jit.pl`, A CONSTRUCTOR READ, A
    * PENDING CONSTRUCTOR): it comes back only if a type filter is read to
    * cover the constructors written inside its operand. A fold's step reaches the representation without it: the type
    * check spells a function the program passes, or a closure holds, by its
    * contract, whose code filters the function's argument and result
    * (`StrategyDispatch`, a CONTRACT).
    */
  private def decodedHeads(representation: Representation, value: JitValue): Stream =
    val point = DecodePoint(representation, value)
    computedStream(run.flatMap(current =>
      current.decodedPoints.found(point) match
        case Some(values) =>
          decodedPointHit(point, values).map(_ => Answers.of[ReadingState, NativeValue](values).map(JitHead.Represented(representation, _)))
        case None =>
          Computation.pure(pointRecorded(valueDecoded(representation, value, None, 0), point, Vector.empty, true).map(JitHead.Represented(representation, _)))
    ))

  /** A decode point found in the table: the lookup and each value it replays
    * charged a step, as an instance's hit is, so that a reading's values are
    * bounded by its budget, and the point completed in the young generation.
    */
  private def decodedPointHit(point: DecodePoint, values: Vector[NativeValue]): Computation[ReadingState, Unit] =
    Computation(state =>
      val spent = state.budget.spent + 1 + values.size
      if spent > state.budget.limit then done(Computed.Stopped(state))
      else
        val current = JitRunState.of(state, configuration)
        val kept =
          if current.decodedPoints.young.contains(point) then current
          else current.copy(decodedPoints = current.decodedPoints.recorded(point, values, configuration.instanceRetention))
        done(Computed.Done((), state.copy(budget = state.budget.copy(spent = spent), jitState = kept)))
    )

  /** The values of a decode point as they come, recorded when they end. Only
    * a reading whose every pull stood outside a fallback point's check and
    * outside every table's evaluation is recorded. A cut inside a check depends
    * on the readings around it, which another context does not have
    * (`tabledInstance`). Inside a table's evaluation a re-entered table answers
    * with its approximation, so the values read there can be fewer than the
    * point's, and the iteration of that table's component reads them again.
    */
  private def pointRecorded(
      values: Answers[ReadingState, NativeValue],
      point: DecodePoint,
      found: Vector[NativeValue],
      settled: Boolean
  ): Answers[ReadingState, NativeValue] =
    Answers(Computation.state[ReadingState].flatMap(state =>
      val current = JitRunState.of(state, configuration)
      val stillSettled =
        settled && current.readingPath == ReadingPath.Empty && !current.instanceTables.inProgress && !state.tables.inProgress
      values.pull.flatMap {
        case None if stillSettled =>
          runModified(after =>
            after.copy(decodedPoints = after.decodedPoints.recorded(point, found, configuration.instanceRetention))
          ).map(_ => None)
        case None                 => Computation.pure(None)
        case Some((value, rest)) => Computation.pure(Some((value, pointRecorded(rest, point, found :+ value, stillSettled))))
      }
    ))

  /** The values the term decodes into at the field depth, from each of its
    * heads, the decoding numbered when a head is first applied to the cases
    * (value_decoded/5).
    */
  private def valueDecoded(representation: Representation, term: JitValue, decoding: Option[Long], level: Int): Answers[ReadingState, NativeValue] =
    if heldAsWritten(representation) then computedAnswers(unreadField(term).map(found => Answers.of(found.toVector)))
    else heads(term).flatMap(headDecoded(representation, _, decoding, level))

  /** A field of a family that holds it as written; none when it
    * holds a case of a decoding, which must not leave the decoding: that
    * value is no value of the family it was read at, and has no answer. The
    * values the check found free of a case are kept in the run state
    * (`JitRunState.caseFree`), so that a later check stops at them.
    */
  private def unreadField(term: JitValue): Computation[ReadingState, Option[NativeValue]] =
    run.flatMap(current =>
      val walk = JitValues.caseWalk(term, current.caseFree, configuration.instanceRetention)
      runModified(found =>
        found.copy(
          caseFree = walk.caseFree.getOrElse(found.caseFree),
          counts = found.counts.copy(decodingCaseVisits = found.counts.decodingCaseVisits + walk.visits)
        )
      ).map(_ => walk.caseFree.map(_ => NativeValue.Unread(term)))
    )

  private def headDecoded(representation: Representation, head: JitHead, decoding: Option[Long], level: Int): Answers[ReadingState, NativeValue] =
    head match
      case JitHead.Represented(found, value) =>
        if found == representation then
          computedAnswers(syntaxRead(decodePointValue(representation, value)).map(Answers.single(_)))
        else encodedHeads(found, value).flatMap(headDecoded(representation, _, decoding, level))
      case _ =>
        computedAnswers(numbered(decoding).map(number =>
          casesApplied(representation, head, number, level).flatMap(answerDecoded(representation, _, number, level))
        ))

  /** The decoding's number: the one given, or the next, counted. */
  private def numbered(decoding: Option[Long]): Computation[ReadingState, Long] = decoding match
    case Some(number) => Computation.pure(number)
    case None =>
      run.flatMap(current =>
        countsModified(counts => counts.copy(decodings = counts.decodings + 1)).map(_ => current.counts.decodings)
      )

  private def casesApplied(representation: Representation, head: JitHead, decoding: Long, level: Int): Stream =
    val number = Decoding.Numbered(decoding)
    val cases = representation match
      case Representation.Data(familyIdentity, parameter) => dataFamily(familyIdentity).decodingCases(number, level, parameter)
      case Representation.ListOf(_) =>
        val (first, second) = ListCodec.decodingCases(number, level)
        Vector(first, second)
    headApplied(head, cases.map(JitValues.fromValue).toList)

  /** The value a head of a value applied to the cases reads
    * (answer_decoded/5).
    *
    * FIXME (carried from jit.pl:2144, the review of the lists' https://github.com/Atry/private-overlay/issues/1939
    * representation, 2026-10-29): an item is kept with no check
    * that it mentions no case of the decoding, which the decoding's argument
    * needs (`gezi.weakhead.ListCodec`, WHY A DECODED LIST STANDS FOR
    * THE FILTERED VALUE). A value that passes its own case to its cons case
    * keeps the decoding's neutral value as an item, and the reader throws on
    * it. Measured 2026-10-29 in the Prolog JIT: on ((\n. \c. c n nil) ∥
    * list_type (\y. y)) (\z. zero) (\h. \t. h) the reference reads
    * \z. zero, the JIT without the natives reads the same, and with them it
    * threw neutral_value_not_opened. Candidates: refuse the decoding when the
    * item's term holds a case of the decoding, a walk that costs, for a list
    * of its own suffixes, the square of its length (derived, not measured);
    * or apply each head to a second set of cases and compare the fields.
    */
  private def answerDecoded(representation: Representation, answered: JitHead, decoding: Long, level: Int): Answers[ReadingState, NativeValue] =
    answered match
      case JitHead.Parallel(left, right) =>
        computedAnswers(
          for
            leftValues <- sideValues(representation, left, decoding, level)
            rightValues <- sideValues(representation, right, decoding, level)
          yield Answers.of(leftValues.distinct.filter(rightValues.contains))
        )
      case JitHead.NativeApplication(instruction, _, _, arguments) =>
        genericApplied(instruction, arguments).flatMap(answerDecoded(representation, _, decoding, level))
      case JitHead.Elimination(found, value, cases) =>
        eliminationEncoded(found, value, cases).flatMap(answerDecoded(representation, _, decoding, level))
      case other => readingDecoded(representation, other, decoding, level)

  private def sideValues(representation: Representation, side: JitValue, decoding: Long, level: Int): Computation[ReadingState, Vector[NativeValue]] =
    heads(side).flatMap(answerDecoded(representation, _, decoding, level)).collected

  /** The value a codec reads of an answered head (case_read/5 and
    * reading_decoded/5).
    */
  private def readingDecoded(representation: Representation, answered: JitHead, decoding: Long, level: Int): Answers[ReadingState, NativeValue] =
    val number = Decoding.Numbered(decoding)
    (representation, answered) match
      case (Representation.Data(familyIdentity, parameter), JitHead.Neutral(DataCase(`number`, `level`, caseFamily, constructor), arguments))
          if caseFamily == familyIdentity && !dataFamily(familyIdentity).excluded(parameter, constructor) &&
            arguments.size == dataFamily(familyIdentity).constructors(parameter)(constructor).fields.size =>
        val family = dataFamily(familyIdentity)
        def built(fields: Vector[NativeValue]): NativeValue = family.built(parameter, DataLayer(constructor, fields))
        def fieldDecoded(field: DataField, argument: JitValue): Answers[ReadingState, NativeValue] =
          valueDecoded(field.representation(parameter), argument, Some(decoding), level + 1)
        // A layer of no field and of one, the naturals' and the booleans', is
        // read with no stream of field vectors between, as the codecs read it.
        family.constructors(parameter)(constructor).fields.zip(arguments) match
          case Vector()                  => Answers.single(built(Vector.empty))
          case Vector((field, argument)) => fieldDecoded(field, argument).map(value => built(Vector(value)))
          case several =>
            several
              .foldLeft(Answers.single[ReadingState, Vector[NativeValue]](Vector.empty)) { case (decoded, (field, argument)) =>
                decoded.flatMap(values => fieldDecoded(field, argument).map(values :+ _))
              }
              .map(built)
      case (Representation.ListOf(_), JitHead.Neutral(ListCase(`number`, `level`, ListConstructor.Nil), arguments)) if arguments.isEmpty =>
        Answers.single(NativeValue.Listed(ListRepresentation.Items(0, Vector.empty)))
      case (Representation.ListOf(_), JitHead.Neutral(ListCase(`number`, `level`, ListConstructor.Cons), Vector(item, tail))) =>
        valueDecoded(representation, tail, Some(decoding), level + 1).map {
          case NativeValue.Listed(ListRepresentation.Items(length, items)) =>
            NativeValue.Listed(ListRepresentation.Items(length + 1, item +: items))
          case NativeValue.Listed(list) => NativeValue.Listed(ListRepresentation.Cell(item, ListTail.Listed(list)))
          case other => throw IllegalStateException(s"a list's tail decoded into $other")
        }
      case _ => Answers.empty

  /** The heads of the term the value of the representation stands for, one
    * layer, the encoding counted (encoded_head/3).
    */
  private def encodedHeads(representation: Representation, value: NativeValue): Stream =
    Answers(countsModified(counts => counts.copy(encodings = counts.encodings + 1)).flatMap(_ =>
      (representation, value) match
        case (Representation.Data(familyIdentity, parameter), _) =>
          val family = dataFamily(familyIdentity)
          val DataLayer(constructor, fields) = family.layer(parameter, value)
          genericApplied(
            facts.constructorDefine(family.constructors(parameter)(constructor).native),
            fieldValues(family, parameter, constructor, fields)
          ).pull
        case (Representation.ListOf(element), NativeValue.Listed(ListRepresentation.Items(length, items))) =>
          if items.isEmpty then genericApplied(facts.nil, Vector.empty).pull
          else
            genericApplied(
              facts.cons,
              Vector(
                JitValue.Parallel(items.head, element),
                JitValue.Represented(representation, NativeValue.Listed(ListRepresentation.Items(length - 1, items.tail)))
              )
            ).pull
        case (Representation.ListOf(element), NativeValue.Listed(ListRepresentation.Cell(item, tail))) =>
          genericApplied(facts.cons, Vector(JitValue.Parallel(item, element), fieldValue(ListCodec.tailField(element, tail)))).pull
        case _ => throw IllegalStateException(s"a value of another representation than ${representation.familyIdentity.shown}")
    ))

  /** The encoding of the value applied to the cases (elimination_encoded/4). */
  private def eliminationEncoded(representation: Representation, value: NativeValue, cases: Vector[JitValue]): Stream =
    encodedHeads(representation, value).flatMap(headApplied(_, cases.toList))

  // ---- the readers' end of a block ----

  /** The parallel sets of the reference's kinds for the JIT's head
    * (jit_observed_head/2): a represented value encoded one layer, an
    * elimination encoded and applied to its cases, a native's application
    * taken as its define's heads, until the head is a lambda or a neutral
    * value, its parts carried for the reader, a parallel set of one head.
    * The JIT's own head of a parallel, whose sides it does not evaluate, is
    * evaluated here, where it leaves the JIT: each parallel set of its left
    * side with each of its right side, as the reference evaluator's
    * (`WeakHead`, THE RULES), the right side evaluated again for each.
    */
  def observed(head: JitHead): Answers[ReadingState, ParallelSet] = head match
    case gezi.jit.Represented(representation, value) => encodedHeads(representation, value).flatMap(observed)
    case gezi.jit.Elimination(representation, value, cases) => eliminationEncoded(representation, value, cases).flatMap(observed)
    case gezi.jit.NativeApplication(instruction, _, _, arguments) => genericApplied(instruction, arguments).flatMap(observed)
    case gezi.ir.Thunk(code, holes, fillings) =>
      Answers.single(ParallelSet.single(Head.Lambda(code, holes, fillings.map(JitValues.carried))))
    case gezi.weakhead.Neutral(variable, arguments) =>
      Answers.single(ParallelSet.single(Head.Neutral(variable, arguments.map(JitValues.carried))))
    case gezi.ir.Parallel(left, right) =>
      heads(left).flatMap(observed).flatMap(leftSet => heads(right).flatMap(observed).map(leftSet.parallel))
    case EmptyParallel => Answers.single(ParallelSet.bottom)

  /** The head with every value it carries encoded whole
    * (jit_values_encoded/2): plain values of the IR for a caller that keeps
    * heads.
    */
  def headEncoded(head: Head): Head = head match
    case gezi.ir.Thunk(code, holes, fillings)          => Head.Lambda(code, holes, fillings.map(valueEncoded))
    case gezi.weakhead.Neutral(variable, arguments)    => Head.Neutral(variable, arguments.map(valueEncoded))

  private def valueEncoded(value: Value): Value =
    JitValues.plain(JitValues.encoded(JitValues.fromValue(value), facts))
