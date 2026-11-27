package gezi.jit

import gezi.weakhead.Answers
import gezi.weakhead.AnswerSet
import gezi.weakhead.Attempt
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
import gezi.weakhead.ParallelSet
import gezi.weakhead.ReadingState
import gezi.weakhead.SharedCompletedTables
import gezi.weakhead.TableSharing
import gezi.weakhead.Tabling
import gezi.ir.Value
import gezi.weakhead.Values
import gezi.weakhead.WeakHead
import gezi.strategies.DispatchDecision
import gezi.ir.CodeLayer
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Layer
import gezi.weakhead.Trampoline
import gezi.weakhead.Trampoline.done
import gezi.weakhead.Trampoline.tailcall
import gezi.ir.{Apply, Choice, Opaque, Parallel, Slot, Thunk, UriNode}
import gezi.ir.{Configured, NativeSpecializer}

/** What the JIT evaluates under, chosen when the program is compiled: the
  * library's backend facts, which carry the natives and data families the JIT
  * runs (`BackendFacts.nativeBackend`, the one place the JIT reads them from),
  * the compilation budget (the number of codes a reading's cache may hold
  * compiled, beyond which an instance is interpreted), the generation strategy,
  * the compilation backend, and the dispatch mode, and whether instances are
  * tabled (`instanceTable`). Built once and passed on: a reading's JIT state
  * belongs to the configuration it was built under (`JitRunState.of`).
  *
  * @param instanceTable
  *   whether instances are tabled: an instance's heads are the least fixed
  *   point of the tabled function whose body is its reading, kept by its code
  *   and fillings (`TabledInstance`, `JitRunState.instanceTables`), so that the
  *   next instance with the same key takes them from the table instead of
  *   running the code again. No default: every caller states its choice, since
  *   tabling is the default and not tabling the speculation: tabling costs at
  *   most a constant factor over not tabling, while not tabling can cost
  *   exponentially more, and an entry's choice comes from its data. The table
  *   gives every head the untabled reading gives, each as it is found
  *   (`Tabling`), and decides instances whose untabled reading has no end, an
  *   instance met again within its own reading being answered by its
  *   approximation. An instance missed while a fallback point's check is in
  *   progress (`JitRunState.readingPath` not empty) is run untabled, since a
  *   cut's heads are the check's, not the instance's anywhere else
  * @param instanceTableTrial
  *   the fewest entries of a code the table judges the code's cost on
  *   (`TableCost.unprofitable`), `TableCost.trial` by default; a test lowers it
  *   so that the cutoff fires on small terms
  * @param nativeBlocks
  *   the native block mechanism (`NativeBlockMechanism`): which instances enter
  *   a block when an application fills a code's last hole, what the block runs,
  *   and when a code is retired; `NoNativeBlocks` by default, the only
  *   implementation (the FIXME on `NativeBlockMechanism`)
  * @param instanceRetention
  *   how the state keeps the instance table's complete tables
  *   (`InstanceRetention`); two generations of
  *   `JitConfiguration.defaultInstanceTableGeneration` entries by default
  * @param instanceCheckpoints
  *   which instances the table looks up and records (`InstanceCheckpoints`),
  *   from costs only; `ProfitableCheckpoints` by default, the table as it was
  *   before checkpoint policies
  * @param instanceLookahead
  *   how far a missed instance's reading is pulled beyond the heads its
  *   consumers ask for (`InstanceLookahead`); `Lazy` by default, the table as
  *   it was before lookaheads
  * @param instanceReuse
  *   whether the table's answers outlive a version of the contents the URI
  *   nodes expand to (`InstanceReuse`); `WithinVersion` by default, the table
  *   as it was before this option
  * @param groupBlocks
  *   the group block mechanism (`GroupBlocks`): which written closed thunks run
  *   as group blocks when applied to enough arguments; `NoGroupBlocks` by
  *   default, which runs none and is deprecated, since it loses answers. FIXME:
  *   the default is to move to group blocks.
  *   https://github.com/Atry/private-overlay/issues/2221
  */
final class JitConfiguration[C <: NativeSpecializer & Singleton](
    val specializer: StorageEncoding & C,
    val budget: Int,
    val strategy: GenerationStrategy,
    val backend: CompilationBackend,
    val dispatch: DispatchMode,
    val instanceTable: Boolean,
    val instanceTableTrial: Long = TableCost.trial,
    val instanceRetention: InstanceRetention = InstanceRetention.Generations(
      JitConfiguration.defaultInstanceTableGeneration
    ),
    val nativeBlocks: NativeBlockMechanism = NoNativeBlocks,
    val instanceCheckpoints: InstanceCheckpoints = ProfitableCheckpoints,
    val instanceLookahead: InstanceLookahead = InstanceLookahead.Lazy,
    val instanceReuse: InstanceReuse = InstanceReuse.WithinVersion,
    val groupBlocks: GroupBlocks = NoGroupBlocks,
    // The capability to read a storage's view, made where the entry is set up and given to the JIT here; no default, so
    // that whether the JIT reads storages is decided where it is configured.
    val storageAccess: gezi.ir.StorageAccess
):

  /** The backend facts the specializer encodes its storages with. */
  def facts: BackendFacts = specializer.facts

  /** The encoding's operations in the configuration `C`. */
  val operations: StorageEncodingOperations[C] = specializer.operations

  /** The configuration of the readings the JIT runs in: its facts' native
    * specializer, its capability and, once built from this configuration, the
    * JIT itself (`Jit.readingConfiguration`). A reading state under the JIT
    * holds one of its configuration `C`, so that the terms the JIT builds and
    * those the reader builds are one configuration's.
    */
  def readingConfigurationOf(
      jit: JitEvaluator[C]
  ): gezi.weakhead.ReadingConfiguration[C] =
    gezi.weakhead.ReadingConfiguration(specializer, storageAccess, Some(jit))

  require(budget >= 0, s"a compilation budget is not negative: $budget")
  require(
    instanceTableTrial >= 0,
    s"a table's trial is not negative: $instanceTableTrial"
  )
  instanceRetention match
    case InstanceRetention.Generations(size) =>
      require(
        size >= 1,
        s"a generation of the instance table holds an entry at least: $size"
      )
    case InstanceRetention.NeverDropped => ()
  instanceLookahead match
    case InstanceLookahead.WithinSteps(steps) =>
      require(steps >= 1, s"a lookahead pulls a step at least: $steps")
    case InstanceLookahead.Lazy => ()

/** The construction under the facts: every term built through their native
  * specializer, a storage's view read with the capability given, and in an
  * e-graph storages built one layer up and the natives callable on storages
  * folded: a value of the configuration `C`, whose specializer is the facts'
  * encoding, with the capability in a second parameter list, which a
  * construction's equality does not read: the capability is a permission held,
  * not a choice of the configuration, so two constructions of one entry made
  * apart are equal.
  */
final case class ConvertedTermConstruction[C <: NativeSpecializer & Singleton](
    specializer: StorageEncoding & C
)(
    val storageAccess: gezi.ir.StorageAccess
) extends gezi.ir.TermConstruction[C]:

  private given C = specializer

  private val operations: StorageEncodingOperations[C] = specializer.operations

  /** The natives the graph may fold, by the define bound to each: those
    * callable on storage values (`StorageReadingOfFacts.callable`, which
    * requires the unique spelling's premise of the facts), of at least one
    * parameter, whose result's family is one whose storages the graph keeps as
    * leaves.
    */
  private lazy val foldable: Map[Configured[C], (String, Native)] =
    val leafFamilies = operations.leafCriteria.map(_._1).toSet
    StorageReadingOfFacts.callable(specializer.facts).collect {
      case (define, (NativeName.Function(name), native))
          if native.parameters.nonEmpty && (native.result match
            case NativePlace.Fixed(Representation.Data(family, None)) =>
              leafFamilies.contains(family)
            case NativePlace.Fixed(
                  parameterized @ Representation.Data(_, Some(_))
                ) =>
              operations.converts(parameterized)
            case _ => false) =>
        Configured.fromPure[C](specializer)(define) -> (name, native)
    }

  override lazy val foldingDefines: Vector[Configured[C]] =
    foldable.keys.toVector

  override lazy val foldingArity: Int =
    foldable.values.map(_._2.parameterCount).foldLeft(0)(_ max _)

  override def folded(
      define: Configured[C],
      arguments: Vector[gezi.ir.NativeStorage]
  ): Option[(Configured[C], String)] =
    foldable.get(define).flatMap { (name, native) =>
      // The storages of the graph's leaves are of this configuration: the graph made them through its construction.
      val typed = arguments.flatMap(argument => StorageOf.typed[C](argument))
      val matching =
        typed.size == arguments.size && native.parameters.size == typed.size && native.parameters
          .zip(typed)
          .forall {
            case (NativePlace.Fixed(representation), storage) =>
              storage.representation == representation
            case _ => false
          }
      Option.when(matching)(native).flatMap { found =>
        val values = typed.map(storage =>
          NativeArgument.Represented(StorageOf.nativeValue(storage))
        )
        val NativePlace.Fixed(result) = found.result: @unchecked
        val term = operations.storageOf(result, found.implementation(values))
        term match
          case JitValue.Stored(storage) if storage.leafInEGraph =>
            gezi.ir.Closed.configured(term).map((_, name))
          case _ => None
      }
    }

  override lazy val storageCriteria: Vector[Configured[C]] =
    operations.leafCriteria.map(_._2)

  override lazy val storageConstructors: Vector[Configured[C]] =
    operations.leafCriteria.flatMap(_._3).distinct

  override lazy val storageArity: Int =
    operations.leafCriteria.map(_._4).foldLeft(0)(_ max _)

  override def storageBuilt(
      constructor: Configured[C],
      fields: Vector[gezi.ir.NativeStorage],
      criterion: Configured[C]
  ): Option[Configured[C]] =
    // The fields are storage leaves of the graph, terms of this configuration: the constructor applied to them, then
    // converted under the criterion, is a storage when it is the unique spelling of one and the graph keeps it a leaf.
    val typed = fields.flatMap(field => StorageOf.typed[C](field))
    Option
      .when(typed.size == fields.size)(
        typed.foldLeft(gezi.ir.Value.of(constructor))((function, field) =>
          gezi.ir.Value.Apply(function, StorageOf.value(field))
        )
      )
      .flatMap(applied =>
        operations.convertedValue(applied, gezi.ir.Value.of(criterion))
      )
      .collect {
        case stored @ JitValue.Stored(storage) if storage.leafInEGraph => stored
      }
      .flatMap(gezi.ir.Closed.configured)

/** The configurations a test or a program builds. */
object JitConfiguration:

  /** The default budget, the Prolog JIT's flag `lambda_jit_compilation_budget`.
    */
  val defaultBudget: Int = 10000

  /** The young generation's default size (`InstanceRetention.Generations`).
    *
    * Measured 2026-11-02 on d702a2487 with this change, `contest-entries-solo`,
    * one reading each, CPUs 4 and 5, -Xmx3g SerialGC as the judge runs it (the
    * table without a bound held 2,084,612 entries after the calls_10000
    * respelled point of a published points file). calls_10000 respelled then
    * direct in one JVM, seconds: no bound 25.3 and 31.2; 2^18 51.6 and 30.6
    * (the point's working set exceeds a generation, so it reads its instances
    * again); 2^20 28.3 and 28.2; 2^21 26.7 and 27.2. That file's whole pass
    * (seed 3417947893, 291 rows): no bound 559.4 s, 2^20 529.6 s, every row
    * with the same outcome but edit_distances/direct/repetitions_1, stopped
    * with no bound and no_answer under 2^20. A choice among these readings, not
    * an optimum: one reading each.
    */
  val defaultInstanceTableGeneration: Int = 1 << 20

  /** The configuration of the facts' encoding (the specializer of `C`), the
    * default budget, the strategy `predicate_per_code`, the closure backend, no
    * dispatch strategy, the instance table as the caller states
    * (`instanceTable`), and the caller's capability.
    */
  def of[C <: NativeSpecializer & Singleton](
      specializer: StorageEncoding & C,
      instanceTable: Boolean,
      storageAccess: gezi.ir.StorageAccess
  ): JitConfiguration[C] =
    JitConfiguration[C](
      specializer,
      defaultBudget,
      PredicatePerCode,
      ClosureBackend,
      DispatchMode.NoDispatch,
      instanceTable,
      storageAccess = storageAccess
    )

/** The emission a strategy gave a code has another slot count than the code
  * (the Prolog JIT's `domain_error(Name/Arity, StubIndicator)`): the code's
  * slot count and the emission's.
  */
final case class EmissionSlotCount(
    code: Code,
    codeSlots: Int,
    emissionSlots: Int
) extends RuntimeException:
  override def getMessage: String =
    s"the emission of code $code reads $emissionSlots slots, the code has $codeSlots"

/** An instance with fewer fillings than its code's slots, reached through a
  * compiled code (the Prolog JIT's `fillings_fewer_than_slots(Count,
  * Fillings)`).
  */
final case class FillingsFewerThanSlots(slots: Int, fillings: Int)
    extends RuntimeException:
  override def getMessage: String =
    s"fillings_fewer_than_slots($slots, $fillings)"

/** The JIT evaluator, the port of `gezi/prolog/gezi/jit.pl`, whose module
  * comment the rules here follow section by section (AN EVALUATOR OVER THE
  * REFERENCE'S VALUES, THE UNIT IS A CODE, THE BUDGET, THE GENERATION STRATEGY,
  * THE BACKEND'S REPRESENTATIONS, ONLY A TYPE-FILTERED CONSTRUCTOR ENTERS A
  * REPRESENTATION, A DECODE POINT, A SLOT STEP, A NATIVE, A PARALLEL STEP, A
  * FALLBACK POINT, A BLOCK, AN ELIMINATION, WHY THE ANSWERS STAY ANSWERS, THE
  * CHECK HAS NO COUNT OF ITS OWN, DISPATCH STRATEGIES, THE CHECK'S EVALUATION
  * IS PASSED ON, THE COST OF A COPY, THE READING OF AN INFINITE VALUE). It
  * answers the heads the reference (`gezi.weakhead.WeakHead` under weak_head)
  * answers, in the same order, except at the backend's representations.
  *
  * THE UNIT IS A CODE, COMPILED AT ITS FIRST INSTANCE. An instance of a code (a
  * thunk with no hole left) is evaluated by the code's compiled closure
  * (`CompiledCode`, from the strategy's emission by the backend); a code is
  * compiled at its first instance in the evaluation order, a function of the
  * term, and kept in the reading's state (`JitRunState`), from one reading of a
  * suite to the next as the Prolog JIT kept it in the process. Beyond the
  * budget an instance is interpreted: its term built as the reference builds it
  * and its heads taken by these rules, so a term's answers depend neither on
  * the budget nor on what was compiled before.
  *
  * THE MACHINE. As the reference's untabled machine, the evaluation is a stack
  * of goals on the heap: a term with the arguments its heads are still to be
  * applied to, the remaining members of a choice, the remaining clauses of a
  * compiled code, or a stream of heads computed by a rule (a decode point's, a
  * native's, an elimination's), so that a run that re-enters the same term, as
  * Omega's does, grows nothing. Reading one layer of a term, and applying one
  * head to one argument, is one step of the reading's budget, as in the
  * reference.
  *
  * APPLICATIONS COUNTED. A reading asked to count them
  * (`ReadingState.codeApplications`, `gezi.hotspot.Budget.countedUnits`) counts
  * one application of a code each time the JIT enters an instance of it: where
  * it meets a thunk of the code with no hole, in a term read or as a compiled
  * clause's start (`ClauseStart.Instance`, a code whose holes the clause filled
  * when it was compiled), and where it fills the last hole of a head of the
  * code. The instance is counted when it is entered, whatever gives its heads
  * then: the instance table, the native block, the compiled clauses or the
  * interpreter. A cell (`JitRules.cellCode`), the JIT's own sharing of an
  * argument and no code of the term, is not counted. A step of the budget is
  * not taken for each count: a clause that starts with an instance enters it
  * within the step that entered its own code, so the counts of a JIT reading
  * may exceed its steps. Counting changes no step, table or head.
  *
  * Departures from the Prolog JIT: the cache, the counts, the decodings'
  * numbers and the readings' path are a value in the reading's state, not in
  * the process and the thread, so there is no drop, no thread and no
  * transaction, and a stopped reading leaves its compiled codes whole (each
  * code is compiled before it runs); the inner instance a clause holds looks
  * its code up in the cache where the Prolog clause called the code's predicate
  * by its literal name (one map lookup, no compilation once the code is
  * compiled); a code is always a code identifier; the decode point's
  * intersection of a parallel's two sides keeps the left side's order where the
  * Prolog JIT sorted it; the backend's constants are read by the reference
  * evaluator (`BackendFacts.constants`).
  *
  * FIXME (carried from jit.pl:598): a natural whose nested readings never
  * https://github.com/Atry/private-overlay/issues/1930 repeat in spelling has a
  * check without end, so the cooperative answer is lost: `((fixpoint (\f. \n.
  * successor (f (successor n)))) zero) zero (\_. zero)`, whose value is the
  * rational `fixpoint successor` with an argument that grows, which HM types
  * and the reference reads as zero, gave no normal form within the Prolog
  * reading's 10,000,000 inferences (measured 2026-10-30): the check needs the
  * whole natural, a big integer, before either path. A list's spine has no such
  * check since its cells keep their tails unread, but an item that is a
  * fallback point is still checked when its cell is built (the FIXME at
  * `itemOutcome`). Candidate: a natural whose successors are not read until a
  * consumer reads them, which a big integer is not; not designed.
  *
  * FIXME (carried from jit.pl:612, decided for steps): the comparison
  * https://github.com/Atry/private-overlay/issues/1931 of
  * `ReadingPath.extended` costs no step beyond the reading that calls it, while
  * its time grows with what the two readings share: the comparison is the
  * structural equality of two operands, which walks them where they agree.
  * Operands that share a long prefix still compare it: in the Prolog JIT the
  * successors of a natural a closure builds, each nested reading's operand one
  * successor shorter, took 138, 140 and 170 microseconds a successor at k =
  * 256, 512 and 900 for the run of (\y. successor^k y) zero (measured on main
  * a4c6c432e), close to linear at those sizes, quadratic beyond. Steps count
  * the evaluator's goals, as inferences counted SWI-Prolog's calls, and neither
  * counts the cells a comparison walks, so the defect is the same under steps.
  * Candidate: a comparison in constant time, which needs a key of the reading
  * that does not walk its operand; not designed.
  *
  * FIXME (carried from jit.pl:623): the readers read a normal form under a
  * https://github.com/Atry/private-overlay/issues/1932 binder by applying a
  * head to a neutral value, and a fallback point over a term that holds one
  * does not hold, so a strategy whose decision is `rejected` throws where the
  * reading reaches one, an error of the reading and of no input (derived from
  * the rules, not measured). Candidate: a reader's neutral, which is no input
  * of the program, takes the untyped path under every strategy; not designed.
  *
  * FIXME (carried from jit.pl:640): the JIT decides a cycle only through the
  * https://github.com/Atry/private-overlay/issues/1933 instance table. A tabled
  * instance met again within its own reading is answered by its approximation
  * and read again to its fixed point (`tabledInstance`), so Omega and the rings
  * of problems/merge_graph end with no head where the cycle runs through tabled
  * instances. A cycle still runs to the budget where an instance on it runs
  * untabled: under `instanceTable` false, which every caller states; inside a
  * fallback point's check (`JitRunState.readingPath` not empty); where the
  * checkpoint policy only looks the instance up
  * (`CheckpointDecision.LookupOnly`); and for a code `TableCost.unprofitable`
  * cut off. The reference reads such programs under tabling(weak_head).
  *
  * The FIXME of jit.pl:145 is closed by the port: the Prolog JIT's predicates
  * outlived a thread that ended without a drop. Here the compiled codes are a
  * value of the reading's state, which nothing keeps once the reading lets it
  * go, and no thread or process holds a cache; the defect has no counterpart.
  */
final case class Jit[C <: NativeSpecializer & Singleton](
    configuration: JitConfiguration[C]
) extends JitEvaluator[C]:

  private given C = configuration.specializer

  // A decode point of `x ∥ T` hands out a declared family's fields as its facts
  // declare them and its elimination drops `∥ T`, which the pattern theorem of
  // the unique spelling allows only when `⟦T⟧ ⊑ ⟦C F̄⟧`, which `⊢ T = C F̄ + R` gives
  // (`docs/design/gezi-set-equations-proofs.md`, section 23).
  // The premise `⊢ T = C F̄ + R` of every criterion the facts register, a declared family's at every parameter and a
  // codec family's of an infinite parameter at a width written as a variable, is the backend facts' obligation, as the
  // natives' agreement with their defines is: checked in the tests on the library's facts and each in-tree entry's
  // (jit's `UniqueSpellingPremiseTest`, contest-in-tree-entries' `EntriesPremiseTest`), never in the host.

  private val rules = JitRules(configuration)

  def heads(term: Value[C]): Answers[ReadingState[C], ParallelSet[C]] =
    // TODO: deleted: the run-time `require` that the reading's state holds the JIT's configuration. Wrong because which
    // configuration a reading runs under is to be the type parameter of its state and of the JIT, not a check at run
    // time; issue https://github.com/Atry/private-overlay/issues/2261, design v38, section 4.
    // Read it back with `git show 7669694cc:gezi/jit/src/main/scala/gezi/jit/Jit.scala`.
    rules.heads(term).flatMap(rules.observed).distinct

  def readingConfiguration: gezi.weakhead.ReadingConfiguration[C] =
    configuration.readingConfigurationOf(this)

  /** The values of a representation the term's heads are: the values a term
    * `x ∥ C` decodes into, C a decoding criterion, with no normal form read;
    * none for a head that is no value of a representation.
    */
  def representedHeads(
      term: JitValue[C]
  ): Answers[ReadingState[C], NativeValue[JitValue[C]]] =
    rules.heads(term).flatMap {
      case JitHead.Represented(_, value) => Answers.single(value)
      case _                             => Answers.empty
    }

  /** The representation the decoding criterion names, if it names one. */
  def representationOf(
      criterion: Configured[C]
  ): Option[Representation[JitValue[C]]] =
    rules.decodingCriterion(
      gezi.ir.Value.of(criterion)(using configuration.specializer)
    )

/** A result of the JIT's reads of syntax (its rules that read terms by their
  * layers, the section "reading terms by their layers" of `JitRules`), with the
  * count of the layers they read. A reading adds the count to
  * `JitCounts.syntaxReads`; the count is returned, never kept in global state.
  * The decoding criteria the reads read by an instruction, not yet known to the
  * reading (`KnownCriteria`), come back with the result (`learned`), and the
  * reading keeps them in its state (`JitRunState.criteria`).
  */
private final case class SyntaxRead[
    C <: NativeSpecializer & Singleton,
    +Result
](
    result: Result,
    reads: Long,
    learned: Map[Configured[C], Option[Representation[JitValue[C]]]] =
      Map.empty[Configured[C], Option[Representation[JitValue[C]]]]
):

  def map[Next](change: Result => Next): SyntaxRead[C, Next] =
    SyntaxRead(change(result), reads, learned)

  def flatMap[Next](
      continuation: Result => SyntaxRead[C, Next]
  ): SyntaxRead[C, Next] =
    val next = continuation(result)
    SyntaxRead(
      next.result,
      reads + next.reads,
      if next.learned.isEmpty then learned else learned ++ next.learned
    )

  /** The same result with the reads and the criteria learned by another read
    * added.
    */
  def joined(other: SyntaxRead[C, Any]): SyntaxRead[C, Result] =
    SyntaxRead(
      result,
      reads + other.reads,
      if other.learned.isEmpty then learned else learned ++ other.learned
    )

  /** The same result with `more` reads counted. */
  def counted(more: Long): SyntaxRead[C, Result] = copy(reads = reads + more)

private object SyntaxRead:

  /** A result read with no read of syntax. */
  def pure[C <: NativeSpecializer & Singleton, Result](
      result: Result
  ): SyntaxRead[C, Result] = SyntaxRead(result, 0)

  /** The continuation's result on the first read's, if there is one; none
    * otherwise, and then the continuation reads nothing.
    */
  def chained[C <: NativeSpecializer & Singleton, First, Next](
      first: SyntaxRead[C, Option[First]]
  )(
      continuation: First => SyntaxRead[C, Option[Next]]
  ): SyntaxRead[C, Option[Next]] =
    first.flatMap {
      case Some(found) => continuation(found)
      case None        => pure(None)
    }

/** The decoding criteria a reading has already read, by the criterion's
  * instruction (`JitRunState.criteria`): the representation each names, or
  * none. `JitRules.decodingCriterionRead` is a pure function of the
  * instruction, the layers under it, which never change, and the backend's
  * facts, which the configuration fixes, so a criterion read once is taken from
  * here by every later read of the reading. A criterion is the syntax of the
  * filter written in the term; what is kept is which backend representation
  * that syntax names, never a fact about a value.
  */
private final case class KnownCriteria[C <: NativeSpecializer & Singleton](
    byInstruction: Map[Configured[C], Option[Representation[JitValue[C]]]]
)

private object KnownCriteria:

  /** No criterion read: the refinement's reads, outside a reading. */
  def none[C <: NativeSpecializer & Singleton]: KnownCriteria[C] =
    KnownCriteria(Map.empty)

/** The outcome of a fallback point's check, or of an argument's reading
  * (jit.pl's `typed(Values)` and `untyped(Untyped)`): the values at the place,
  * or the run-time value that carries the operand's heads.
  */
enum Outcome[C <: NativeSpecializer & Singleton]:
  case Typed(values: Vector[NativeArgument[JitValue[C]]])
  case Untyped(value: JitValue[C])

/** The place of a native's parameter once the list's element filter is known: a
  * representation, a list's item in the representation of the element filter,
  * or a list's tail in the list's representation.
  */
enum Place[C <: NativeSpecializer & Singleton]:
  case In(representation: Representation[JitValue[C]])
  case ItemOf(element: JitValue[C])
  case TailOf(element: JitValue[C])

/** An argument of a native given its last argument (arguments_valued/3): its
  * values, its untyped outcome, or the argument to read when the native is
  * called.
  */
private enum Valued[C <: NativeSpecializer & Singleton]:
  case Values(values: Vector[NativeArgument[JitValue[C]]])
  case Unvalued(value: JitValue[C])
  case Lazy(argument: JitValue[C], place: Place[C])

/** The bounds of the rules. */
/** What a decoding reads of one member of a decode point. */
private enum Decoded[C <: NativeSpecializer & Singleton]:
  /** A value of the representation, exactly the member. */
  case Read(value: NativeValue[JitValue[C]])

  /** No value of the criterion's shapes (a constructor it excludes, a head that
    * is no case of the decoding, a field that reads none): the member has no
    * normal form of its own, so read for it the decode point gives no head,
    * exactly; under arguments it gives the parallel, which the criterion's
    * other shapes can meet there.
    */
  case Refuted()

  /** A member of the criterion's shapes that is no storage: a list cell whose
    * fields are not in the unique spelling (`layer`, the one layer read, its
    * item and tail as written, which a block's entry asks again,
    * `writtenCell`), a generic layer whose filtered field is not written
    * `f ∥ F`, a layer whose field reads several heads, or sides of a parallel
    * that read apart (no layer). It is read as written, the parallel, under
    * arguments or not: it can have normal forms, which a refutation would drop.
    */
  case AsWritten(layer: Option[NativeValue[JitValue[C]]])

object JitRules:

  /** The steps a native block's entry may spend reading a filling to its head
    * to find the self filling (`JitRules.selfFound`): a choice, not a
    * measurement; Turing's fixed point combinator, the library's `fixpoint`,
    * reaches its function's lambda in a few steps.
    */
  val selfReadingSteps: Long = 64

  /** Whether two values spell one term: equal, or applications whose parts
    * spell one term, an instruction read through its application layer
    * (`JitRules.selfFound`). It reads syntax only, and decides whether a
    * filling holds itself, never what a value is.
    */
  def spelledAlike[C <: NativeSpecializer & Singleton](
      left: JitValue[C],
      right: JitValue[C]
  )(using C): Boolean =
    Value
      .same(left, right) || ((applicationOf(left), applicationOf(right)) match
      case (
            Some((leftFunction, leftArgument)),
            Some((rightFunction, rightArgument))
          ) =>
        spelledAlike(leftFunction, rightFunction) && spelledAlike(
          leftArgument,
          rightArgument
        )
      case _ => false)

  private def applicationOf[C <: NativeSpecializer & Singleton](
      value: JitValue[C]
  )(using C): Option[(JitValue[C], JitValue[C])] = value match
    case JitValue.Apply(function, argument) => Some((function, argument))
    case _                                  => None

  /** The code of a cell (`JitRules.shared`): slot 0, whose instance under the
    * fillings `[v]` is v.
    */
  val cellCode: Code = Code.Slot(0)

/** The rules of the JIT under one configuration (`Jit`'s comment). */
final case class JitRules[C <: NativeSpecializer & Singleton](
    configuration: JitConfiguration[C]
):

  // The types of this configuration, under the names the rules read them by: a value, a head, a reading's state, a
  // representation and native data of `C`'s terms. Each is the generic type at `C`, nothing more.
  private type JitValue = gezi.jit.JitValue[C]
  private type Value = gezi.ir.Value[C]
  private type Term = Configured[C]
  private type JitHead = gezi.jit.JitHead[C]
  private type Head = gezi.weakhead.Head[C]
  private type ReadingState = gezi.weakhead.ReadingState[C]
  private type ParallelSet = gezi.weakhead.ParallelSet[C]
  private type JitRunState = gezi.jit.JitRunState[C]
  private type Representation = gezi.jit.Representation[JitValue]
  private type NativeValue = gezi.jit.NativeValue[JitValue]
  private type NativeArgument = gezi.jit.NativeArgument[JitValue]
  private type FamilyParameter = gezi.jit.FamilyParameter[JitValue]
  private type DataLayer = gezi.jit.DataLayer[JitValue]
  private type SyntaxRead[+Result] = gezi.jit.SyntaxRead[C, Result]
  private type KnownCriteria = gezi.jit.KnownCriteria[C]
  private type Outcome = gezi.jit.Outcome[C]
  private type Place = gezi.jit.Place[C]
  private type Valued = gezi.jit.Valued[C]
  private type Decoded = gezi.jit.Decoded[C]
  private type TabledInstance = gezi.jit.TabledInstance[C]
  private type OperandReading = gezi.jit.OperandReading[C]
  private type ReadingPath = gezi.jit.ReadingPath[C]
  private type DecodePoint = gezi.jit.DecodePoint[C]
  private type DecodedPoints = gezi.jit.DecodedPoints[C]
  private type CheckedOperand = gezi.jit.CheckedOperand[C]
  private type CheckedHeads = gezi.jit.CheckedHeads[C]
  private type SharedTerms = gezi.jit.SharedTerms[C]
  private type ClauseStart = gezi.jit.ClauseStart[C]
  private type CompiledCode = gezi.jit.CompiledCode[C]
  private type GroupBlockResult = gezi.jit.GroupBlockResult[C]
  private type BlockEntry = gezi.jit.BlockEntry[C]
  private type BlockResult = gezi.jit.BlockResult[C]
  private type BlockOutcome = gezi.jit.BlockOutcome[C]
  private type SelfFilling = gezi.jit.SelfFilling[C]
  private type InstanceRead = gezi.jit.InstanceRead[C]
  private type ReadTrace = gezi.jit.ReadTrace[C]
  private type HeldRead = gezi.jit.HeldRead[C]
  private type VerifiableTable = gezi.jit.VerifiableTable[C]

  private given C = configuration.specializer

  /** The reads of syntax of this configuration: `gezi.jit.SyntaxRead`'s
    * constructions with `C` named, which a call whose arguments mention no `C`
    * cannot infer (a type parameter bounded by `Singleton` is inferred as the
    * singleton type of a stable argument).
    */
  private object SyntaxRead:
    def apply[Result](result: Result, reads: Long): SyntaxRead[Result] =
      gezi.jit.SyntaxRead[C, Result](result, reads)

    def pure[Result](result: Result): SyntaxRead[Result] =
      gezi.jit.SyntaxRead.pure[C, Result](result)

    def chained[First, Next](first: SyntaxRead[Option[First]])(
        continuation: First => SyntaxRead[Option[Next]]
    ): SyntaxRead[Option[Next]] =
      gezi.jit.SyntaxRead.chained[C, First, Next](first)(continuation)

  private val facts = configuration.facts

  /** The facts' part in this configuration: their keys as terms of `C`, the
    * crossed index, the constants.
    */
  private val operations: StorageEncodingOperations[C] =
    configuration.operations

  private val nativeBackend = facts.nativeBackend

  /** The node `left ∥ right` built by the configuration's native specializer.
    */
  private def parallel(left: JitValue, right: JitValue): JitValue =
    gezi.ir.Value.Parallel(left, right)

  /** A pure key of the facts as a term of this configuration: the same object.
    */
  private def pureTerm(key: gezi.ir.Pure): Term =
    Configured.fromPure(configuration.specializer)(key)

  /** The head a value of a representation is: the storage of the value in this
    * configuration, its own head.
    */
  private def represented(
      representation: Representation,
      value: NativeValue
  ): JitHead =
    operations.storageOf(representation, value) match
      case JitValue.Stored(storage) => storage
      case other                    =>
        throw IllegalStateException(
          s"the storage of a native value is no storage: $other"
        )

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
      * native: the generic reading of a native-bound library file's term, whose
      * layer is that term itself now that an instruction is its own layer
      * (`genericApplied`).
      */
    case LayerEvaluation(layer: JitValue, arguments: List[JitValue])
    case Members(
        members: Vector[JitValue],
        from: Int,
        arguments: List[JitValue]
    )
    case Clauses(
        code: CompiledCode,
        fillings: Vector[JitValue],
        from: Int,
        arguments: List[JitValue]
    )
    case Heads(heads: Stream, arguments: List[JitValue])
    case Untabled(code: Code, fillings: Vector[JitValue])

    /** The instance read as any instance met in a term is (`instance`). */
    case Tabled(code: Code, fillings: Vector[JitValue])

    /** The term evaluated as `Evaluation` evaluates it, but for the lookup of
      * the shared terms: the body of the instance
      * `TabledInstance(cellCode, [term])`, whose subject is this term, so that
      * it does not read its own table.
      */
    case SharedBody(term: JitValue, arguments: List[JitValue])

  private final case class Machine(goals: List[Goal])

  /** The heads of the closed term, one at a time, in the reference's order
    * (jit_head/2).
    */
  def heads(term: JitValue): Stream = headsApplied(term, Nil)

  /** The heads of the term applied to the arguments in turn. */
  private def headsApplied(term: JitValue, arguments: List[JitValue]): Stream =
    running(Machine(List(Goal.Evaluation(term, arguments))))

  /** The heads of the head applied to the arguments in turn (heads_applied/3).
    */
  private def headApplied(head: JitHead, arguments: List[JitValue]): Stream =
    running(Machine(List(Goal.Heads(Answers.single(head), arguments))))

  /** The heads the machine reads, its goals run in turn on the reading's state.
    *
    * FIXME (2026-11-07): a reading can still run out of
    * https://github.com/Atry/private-overlay/issues/1934 memory here. The hot
    * ladder's `calls_100000_hot` direct, read as written with the instance
    * table on (CPUs 2 and 3), ran out of memory with a 2 GB heap after 120 s
    * and with a 1 GB heap after 58 s, after the trampoline and the miss's
    * continuation removed the retention of run and reading states. At the last
    * JFR object count the heap held `JitValue.Apply` (157 MB) and pending
    * `Trampoline` continuations and `JitRules` lambdas (about 320 MB). The
    * cause is not localized. An unverified guess: a by-need reading of
    * iterate's state builds a chain of applications as long as the calls.
    * Candidates, not designed: find what holds the applications (JFR old object
    * samples with paths to the roots), then force a goal's state where the
    * reading's semantics allows it, or bound the pending goals.
    */
  private def running(machine: Machine): Stream =
    Answers(
      Computation(state =>
        nextHead(machine.goals, state).map {
          case Computed.Done(Some((head, rest)), after) =>
            Computed.Done(Some((head, running(rest))), after)
          case Computed.Done(None, after) => Computed.Done(None, after)
          case Computed.Stopped(stopped)  => Computed.Stopped(stopped)
        }
      )
    )

  private type Next =
    Trampoline[Computed[ReadingState, Option[(JitHead, Machine)]]]

  private def nextHead(goals: List[Goal], state: ReadingState): Next =
    goals match
      case Nil => done(Computed.Done(None, state))
      case Goal.Untabled(code, fillings) :: rest =>
        untabledInstance(code, fillings, Nil, rest, state)
      case Goal.Tabled(code, fillings) :: rest =>
        instance(code, fillings, Nil, rest, state)
      case Goal.Members(members, from, arguments) :: rest =>
        val remaining =
          if from + 1 < members.size then
            Goal.Members(members, from + 1, arguments) :: rest
          else rest
        tailcall(
          nextHead(
            Goal.Evaluation(members(from), arguments) :: remaining,
            state
          )
        )
      case Goal.Clauses(code, fillings, from, arguments) :: rest =>
        val remaining =
          if from + 1 < code.emission.clauses.size then
            Goal.Clauses(code, fillings, from + 1, arguments) :: rest
          else rest
        code.clause(from, fillings) match
          case ClauseStart.Evaluation(term, clauseArguments) =>
            tailcall(
              nextHead(
                Goal.Evaluation(
                  term,
                  clauseArguments.toList ++ arguments
                ) :: remaining,
                state
              )
            )
          case ClauseStart.Answer(head) =>
            applied(head, arguments, remaining, state)
          case ClauseStart.Instance(inner, innerFillings, clauseArguments) =>
            instance(
              inner,
              innerFillings,
              clauseArguments.toList ++ arguments,
              remaining,
              state.entered(inner)
            )
          case ClauseStart.ParallelHead(left, right, clauseArguments) =>
            tailcall(
              nextHead(
                Goal.Evaluation(
                  parallel(left, right),
                  clauseArguments.toList ++ arguments
                ) :: remaining,
                state
              )
            )
      case Goal.Heads(stream, arguments) :: rest =>
        tailcall(stream.pull.run(state)).flatMap {
          case Computed.Done(None, after) => tailcall(nextHead(rest, after))
          case Computed.Done(Some((head, more)), after) =>
            applied(head, arguments, Goal.Heads(more, arguments) :: rest, after)
          case Computed.Stopped(stopped) => done(Computed.Stopped(stopped))
        }
      case Goal.Evaluation(term, arguments) :: rest =>
        state.budget.charged match
          case None          => done(Computed.Stopped(state))
          case Some(charged) =>
            extremeOrEvaluated(
              term,
              arguments,
              rest,
              state.copy(budget = charged),
              sharedLookup = true
            )
      // The body of a shared term's cell reads the term as an evaluation does, the listed extremes included: a shared
      // term may be one, such as `top` filling a slot.
      case Goal.SharedBody(term, arguments) :: rest =>
        state.budget.charged match
          case None          => done(Computed.Stopped(state))
          case Some(charged) =>
            extremeOrEvaluated(
              term,
              arguments,
              rest,
              state.copy(budget = charged),
              sharedLookup = false
            )
      case Goal.LayerEvaluation(layer, arguments) :: rest =>
        state.budget.charged match
          case None          => done(Computed.Stopped(state))
          case Some(charged) =>
            layerEvaluated(layer, arguments, rest, state.copy(budget = charged))

  /** The term evaluated, unless it is a listed extreme of ⊑_O, which is not
    * evaluated, whatever it is applied to, as under the weak head's machines
    * (`WeakHead.knownExtreme`): a greatest term gives no head, a least term the
    * empty parallel set. One pool interns values and instructions, so a listed
    * extreme and the JIT's value of the same term are one object.
    */
  private def extremeOrEvaluated(
      term: JitValue,
      arguments: List[JitValue],
      rest: List[Goal],
      stepped: ReadingState,
      sharedLookup: Boolean
  ): Next =
    val extremes = stepped.extremes
    if !extremes.isEmpty && extremes.top(term) then
      tailcall(nextHead(rest, stepped))
    else if !extremes.isEmpty && extremes.bottom(term) then
      done(Computed.Done(Some((EmptyParallel, Machine(rest))), stepped))
    else evaluated(term, arguments, rest, stepped, sharedLookup)

  /** One layer of the term read and dispatched by its constructor (jit_head/2).
    * First, a shared term (`SharedTerms`, unless `sharedLookup` is off, in the
    * body of its own instance) is read through the instance table under
    * `TabledInstance(cellCode, [term])`, always tabled; then the heads an uncut
    * check found for the term under this dispatch mode (`CheckedHeads`) are
    * replayed, the lookup and each head charged a step as an instance's hit is,
    * and the reading's trace made opaque, the check's reads having been noted
    * for no instance that reads this hit.
    */
  private def evaluated(
      term: JitValue,
      arguments: List[JitValue],
      rest: List[Goal],
      state: ReadingState,
      sharedLookup: Boolean
  ): Next =
    val run = JitRunState.of(state, configuration)
    if sharedLookup && run.sharedTerms.contains(term) then
      instance(JitRules.cellCode, Vector(term), arguments, rest, state)
    else
      run.checkedHeads.found(CheckedOperand(term, configuration.dispatch)) match
        case Some(found) =>
          val spent = state.budget.spent + 1 + found.size
          if spent > state.budget.bound then done(Computed.Stopped(state))
          else
            val hit = state.copy(
              budget = state.budget.copy(spent = spent),
              jitState = run.traceMadeOpaque
            )
            tailcall(
              nextHead(Goal.Heads(Answers.of(found), arguments) :: rest, hit)
            )
        case None => layerDispatched(term, arguments, rest, state)

  /** The term's layer dispatched by its constructor, after the lookups of
    * `evaluated`.
    */
  private def layerDispatched(
      term: JitValue,
      arguments: List[JitValue],
      rest: List[Goal],
      state: ReadingState
  ): Next =
    term match
      case JitValue.Stored(storage) =>
        applied(storage, arguments, rest, state)
      // A group of storages is the choice of its members, each its own head,
      // read one at a time as a choice's members are, its view not made.
      case JitValue.Grouped(members) =>
        tailcall(nextHead(Goal.Members(members, 0, arguments) :: rest, state))
      // A URI node is its expansion, the δ step, as under the weak head
      // (`WeakHead.uriExpanded`): the expansion the state remembers, or the
      // front end's (`DirectoryTree.expansion`), remembered from now on; no
      // evaluator step. A cell reads the directory tree off its state through
      // its root's URI node.
      case JitValue.IrTerm(instruction) if instruction.uri.isDefined =>
        val (expansion, expansions) =
          state.expansions.expanded(instruction, state.specializer)
        val expanded = state.copy(expansions = expansions)
        val noted =
          if configuration.instanceReuse == InstanceReuse.WithinVersion then
            expanded
          else
            expanded.copy(jitState =
              JitRunState
                .of(state, configuration)
                .readNoted(InstanceRead.Expansion(instruction, expansion))
            )
        tailcall(
          nextHead(
            Goal.Evaluation(Value.of(expansion), arguments) :: rest,
            noted
          )
        )
      case JitValue.IrTerm(instruction)
          if operations.nativeOfParameters(Value.of(instruction)).isDefined =>
        val native = operations.nativeOfParameters(Value.of(instruction)).get
        applied(
          JitHead.NativeApplication(
            instruction,
            native,
            native.parameterCount,
            Vector.empty
          ),
          arguments,
          rest,
          state
        )
      case JitValue.IrTerm(instruction)
          if groupBlockAsked(instruction, arguments) =>
        groupBlockEntered(term, instruction, arguments, rest, state)
      case _ =>
        val read = layer(term)
        layerEvaluated(read.result, arguments, rest, syntaxCounted(state, read))

  /** Whether the machine asks the group block mechanism about the written
    * closed thunk applied to the arguments: the configuration has a mechanism,
    * the instruction's layer is a thunk with holes, no more than the arguments,
    * and the mechanism could run a block on the first arguments, their holes'
    * count (`GroupBlocks.runnable`).
    */
  private def groupBlockAsked(
      instruction: Term,
      arguments: List[JitValue]
  ): Boolean =
    (configuration.groupBlocks ne NoGroupBlocks) && !instruction.heldAsLeaf && !instruction.opaque && (instruction.layer match
      case gezi.ir.Thunk(_, holes, _) =>
        holes.nonEmpty && arguments.sizeCompare(
          holes.size
        ) >= 0 && configuration.groupBlocks.runnable(
          arguments.take(holes.size).toVector
        )
      case _ => false)

  /** The application of the written closed thunk to the arguments, by its group
    * block when it has one that runs on the first arguments, its holes' count
    * of them, each read first through its decode point `a ∥ T` (`entryDecoded`,
    * T the criterion of the block's representation of that parameter), the
    * decoding and the block within what is left of the mechanism's share of the
    * budget's steps (`GroupBlocks.allowance`): the steps charged to the budget
    * and the machine continuing from the block's value applied to the rest of
    * the arguments. A decoding that runs out of the share goes back to the
    * state before it, its steps still spent, as an instance's lookahead does
    * (`InstanceLookahead.lookedAhead`), so that no value it read in part is
    * kept; one that gives a head of no storage leaves the state it read. The
    * share is of the budget's steps (a Moore run's state reads under what is
    * left of the run's budget), for the steps all the blocks of the reading
    * waste together (`JitRunState.wastedGroupBlockSteps`: a decoding that ran
    * out or read no storage, a block that admitted no argument or stopped), so
    * that the machine keeps the rest whatever thunks the blocks run, closures
    * the JIT built included, while the steps of a block that gives a value,
    * which replace the machine's, are not counted; and a thunk whose decoding
    * ran out of the share, or whose block stopped other than on a rejected row,
    * is given up for the rest of the reading
    * (`JitRunState.givenUpGroupBlocks`), so that a thunk that does not end does
    * not waste the share of every other. A decoding that read no storage, a
    * block that admitted no argument, or one that stopped on a rejected row
    * (`GroupBlockResult.Rejected`), does not give its thunk up: that outcome is
    * the argument's, and another argument may give a value; such waste is
    * bounded by the share all the same. Both are costs, never types, and both
    * are cleared when a reading starts (`JitState.readingStarted`). A thunk
    * given up for one argument runs no block for another in that reading, a
    * refinement as any application the machine reads. The block of each thunk
    * is kept in the reading's state (`JitRunState.groupBlocks`), in two
    * generations under the instance retention's `Generations(size)`: when the
    * young one holds `size` thunks it becomes the old one, the old one dropped,
    * and a thunk found in the old one is kept in the young one again. When
    * there is no block, or it stopped (its steps charged all the same), the
    * machine reads the application as it reads any.
    */
  private def groupBlockEntered(
      term: JitValue,
      instruction: Term,
      arguments: List[JitValue],
      rest: List[Goal],
      state: ReadingState
  ): Next =
    val run = JitRunState.of(state, configuration)
    val artifact = run.groupBlocks
      .get(instruction)
      .orElse(run.olderGroupBlocks.get(instruction))
      .getOrElse(configuration.groupBlocks.compiled(instruction, operations))
    val kept = state.copy(jitState = configuration.instanceRetention match
      case InstanceRetention.Generations(size)
          if !run.groupBlocks
            .contains(instruction) && run.groupBlocks.size >= size =>
        run.copy(
          groupBlocks = Map(instruction -> artifact),
          olderGroupBlocks = run.groupBlocks
        )
      case _ =>
        run.copy(groupBlocks = run.groupBlocks.updated(instruction, artifact)))
    val holes = instruction.layer match
      case gezi.ir.Thunk(_, thunkHoles, _) => thunkHoles.size
      case other                           =>
        throw IllegalStateException(
          s"a group block's thunk is a thunk, not $other"
        )
    val (taken, later) = arguments.splitAt(holes)
    val budget = kept.budget
    def unentered(from: ReadingState): Next =
      val read = layer(term)
      layerEvaluated(read.result, arguments, rest, syntaxCounted(from, read))
    def givenUp(from: ReadingState): ReadingState =
      val current = JitRunState.of(from, configuration)
      from.copy(jitState =
        current.copy(givenUpGroupBlocks =
          current.givenUpGroupBlocks + instruction
        )
      )
    // The steps since the entry began, which gave no value, added to the reading's waste.
    def wasted(from: ReadingState): ReadingState =
      val current = JitRunState.of(from, configuration)
      from.copy(jitState =
        current.copy(wastedGroupBlockSteps =
          current.wastedGroupBlockSteps + from.budget.spent - budget.spent
        )
      )
    val keptRun = JitRunState.of(kept, configuration)
    val allowed = math.min(
      budget.bound - budget.spent,
      configuration.groupBlocks.allowance(
        budget.limit
      ) - keptRun.wastedGroupBlockSteps
    )
    artifact match
      case None => unentered(kept)
      case Some(_)
          if allowed <= 0 || keptRun.givenUpGroupBlocks.contains(instruction) =>
        unentered(kept)
      case Some(block) =>
        val ceiling = budget.spent + allowed
        tailcall(
          ReadingState
            .attempted(
              entryDecoded(taken.toVector, block.entryRepresentations),
              allowed,
              speculative = true
            )
            .run(kept)
        ).flatMap {
          case Computed.Done(Attempt.Finished(Some(decoded)), after) =>
            def charged(steps: Long): ReadingState = after.copy(budget =
              after.budget.copy(spent = after.budget.spent + steps)
            )
            block.run(decoded, ceiling - after.budget.spent, budget.stop) match
              case Some(GroupBlockResult.Gave(value, steps)) =>
                tailcall(
                  nextHead(
                    Goal.Evaluation(value, later) :: rest,
                    charged(steps)
                  )
                )
              case Some(GroupBlockResult.Rejected(steps)) =>
                unentered(wasted(charged(steps)))
              case Some(GroupBlockResult.Stopped(steps)) =>
                unentered(givenUp(wasted(charged(steps))))
              case None => unentered(wasted(after))
          case Computed.Done(Attempt.Finished(None), after) =>
            unentered(wasted(after))
          case Computed.Done(Attempt.OutOfSteps(_), after) =>
            unentered(givenUp(wasted(after)))
          case Computed.Stopped(stopped) => done(Computed.Stopped(stopped))
        }

  /** The arguments of a group block read whole through their decode points
    * `a ∥ T`, T the criterion of each parameter's representation: each the
    * choice of its decode point's heads, every one a storage, interned, a
    * list's cell of an array list's parameter read into the array list
    * (`entryArrayList`), a cell read as written included, whose layer the entry
    * walks (`writtenCell`); none when a decode point gives no head or any other
    * head that is no storage (a value left as written, a parallel kept whole),
    * for which the block does not run.
    *
    * A member of an argument that the parameter's criterion excludes (`0` of
    * `0 + 2` under the positive naturals) is read by the decode point as the
    * parallel `0 ∥ P` (`membersDecoded`), which is no storage, so the block
    * does not run and the reader reads the application.
    */
  private def entryDecoded(
      arguments: Vector[JitValue],
      representations: Vector[Representation]
  ): Computation[ReadingState, Option[Vector[JitValue]]] =
    require(
      arguments.size == representations.size,
      s"a block has a representation for each of its ${arguments.size} parameters, not ${representations.size}"
    )
    Computation.folded(
      arguments.zip(representations),
      Option(Vector.empty[JitValue])
    ) {
      case (None, _)                                 => Computation.pure(None)
      case (Some(found), (argument, representation)) =>
        heads(
          parallel(argument, operations.criterionOf(representation))
        ).collected.flatMap(decoded =>
          Computation
            .traversed(decoded)(entryStorage(_, representation))
            .map(storages =>
              Option.when(decoded.nonEmpty && storages.forall(_.isDefined))(
                found :+ JitValue.Choice(storages.flatten)
              )
            )
        )
    }

  /** The storage a head of an entry's decode point stands for: the storage the
    * head is, or, for an array list's parameter, the array list of a list's
    * cells the head is; none for any other head.
    */
  private def entryStorage(
      head: JitHead,
      representation: Representation
  ): Computation[ReadingState, Option[JitValue]] =
    (representation, head) match
      case (
            Representation.ArrayListOf(element),
            JitHead.Represented(Representation.ListOf(_), listed)
          ) =>
        entryArrayList(representation, element, listed)
      case (
            Representation.ArrayListOf(element),
            JitHead.Parallel(member, criterion)
          )
          if Value.same(
            criterion,
            operations.criterionOf(
              Representation.ListOf(operations.criterionOf(element))
            )
          ) =>
        writtenCell(
          Representation.ListOf(operations.criterionOf(element)),
          member
        ).flatMap {
          case Some(layer) => entryArrayList(representation, element, layer)
          case None        => Computation.pure(None)
        }
      case (_, JitHead.StorageHead(storage)) =>
        Computation.pure(Some(StorageOf.value(storage)))
      case _ => Computation.pure(None)

  /** The one layer of a list member the decode point reads as written, a cell
    * whose fields are not in the unique spelling (`Decoded.AsWritten`): the
    * member's one head, decoded into one layer; none for several heads or any
    * other reading. The decode point gave the member as a parallel head, which
    * carries no layer, so the head is decoded here a second time, charged to
    * the reading and counted as a decoding.
    */
  private def writtenCell(
      listRepresentation: Representation,
      member: JitValue
  ): Computation[ReadingState, Option[NativeValue]] =
    heads(member).collected.flatMap {
      case Vector(head) =>
        headDecoded(listRepresentation, head, None, 0).collected.map {
          case Vector(Decoded.AsWritten(Some(layer))) => Some(layer)
          case Vector(Decoded.Read(layer))            => Some(layer)
          case _                                      => None
        }
      case _ => Computation.pure(None)
    }

  /** The array list's storage of a list's cells read whole, from the first:
    * each item a storage of the element, or read through its decode point to
    * one storage of it; each tail a storage of the list or of the array list,
    * or read through its decode point to one, or to a cell it reads as written,
    * whose one layer is walked on (`writtenCell`); none at the first item or
    * tail that reads otherwise (several heads, or a head that is no such
    * storage), so that a list the reading does not hold whole enters no block.
    * A list read so, one head at every layer, is the array list's term by the
    * pattern theorem and β, so the block loses no answer. Each decode point the
    * entry reads is charged to the reading as any.
    *
    * FIXME: a conversion at run time, which the blueprint's vision does not
    * https://github.com/Atry/private-overlay/issues/2238 have: a cooperative
    * program converts nothing, an intermediate step of the blueprint allowing
    * it until the blueprint is realized. It stands until the typed rounds write
    * a program's literal lists in the unique spelling and the block reads their
    * storages.
    */
  private def entryArrayList(
      representation: Representation,
      element: Representation,
      first: NativeValue
  ): Computation[ReadingState, Option[JitValue]] =
    val encoding = operations
    val listRepresentation =
      Representation.ListOf(encoding.criterionOf(element))
    // One head only, a value of the representation: a member read as the parallel, or a value that may hold a case
    // of a decoding, leaves the list unread whole, so that no block runs without it.
    def onlyHead(stream: Stream): Computation[ReadingState, Option[JitHead]] =
      stream.collected.map {
        case Vector(only @ JitHead.Represented(_, found))
            if !JitValues.mayHoldDecodingCase(found) =>
          Some(only)
        case _ => None
      }
    def item(node: JitValue): Computation[ReadingState, Option[ArrayItem]] =
      def natural(found: AnyRef): Option[ArrayItem] = found match
        case storage: BinaryNaturalStorage
            if storage.representation == element =>
          Some(storage.natural.bigInteger)
        case storage: IntStorage if storage.representation == element =>
          Some(storage.bits)
        case _ => None
      encoding.storedThrough(node) match
        case Some(JitValue.Stored(storage)) =>
          Computation.pure(natural(storage))
        case _ =>
          onlyHead(decodePointHeads(element, node, applied = true))
            .map(_.flatMap(natural))
    // A tail's value, a list's to walk on or an array list's suffix to end with.
    def tail(node: JitValue): Computation[ReadingState, Option[
      Either[NativeValue, Vector[ArrayItem]]
    ]] =
      def read(found: JitHead): Option[Either[NativeValue, Vector[ArrayItem]]] =
        found match
          case storage: ArrayListStorage
              if storage.representation == representation =>
            Some(Right(storage.listed.suffix))
          case JitHead.StorageHead(storage)
              if storage.representation == listRepresentation =>
            Some(Left(StorageOf.nativeValue(storage)))
          case _ => None
      encoding.storedThrough(node) match
        case Some(JitValue.Stored(storage)) => Computation.pure(read(storage))
        case _                              =>
          decodePointHeads(listRepresentation, node, applied = true).collected
            .flatMap {
              // A tail the decode point reads as written: its one layer, walked on.
              case Vector(JitHead.Parallel(member, _)) =>
                writtenCell(listRepresentation, member).map(_.map(Left(_)))
              case Vector(only @ JitHead.Represented(_, found))
                  if !JitValues.mayHoldDecodingCase(found) =>
                Computation.pure(read(only))
              case _ => Computation.pure(None)
            }
    def walked(
        value: NativeValue,
        found: Vector[ArrayItem]
    ): Computation[ReadingState, Option[Vector[ArrayItem]]] =
      value match
        case NativeValue.Listed(ListRepresentation.Items(_, items)) =>
          Computation
            .traversed(items)(item)
            .map(read =>
              Option.when(read.forall(_.isDefined))(found ++ read.flatten)
            )
        case NativeValue.Listed(ListRepresentation.Cell(itemNode, tailNode)) =>
          item(itemNode).flatMap {
            case None         => Computation.pure(None)
            case Some(number) =>
              tail(tailNode).flatMap {
                case None              => Computation.pure(None)
                case Some(Left(next))  => walked(next, found :+ number)
                case Some(Right(rest)) =>
                  Computation.pure(Some((found :+ number) ++ rest))
              }
          }
        case listed: NativeValue.ArrayListed =>
          Computation.pure(Some(found ++ listed.suffix))
        case _ => Computation.pure(None)
    walked(first, Vector.empty).map(
      _.map(values =>
        encoding.storageOf(
          representation,
          encoding.arrayList(representation, values)
        )
      )
    )

  private def layerEvaluated(
      layer: JitValue,
      arguments: List[JitValue],
      rest: List[Goal],
      state: ReadingState
  ): Next =
    layer match
      case JitValue.Thunk(code, holes, fillings) =>
        if holes.nonEmpty then
          applied(JitHead.Lambda(code, holes, fillings), arguments, rest, state)
        else instance(code, fillings, arguments, rest, state.entered(code))
      // A cell is now the IR thunk Thunk(cellCode, [], [inner]) itself, an instance like any other thunk with no holes.
      case JitValue.Apply(function, argument) =>
        tailcall(
          nextHead(
            Goal.Evaluation(function, argument :: arguments) :: rest,
            state
          )
        )
      case JitValue.Choice(members) =>
        given KnownCriteria = known(state)
        val read = fallbackMembers(members)
        val counted = syntaxCounted(state, read)
        read.result match
          case Some((operand, representation)) =>
            tailcall(
              nextHead(
                Goal.Heads(
                  fallbackPointHeads(representation, operand),
                  arguments
                ) :: rest,
                counted
              )
            )
          case None =>
            if members.isEmpty then tailcall(nextHead(rest, counted))
            else
              tailcall(
                nextHead(Goal.Members(members, 0, arguments) :: rest, counted)
              )
      case JitValue.Parallel(left, right) =>
        given KnownCriteria = known(state)
        val read = decodingRepresentation(right)
        val counted = syntaxCounted(state, read)
        read.result match
          case Some(representation) =>
            tailcall(
              nextHead(
                Goal.Heads(
                  checkedDecodePointHeads(
                    representation,
                    left,
                    right,
                    arguments.nonEmpty
                  ),
                  arguments
                ) :: rest,
                counted
              )
            )
          // FIXME: the https://github.com/Atry/private-overlay/issues/2038
          // JIT does not read `ReadingState.parallels`; a parallel head is
          // applied with both sides as under `ParallelReading.BothSides`,
          // so `HeadsMet` does not reach an entry's reading.
          case None =>
            applied(JitHead.Parallel(left, right), arguments, rest, counted)
      case JitValue.Neutral(variable, neutralArguments) =>
        applied(
          JitHead.Neutral(variable, neutralArguments),
          arguments,
          rest,
          state
        )
      case other =>
        throw IllegalStateException(s"a layer read is no layer: ${other.layer}")

  /** The instance of the code under the fillings applied to the arguments
    * (jit_instance_head/3). Under `instanceTable`, the instance's heads come
    * from the table when its key is complete there; otherwise they are the
    * instance's tabled heads (`tabledInstance`), each applied to the arguments
    * as it comes. A reading the budget stops while it reads them completes
    * nothing in the table. An instance whose code the table does not pay for
    * (`TableCost`), a cell's excepted (`shared`), is run as it is, without the
    * table. An instance is keyed by its code and its fillings
    * (`TabledInstance`), all interned. A lookup is charged as steps what its
    * key costs to hash and compare, the number of its fillings: a hit takes an
    * instance's heads for no other step, so without the charge a budget of
    * steps bought more work under the table than without it.
    *
    * MEASURED (2026-11-01 06:18 UTC, a probe that is not committed, CPUs 0 and
    * 1, `contest-entries-osprey` with the table on, before lookups were charged
    * and codes cut off): the longest common subsequence written by definition
    * (the published repeated_library_longest_common_subsequences, one site,
    * binary naturals) is read correctly at n = 10 to 320 in 10,912 to
    * 45,520,688 steps, 0.35 to 30.4 s, with 9 to 13 table entries a cell of the
    * (n + 1)^2; without the table it is exponential in n.
    *
    * MEASURED (2026-11-01 20:51 UTC, the same kind of probe over 208 published
    * points in the pass's order, CPUs 0 and 1, `contest-entries-osprey` with
    * the table on, lookups charged and codes cut off by `TableCost`): every
    * outcome the same as without the table (196 correct, 8 stopped, 4 member
    * judgments unproved), 287 s against 388 s in all;
    * repeated_reduction_problems_grids 1.1 s against 5.5 s,
    * repeated_library_billboards 22.0 s against 28.9 s,
    * repeated_library_unshared_doublings 11.1 s against 14.6 s,
    * repeated_set_free_scope_judgments 56.4 s against 49.1 s. Before the charge
    * and the cutoff the same probe took 520 s, the points that read to their
    * budget up to three times as long as without the table.
    *
    * MEASURED (2026-11-02, a probe that is not committed, CPUs 2 and 3, the
    * plain JIT with no dispatch and the table on, the longest common
    * subsequence's direct site of two random strings of n characters below 4):
    * when an instance whose fillings exceeded 64 nodes ran untabled, the steps
    * a cell were 250, 1,099, 1,523 and 112,826 at n = 2, 4, 6 and 8 and grew
    * with n beyond; keyed by the identity of their fillings, those instances
    * are tabled, and the steps a cell are 193, 169, 183, 159 and 157 at n = 8,
    * 24, 50, 100 and 200 (6,331,399 steps and 2.2 s at n = 200). At the nominal
    * n = 3000 that is still about 1.4 * 10^9 steps and 9 * 10^6 entries.
    */
  private def instance(
      code: Code,
      fillings: Vector[JitValue],
      arguments: List[JitValue],
      rest: List[Goal],
      state: ReadingState
  ): Next =
    if !configuration.instanceTable then
      untabledInstance(code, fillings, arguments, rest, state)
    else
      val run = JitRunState.of(state, configuration)
      val cost = run.tableCosts.getOrElse(code, TableCost.none)
      val decision =
        if code == JitRules.cellCode then CheckpointDecision.Tabled
        else
          configuration.instanceCheckpoints.decided(
            cost,
            run.stepsSinceCheckpoint(state.budget.spent),
            configuration.instanceTableTrial
          )
      if decision == CheckpointDecision.Untabled then
        untabledInstance(code, fillings, arguments, rest, state)
      else
        val key = TabledInstance(code, fillings)
        val charged = fillings.size
        val lookup = state.budget.spent + charged
        if lookup > state.budget.bound then done(Computed.Stopped(state))
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

  /** The instance under the table with its key, the checkpoint strategy having
    * chosen to look it up (`instance`), each case charged the key's lookup: a
    * complete table's heads, counted as a hit in the code's cost; otherwise,
    * when `recording` (`CheckpointDecision.Tabled`) and outside a fallback
    * point's check, the instance's tabled heads (`instanceTabling`), each as it
    * is found, its reading's steps entered in the code's cost when its table
    * completes, a checkpoint (`JitRunState.lastCheckpointSpent`); and the
    * instance run untabled, with nothing recorded, otherwise
    * (`CheckpointDecision.LookupOnly`, or inside a check). An instance met
    * again within its own reading is answered by its approximation, and its
    * component read again until its reads grow no more (`Tabling`): the table
    * decides an instance whose untabled reading has no end, Omega's among them,
    * where running such a re-entry untabled read it to the budget.
    *
    * A hit is also charged one step for each head it replays, as the untabled
    * machine spends at least a step on each head it reads: a reading's heads
    * are then bounded by its budget. Charged the lookup alone, a hit replayed
    * any number of heads for free, and an instance whose body reads a tabled
    * instance in several branches of a choice multiplied its heads at every
    * nesting. MEASURED 2026-11-03: `InstanceTableClearingLawTest` drew the term
    * `randomLatticeApplication(26, SplitMix(272145737283953041))`, whose
    * reading under the table hit one instance with 2,187 heads at step 102 and
    * with 1,594,323 heads at step 168, three times as many every 11 steps, and
    * ran out of a 512 MB heap within a budget of 2,000 steps; untabled, it
    * spent its 20,000 steps in 20 MB.
    *
    * Inside a fallback point's check (`JitRunState.readingPath` not empty) a
    * miss opens a table as it does outside one, noted as opened in a check
    * (`JitRunState.checkOpened`). A cut there answers `Untyped` because the
    * reading recurred among the readings around it, which another context does
    * not have, so a table whose reading saw a cut holds the check's heads: it
    * is dropped when its component completes
    * (`JitRunState.componentCompleted`), and read again where it is met. A
    * table whose reading saw no cut depends on no reading around it and is
    * kept. Run untabled, every instance below a check was read again by each
    * check above it, a cost that multiplies with the depth of the recursion,
    * since each typed call below has a check of its own. An instance met in a
    * check while its own table is open is still run untabled: the table's
    * approximation would answer the recurrence that the check's cycle detection
    * (`ReadingPath.extended`) cuts, and a value without end,
    * `fixpoint successor`, read under a check, would then grow its open table
    * with no cut to end it. When the reading shares its complete tables
    * (`TableSharing.Shared`) a completed table is kept in the cache service
    * before the state can drop it, so a miss in a check is run untabled there.
    * A complete table is read in a check either way.
    *
    * The state keeps the complete tables as the configuration's
    * `instanceRetention` says: under `InstanceRetention.Generations` the
    * complete tables of `instanceTables` are the young generation, and when it
    * holds `size` of them it becomes the old generation
    * (`JitRunState.olderInstances`); under `NeverDropped` nothing is dropped. A
    * table found in the old generation, or in the cache service when the
    * reading shares its complete tables (`sharedInstances`, the second level),
    * is completed in the young one again and charged as a hit.
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
      case InstanceRetention.Generations(size)
          if tables.complete.size >= size && !tables.complete.contains(key) =>
        run.copy(
          instanceTables = tables.copy(complete = Map.empty),
          olderInstances = tables.complete
        )
      case InstanceRetention.Generations(_) | InstanceRetention.NeverDropped =>
        run
    rolled.instanceTables.complete
      .get(key)
      .orElse(rolled.olderInstances.get(key))
      .orElse(sharedInstances(state).found(key).map(_._1)) match
      case Some(heads) =>
        val replayed = state.budget.spent + heads.ordered.size
        if replayed > state.budget.bound then done(Computed.Stopped(state))
        else
          val young = rolled.instanceTables
          val kept = if young.complete.contains(key) then rolled
          else
            rolled.copy(instanceTables =
              young.copy(complete = young.complete.updated(key, heads))
            )
          val counted = state.copy(
            budget = state.budget.copy(spent = replayed),
            jitState = kept
              .copy(tableCosts =
                run.tableCosts.updated(code, cost.hit(lookupNodes))
              )
              .readNoted(InstanceRead.Table(key))
          )
          tailcall(
            nextHead(
              Goal.Heads(Answers.of(heads.ordered), arguments) :: rest,
              counted
            )
          )
      case None
          if !recording || (run.readingPath != ReadingPath.Empty() &&
            (state.sharing != TableSharing.Local || rolled.instanceTables.open
              .contains(key))) =>
        untabledInstance(code, fillings, arguments, rest, state)
      case None =>
        val noted =
          (if run.readingPath == ReadingPath.Empty() then rolled
           else rolled.checkOpened(key)).readNoted(InstanceRead.Table(key))
        // A table of an earlier version is verified outside a fallback point's check only, where it was verified
        // before misses in a check were tabled: its reads, made under the check's path, could be cut.
        noted.earlierVerifiable
          .get(key)
          .filterNot(_ =>
            run.readingPath != ReadingPath.Empty() || noted.instanceTables.open
              .contains(key) || noted.verifying.contains(key)
          ) match
          case Some(table) =>
            tailcall(
              nextHead(
                Goal.Heads(
                  verifiedOrRead(key, table, lookupNodes),
                  arguments
                ) :: rest,
                state.copy(jitState = noted)
              )
            )
          case None =>
            val missed =
              noted.tableCosts.getOrElse(code, TableCost.none).missOpened
            val opened =
              noted.copy(tableCosts = noted.tableCosts.updated(code, missed))
            tailcall(
              nextHead(
                Goal.Heads(instanceRead(key, lookupNodes), arguments) :: rest,
                state.copy(jitState = opened)
              )
            )

  /** The heads of the instance's table as its reading finds them, under the
    * configuration's lookahead.
    */
  private def instanceRead(key: TabledInstance, lookupNodes: Int): Stream =
    val heads = instanceTabling.answers(key)
    configuration.instanceLookahead match
      case InstanceLookahead.Lazy => entered(heads, key, lookupNodes, 0)
      case InstanceLookahead.WithinSteps(steps) =>
        InstanceLookahead.lookedAhead(
          entered(heads, key, lookupNodes, 0),
          steps
        )

  /** The heads of an instance with a table of an earlier version
    * (`InstanceReuse`): that table's, completed in this version, when each of
    * its reads gives what it gave; otherwise the instance read as a miss. A key
    * the verification's reads completed keeps that table, and one they left
    * open is read through its producer. The reads the check makes are the
    * instance's and not its reader's, whose trace holds the instance alone:
    * noted there, every reader's trace would hold the whole closure of what it
    * depends on.
    */
  private def verifiedOrRead(
      key: TabledInstance,
      table: VerifiableTable,
      lookupNodes: Int
  ): Stream =
    computedStream(run.flatMap(before =>
      val reader = before.instanceTables.innermostKey
      val trace = reader.flatMap(before.openTraces.get)
      verificationOf(key, table).flatMap(held =>
        runModified(_.traceRestored(reader, trace)).flatMap(_ =>
          run.flatMap(current =>
            current.completeAnswers(key) match
              case Some(answers) =>
                Computation.pure(
                  Answers.of[ReadingState, JitHead](answers.ordered)
                )
              case None if held && !current.instanceTables.open.contains(key) =>
                runModified(found =>
                  found
                    .tableVerified(key, table)
                    .copy(tableCosts =
                      found.tableCosts.updated(
                        key.code,
                        found.tableCosts
                          .getOrElse(key.code, TableCost.none)
                          .hit(lookupNodes)
                      )
                    )
                ).map(_ =>
                  Answers.of[ReadingState, JitHead](table.answers.ordered)
                )
              case None =>
                runModified(found =>
                  found.copy(
                    earlierVerifiable = found.earlierVerifiable - key,
                    tableCosts = found.tableCosts.updated(
                      key.code,
                      found.tableCosts
                        .getOrElse(key.code, TableCost.none)
                        .missOpened
                    )
                  )
                ).map(_ => instanceRead(key, lookupNodes))
          )
        )
      )
    ))

  /** Whether the reads of the table still hold, the key marked as being
    * verified meanwhile (`JitRunState.verifying`): an instance met again while
    * it is verified is read as any miss, so that tables of different versions
    * that read each other do not verify each other without end.
    */
  private def verificationOf(
      key: TabledInstance,
      table: VerifiableTable
  ): Computation[ReadingState, Boolean] =
    runModified(found => found.copy(verifying = found.verifying + key)).flatMap(
      _ =>
        readsHold(table.reads.toList).flatMap(held =>
          runModified(found => found.copy(verifying = found.verifying - key))
            .map(_ => held)
        )
    )

  /** Whether each read, in order, still gives what it gave, each charged a
    * step, so that a check is bounded by the reading's budget. The first read
    * that differs ends the check, so every read checked is one the instance's
    * reading would make.
    */
  private def readsHold(
      reads: List[HeldRead]
  ): Computation[ReadingState, Boolean] = reads match
    case Nil           => Computation.pure(true)
    case read :: later =>
      readCharged
        .flatMap(_ =>
          read match
            case HeldRead.Expansion(node, expansion) =>
              Computation
                .state[ReadingState]
                .flatMap(state =>
                  val (now, expansions) =
                    state.expansions.expanded(node, state.specializer)
                  Computation
                    .replaced(state.copy(expansions = expansions))
                    .map(_ => Configured.same(now, expansion))
                )
            case HeldRead.Table(key, answers) => tableHolds(key, answers)
        )
        .flatMap(held =>
          if held then readsHold(later) else Computation.pure(false)
        )

  /** One step of the reading's budget, for a read a verification checks. */
  private val readCharged: Computation[ReadingState, Unit] =
    Computation(state =>
      val spent = state.budget.spent + 1
      if spent > state.budget.bound then done(Computed.Stopped(state))
      else
        done(
          Computed.Done(
            (),
            state.copy(budget = state.budget.copy(spent = spent))
          )
        )
    )

  /** Whether the instance still has the answers: compared with its complete
    * table if it has one; otherwise, when a table of an earlier version holds
    * those answers, by that table's own reads, with no machine run; otherwise
    * read to its end through the table.
    */
  private def tableHolds(
      key: TabledInstance,
      answers: AnswerSet[JitHead]
  ): Computation[ReadingState, Boolean] =
    run.flatMap(current =>
      current.completeAnswers(key) match
        case Some(found) => Computation.pure(found.ordered == answers.ordered)
        case None        =>
          current.earlierVerifiable
            .get(key)
            .filter(table =>
              !current.verifying.contains(key) && !current.instanceTables.open
                .contains(key) && table.answers.ordered == answers.ordered
            ) match
            case Some(table) =>
              verificationOf(key, table).flatMap {
                case true =>
                  runModified(_.tableVerified(key, table)).flatMap(_ =>
                    run.map(
                      _.completeAnswers(key).exists(
                        _.ordered == answers.ordered
                      )
                    )
                  )
                case false =>
                  runModified(found =>
                    found.copy(earlierVerifiable =
                      found.earlierVerifiable - key
                    )
                  ).flatMap(_ => readToItsEnd(key, answers))
              }
            case None => readToItsEnd(key, answers)
    )

  /** Whether the instance, read to its end, has the answers in a complete
    * table: answers found while it depends on a table in progress are an
    * approximation, which proves nothing.
    */
  private def readToItsEnd(
      key: TabledInstance,
      answers: AnswerSet[JitHead]
  ): Computation[ReadingState, Boolean] =
    running(Machine(List(Goal.Tabled(key.code, key.fillings)))).collected
      .flatMap(_ =>
        run.map(_.completeAnswers(key).exists(_.ordered == answers.ordered))
      )

  /** The instance table: the tabled function whose body is an instance's own
    * reading, a machine of its own (`Goal.Untabled`), within which the
    * instances it meets are again looked up in the table (`instance`); its
    * tables are `JitRunState.instanceTables`.
    */
  private val instanceTabling: Tabling[ReadingState, TabledInstance, JitHead] =
    Tabling(
      state => JitRunState.of(state, configuration).instanceTables,
      (state, tables) =>
        state.copy(jitState =
          JitRunState.of(state, configuration).copy(instanceTables = tables)
        ),
      // The complete tables are also kept in the cache service when the reading shares its complete tables; the
      // instances in progress, which the cycle check marks, stay in the state.
      sharedInstances,
      (key, _) => running(Machine(List(Goal.Untabled(key.code, key.fillings)))),
      (state, leader, members) =>
        state.copy(jitState =
          JitRunState
            .of(state, configuration)
            .componentCompleted(leader, members)
        ),
      state =>
        state.copy(jitState =
          JitRunState.of(state, configuration).openReadingsStopped
        )
    )

  /** Where a reading keeps the instance table's complete tables beside the
    * JIT's state, as its `ReadingState.sharing` says: nowhere under `Local`;
    * under `Shared`, the cache service's namespace of this configuration and of
    * the state's extremes, application reading and expansion source, read off
    * the state at each call (`CompletedInstanceNamespace`).
    */
  private def sharedInstances(
      state: ReadingState
  ): CompletedTables[ReadingState, TabledInstance, JitHead] =
    state.sharing match
      case TableSharing.Local => CompletedTables.unshared
      case TableSharing.Shared(cache, retention, source) =>
        SharedCompletedTables(
          cache,
          CompletedInstanceNamespace(
            configuration,
            state.extremes,
            state.applications,
            source,
            retention
          )
        )

  /** The heads of the instance's table as they come, and, when they end with
    * the instance's table complete, the steps their pulls spent entered in the
    * code's cost (`TableCost.entered`), a checkpoint. The steps are counted
    * over the pulls alone: what the caller does with a head between them is no
    * part of the instance's reading.
    */
  private def entered(
      heads: Stream,
      key: TabledInstance,
      lookupNodes: Int,
      steps: Long
  ): Stream =
    Answers(Computation(state =>
      val spentBefore = state.budget.spent
      tailcall(heads.pull.run(state)).map {
        case Computed.Done(Some((head, more)), after) =>
          Computed.Done(
            Some(
              (
                head,
                entered(
                  more,
                  key,
                  lookupNodes,
                  steps + (after.budget.spent - spentBefore)
                )
              )
            ),
            after
          )
        case Computed.Done(None, after) =>
          val run = JitRunState.of(after, configuration)
          if !run.instanceTables.complete.contains(key) then
            Computed.Done(None, after)
          else
            val cost = run.tableCosts.getOrElse(key.code, TableCost.none)
            val spent = steps + (after.budget.spent - spentBefore)
            Computed.Done(
              None,
              after.copy(jitState =
                run.copy(
                  lastCheckpointSpent = after.budget.spent,
                  tableCosts = run.tableCosts
                    .updated(key.code, cost.entered(lookupNodes, spent))
                )
              )
            )
        case Computed.Stopped(stopped) => Computed.Stopped(stopped)
      }
    ))

  /** An instance of the code with the fillings applied to the arguments, by the
    * code's compiled clauses, taken into the state at its first instance
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
    if code == JitRules.cellCode then
      val Vector(shared) = fillings: @unchecked
      tailcall(nextHead(Goal.SharedBody(shared, arguments) :: rest, state))
    else
      run.compiled.get(code) match
        case Some(compiled) =>
          clausesCalled(compiled, fillings, arguments, rest, state)
        // A requested stop (the reading's signal) leaves the code uncompiled: the case below reads it as it is.
        case None
            if run.compiled.size < configuration.budget && !state.budget.stop.stopRequested =>
          val compiled = sharedCode(code, state)
          val after = state.copy(jitState =
            run.copy(
              compiled = run.compiled.updated(code, compiled),
              compilationOrder = run.compilationOrder :+ code
            )
          )
          clausesCalled(compiled, fillings, arguments, rest, after)
        case None =>
          tailcall(
            nextHead(
              Goal.Evaluation(
                CodeReading.instance(code, fillings, parallel),
                arguments
              ) :: rest,
              state
            )
          )

  /** The code's compiled form for a state that holds none: compiled here when
    * the reading keeps its memos in its state alone; otherwise the one the
    * cache service holds under the code and this JIT's configuration
    * (`CompiledCodes`, of the reading's retention), compiled and written there
    * when it holds none. A compiled form is a pure function of the code's
    * syntax under the configuration, so a form found there is the one compiled
    * here, and clearing the service changes only cost.
    */
  private def sharedCode(code: Code, state: ReadingState): CompiledCode =
    state.sharing match
      case TableSharing.Local                       => compiledCode(code)
      case TableSharing.Shared(cache, retention, _) =>
        cache.locked(CompiledCodes(configuration, retention))(
          _.getOrElseUpdate(code, compiledCode(code))
        )

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
    else
      tailcall(
        nextHead(Goal.Clauses(compiled, fillings, 0, arguments) :: rest, state)
      )

  /** The code compiled by the configuration's strategy and backend
    * (code_compiled/2): the emission's slot count is the code's, or the
    * strategy broke its contract and the compilation throws.
    */
  def compiledCode(code: Code): CompiledCode =
    val emission = configuration.strategy.emission(code)
    val slots = CodeReading.slotCount(code)
    if emission.slotCount != slots then
      throw EmissionSlotCount(code, slots, emission.slotCount)
    configuration.backend.compiled(code, emission, parallel)

  /** A head applied to the arguments: the head itself when there is none;
    * otherwise one step, the head applied to the first (jit_applied/3), and the
    * rest applied to its heads.
    */
  private def applied(
      head: JitHead,
      arguments: List[JitValue],
      rest: List[Goal],
      state: ReadingState
  ): Next =
    arguments match
      case Nil => done(Computed.Done(Some((head, Machine(rest))), state))
      // The empty parallel set applied to anything is itself (a least term
      // of ⊑_O applied to anything is one).
      case _ if head == EmptyParallel =>
        done(Computed.Done(Some((head, Machine(rest))), state))
      case argument :: later =>
        state.budget.charged match
          case None          => done(Computed.Stopped(state))
          case Some(charged) =>
            appliedTo(head, argument, later, rest, state.copy(budget = charged))

  private def appliedTo(
      head: JitHead,
      argument: JitValue,
      later: List[JitValue],
      rest: List[Goal],
      state: ReadingState
  ): Next = head match
    case EmptyParallel =>
      done(Computed.Done(Some((EmptyParallel, Machine(rest))), state))
    case gezi.ir.Thunk(code, holes, fillings) =>
      val (filling, sharing) = shared(code, holes.head, argument, state)
      val filled =
        CodeReading.holeFilled(holes.head, holes.tail, fillings, filling)
      if holes.tail.nonEmpty then
        applied(JitHead.Lambda(code, holes.tail, filled), later, rest, sharing)
      else
        val entry = BlockEntry(code, holes.head, fillings, argument)
        val entered = sharing.entered(code)
        if configuration.nativeBlocks.entered(
            entry,
            JitRunState.of(entered, configuration).blockRecord
          )
        then blockEntered(entry, filled, later, rest, entered)
        else instance(code, filled, later, rest, entered)
    case gezi.weakhead.Neutral(variable, neutralArguments) =>
      applied(
        JitHead.Neutral(variable, neutralArguments :+ argument),
        later,
        rest,
        state
      )
    case ParallelHead(left, right) =>
      tailcall(
        nextHead(
          Goal.Evaluation(
            parallel(
              JitValue.Apply(left, argument),
              JitValue.Apply(right, argument)
            ),
            later
          ) :: rest,
          state
        )
      )
    case represented: RepresentedStorage[?] =>
      val storage = StorageOf.ofHead[C](represented)
      val representation = storage.representation
      val value = StorageOf.nativeValue(storage)
      if facts.shapeChecked(representation.familyIdentity) then
        eliminationExtended(
          representation,
          value,
          Vector.empty,
          argument,
          later,
          rest,
          state
        )
      else
        tailcall(
          nextHead(
            Goal.Heads(
              eliminationEncoded(representation, value, Vector(argument)),
              later
            ) :: rest,
            state
          )
        )
    case gezi.jit.Elimination(representation, value, cases) =>
      eliminationExtended(
        representation,
        value,
        cases,
        argument,
        later,
        rest,
        state
      )
    case gezi.jit.NativeApplication(
          instruction,
          native,
          missing,
          nativeArguments
        ) =>
      val extended = nativeArguments :+ argument
      if missing - 1 > 0 then
        applied(
          JitHead.NativeApplication(instruction, native, missing - 1, extended),
          later,
          rest,
          state
        )
      else
        tailcall(
          nextHead(
            Goal.Heads(
              nativeAppliedHeads(instruction, native, extended),
              later
            ) :: rest,
            state
          )
        )

  /** The argument as it fills the hole of the code, and the state: under
    * `instanceTable`, when the hole's slot is one the code may read more than
    * once (`Code.slotsReadMoreThanOnce`) and reading the argument may cost more
    * than one layer, the argument is shared. A closed canonical term (an
    * instruction) fills the slot as itself and is added to the state's
    * `SharedTerms`, so that every evaluation of it reads the instance
    * `TabledInstance(cellCode, [term])`; wrapping it would give the same term a
    * second spelling. Any other argument, which holds a neutral value or a
    * value of the JIT's own and so can make no storage, fills the slot as the
    * IR thunk of `JitRules.cellCode` with the argument as its one filling, a
    * cell. Either way the instance is always tabled (`instance` skips its
    * `TableCost`), so the slot's reads after the first take its heads from the
    * table: the value is shared as call by need shares it, whatever the costs
    * counted on the codes the argument's reading runs. Its purpose (the defect
    * of 2026-11-02): a code judged unprofitable in a hot loop, and so no longer
    * tabled, took the sharing away from a later loop over the same code that
    * read each value twice, which then took steps exponential in its length;
    * the law test `TableSharingLawTest` reproduces it. Which slots are read
    * twice is syntax, a count of occurrences, and no type.
    *
    * MEASURED (2026-11-02, a scratch probe of `TableSharingLawTest`'s programs,
    * the trial 4, after a hot loop of 64 calls of `iterate` and of the function
    * that reads its argument twice): without cells, the steps at k = 8, 12 and
    * 16 were 11,510, 184,310 and 2,949,110, those of the JIT with no table,
    * against 1,221, 2,005 and 2,949 from an empty table.
    */
  private def shared(
      code: Code,
      hole: Hole,
      argument: JitValue,
      state: ReadingState
  ): (JitValue, ReadingState) = hole match
    case Hole.Bound(slot)
        if configuration.instanceTable && Code
          .slotsReadMoreThanOnce(code)
          .contains(slot) && readingCosts(argument) =>
      // A closed value, a term or one holding a suspension, is shared by the table key `TabledInstance(cellCode, [v])`;
      // only an open one, which holds a neutral value, is shared by a cell around it.
      Value.open(argument) match
        case None =>
          val run = JitRunState.of(state, configuration)
          (
            argument,
            state.copy(jitState =
              run.copy(sharedTerms =
                run.sharedTerms.added(argument, configuration.instanceRetention)
              )
            )
          )
        case Some(open) => (SharingCell(open), state)
    case _ => (argument, state)

  /** Whether reading the value to its heads may cost more than one layer: not
    * for a value that is its own head (represented, neutral) or a group of such
    * (its members are its heads), a lambda, a sharing cell (`SharingCell`), or
    * an opaque instruction; for a suspension (a code whose holes are all
    * filled), an application, a choice and a parallel.
    */
  private def readingCosts(value: JitValue): Boolean = value match
    case JitValue.Represented(_, _) | JitValue.Grouped(_) |
        JitValue.Neutral(_, _) =>
      false
    case SharingCell(_)                                     => false
    case JitValue.IrTerm(instruction) if instruction.opaque => false
    case JitValue.Thunk(_, _, _)                            => false
    case gezi.weakhead.SuspensionValue(_, _)                => true
    case JitValue.Apply(_, _) | JitValue.Choice(_) | JitValue.Parallel(_, _) =>
      true
    case _ => false

  /** The instance at the entry, its last hole filled, run as a native block of
    * the configuration's mechanism (`NativeBlockMechanism`): the fillings that
    * may be the self filling read to their heads first, each within
    * `JitRules.selfReadingSteps` steps (`selfFound`); the block run with the
    * artifact kept for the code (`JitRunState.blockArtifacts`); its outcome
    * recorded (`JitRunState.blockRecord`, costs, never a type) and the artifact
    * it returns kept; the block's value then taken as the instance's head or
    * evaluated by the machine, its steps and native calls counted. A block that
    * falls back leaves the instance to the machine from its entry.
    */
  private def blockEntered(
      entry: BlockEntry,
      filled: Vector[JitValue],
      later: List[JitValue],
      rest: List[Goal],
      state: ReadingState
  ): Next =
    val candidates = entry.fillings.toList.filter {
      case JitValue.IrTerm(_) | JitValue.Represented(_, _) => false
      case _                                               => true
    }
    tailcall(selfFound(candidates, state)).flatMap { (self, afterSelf) =>
      val budget = afterSelf.budget
      val run = JitRunState.of(afterSelf, configuration)
      val result = configuration.nativeBlocks.run(
        this,
        entry,
        self,
        run.blockArtifacts.get(entry.code),
        budget.bound - budget.spent,
        budget.spent,
        budget.stop
      )
      val recorded = run.copy(
        blockRecord = run.blockRecord.recorded(entry.code, result.outcome),
        blockArtifacts = result.artifact.fold(run.blockArtifacts)(
          run.blockArtifacts.updated(entry.code, _)
        )
      )
      result.outcome match
        case BlockOutcome.FellBack(_) =>
          instance(
            entry.code,
            filled,
            later,
            rest,
            afterSelf.copy(jitState = recorded)
          )
        case BlockOutcome.Finished(value, costs) =>
          val counts =
            costs.callsByNative.foldLeft(recorded.counts)((current, call) =>
              current.copy(
                nativeCalls = current.nativeCalls + call._2,
                callsByNative = current.callsByNative
                  .updated(call._1, current.callsOf(call._1) + call._2)
              )
            )
          val counted = afterSelf.copy(
            budget = budget.copy(spent = budget.spent + costs.steps),
            jitState = recorded.copy(counts = counts)
          )
          value match
            case JitValue.Stored(storage) =>
              applied(storage, later, rest, counted)
            case other =>
              tailcall(nextHead(Goal.Evaluation(other, later) :: rest, counted))
    }

  /** The first of the fillings whose only head, read within
    * `JitRules.selfReadingSteps` steps, is a lambda that holds the filling
    * itself among its fillings, spelled alike (the recursion of a fixed point
    * combinator: reading the self gives a lambda over the self), with that
    * head; and the state after the reads. A read that stops at that bound reads
    * no head, and the reading's own limit is kept.
    */
  private def selfFound(
      pending: List[JitValue],
      state: ReadingState
  ): Trampoline[(Option[SelfFilling], ReadingState)] =
    pending match
      case Nil                 => done((None, state))
      case candidate :: others =>
        // The candidate's first two heads within the bound: the self filling when it reads one lambda head that holds
        // the candidate itself; a read stopped at the bound keeps the state it stopped in, as a stopped one does.
        val firstTwo = heads(candidate).pull.flatMap {
          case Some(
                (JitHead.Lambda(foundCode, foundHoles, foundFillings), more)
              ) if foundFillings.exists(JitRules.spelledAlike(_, candidate)) =>
            more.pull.map(next =>
              Option.when(next.isEmpty)(
                SelfFilling(candidate, foundCode, foundHoles, foundFillings)
              )
            )
          case _ => Computation.pure(None)
        }
        tailcall(
          ReadingState
            .attempted(firstTwo, JitRules.selfReadingSteps, speculative = true)
            .run(state)
        ).flatMap {
          case Computed.Done(Attempt.Finished(Some(found)), after) =>
            done((Some(found), after))
          case Computed.Done(Attempt.Finished(None), after) =>
            tailcall(selfFound(others, after))
          case Computed.Done(Attempt.OutOfSteps(stopped), _) =>
            tailcall(selfFound(others, stopped))
          case Computed.Stopped(after) => tailcall(selfFound(others, after))
        }

  /** The represented value applied to the cases and then to the argument
    * (elimination_extended/5): an elimination head while the codec's count of
    * cases is not reached; then the chosen case's heads applied to its fields.
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
    if count - extended.size > 0 then
      applied(
        JitHead.Elimination(representation, value, extended),
        later,
        rest,
        state
      )
    else
      tailcall(
        nextHead(
          Goal.Evaluation(extended(branch - 1), fields.toList ++ later) :: rest,
          state
        )
      )

  /** The codec's reading of the value as the branch-th of its count of cases,
    * over the run-time values of the fields (codec_branch/5).
    */
  def codecBranch(
      representation: Representation,
      value: NativeValue
  ): (Int, Int, Vector[JitValue]) =
    (representation, value) match
      case (Representation.Data(familyIdentity, parameter), _) =>
        val family = dataFamily(familyIdentity)
        val DataLayer(constructor, fields) = family.layer(parameter, value)
        (
          family.constructors(parameter).size,
          constructor + 1,
          fieldValues(family, parameter, constructor, fields)
        )
      case (Representation.ListOf(element), NativeValue.Listed(list)) =>
        val (count, branch, fields) = ListCodec.eliminatedBranch(element, list)
        (count, branch, fields.map(fieldValue))
      case (Representation.ArrayListOf(_), listed: NativeValue.ArrayListed) =>
        if listed.nil then (2, 1, Vector.empty)
        else (2, 2, arrayListFields(representation, listed))
      case _ =>
        throw IllegalStateException(
          s"a value of another representation than ${representation.familyIdentity.shown}"
        )

  /** The fields of an array list's cell: the storage of its first element and
    * the storage of the suffix after it, the same elements one on.
    */
  private def arrayListFields(
      representation: Representation,
      listed: NativeValue.ArrayListed
  ): Vector[JitValue] =
    val encoding = operations
    representation match
      case Representation.ArrayListOf(element) =>
        Vector(
          encoding.storageOf(
            element,
            encoding.arrayElement(element, listed.elements.values(listed.start))
          ),
          encoding.storageOf(
            representation,
            NativeValue.ArrayListed(listed.elements, listed.start + 1)
          )
        )
      case other =>
        throw IllegalStateException(s"an array list's cell under $other")

  /** The data family of the identity, which a representation of the JIT names
    * only when the backend has it.
    */
  private def dataFamily(identity: FamilyIdentity): DataFamily =
    nativeBackend
      .family(identity)
      .getOrElse(
        throw IllegalStateException(
          s"no data family ${identity.shown} in the backend"
        )
      )

  /** The run-time values of a layer's fields at the parameter, each represented
    * in its field's family at its field's parameter.
    */
  private def fieldValues(
      family: DataFamily,
      parameter: Option[FamilyParameter],
      constructor: Int,
      fields: Vector[NativeValue]
  ): Vector[JitValue] =
    family
      .constructors(parameter)(constructor)
      .fields
      .zip(fields)
      .map((field, value) =>
        JitValues.fieldTerm(operations, field.representation(parameter), value)
      )

  /** The run-time value of a field a list hands out. */
  private def fieldValue(field: ListElementField[JitValue]): JitValue =
    field match
      case ListElementField.Filtered(item, element) => parallel(item, element)
      case ListElementField.Node(node)              => node

  // ---- reading terms by their layers ----

  /** The value read one layer (term_layer/2). Every value is its own layer;
    * reading a value that is an instruction (the program's syntax, or a value
    * the JIT built that equals an instruction, one object in the pool) is one
    * read of syntax (`JitCounts.syntaxReads`), and any other value is read
    * without one. An opaque instruction has no layer.
    */
  private def layer(value: JitValue): SyntaxRead[JitValue] = value match
    case JitValue.IrTerm(instruction) =>
      if instruction.opaque then
        throw IllegalStateException(s"the $instruction has no layer")
      SyntaxRead(value, 1)
    case other => SyntaxRead.pure(other)

  /** The value's layer when it has one, read through a sharing cell
    * (`SharingCell`): a represented value has none.
    */
  private def layerOf(value: JitValue): SyntaxRead[Option[JitValue]] =
    value match
      case JitValue.Represented(_, _) => SyntaxRead.pure(None)
      case SharingCell(inner)         => layerOf(inner)
      case other                      => layer(other).map(Some(_))

  /** The representation whose decoding criterion the term is
    * (jit_decoding_criterion/2): the instruction of a define that names a data
    * family of the backend that takes no parameter
    * (`BackendFacts.criterionFamily`: a declared family's criterion, or a
    * define whose first `native_specialization` names a codec); the application
    * of a define that names a family taking a criterion parameter to as many
    * criteria; the application of a define whose first `native_specialization`
    * names a family that takes one, F, to a term P that decodes by its syntax
    * in the parameter's family, the representation of F at that value; or the
    * application of a define with `native_specialization(list)` to an element
    * filter E, the representation list(E). The reads of syntax are not counted:
    * the refinement asks it while it compiles, outside a reading.
    */
  def decodingCriterion(criterion: JitValue): Option[Representation] =
    decodingCriterionRead(criterion)(using KnownCriteria.none).result

  /** `decodingCriterion`, with its reads of syntax: an instruction's criterion
    * is taken from the criteria the reading already read, and otherwise read
    * and returned as learned (`KnownCriteria`).
    */
  private def decodingCriterionRead(criterion: JitValue)(using
      known: KnownCriteria
  ): SyntaxRead[Option[Representation]] =
    criterion match
      case JitValue.IrTerm(instruction) =>
        known.byInstruction.get(instruction) match
          case Some(found) => SyntaxRead.pure(found)
          case None        =>
            val read = criterionRead(criterion)
            read.copy(learned = read.learned.updated(instruction, read.result))
      case _ => criterionRead(criterion)

  /** The representation whose decoding criterion the term is, read from its
    * syntax (`decodingCriterion`).
    */
  private def criterionRead(criterion: JitValue)(using
      KnownCriteria
  ): SyntaxRead[Option[Representation]] =
    criterion match
      case JitValue.IrTerm(instruction)
          if operations.criterionFamily.contains(Value.of(instruction)) =>
        SyntaxRead.pure(
          nativeBackend
            .family(operations.criterionFamily(Value.of(instruction)))
            .filter(family =>
              family.parameterFamily.isEmpty && family.criterionArity == 0
            )
            .map(family => Representation.Data(family.identity, None))
        )
      case _ =>
        criterionSpine(criterion, Vector.empty).flatMap {
          case Some((function, arguments)) =>
            criterionFamily(function, arguments.size) match
              case Some(family) =>
                arguments
                  .foldLeft(
                    SyntaxRead.pure(Option(Vector.empty[Representation]))
                  )((found, argument) =>
                    // A criterion parameter that names no family filters the
                    // fields it stands for (`FilteredFamily`); at the top of a
                    // term such a criterion is no decode point.
                    SyntaxRead.chained(found)(sofar =>
                      decodingCriterionRead(argument).map(read =>
                        Some(
                          sofar :+ read.getOrElse(FilteredFamily.of(argument))
                        )
                      )
                    )
                  )
                  .map(
                    _.map(criteria =>
                      Representation.Data(
                        family.identity,
                        Some(CriterionParameters(criteria))
                      )
                    )
                  )
              case None => valueParameterCriterionRead(criterion)
          case None => valueParameterCriterionRead(criterion)
        }

  /** The family of criterion parameters whose criterion is the instruction,
    * applied to as many criteria as the family takes (`criterionArity`), at
    * least one.
    */
  private def criterionFamily(
      function: Term,
      arguments: Int
  ): Option[DataFamily] =
    operations.criterionFamily
      .get(Value.of(function))
      .flatMap(nativeBackend.family)
      .filter(family => arguments > 0 && family.criterionArity == arguments)

  /** The term as an instruction that names a family
    * (`BackendFacts.criterionFamily`) applied to arguments, read along its
    * spine of applications, through the layers of the instructions and thunks
    * it meets: a filter writes a family's criterion applied to its parameters,
    * `C @ P1 @ … @ Pk`, and the parameters are read from it as written, never
    * from a value.
    */
  private def criterionSpine(
      term: JitValue,
      arguments: Vector[JitValue]
  ): SyntaxRead[Option[(Term, Vector[JitValue])]] =
    term match
      case JitValue.IrTerm(instruction)
          if operations.criterionFamily.contains(Value.of(instruction)) =>
        SyntaxRead.pure(Some((instruction, arguments)))
      case JitValue.Apply(function, argument) =>
        criterionSpine(function, argument +: arguments)
      case _ =>
        layerOf(term).flatMap {
          case Some(JitValue.Apply(function, argument)) =>
            criterionSpine(function, argument +: arguments)
          case _ => SyntaxRead.pure(None)
        }

  /** The representation whose decoding criterion the term is, a list's or a
    * family's at a value parameter (`decodingCriterion`).
    */
  private def valueParameterCriterionRead(
      criterion: JitValue
  )(using KnownCriteria): SyntaxRead[Option[Representation]] =
    layerOf(criterion).flatMap {
      case Some(JitValue.Apply(JitValue.IrTerm(function), element))
          if operations.criterionFamily
            .get(Value.of(function))
            .contains(Representation.listFamily) =>
        SyntaxRead.pure(Some(Representation.ListOf(element)))
      // An array list's criterion `array_list E`, E read as the criterion of
      // a scalar representation the encoding makes array lists of.
      case Some(JitValue.Apply(JitValue.IrTerm(function), element))
          if operations.criterionFamily
            .get(Value.of(function))
            .contains(Representation.arrayListFamily) =>
        decodingCriterionRead(element).map(
          _.map(Representation.ArrayListOf(_)).filter(operations.converts)
        )
      case Some(JitValue.Apply(JitValue.IrTerm(function), parameterTerm)) =>
        operations.criterionFamily
          .get(Value.of(function))
          .flatMap(nativeBackend.family) match
          case Some(family) =>
            family.parameterFamily match
              case Some(parameterFamily) =>
                syntaxDecoded(parameterFamily, None, parameterTerm).map(
                  _.map(value =>
                    Representation.Data(
                      family.identity,
                      Some(family.parameterOf(value))
                    )
                  )
                )
              case None => SyntaxRead.pure(None)
          case None => SyntaxRead.pure(None)
      case _ => SyntaxRead.pure(None)
    }

  /** The value of the family at the parameter that the term spells by its
    * syntax alone, read layer by layer: an application, along its spine, of the
    * define bound to one of the family's constructors at the parameter to as
    * many arguments as the constructor has fields, each argument the spelling
    * of a value of its field's family at its field's parameter; `None` for any
    * other term. A term that is a fallback point `x + (x ∥ T')`
    * (`fallbackPoint`), as the refinement writes at every level of a literal,
    * is read through to its operand x, decoded at the same family and
    * parameter: the choice equals x whatever T' names, by equation (6) of the
    * formal definition, M + (M ∥ N) = M, so T' need not name the field's
    * representation. It evaluates nothing: a parameter is read from the
    * decoding criterion the term carries (`x ∥ word_type W`, W a numeral
    * written out), never from a value.
    */
  private def syntaxDecoded(
      familyIdentity: FamilyIdentity,
      parameter: Option[FamilyParameter],
      term: JitValue
  )(using KnownCriteria): SyntaxRead[Option[NativeValue]] =
    nativeBackend.family(familyIdentity) match
      case None         => SyntaxRead.pure(None)
      case Some(family) =>
        val constructors = family.constructors(parameter)
        val defines = constructors.map(constructor =>
          operations.boundDefine(constructor.native)
        )
        spineRead(term, Vector.empty).flatMap {
          case Some((JitValue.IrTerm(head), arguments)) =>
            defines.indexOf(Some(head)) match
              case -1 => SyntaxRead.pure(None)
              case index
                  if constructorExcluded(
                    familyIdentity,
                    parameter,
                    index
                  ) || constructors(index).fields.size != arguments.size =>
                SyntaxRead.pure(None)
              case index =>
                constructors(index).fields
                  .zip(arguments)
                  .foldLeft(
                    SyntaxRead.pure(Option(Vector.empty[NativeValue]))
                  ) { case (decoded, (field, argument)) =>
                    SyntaxRead.chained(decoded)(values =>
                      field.representation(parameter) match
                        case Representation.Data(fieldFamily, fieldParameter) =>
                          syntaxDecoded(fieldFamily, fieldParameter, argument)
                            .map(_.map(values :+ _))
                        case Representation.ListOf(_) |
                            Representation.ArrayListOf(_) =>
                          SyntaxRead.pure(None)
                    )
                  }
                  .map(
                    _.map(fields =>
                      family.built(parameter, DataLayer(index, fields))
                    )
                  )
          case Some(_) => SyntaxRead.pure(None)
          case None    =>
            SyntaxRead.chained(fallbackPoint(term)) { case (operand, _) =>
              syntaxDecoded(familyIdentity, parameter, operand)
            }
        }

  /** The head and the arguments of the term's spine of applications, read layer
    * by layer until an instruction that is the define bound to a native, or a
    * layer that is no application; `None` when the head is not an instruction.
    */
  private def spineRead(
      term: JitValue,
      arguments: Vector[JitValue]
  ): SyntaxRead[Option[(JitValue, Vector[JitValue])]] =
    term match
      case JitValue.IrTerm(instruction)
          if operations.isBoundToNative(Value.of(instruction)) =>
        SyntaxRead.pure(Some((term, arguments)))
      case JitValue.Apply(function, argument) =>
        spineRead(function, argument +: arguments)
      case _ =>
        layerOf(term).flatMap {
          case Some(JitValue.Apply(function, argument)) =>
            spineRead(function, argument +: arguments)
          case _ => SyntaxRead.pure(None)
        }

  /** The criterion the value reaches by slot steps (criterion_reached/2):
    * itself when it is a decoding criterion, or the instance of a thunk of one
    * hole whose code is a slot, applied to an argument, when that reaches one.
    */
  private def criterionReached(
      term: JitValue
  )(using KnownCriteria): SyntaxRead[Option[JitValue]] =
    decodingCriterionRead(term).flatMap(criterion =>
      if criterion.isDefined then SyntaxRead.pure(Some(term))
      else
        SyntaxRead.chained(
          SyntaxRead.chained(layerOf(term))(lastHoleStep(slotSteps = true, _))
        )(
          criterionReached(_)
        )
    )

  /** The representation of the decode point whose criterion side the value is,
    * if it is one.
    */
  private def decodingRepresentation(
      criterionSide: JitValue
  )(using KnownCriteria): SyntaxRead[Option[Representation]] =
    SyntaxRead.chained(criterionReached(criterionSide))(
      decodingCriterionRead(_)
    )

  /** The β step's instance when the layer applies a thunk to the last of its
    * holes and the thunk's code is a slot, or with `slotSteps` false also a
    * parallel (last_hole_step/3).
    */
  private def lastHoleStep(
      slotSteps: Boolean,
      layer: JitValue
  ): SyntaxRead[Option[JitValue]] =
    layer match
      case JitValue.Apply(function, argument) =>
        lastHoleThunk(function).map(_.flatMap {
          case (code, Vector(hole), fillings) =>
            val admitted = code.layer match
              case Slot(_)        => true
              case Parallel(_, _) => !slotSteps
              case _              => false
            if admitted then
              Some(
                CodeReading.instance(
                  code,
                  CodeReading
                    .holeFilled(hole, Vector.empty, fillings, argument),
                  parallel
                )
              )
            else None
          case _ => None
        })
      case _ => SyntaxRead.pure(None)

  /** The value is a thunk with holes, or one applied to fewer arguments than
    * its holes, and the thunk with those arguments filled in
    * (last_hole_thunk/2).
    */
  private def lastHoleThunk(
      value: JitValue
  ): SyntaxRead[Option[(Code, Vector[Hole], Vector[JitValue])]] =
    layerOf(value).flatMap {
      case Some(JitValue.Thunk(code, holes, fillings)) if holes.nonEmpty =>
        SyntaxRead.pure(Some((code, holes, fillings)))
      case Some(JitValue.Apply(inner, argument)) =>
        lastHoleThunk(inner).map(_.flatMap { (code, holes, fillings) =>
          if holes.size >= 2 then
            Some(
              (
                code,
                holes.tail,
                CodeReading
                  .holeFilled(holes.head, holes.tail, fillings, argument)
              )
            )
          else None
        })
      case _ => SyntaxRead.pure(None)
    }

  /** The members are a fallback point's (fallback_members/3): an operand and
    * its parallel, compared by spelling (every value interned, one spelling is
    * one object, compared by reference), whose criterion reaches a decoding
    * criterion; the operand and the representation.
    */
  private def fallbackMembers(members: Vector[JitValue])(using
      KnownCriteria
  ): SyntaxRead[Option[(JitValue, Representation)]] =
    members match
      // `x + (x ∥ T)` with `x ∥ T` in the unique spelling of a storage, which is how the specialized spelling writes it:
      // the storage is the typed path's value, read in its own representation (its view, one layer, is `x ∥ T`).
      case Vector(operand, stored @ JitValue.Stored(storage))
          if fallbackOverStorage(operand, storage) =>
        SyntaxRead.pure(Some((stored, storage.representation)))
      case Vector(operand, filtered) =>
        layerOf(filtered).flatMap {
          case Some(JitValue.Parallel(filteredOperand, criterion))
              if Value.same(filteredOperand, operand) =>
            decodingRepresentation(criterion).map(_.map((operand, _)))
          case _ => SyntaxRead.pure(None)
        }
      case _ => SyntaxRead.pure(None)

  /** Whether the argument is valued as a storage with no reading: a storage, or
    * a fallback point `x + S` whose typed side is the storage S of `x ∥ T`
    * (`fallbackMembers`), so that a constructor's native makes its storage of
    * storages only, its fields in the unique spelling.
    */
  private def storageValued(argument: JitValue): Boolean = argument match
    case JitValue.Stored(_)                                         => true
    case JitValue.Choice(Vector(operand, JitValue.Stored(storage))) =>
      fallbackOverStorage(operand, storage)
    case _ => false

  /** Whether `operand + S` is a fallback point whose typed side is the storage
    * S: S is `operand ∥ T` in the unique spelling (its view's value is the
    * operand), or the operand is S itself, `S + (S ∥ T)` with `S ∥ T` written S
    * (`StorageEncoding.filteredAlready`).
    */
  private def fallbackOverStorage(
      operand: JitValue,
      storage: RepresentedStorage[JitValue]
  ): Boolean =
    Value.same(operand, StorageOf.value(storage)) || Value.same(
      storageViewValue(storage),
      operand
    )

  /** The value of the storage's one-layer view, `x` of `x ∥ T`, read by this
    * configuration's specializer.
    */
  private def storageViewValue(
      storage: RepresentedStorage[JitValue]
  ): JitValue =
    given gezi.ir.StorageAccess = configuration.storageAccess
    Value.of(configuration.specializer.viewOf(storage).value)

  /** The value, read as written, is a fallback point (fallback_point/3). */
  private def fallbackPoint(term: JitValue)(using
      KnownCriteria
  ): SyntaxRead[Option[(JitValue, Representation)]] =
    term match
      case JitValue.IrTerm(instruction)
          if operations.bound(Value.of(instruction)) =>
        SyntaxRead.pure(None)
      case _ =>
        layerOf(term).flatMap {
          case Some(JitValue.Choice(members)) => fallbackMembers(members)
          case _                              => SyntaxRead.pure(None)
        }

  /** The value is a decode point, or reaches one by slot steps and parallel
    * steps (decode_point_reached/3): its operand and representation.
    */
  private def decodePointReached(
      value: JitValue
  )(using KnownCriteria): SyntaxRead[Option[(JitValue, Representation)]] =
    SyntaxRead.chained(layerOf(value)) {
      case JitValue.Parallel(operand, criterion) =>
        decodingRepresentation(criterion).map(_.map((operand, _)))
      case other =>
        SyntaxRead.chained(lastHoleStep(slotSteps = false, other))(
          decodePointReached(_)
        )
    }

  /** The representation the value is ready in for a native (native_ready/2 read
    * for its representation): a represented value's, a decode point's or a
    * fallback point's.
    */
  private def readyRepresentation(value: JitValue)(using
      KnownCriteria
  ): SyntaxRead[Option[Representation]] =
    Value.closed(value).flatMap(StorageOf.group[C]) match
      case Some(group) => SyntaxRead.pure(Some(group.representation))
      case None        => representationReady(value)

  private def representationReady(value: JitValue)(using
      KnownCriteria
  ): SyntaxRead[Option[Representation]] =
    value match
      case JitValue.Represented(found, _) => SyntaxRead.pure(Some(found))
      case term                           =>
        decodePointReached(term).flatMap {
          case Some((_, representation)) =>
            SyntaxRead.pure(Some(representation))
          case None => fallbackPoint(term).map(_.map(_._2))
        }

  /** The value is ready in the place (native_ready/2). */
  private def nativeReady(value: JitValue, place: Place)(using
      KnownCriteria
  ): SyntaxRead[Boolean] = place match
    case Place.In(representation) =>
      readyRepresentation(value).map(_.contains(representation))
    case Place.ItemOf(element) =>
      decodingCriterionRead(element).flatMap {
        case Some(representation) =>
          nativeReady(value, Place.In(representation))
        case None => SyntaxRead.pure(false)
      }
    case Place.TailOf(element) =>
      nativeReady(value, Place.In(Representation.ListOf(element)))

  /** The places of the native's parameters when its result is in the
    * representation, if it can be (representation_matched/2). A result at the
    * call's parameter (`NativePlace.Parameter`) takes the parameter of the
    * representation, which a decoding criterion written in the term named,
    * where the native admits it (`Native.parameterAdmitted`).
    */
  private def placesFor(
      native: NativeName,
      representation: Representation
  ): Option[Vector[Place]] =
    val representations = nativeBackend.natives(native)
    val bound: Option[(Option[JitValue], Option[FamilyParameter])] =
      (representations.result, representation) match
        case (NativePlace.Fixed(found), _) if found == representation =>
          Some((None, None))
        case (NativePlace.AnyList, Representation.ListOf(found)) =>
          Some((Some(found), None))
        case (
              NativePlace.Parameter(family),
              Representation.Data(found, parameter)
            )
            if found == family && representations.parameterAdmitted(
              parameter
            ) =>
          Some((None, parameter))
        case _ => None
    bound
      .filterNot(_ => representations.takesNaturalList)
      .map((element, parameter) =>
        representations.parameters.map(place(_, element, parameter))
      )

  /** The place of a native's parameter under the call's list element filter and
    * family parameter.
    */
  private def place(
      native: NativePlace,
      element: Option[JitValue],
      parameter: Option[FamilyParameter]
  ): Place =
    (native, element) match
      case (NativePlace.Fixed(representation), _) => Place.In(representation)
      case (NativePlace.Parameter(family), _)     =>
        Place.In(Representation.Data(family, parameter))
      case (NativePlace.OfParameter(of), _)   => Place.In(of(parameter))
      case (NativePlace.AnyList, Some(found)) =>
        Place.In(Representation.ListOf(found))
      case (NativePlace.Item, Some(found)) => Place.ItemOf(found)
      case (NativePlace.Tail, Some(found)) => Place.TailOf(found)
      case _                               =>
        throw IllegalStateException(
          s"a list's place with no element filter: $native"
        )

  /** The spine of applications read through the layers (spine_listed/4): its
    * head and the arguments in order; a native's instruction and a represented
    * value are heads.
    */
  private def spineListed(
      value: JitValue
  ): SyntaxRead[(JitValue, Vector[JitValue])] =
    @scala.annotation.tailrec
    def listed(
        current: JitValue,
        arguments: List[JitValue],
        reads: Long
    ): SyntaxRead[(JitValue, Vector[JitValue])] =
      current match
        case term @ JitValue.Represented(_, _) =>
          SyntaxRead((term, arguments.toVector), reads)
        case term @ JitValue.IrTerm(instruction)
            if operations.bound(Value.of(instruction)) =>
          SyntaxRead((term, arguments.toVector), reads)
        case term =>
          val found = layerOf(term)
          found.result match
            case Some(JitValue.Apply(function, argument)) =>
              listed(function, argument :: arguments, reads + found.reads)
            case _ =>
              SyntaxRead((term, arguments.toVector), reads + found.reads)
    listed(value, Nil, 0)

  /** The natives bound to the spine's head, in the index's order. */
  private def headNatives(head: JitValue): Vector[BoundNative] = head match
    case JitValue.IrTerm(instruction) =>
      operations.natives.getOrElse(Value.of(instruction), Vector.empty)
    case _ => Vector.empty

  /** The value is a type-filtered constructor of the representation, whose
    * native has the count of parameters (filtered_constructor_parameters/3).
    */
  private def filteredConstructorParameters(
      value: JitValue,
      representation: Representation
  )(using KnownCriteria): SyntaxRead[Option[Int]] =
    filteredCount(value, representation).result

  /** The count of `filteredConstructorParameters`, trampolined: a chain of
    * type-filtered constructors, a list of a thousand conses among them, is
    * read down its arguments on the heap.
    */
  private def filteredCount(value: JitValue, representation: Representation)(
      using KnownCriteria
  ): Trampoline[SyntaxRead[Option[Int]]] =
    value match
      case JitValue.Represented(_, _) => done(SyntaxRead.pure(None))
      case term                       =>
        val spine = spineListed(term)
        val (head, arguments) = spine.result
        def first(
            natives: List[BoundNative],
            sofar: SyntaxRead[Unit]
        ): Trampoline[SyntaxRead[Option[Int]]] = natives match
          case Nil            => done(SyntaxRead.pure(None).joined(sofar))
          case native :: rest =>
            placesFor(native.name, representation) match
              case Some(places) if native.parameterCount == arguments.size =>
                tailcall(filteredArguments(arguments.zip(places).toList))
                  .flatMap(filtered =>
                    if filtered.result then
                      done(
                        SyntaxRead
                          .pure(Some(native.parameterCount))
                          .joined(sofar)
                          .joined(filtered)
                      )
                    else first(rest, sofar.joined(filtered))
                  )
              case _ => tailcall(first(rest, sofar))
        first(headNatives(head).toList, spine.map(_ => ()))

  private def filteredArguments(pairs: List[(JitValue, Place)])(using
      KnownCriteria
  ): Trampoline[SyntaxRead[Boolean]] = pairs match
    case Nil                       => done(SyntaxRead.pure(true))
    case (argument, place) :: rest =>
      val ready = nativeReady(argument, place)
      if ready.result then
        tailcall(filteredArguments(rest)).map(_.joined(ready))
      else
        val constructed = place match
          case Place.TailOf(element)    => Some(Representation.ListOf(element))
          case Place.In(representation) => Some(representation)
          case Place.ItemOf(_)          => None
        constructed match
          case None        => done(ready)
          case Some(found) =>
            tailcall(filteredCount(argument, found)).flatMap(count =>
              if count.result.exists(_ > 0) then
                filteredArguments(rest).map(_.joined(ready).joined(count))
              else done(SyntaxRead.pure(false).joined(ready).joined(count))
            )

  private def filteredConstructor(
      value: JitValue,
      representation: Representation
  )(using KnownCriteria): SyntaxRead[Boolean] =
    filteredConstructorParameters(value, representation).map(_.isDefined)

  // ---- state ----

  /** The state with the reads of syntax counted (`JitCounts.syntaxReads`) and
    * the criteria they learned kept (`JitRunState.criteria`).
    */
  private def syntaxCounted(
      state: ReadingState,
      read: SyntaxRead[Any]
  ): ReadingState =
    if read.reads == 0 && read.learned.isEmpty then state
    else
      val current = JitRunState.of(state, configuration)
      state.copy(jitState =
        current.copy(
          counts = current.counts
            .copy(syntaxReads = current.counts.syntaxReads + read.reads),
          criteria = if read.learned.isEmpty then current.criteria
          else current.criteria ++ read.learned
        )
      )

  /** The criteria the reading has already read (`KnownCriteria`). */
  private def known(state: ReadingState): KnownCriteria = KnownCriteria(
    JitRunState.of(state, configuration).criteria
  )

  /** The result of the reads of syntax, the reads counted and the criteria
    * learned kept in the state.
    */
  private def syntaxResult[Result](
      read: SyntaxRead[Result]
  ): Computation[ReadingState, Result] =
    Computation
      .modified[ReadingState](syntaxCounted(_, read))
      .map(_ => read.result)

  /** The result of the reads of syntax under the reading's known criteria, the
    * reads counted and the criteria learned kept in the state.
    */
  private def syntaxRead[Result](
      reading: KnownCriteria ?=> SyntaxRead[Result]
  ): Computation[ReadingState, Result] =
    Computation
      .state[ReadingState]
      .flatMap(state => syntaxResult(reading(using known(state))))

  /** The reading's known criteria. */
  private def syntaxContext: Computation[ReadingState, KnownCriteria] =
    Computation.state[ReadingState].map(known)

  private def run: Computation[ReadingState, JitRunState] =
    Computation.state[ReadingState].map(JitRunState.of(_, configuration))

  private def runModified(
      change: JitRunState => JitRunState
  ): Computation[ReadingState, Unit] =
    Computation.modified[ReadingState](state =>
      state.copy(jitState = change(JitRunState.of(state, configuration)))
    )

  private def countsModified(
      change: JitCounts => JitCounts
  ): Computation[ReadingState, Unit] =
    runModified(found => found.copy(counts = change(found.counts)))

  private def computedStream(
      computation: Computation[ReadingState, Stream]
  ): Stream =
    computedAnswers(computation)

  // ---- natives ----

  /** The native applied to the values, its result in the representation; the
    * call counted (native_called/3).
    *
    * FIXME: a native's result holds its arguments as given, so cons's result
    * https://github.com/Atry/private-overlay/issues/2213 is a list storage
    * whose item may be the JIT's own layer (a sharing cell) or an open term: a
    * storage that is no instruction, and a second storage of the term the
    * item's instruction form spells, against #2163 B1's "a storage is a closed
    * term" and one object for one term; sound, the view standing for the same
    * term.
    */
  private def nativeCalled(
      native: NativeName,
      values: Vector[NativeArgument],
      representation: Representation
  ): Computation[ReadingState, NativeValue] =
    countsModified(counts =>
      counts.copy(
        nativeCalls = counts.nativeCalls + 1,
        callsByNative =
          counts.callsByNative.updated(native, counts.callsOf(native) + 1)
      )
    ).map(_ => nativeBackend.natives(native).implementation(values))

  /** The heads of the define at the instruction, bound to the native, given its
    * last argument (jit_applied/3 on a native application): the native's result
    * on each combination of its arguments' values when every argument is ready
    * (for a data family's constructor, when every argument is written
    * represented, below); otherwise the define's own heads applied to the
    * arguments.
    *
    * What licenses forcing the operands of a native other than a constructor: a
    * ready argument (written represented, or under a decode point or a fallback
    * point of the place's criterion) is read to its values (`argumentsValued`,
    * `nativeValue`) before the native is called, so an operand with no head
    * gives the application no head. That equals the define only where the
    * `native` declaration's equivalence, native = define, also covers an
    * operand with no head: the define applied to such an operand at that place
    * has no head either, that is, the define is strict in the place. The host
    * chooses nothing here: the `native` declaration and the criterion written
    * in the term decide, and the equivalence is the declaration's proof
    * obligation.
    *
    * A data family's constructor (`NativeBackend.constructorNatives`, a backend
    * fact) is not strict in its fields: its define answers a lambda without
    * reading them (`successor` is λn.λz.λs. s n). So its native is called only
    * when every argument is already written represented, which forces nothing;
    * otherwise the define's heads are taken, the fields left as the term writes
    * them, decode points included, until a strict native or a decoding reads
    * them.
    *
    * FIXME: the strictness of the natives of the corpus modules is not yet
    * https://github.com/Atry/private-overlay/issues/1935 audited
    * (`natural_plus` and the unary comparisons, the binary and twin arithmetic,
    * `fixpoint` by derivation, `every_assignment`, `billboard_go`,
    * `concatenation_fit`, `workers_place`, the `wren_binary_*` operations): a
    * native whose define is not strict in a place it forces loses answers as
    * `successor` did. Candidate: a native is called eagerly only where the term
    * spells a proved strictness property at the call (the whole-block proof
    * structure of the interface review of 2026-11-03).
    */
  private def nativeAppliedHeads(
      instruction: Term,
      native: BoundNative,
      arguments: Vector[JitValue]
  ): Stream =
    computedStream(syntaxRead(argumentsReady(native.name, arguments)).flatMap {
      case None => Computation.pure(genericApplied(instruction, arguments))
      case Some(_)
          if nativeBackend.constructorNatives
            .contains(native.name) && !arguments.forall(storageValued) =>
        Computation.pure(genericApplied(instruction, arguments))
      case Some((places, result)) =>
        argumentsValued(arguments, places).map(valued =>
          if valued.exists(_.isInstanceOf[Valued.Unvalued[?]]) then
            genericApplied(instruction, valuedTerms(valued, places))
          else
            valuedCombinations(valued).flatMap(values =>
              Answers.computed(
                nativeCalled(native.name, values, result).map(found =>
                  Vector(represented(result, found))
                )
              )
            )
        )
    })

  /** Every argument is ready at its place, the list's element filter taken from
    * the tail before the items are read (native_arguments_ready/2): the places
    * and the result's representation. A native whose result is at the call's
    * parameter is never ready here: its result's parameter is read from the
    * criterion written in the term, where a decoding point reads it
    * (`placesFor`), and the application is read generically. The host derives
    * no parameter from the operands' values; a type-preservation lemma
    * (`corpora/compiler/word_type_preservation`, `binary_type_preservation`)
    * writes the criterion at a constructor's node.
    */
  private def argumentsReady(native: NativeName, arguments: Vector[JitValue])(
      using KnownCriteria
  ): SyntaxRead[Option[(Vector[Place], Representation)]] =
    val representations = nativeBackend.natives(native)
    representations.result match
      case NativePlace.Parameter(_) => SyntaxRead.pure(None)
      case _ => listedOrFixedReady(representations, arguments)

  /** `argumentsReady` of a native whose result is in a fixed representation or
    * a list.
    */
  private def listedOrFixedReady(
      representations: Native,
      arguments: Vector[JitValue]
  )(using KnownCriteria): SyntaxRead[Option[(Vector[Place], Representation)]] =
    val pairs = representations.parameters.zip(arguments)
    val element = pairs.foldLeft(
      SyntaxRead.pure(Option(Option.empty[JitValue]))
    ) { (sofar, pair) =>
      SyntaxRead.chained(sofar)(bound =>
        pair match
          case (NativePlace.Fixed(representation), argument) =>
            nativeReady(argument, Place.In(representation)).map(ready =>
              if ready then Some(bound) else None
            )
          case (NativePlace.Tail | NativePlace.AnyList, argument) =>
            readyRepresentation(argument).map {
              case Some(Representation.ListOf(found))
                  if bound.forall(Value.same(_, found)) =>
                Some(Some(found))
              case _ => None
            }
          case (NativePlace.Item, _) => SyntaxRead.pure(Some(bound))
          case (
                NativePlace.NaturalList(_) | NativePlace.NaturalRecordList(_),
                _
              ) =>
            SyntaxRead.pure(None)
          case (NativePlace.DeclaredFamilyValue, _) =>
            throw IllegalStateException(
              "a declared family's value is a native's result, never its parameter"
            )
          case (NativePlace.Parameter(_) | NativePlace.OfParameter(_), _) =>
            throw IllegalStateException(
              s"a place at the call's parameter in a native whose result is not: ${representations.result}"
            )
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
        case NativePlace.AnyList => bound.map(Representation.ListOf(_))
        case _                   => None
      itemsReady.map(ready =>
        if ready then
          result.map(found =>
            (representations.parameters.map(place(_, bound, None)), found)
          )
        else None
      )
    )

  /** For each ready argument, its outcome taken once (arguments_valued/3). */
  private def argumentsValued(
      arguments: Vector[JitValue],
      places: Vector[Place]
  ): Computation[ReadingState, Vector[Valued]] =
    Computation.traversed(arguments.zip(places)) { (argument, place) =>
      place match
        case Place.ItemOf(element) =>
          itemOutcome(argument, element).map(outcomeValued)
        case Place.TailOf(element) =>
          tailOutcome(argument, element).map(outcomeValued)
        case Place.In(representation) =>
          Value.closed(argument).flatMap(StorageOf.group[C]) match
            // A group of storages of the representation, `(s₁ + … + sₙ) ∥ T` in its unique spelling, is the choice of
            // its members: each member's value, as a choice of storages is valued member by member.
            case Some(group) if group.representation == representation =>
              Computation.pure(
                Valued.Values(
                  group.members.map(member =>
                    NativeArgument.Represented(StorageOf.nativeValue(member))
                  )
                )
              )
            case _ =>
              syntaxRead(fallbackPoint(argument)).flatMap {
                case Some((operand, _)) =>
                  fallbackOutcome(representation, operand).map(outcomeValued)
                case None => Computation.pure(Valued.Lazy(argument, place))
              }
    }

  private def outcomeValued(outcome: Outcome): Valued = outcome match
    case Outcome.Typed(values)  => Valued.Values(values)
    case Outcome.Untyped(value) => Valued.Unvalued(value)

  /** Each combination of the arguments' values, in order (valued_values/2). */
  private def valuedCombinations(
      valued: Vector[Valued]
  ): Answers[ReadingState, Vector[NativeArgument]] =
    valued.foldLeft(
      Answers.single[ReadingState, Vector[NativeArgument]](Vector.empty)
    ) { (combinations, argument) =>
      combinations.flatMap(found =>
        (argument match
          case Valued.Values(values) =>
            Answers.of[ReadingState, NativeArgument](values)
          case Valued.Lazy(argument, place) => nativeValue(argument, place)
          case Valued.Unvalued(_) => Answers.empty[ReadingState, NativeArgument]
        ).map(found :+ _)
      )
    }

  /** The arguments the define takes when the native falls back to it
    * (valued_terms/3).
    */
  private def valuedTerms(
      valued: Vector[Valued],
      places: Vector[Place]
  ): Vector[JitValue] =
    valued.zip(places).map {
      case (Valued.Values(values), place) =>
        outcomeTerm(Outcome.Typed(values), place)
      case (Valued.Unvalued(value), _)   => value
      case (Valued.Lazy(argument, _), _) => argument
    }

  /** The heads of the native-bound library file's term at the instruction, from
    * its own layer, applied to the arguments (generic_applied/3). The layer is
    * dispatched by its constructor alone (`Goal.LayerEvaluation`): it is the
    * term itself, which evaluated again would be dispatched to its native, the
    * very native this reading stands in for.
    */
  private def genericApplied(
      instruction: Term,
      arguments: Vector[JitValue]
  ): Stream =
    computedStream(
      syntaxRead(layer(Value.of(instruction))).map(found =>
        running(Machine(List(Goal.LayerEvaluation(found, arguments.toList))))
      )
    )

  // ---- fallback points ----

  /** The heads of a fallback point of the representation over the operand
    * (fallback_point_head/3).
    *
    * FIXME (carried from jit.pl:768; a fallback point is taken when the
    * https://github.com/Atry/private-overlay/issues/1937 input cannot be proved
    * in the domain, and the check should be fast): the check of a fallback
    * point reads all of the operand's heads before either path (`valueRead`),
    * so an operand whose heads do not all end proves nothing and runs neither
    * path: [zero, Ω] as an operand gives no head where the reference gives
    * zero's first (derived from the rules, not measured). The same holds of
    * `argumentsValued` for a native's argument. Candidate: take the untyped
    * path's heads beside a reading that has not ended, interleaved fairly,
    * which is not designed.
    */
  private def fallbackPointHeads(
      representation: Representation,
      operand: JitValue
  ): Stream =
    if heldAsWritten(representation) then
      heads(operand) // x + (x ∥ C) is x for a least term C
    else
      computedStream(fallbackOutcome(representation, operand).map {
        case Outcome.Typed(values) =>
          Answers.of(values.map(headOfValue(representation, _)))
        case Outcome.Untyped(untyped) => heads(untyped)
      })

  private def headOfValue(
      representation: Representation,
      value: NativeArgument
  ): JitHead = value match
    case NativeArgument.Represented(found) => represented(representation, found)
    case other                             =>
      throw IllegalStateException(
        s"a value of a representation is no ${other.productPrefix}"
      )

  /** The reading of a fallback point, taken once (fallback_outcome/3).
    */
  private def fallbackOutcome(
      representation: Representation,
      operand: JitValue
  ): Computation[ReadingState, Outcome] =
    countsModified(counts =>
      counts.copy(fallbackChecks = counts.fallbackChecks + 1)
    ).flatMap(_ => fallbackOutcomeCounted(representation, operand))

  private def fallbackOutcomeCounted(
      representation: Representation,
      operand: JitValue
  ): Computation[ReadingState, Outcome] =
    val read = syntaxRead(
      constructorOutcome(operand, representation).flatMap {
        case found @ Some(_) => SyntaxRead.pure(found)
        case None            =>
          codecLiteralOutcome(operand, representation).map(
            _.map(Computation.pure(_))
          )
      }
    ).flatMap {
      case Some(outcome) => outcome
      case None          =>
        syntaxRead(fallbackPoint(operand)).flatMap {
          case Some((inner, innerRepresentation)) =>
            fallbackOutcome(innerRepresentation, inner).flatMap(innerOutcome =>
              if innerRepresentation == representation then
                Computation.pure(innerOutcome)
              else
                valueRead(
                  representation,
                  outcomeTerm(innerOutcome, Place.In(innerRepresentation))
                )
            )
          case None => valueRead(representation, operand)
        }
    }
    read.map {
      case Outcome.Untyped(_)
          if configuration.dispatch.outsideDecided == DispatchDecision.Rejected =>
        throw TypedVersionDomain(representation, operand.representation)
      case outcome => outcome
    }

  /** The reading of a type-filtered constructor, each argument read once
    * (constructor_outcome/3).
    */
  private def constructorOutcome(
      operand: JitValue,
      representation: Representation
  )(using
      KnownCriteria
  ): SyntaxRead[Option[Computation[ReadingState, Outcome]]] =
    filteredConstructor(operand, representation).flatMap(filtered =>
      if !filtered then SyntaxRead.pure(None)
      else
        spineListed(operand).map(constructorArgumentsOutcome(representation, _))
    )

  /** Whether the native's result is at the call's parameter
    * (`NativePlace.Parameter`).
    */
  private def parameterised(native: NativeName): Boolean =
    nativeBackend.natives(native).result match
      case NativePlace.Parameter(_) => true
      case _                        => false

  /** The reading of a literal of a data family that has a codec and whose
    * spine's head has no constructor native of a fixed place at the
    * representation (the words and the binary naturals, whose constructors'
    * natives are at the family's parameter): the value the operand spells by
    * its syntax alone at the representation's parameter (`syntaxDecoded`),
    * typed; `None` when the representation is no data family with a codec, when
    * the head has a constructor native of a fixed place there
    * (`constructorOutcome` reads such a literal), or when the syntax does not
    * decode, and the operand is then read as before. A constructor native at
    * the family's parameter does not stop the decoding: `constructorOutcome`
    * reads a literal only when it is type-filtered, so a literal under a decode
    * point reads as it did before those natives existed. The decision rests on
    * the criterion written in the fallback point, which named the
    * representation, and on the operand's syntax; nothing is evaluated and no
    * value is guessed.
    */
  private def codecLiteralOutcome(
      operand: JitValue,
      representation: Representation
  )(using KnownCriteria): SyntaxRead[Option[Outcome]] =
    representation match
      case Representation.Data(familyIdentity, parameter)
          if nativeBackend.family(familyIdentity).isDefined =>
        val term = operand
        spineRead(term, Vector.empty).flatMap {
          case Some((head, _))
              if headNatives(head).exists(native =>
                !parameterised(native.name) && placesFor(
                  native.name,
                  representation
                ).isDefined
              ) =>
            SyntaxRead.pure(None)
          case Some(_) =>
            syntaxDecoded(familyIdentity, parameter, term).map(
              _.map(value =>
                Outcome.Typed(Vector(NativeArgument.Represented(value)))
              )
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
      case JitValue.IrTerm(found) => found
      case other                  =>
        throw IllegalStateException(
          s"a type-filtered constructor's head is a ${other.layer}"
        )
    headNatives(head)
      .find(native =>
        native.parameterCount == arguments.size && placesFor(
          native.name,
          representation
        ).isDefined
      )
      .map(native =>
        val places = placesFor(native.name, representation).get
        Computation
          .traversed(arguments.zip(places))(argumentOutcome)
          .flatMap(outcomes =>
            val typed =
              outcomes.collect { case Outcome.Typed(values) => values }
            val combinations =
              if typed.size == outcomes.size then
                typed.foldLeft(Vector(Vector.empty[NativeArgument]))(
                  (found, values) =>
                    found.flatMap(prefix => values.map(prefix :+ _))
                )
              else Vector.empty
            Computation
              .traversed(combinations)(values =>
                nativeCalled(native.name, values, representation)
              )
              .map(results =>
                if typed.size == outcomes.size && results.nonEmpty then
                  Outcome.Typed(results.map(NativeArgument.Represented(_)))
                else
                  val terms = outcomes
                    .zip(places)
                    .map((outcome, place) => outcomeTerm(outcome, place))
                  Outcome.Untyped(
                    terms.foldLeft(Value.of(instruction))(JitValue.Apply(_, _))
                  )
              )
          )
      )

  /** The reading of an argument of a type-filtered constructor, taken once
    * (argument_outcome/3).
    */
  private def argumentOutcome(
      argument: JitValue,
      place: Place
  ): Computation[ReadingState, Outcome] =
    place match
      case Place.ItemOf(element)    => itemOutcome(argument, element)
      case Place.TailOf(element)    => tailOutcome(argument, element)
      case Place.In(representation) =>
        syntaxRead(fallbackPoint(argument)).flatMap {
          case Some((operand, _)) => fallbackOutcome(representation, operand)
          case None               =>
            syntaxRead(
              nativeReady(argument, place).flatMap(ready =>
                if ready then SyntaxRead.pure(None)
                else constructorOutcome(argument, representation)
              )
            ).flatMap(notReadyConstructor =>
              notReadyConstructor.getOrElse(
                argument match
                  case JitValue.Represented(found, value)
                      if found == representation =>
                    Computation.pure(
                      Outcome.Typed(Vector(NativeArgument.Represented(value)))
                    )
                  case _ =>
                    nativeValue(argument, place).collected.map(values =>
                      if values.isEmpty then Outcome.Untyped(argument)
                      else Outcome.Typed(values)
                    )
              )
            )
        }

  /** The reading of a list's item (item_outcome/3).
    *
    * FIXME (carried from jit.pl:1096, the re-check of the lists'
    * https://github.com/Atry/private-overlay/issues/1938 representation,
    * 2026-10-29): the check of a fallback point runs when its cell is built, so
    * a list holding one is less lazy than the define, which leaves the item
    * unread until a consumer reads it; in a compiled run every item cons's
    * native receives is such a point. Where the check does not end, a reading
    * of the list's spine loses its answer: measured 2026-10-29 in the Prolog
    * JIT, list_fold zero (\h. \a. successor a) (cons [Ω, Ω ∥ nat_type] (nil ∥
    * list_type nat_type)), Ω = (\x. x x) (\y. y y), runs past 2,000,000
    * inferences, while the same term with the tail nil reads successor zero.
    * This is the check that does not end of the FIXME at `fallbackPointHeads`
    * (jit.pl's fallback_point_head/3), met here where the item is never read.
    * Candidate: keep such an item unread in the cell, marked as not filtered by
    * the element, hand it out as it is, and filter the marked items at a strict
    * decode point over the list; not designed.
    */
  private def itemOutcome(
      argument: JitValue,
      element: JitValue
  ): Computation[ReadingState, Outcome] =
    syntaxRead(fallbackPoint(argument)).flatMap {
      case Some((operand, _)) =>
        syntaxRead(decodingCriterionRead(element)).flatMap(criterion =>
          val representation = criterion.getOrElse(
            throw IllegalStateException(
              "a list's item read in a list whose element filter is no decoding criterion"
            )
          )
          fallbackOutcome(representation, operand).map {
            case Outcome.Typed(values) =>
              Outcome.Typed(
                values.map(value =>
                  NativeArgument.Item(
                    headOfValue(representation, value).asValue
                  )
                )
              )
            case untyped => untyped
          }
        )
      case None =>
        Computation.pure(Outcome.Typed(Vector(NativeArgument.Item(argument))))
    }

  /** The reading of a list's tail (tail_outcome/3): a represented list by its
    * storage; any other tail untyped, so that the cell gets no storage: a
    * cell's storage is the unique spelling `cons (h ∥ E) (t ∥ L) ∥ L`, whose
    * tail node filters t, and committing a tail that is a fallback point to its
    * typed member would drop the untyped path the fallback point keeps.
    *
    * FIXME: so under the conversion a list a program computes cell by cell
    * https://github.com/Atry/private-overlay/issues/2176 under the fallback
    * dispatch is read untyped, with no call of cons's native; the compiled
    * blocks of step 8 build such a list whole, natively. Under a strict
    * strategy such a read throws `TypedVersionDomain` at the fallback point, an
    * answer lost, never a wrong one; the one admission of the conversion
    * (`StorageEncoding.parallel`) refuses a cell whose item sits in a sharing
    * cell, which reads untyped for the same cause.
    */
  private def tailOutcome(
      argument: JitValue,
      element: JitValue
  ): Computation[ReadingState, Outcome] =
    argument match
      case stored @ JitValue.Represented(Representation.ListOf(found), _)
          if Value.same(found, element) =>
        Computation.pure(Outcome.Typed(Vector(NativeArgument.Tail(stored))))
      case _ =>
        Computation.pure(Outcome.Untyped(argument))

  /** Whether the written term is `t ∥ L`, L the lists' criterion of the element
    * (`StorageEncoding.holdsAsTail`). A closure instance whose body is such a
    * parallel is not seen as one, and is filtered once more.
    */
  private def filteredAsList(term: JitValue, element: JitValue): Boolean =
    operations.holdsAsTail(term, Representation.ListOf(element))

  /** An outcome as a term (outcome_term/3). */
  private def outcomeTerm(outcome: Outcome, place: Place): JitValue =
    (outcome, place) match
      case (Outcome.Untyped(untyped), _)            => untyped
      case (Outcome.Typed(values), Place.ItemOf(_)) =>
        oneOrChoice(values.map {
          case NativeArgument.Item(item) => item
          case other                     =>
            throw IllegalStateException(
              s"an item's outcome holds a ${other.productPrefix}"
            )
        })
      case (Outcome.Typed(values), Place.TailOf(element)) =>
        oneOrChoice(values.map {
          case NativeArgument.Tail(tail) => tail
          case other                     =>
            throw IllegalStateException(
              s"a tail's outcome holds a ${other.productPrefix}"
            )
        })
      case (Outcome.Typed(values), Place.In(representation)) =>
        oneOrChoice(
          values.map(value => headOfValue(representation, value).asValue)
        )

  private def oneOrChoice(values: Vector[JitValue]): JitValue = values match
    case Vector(one) => one
    case several     => JitValue.Choice(several)

  /** The reading of an operand that is neither a type-filtered constructor nor
    * a fallback point (value_read/3): its heads read once, typed when every one
    * stands for a value of the representation, otherwise the operand as it is,
    * untyped; a reading that recurs among the readings around it stands for no
    * value. The heads of a reading that saw no cut (the reading's cuts the same
    * before and after) are recorded in `CheckedHeads` under the operand and the
    * dispatch mode, so that a later evaluation of the operand replays them
    * (`evaluated`); a cut's heads depend on the readings around it and are not
    * recorded. Only heads are recorded: whether they are of the representation
    * is read off them at each use, here by `headsValues`.
    */
  private def valueRead(
      representation: Representation,
      value: JitValue
  ): Computation[ReadingState, Outcome] =
    run.flatMap(current =>
      current.readingPath.extended(OperandReading(representation, value)) match
        case None =>
          runModified(cut => cut.copy(cuts = cut.cuts + 1)).map(_ =>
            Outcome.Untyped(value)
          )
        case Some(extended) =>
          for
            _ <- runModified(_.copy(readingPath = extended))
            found <- heads(value).collected
            _ <- runModified(after =>
              val restored = after.copy(readingPath = current.readingPath)
              if after.cuts == current.cuts then
                restored.copy(checkedHeads =
                  after.checkedHeads.recorded(
                    CheckedOperand(value, configuration.dispatch),
                    found,
                    configuration.instanceRetention
                  )
                )
              else restored
            )
            values <- headsValues(representation, found)
          yield values match
            case Some(typed) => Outcome.Typed(typed)
            case None        => Outcome.Untyped(value)
    )

  /** Every head, one at least, stands for a value of the representation
    * (heads_values/3), the values in order.
    */
  private def headsValues(
      representation: Representation,
      found: Vector[JitHead]
  ): Computation[ReadingState, Option[Vector[NativeArgument]]] =
    if found.isEmpty then Computation.pure(None)
    else
      Computation.folded(found, Option(Vector.empty[NativeArgument])) {
        case (None, _)            => Computation.pure(None)
        case (Some(values), head) =>
          headValue(representation, head).map(
            _.map(values :+ NativeArgument.Represented(_))
          )
      }

  /** The value of the representation the head stands for (head_value/3): a
    * value of it; a value of another representation whose encoding of one layer
    * stands for one; or the head of a define bound to a native of no parameter
    * whose result is in the representation.
    */
  private def headValue(
      representation: Representation,
      head: JitHead
  ): Computation[ReadingState, Option[NativeValue]] =
    head match
      case JitHead.Represented(found, value) =>
        if found == representation then Computation.pure(Some(value))
        else firstHeadValue(representation, encodedHeads(found, value))
      case JitHead.Lambda(code, holes, fillings) if fillings.isEmpty =>
        Computation.pure(
          operations.constants.collectFirst {
            case BackendConstant(`code`, `holes`, value, place)
                if placeHolds(place, representation) =>
              value
          }
        )
      case _ => Computation.pure(None)

  /** Whether a native's result at the place is in the representation. */
  private def placeHolds(
      place: NativePlace,
      representation: Representation
  ): Boolean = (place, representation) match
    case (NativePlace.Fixed(found), _) => found == representation
    case (NativePlace.AnyList, Representation.ListOf(_)) => true
    case _                                               => false

  private def firstHeadValue(
      representation: Representation,
      stream: Stream
  ): Computation[ReadingState, Option[NativeValue]] =
    stream.pull.flatMap {
      case None               => Computation.pure(None)
      case Some((head, rest)) =>
        headValue(representation, head).flatMap {
          case found @ Some(_) => Computation.pure(found)
          case None            => firstHeadValue(representation, rest)
        }
    }

  // ---- decode points ----

  /** The heads of the decode point `value ∥ criterion` of the representation
    * (`decodePointHeads`), each decoded value checked. The decoded values stand
    * for the filtered value (`gezi.weakhead.ListCodec`, WHY A DECODED LIST
    * STANDS FOR THE FILTERED VALUE) only when they hold no case of a decoding.
    * So a value that may hold one (`JitValues.mayHoldDecodingCase`) gives in
    * its place the parallel itself as a head, both sides read (`observed`), as
    * the reference reads it.
    */
  private def checkedDecodePointHeads(
      representation: Representation,
      value: JitValue,
      criterion: JitValue,
      applied: Boolean
  ): Stream =
    decodePointHeads(representation, value, applied).flatMap {
      case JitHead.Represented(_, found)
          if JitValues.mayHoldDecodingCase(found) =>
        Answers.single(JitHead.Parallel(value, criterion))
      case head => Answers.single(head)
    }

  /** The decoded values of a stream of a decode point's heads that stand for
    * the filtered value: a value that may hold a case of a decoding
    * (`JitValues.mayHoldDecodingCase`) gives no native argument.
    */
  /** The decoded values of a stream of a decode point's heads that stand for
    * the filtered value, as native arguments: none at all when one head is a
    * member the decoding cannot read exactly (the parallel of it with the
    * criterion, `decodedHeads`) or a value that may hold a case of a decoding
    * (`JitValues.mayHoldDecodingCase`), so that the native is not run without
    * that member and its caller reads the argument otherwise (a native falls
    * back to its define, `argumentOutcome`; a decode point reads the codecs,
    * `listOrDataDecodePointHeads`).
    */
  private def heldDecodings(heads: Stream): Stream =
    computedAnswers(heads.collected.map(found =>
      val unheld = found.exists {
        case JitHead.Represented(_, value) =>
          JitValues.mayHoldDecodingCase(value)
        case JitHead.Parallel(_, _) => true
        case _                      => false
      }
      if unheld then Answers.empty else Answers.of(found)
    ))

  /** The heads of a decode point of the representation over the value
    * (decode_point_head/3).
    */
  private def decodePointHeads(
      representation: Representation,
      value: JitValue,
      applied: Boolean
  ): Stream =
    representation match
      // `x ∥ array_list E` is `x ∥ list_type E` by the β rule: the list read as
      // that decode point reads it, its cells packed into one array when every
      // item is a storage of E and every tail a storage of the list, and the
      // list's head kept as it is otherwise, which stands for the same term.
      // Not memoized in `DecodedPoints` as `decodedHeads` does for other
      // points: a head that is the array list's storage passes in one step,
      // and any other is packed by a walk of its cells after a hit anyway.
      // A storage of the array list itself is its own head, as a decode point
      // of its own representation reads any value (`headDecoded`): written so,
      // or a head the value evaluates to (another block's result, a closure's
      // value), it crosses the filter with no cell made and no element read.
      // A storage of an array list of another element representation of one
      // family is relabelled as a group block relabels it
      // (`StorageEncoding.relabelled`), so that the two read one spelling of
      // the term. Any other head, and a list relabelling refuses, is decoded
      // as the list's decode point decodes it.
      case Representation.ArrayListOf(element) =>
        val encoding = operations
        val listRepresentation =
          Representation.ListOf(encoding.criterionOf(element))
        def packed(head: JitHead): JitHead = JitValues
          .arrayPacked(encoding, representation, element, head)
          .getOrElse(head)
        def own(found: AnyRef): Option[JitHead] = found match
          case storage: ArrayListStorage
              if storage.representation == representation =>
            Some(storage)
          case storage: ArrayListStorage =>
            // Interned, the object the block's exit gives (`StorageEncoding.storageOf`).
            encoding
              .relabelled(storage.listed, representation)
              .map(relabelled => represented(representation, relabelled))
          case _ => None
        val writtenOwn = value match
          case JitValue.Stored(storage) => own(storage)
          case _                        => None
        writtenOwn match
          case Some(head) => Answers.single(head)
          case None       =>
            computedStream(
              syntaxRead(filteredConstructor(value, listRepresentation)).map(
                filtered =>
                  if filtered then
                    decodePointHeads(listRepresentation, value, applied).map(
                      packed
                    )
                  else
                    heads(value).flatMap(head =>
                      own(head) match
                        case Some(owned) => Answers.single(owned)
                        case None        =>
                          headDecoded(listRepresentation, head, None, 0)
                            .flatMap {
                              case Decoded.Read(decoded) =>
                                Answers.single(
                                  packed(
                                    represented(listRepresentation, decoded)
                                  )
                                )
                              case unread =>
                                unreadMember(
                                  memberValue(head, value),
                                  encoding.criterionOf(listRepresentation),
                                  unread,
                                  applied
                                )
                            }
                    )
              )
            )
      case _ => listOrDataDecodePointHeads(representation, value, applied)

  /** Whether the constructor is no member of the family's criterion at the
    * parameter: the backend's fact (`DataFamily.excluded`), which the premise
    * of section 23, the facts' obligation, makes agree with the criterion.
    */
  private def constructorExcluded(
      familyIdentity: FamilyIdentity,
      parameter: Option[FamilyParameter],
      constructor: Int
  ): Boolean =
    dataFamily(familyIdentity).excluded(parameter, constructor)

  /** `decodePointHeads` of a representation that is no array list's. A
    * type-filtered constructor is read by the natives, which give no value at
    * all when a field holds a member they cannot read exactly; such a
    * constructor is read by the codecs instead, which give that member as the
    * parallel under arguments and no head for its own normal form
    * (`decodedHeads`).
    */
  private def listOrDataDecodePointHeads(
      representation: Representation,
      value: JitValue,
      applied: Boolean
  ): Stream =
    if heldAsWritten(representation) then
      heads(value) // x ∥ C is x for a least term C
    else
      computedStream(
        syntaxRead(filteredConstructor(value, representation)).map(filtered =>
          if filtered then
            val natively: Stream =
              nativeValue(value, Place.In(representation)).flatMap {
                case NativeArgument.Represented(result) =>
                  Answers.single(represented(representation, result))
                case other =>
                  throw IllegalStateException(
                    s"a decode point's value is a ${other.productPrefix}"
                  )
              }
            // The natives' one result, or the codecs: the natives give none when a field holds a member they cannot
            // read exactly (`heldDecodings`), and several when a field has several values, each a run of the
            // constructor's native, whose choice `C a + C b` is below `C (a + b)` in ⊑_O (a context that reads the
            // field twice meets the two); the codecs read such a member by its heads, a layer whose field has several
            // values as written (`valueDecoded`).
            Answers(firstDistinct(natively, 2, Vector.empty).flatMap {
              case Vector(only) =>
                Computation.pure(
                  Some((only, Answers.empty[ReadingState, JitHead]))
                )
              case _ => decodedHeads(representation, value, applied).pull
            })
          else decodedHeads(representation, value, applied)
        )
      )

  /** The values of the place the term, ready in it or a type-filtered
    * constructor of it, evaluates to by the natives and the codecs
    * (native_value/3).
    */
  private def nativeValue(
      operand: JitValue,
      place: Place
  ): Answers[ReadingState, NativeArgument] =
    Answers(syntaxContext.flatMap(knownCriteria =>
      given KnownCriteria = knownCriteria
      (place match
        case Place.ItemOf(element) =>
          Answers.computed(itemOutcome(operand, element).map {
            case Outcome.Typed(items)   => items
            case Outcome.Untyped(value) => Vector(NativeArgument.Item(value))
          })
        case Place.TailOf(element) =>
          operand match
            case stored @ JitValue
                  .Represented(representation @ Representation.ListOf(found), _)
                if Value.same(found, element) =>
              Answers.single(NativeArgument.Tail(stored))
            case written =>
              // FIXME: loses answers. A native's tail argument is held filtered by the list's https://github.com/Atry/private-overlay/issues/2202
              // criterion, unread, `cons h (t ∥ L) ∥ L` for `cons h t ∥ L`, which is below it in ⊑_O
              // (`(cons (zero ∥ nat_type) I ∥ list_type nat_type) I (λh t. t)` has the answer I, which the filtered tail
              // drops). The cell is to be in the unique spelling when made.
              computedAnswers(
                syntaxResult(
                  nativeReady(operand, Place.In(Representation.ListOf(element)))
                ).map(ready =>
                  nativeValue(operand, Place.In(Representation.ListOf(element)))
                    .map {
                      case NativeArgument.Represented(
                            found @ NativeValue.Listed(_)
                          ) =>
                        NativeArgument.Tail(
                          operations
                            .storageOf(Representation.ListOf(element), found)
                        )
                      case other =>
                        throw IllegalStateException(
                          s"a list's value is a ${other.productPrefix}"
                        )
                    }
                )
              )
        case Place.In(representation) =>
          representedValues(operand, representation)
      ).pull
    ))

  private def representedValues(
      operand: JitValue,
      representation: Representation
  )(using
      KnownCriteria
  ): Answers[ReadingState, NativeArgument] =
    operand match
      case _ if heldAsWritten(representation) =>
        computedAnswers(
          unreadField(operand).map(found =>
            Answers.of(found.toVector.map(NativeArgument.Represented(_)))
          )
        )
      case _ if FilteredFamily.criterionOf(representation).isDefined =>
        // A constructor's field filtered by F: the node `f ∥ F` as written, unread. A field not written so is no value
        // of the representation, `C (f ∥ F) ∥ T` being below `C f ∥ T` in ⊑_O, so it has none here: the natives then
        // give none, and the decode point reads the layer by its codecs or as written.
        val filter = FilteredFamily
          .criterionOf(representation)
          .getOrElse(throw IllegalStateException(s"$representation"))
        operations.filteredAlready(operand, filter) match
          case Some(filtered) =>
            computedAnswers(
              unreadField(filtered).map(found =>
                Answers.of(found.toVector.map(NativeArgument.Represented(_)))
              )
            )
          case None => Answers.empty
      case _ =>
        computedAnswers(
          Computation
            .state[ReadingState]
            .map(state =>
              if JitRunState
                  .of(state, configuration)
                  .checkedHeads
                  .found(CheckedOperand(operand, configuration.dispatch))
                  .isDefined
              then
                // The operand's check ran uncut under this dispatch mode (`CheckedHeads`): its heads are decoded as
                // `evaluated` replays them, and the check is not run again.
                heldDecodings(
                  decodedHeads(representation, operand, applied = true)
                ).map(representedArgument)
              else uncheckedValues(operand, representation)
            )
        )

  /** The values of an operand no uncut check has read under this dispatch mode:
    * a represented value as it is, a decode point's or a fallback point's
    * decodings, or a native's result.
    */
  private def uncheckedValues(term: JitValue, representation: Representation)(
      using KnownCriteria
  ): Answers[ReadingState, NativeArgument] =
    term match
      case JitValue.Represented(found, value) =>
        if found == representation then
          Answers.single(NativeArgument.Represented(value))
        else
          throw IllegalStateException(
            s"a ${found.familyIdentity.shown} value read as ${representation.familyIdentity.shown}"
          )
      case _ =>
        computedAnswers(syntaxResult(decodePointReached(term)).flatMap {
          case Some((filtered, _)) =>
            Computation.pure(
              heldDecodings(
                decodePointHeads(representation, filtered, applied = true)
              ).map(representedArgument)
            )
          case None =>
            syntaxResult(fallbackPoint(term)).flatMap {
              case Some((fallbackOperand, _)) =>
                Computation.pure(
                  computedAnswers(
                    fallbackOutcome(representation, fallbackOperand).map {
                      case Outcome.Typed(values)    => Answers.of(values)
                      case Outcome.Untyped(untyped) =>
                        heldDecodings(
                          decodedHeads(representation, untyped, applied = true)
                        ).map(representedArgument)
                    }
                  )
                )
              case None =>
                syntaxResult(spineListed(term)).map((head, arguments) =>
                  Answers
                    .of[ReadingState, BoundNative](headNatives(head))
                    .flatMap(native =>
                      placesFor(native.name, representation) match
                        case None         => Answers.empty
                        case Some(places) =>
                          if places.size != arguments.size then Answers.empty
                          else
                            nativeValues(arguments, places).flatMap(values =>
                              Answers.computed(
                                nativeCalled(
                                  native.name,
                                  values,
                                  representation
                                ).map(found =>
                                  Vector(NativeArgument.Represented(found))
                                )
                              )
                            )
                    )
                )
            }
        })

  private def computedAnswers[Answer](
      computation: Computation[ReadingState, Answers[ReadingState, Answer]]
  ): Answers[ReadingState, Answer] =
    Answers(computation.flatMap(_.pull))

  private def representedArgument(head: JitHead): NativeArgument = head match
    case JitHead.Represented(_, value) => NativeArgument.Represented(value)
    case other                         =>
      throw IllegalStateException(s"a decoded head is a ${other.name}")

  /** Each combination of the arguments' values at their places
    * (native_values/3).
    */
  private def nativeValues(
      arguments: Vector[JitValue],
      places: Vector[Place]
  ): Answers[ReadingState, Vector[NativeArgument]] =
    arguments
      .zip(places)
      .foldLeft(
        Answers.single[ReadingState, Vector[NativeArgument]](Vector.empty)
      ) { case (combinations, (argument, place)) =>
        combinations
          .flatMap(found => nativeValue(argument, place).map(found :+ _))
      }

  // ---- the codecs ----

  /** The heads `Represented(R, V)` of the values V the value decodes into by
    * the representation's codec (decoded_head/3).
    *
    * TODO (carried from jit.pl:287): a decoding that meets a constructor of R's
    * codec applied to its fields, untyped, at the top or at a field, reads the
    * fields and calls the native, and a codec constructor given a field not
    * ready keeps its fields for such a read (`git show
    * 675d169e4:lambda_jit/prolog/lambda_jit/jit.pl`, A CONSTRUCTOR READ, A
    * PENDING CONSTRUCTOR): it comes back only if a type filter is read to cover
    * the constructors written inside its operand. A fold's step reaches the
    * representation without it: the type check spells a function the program
    * passes, or a closure holds, by its contract, whose code filters the
    * function's argument and result (`StrategyDispatch`, a CONTRACT).
    */
  private def decodedHeads(
      representation: Representation,
      value: JitValue,
      applied: Boolean
  ): Stream =
    val point = DecodePoint(representation, value)
    computedStream(
      run.flatMap(current =>
        current.decodedPoints.found(point) match
          case Some(values) =>
            decodedPointHit(point, values).map(_ =>
              Answers
                .of[ReadingState, NativeValue](values)
                .map(represented(representation, _))
            )
          case None =>
            Computation.pure(
              pointRecorded(
                membersDecoded(representation, value),
                point,
                Vector.empty,
                true
              ).flatMap {
                case Right(decoded) =>
                  Answers.single(represented(representation, decoded))
                case Left((member, unread)) =>
                  unreadMember(
                    member,
                    operations.criterionOf(representation),
                    unread,
                    applied
                  )
              }
            )
      )
    )

  /** A member the decoding cannot read exactly, as the decode point gives it: a
    * member read as written (`Decoded.AsWritten`), the parallel of it with the
    * criterion, under arguments or not; a refuted one, under arguments
    * (`applied`), the parallel, the reference's reading, since the criterion's
    * other shapes can meet it there (`(zero ∥ binary_set false) v (λ_. v) (λ_.
    * v)` reads v), and read for its own normal form, no head, which is exact: a
    * normal form of the member has its constructor's shape and the criterion's
    * members other shapes, which are separable, so the parallel has no normal
    * form, and reading the criterion's members one by one need not end (`v ∥
    * nat_type` reads every natural).
    */
  private def unreadMember(
      member: JitValue,
      criterion: JitValue,
      unread: Decoded,
      applied: Boolean
  ): Stream =
    val asWritten = unread match
      case Decoded.AsWritten(_) => true
      case _                    => false
    if applied || asWritten then
      Answers.single(JitHead.Parallel(member, criterion))
    else Answers.empty

  /** The values a field's or a side's heads decode into, refuted when they give
    * none: a member with nothing read has no normal form.
    */
  private def unreadWhenEmpty(
      values: Answers[ReadingState, Decoded]
  ): Answers[ReadingState, Decoded] =
    Answers(values.pull.map {
      case None =>
        Some((Decoded.Refuted(), Answers.empty[ReadingState, Decoded]))
      case found => found
    })

  /** The members of the value decoded at the top, each head by itself: its
    * values, or, where its decoding cannot read it exactly (a constructor the
    * criterion excludes, a parallel whose sides decode apart, a field that
    * cannot be read, at any depth), the member itself (`Left`), which the
    * decode point gives as the parallel of it with the criterion, the
    * reference's reading of that member. Values it gave before are refinements
    * of the parallel (x ∥ T ⊑ d for each), so they add no answer beside it.
    */
  private def membersDecoded(
      representation: Representation,
      value: JitValue
  ): Answers[ReadingState, Either[(JitValue, Decoded), NativeValue]] =
    def member(found: JitValue)(
        decoded: Decoded
    ): Either[(JitValue, Decoded), NativeValue] = decoded match
      case Decoded.Read(read) => Right(read)
      case unread             => Left((found, unread))
    if heldAsWritten(representation) || FilteredFamily
        .criterionOf(representation)
        .isDefined
    then valueDecoded(representation, value, None, 0).map(member(value))
    else
      heads(value).flatMap(head =>
        headDecoded(representation, head, None, 0).map(
          member(memberValue(head, value))
        )
      )

  /** The member a head of the value stands for: the head itself where it is a
    * value, else the whole value, whose reading holds the head's.
    */
  private def memberValue(head: JitHead, value: JitValue): JitValue = head match
    case JitHead.NativeApplication(_, _, _, _) | JitHead.Elimination(_, _, _) =>
      value
    case _ => head.asValue

  /** A decode point found in the table: the lookup and each value it replays
    * charged a step, as an instance's hit is, so that a reading's values are
    * bounded by its budget, and the point completed in the young generation.
    */
  private def decodedPointHit(
      point: DecodePoint,
      values: Vector[NativeValue]
  ): Computation[ReadingState, Unit] =
    Computation(state =>
      val spent = state.budget.spent + 1 + values.size
      if spent > state.budget.bound then done(Computed.Stopped(state))
      else
        val current = JitRunState.of(state, configuration)
        val kept =
          if current.decodedPoints.young.contains(point) then current
          else
            current.copy(decodedPoints =
              current.decodedPoints
                .recorded(point, values, configuration.instanceRetention)
            )
        // The point's reads were noted for no instance reading this hit.
        done(
          Computed.Done(
            (),
            state.copy(
              budget = state.budget.copy(spent = spent),
              jitState = kept.traceMadeOpaque
            )
          )
        )
    )

  /** The values of a decode point as they come, recorded when they end. Only a
    * reading whose every pull stood outside a fallback point's check and
    * outside every table's evaluation is recorded. A cut inside a check depends
    * on the readings around it, which another context does not have
    * (`tabledInstance`). Inside a table's evaluation a re-entered table answers
    * with its approximation, so the values read there can be fewer than the
    * point's, and the iteration of that table's component reads them again.
    */
  private def pointRecorded(
      values: Answers[ReadingState, Either[(JitValue, Decoded), NativeValue]],
      point: DecodePoint,
      found: Vector[NativeValue],
      settled: Boolean
  ): Answers[ReadingState, Either[(JitValue, Decoded), NativeValue]] =
    Answers(
      Computation
        .state[ReadingState]
        .flatMap(state =>
          val current = JitRunState.of(state, configuration)
          val stillSettled =
            settled && current.readingPath == ReadingPath
              .Empty() && !current.instanceTables.inProgress && !state.tables.inProgress
          values.pull.flatMap {
            case None if stillSettled =>
              runModified(after =>
                after.copy(decodedPoints =
                  after.decodedPoints
                    .recorded(point, found, configuration.instanceRetention)
                )
              ).map(_ => None)
            case None                       => Computation.pure(None)
            case Some((Right(value), rest)) =>
              Computation.pure(
                Some(
                  (
                    Right(value),
                    pointRecorded(rest, point, found :+ value, stillSettled)
                  )
                )
              )
            // A point with a member read as the parallel is not recorded: the memo replays values only.
            case Some((member, rest)) =>
              Computation
                .pure(Some((member, pointRecorded(rest, point, found, false))))
          }
        )
    )

  /** The values the term decodes into at the field depth, from each of its
    * heads, the decoding numbered when a head is first applied to the cases
    * (value_decoded/5).
    */
  private def valueDecoded(
      representation: Representation,
      term: JitValue,
      decoding: Option[Long],
      level: Int
  ): Answers[ReadingState, Decoded] =
    def held(found: Option[NativeValue]): Answers[ReadingState, Decoded] =
      Answers.single(found.fold(Decoded.Refuted())(Decoded.Read(_)))
    if heldAsWritten(representation) then
      computedAnswers(unreadField(term).map(held))
    else
      FilteredFamily.criterionOf(representation) match
        // A generic single-layer ADT's field: the layer is a storage only when the field is written `f ∥ F`, the layer
        // `C (f1 ∥ F1) … ∥ T` with fields that need not be storages already; any other field leaves the layer as
        // written, since `C (f ∥ F) ∥ T` is below `C f ∥ T` in ⊑_O: `(some I ∥ T) I (λa. a)`, T = `some F + none`,
        // has the answer I by the β rule and the λ-lattice laws, and `some (I ∥ F) ∥ T` none when I is not in F.
        case Some(filter) =>
          operations.filteredAlready(term, filter) match
            case Some(field) => computedAnswers(unreadField(field).map(held))
            case None        => Answers.single(Decoded.AsWritten(None))
        case None =>
          term match
            // A field that is itself this representation's decode point: its members decoded here, so that one its
            // criterion refutes refutes the layer around it, which a reading of the field's heads would drop unseen;
            // one answer or the layer as written, as below.
            case JitValue.Parallel(inner, criterion)
                if Value.same(
                  operations.criterionOf(representation),
                  criterion
                ) =>
              computedAnswers(
                firstDistinct(
                  membersDecoded(representation, inner).map(
                    _.fold(_._2, Decoded.Read(_))
                  ),
                  2,
                  Vector.empty
                ).map {
                  case Vector(answer) => Answers.single(answer)
                  case Vector()       => Answers.empty
                  case _              => Answers.single(Decoded.AsWritten(None))
                }
              )
            // A layer is a storage only when its field decodes to exactly one answer, which then stands for the
            // field: a field of several heads, or of one head that decodes to several values (one abstraction
            // `λz e o. z + o zero` is zero + one), leaves its layer as written, since `C (a + b)` is not `C a + C b`
            // (application distributes over a choice in its function only), and a field that is a type, such as N
            // in `N ∥ N` where a case meets a list type's cons case, has infinitely many members below it. At most
            // two heads and two answers are pulled, so a field whose heads do not end is not read to its end.
            // FIXME: a specialized family's field of one value is decoded layer by layer, so a decode point reads https://github.com/Atry/private-overlay/issues/2238
            // a value written as layers to its end, an O(n) conversion, where a specialized storage is one when its
            // fields are storages of their families already, any other layer as written, and a filter point reads no
            // O(n). Exact (a field whose decoding gives one value is that value by the family's pattern theorem), so
            // no answer is lost; it stands until typed rounds write literals in the unique spelling, an intermediate
            // step of the blueprint.
            case _ =>
              computedAnswers(
                firstDistinct(heads(term), 2, Vector.empty).flatMap {
                  case Vector(only) =>
                    firstDistinct(
                      headDecoded(representation, only, decoding, level),
                      2,
                      Vector.empty
                    ).map {
                      case Vector(answer) => Answers.single(answer)
                      case Vector()       => Answers.empty
                      case _ => Answers.single(Decoded.AsWritten(None))
                    }
                  case Vector() => Computation.pure(Answers.empty)
                  case _        =>
                    Computation.pure(Answers.single(Decoded.AsWritten(None)))
                }
              )

  /** The first `count` distinct answers of the stream, or all it has when it
    * has fewer, pulling no further.
    */
  private def firstDistinct[Answer](
      answers: Answers[ReadingState, Answer],
      count: Int,
      found: Vector[Answer]
  ): Computation[ReadingState, Vector[Answer]] =
    if found.size >= count then Computation.pure(found)
    else
      answers.pull.flatMap {
        case None               => Computation.pure(found)
        case Some((next, rest)) =>
          firstDistinct(
            rest,
            count,
            if found.contains(next) then found else found :+ next
          )
      }

  /** A field of a family that holds it as written; none when it holds a case of
    * a decoding, which must not leave the decoding: that value is no value of
    * the family it was read at, and has no answer. The values the check found
    * free of a case are kept in the run state (`JitRunState.caseFree`), so that
    * a later check stops at them.
    */
  private def unreadField(
      term: JitValue
  ): Computation[ReadingState, Option[NativeValue]] =
    run.flatMap(current =>
      val walk = JitValues.caseWalk(
        term,
        current.caseFree,
        configuration.instanceRetention
      )
      runModified(found =>
        found.copy(
          caseFree = walk.caseFree.getOrElse(found.caseFree),
          counts = found.counts.copy(decodingCaseVisits =
            found.counts.decodingCaseVisits + walk.visits
          )
        )
      ).map(_ => walk.caseFree.map(_ => NativeValue.Unread(term)))
    )

  /** The values a head decodes into, a member the decoding cannot read exactly
    * refuted or as written (`Decoded`).
    */
  private def headDecoded(
      representation: Representation,
      head: JitHead,
      decoding: Option[Long],
      level: Int
  ): Answers[ReadingState, Decoded] =
    head match
      case JitHead.Represented(found, value) =>
        if found == representation then Answers.single(Decoded.Read(value))
        else
          encodedHeads(found, value).flatMap(
            headDecoded(representation, _, decoding, level)
          )
      case _ =>
        computedAnswers(
          numbered(decoding).map(number =>
            casesApplied(representation, head, number, level).flatMap(
              answerDecoded(representation, _, number, level)
            )
          )
        )

  // FIXME: a decode point keeps a list's items unevaluated, so the storage it https://github.com/Atry/private-overlay/issues/2213
  // hands out may hold an open item or the JIT's own layer (a sharing cell, an
  // evaluation passed on): a storage that is no instruction, against #2163
  // B1's "a storage is a closed term".
  /** The decoding's number: the one given, or the next, counted. */
  private def numbered(
      decoding: Option[Long]
  ): Computation[ReadingState, Long] = decoding match
    case Some(number) => Computation.pure(number)
    case None         =>
      run.flatMap(current =>
        countsModified(counts => counts.copy(decodings = counts.decodings + 1))
          .map(_ => current.counts.decodings)
      )

  private def casesApplied(
      representation: Representation,
      head: JitHead,
      decoding: Long,
      level: Int
  ): Stream =
    val number = Decoding.Numbered(decoding)
    val cases: Vector[JitValue] = representation match
      case Representation.Data(familyIdentity, parameter) =>
        dataFamily(familyIdentity).decodingCases(number, level, parameter)
      case Representation.ListOf(_) =>
        val (first, second) = ListCodec.decodingCases[C](number, level)
        Vector(first, second)
      case Representation.ArrayListOf(_) =>
        throw IllegalStateException(
          "an array list is decoded as the list it is β-equal to, never by cases of its own"
        )
    headApplied(head, cases.toList)

  /** The value a head of a value applied to the cases reads (answer_decoded/5).
    *
    * An item is kept as it is, with no check here that it mentions no case of
    * the decoding, which the decoding's argument needs
    * (`gezi.weakhead.ListCodec`, WHY A DECODED LIST STANDS FOR THE FILTERED
    * VALUE): the decode point checks each value it takes
    * (`checkedDecodePointHeads`, `heldDecodings`), so that a value that passes
    * its own case to its cons case, such as (λn c. c n nil) ∥ list_type (λy.
    * y), is read as the parallel it is rather than as a list holding the
    * decoding's neutral value.
    */
  private def answerDecoded(
      representation: Representation,
      answered: JitHead,
      decoding: Long,
      level: Int
  ): Answers[ReadingState, Decoded] =
    answered match
      // The values both sides read; and the member read as written when the sides read apart (two values that
      // differ as JIT values can share a normal form) or a side has one so, refuted when a side has one refuted.
      case JitHead.Parallel(left, right) =>
        computedAnswers(
          for
            leftValues <- sideValues(representation, left, decoding, level)
            rightValues <- sideValues(representation, right, decoding, level)
          yield
            def read(values: Vector[Decoded]): Vector[NativeValue] =
              values.collect { case Decoded.Read(value) => value }.distinct
            val leftRead = read(leftValues)
            val rightRead = read(rightValues)
            val sides = leftValues ++ rightValues
            val asWritten = sides.exists {
              case Decoded.AsWritten(_) => true
              case _                    => false
            }
            val unread: Option[Decoded] =
              if asWritten || leftRead.toSet != rightRead.toSet then
                Some(Decoded.AsWritten(None))
              else
                Option.when(sides.contains(Decoded.Refuted()))(
                  Decoded.Refuted()
                )
            Answers.of(
              leftRead.filter(rightRead.contains).map(Decoded.Read(_)) ++ unread
            )
        )
      case JitHead.NativeApplication(instruction, _, _, arguments) =>
        genericApplied(instruction, arguments).flatMap(
          answerDecoded(representation, _, decoding, level)
        )
      case JitHead.Elimination(found, value, cases) =>
        eliminationEncoded(found, value, cases).flatMap(
          answerDecoded(representation, _, decoding, level)
        )
      case other => readingDecoded(representation, other, decoding, level)

  private def sideValues(
      representation: Representation,
      side: JitValue,
      decoding: Long,
      level: Int
  ): Computation[ReadingState, Vector[Decoded]] =
    unreadWhenEmpty(
      heads(side).flatMap(answerDecoded(representation, _, decoding, level))
    ).collected

  /** The value a codec reads of an answered head (case_read/5 and
    * reading_decoded/5); refuted for a head that is no case of this decoding or
    * a constructor the criterion excludes (`zero ∥ binary_set false`), which a
    * context consuming the parallel can still read an answer of (`(zero ∥
    * binary_set false) a b c` when the three cases agree).
    */
  private def readingDecoded(
      representation: Representation,
      answered: JitHead,
      decoding: Long,
      level: Int
  ): Answers[ReadingState, Decoded] =
    val number = Decoding.Numbered(decoding)
    (representation, answered) match
      case (
            Representation.Data(familyIdentity, parameter),
            JitHead.Neutral(
              DataCase(`number`, `level`, caseFamily, constructor),
              arguments
            )
          )
          if caseFamily == familyIdentity && !constructorExcluded(
            familyIdentity,
            parameter,
            constructor
          ) &&
            arguments.size == dataFamily(familyIdentity)
              .constructors(parameter)(constructor)
              .fields
              .size =>
        val family = dataFamily(familyIdentity)
        def built(fields: Vector[NativeValue]): NativeValue =
          family.built(parameter, DataLayer(constructor, fields))
        def fieldDecoded(
            field: DataField,
            argument: JitValue
        ): Answers[ReadingState, Decoded] =
          unreadWhenEmpty(
            valueDecoded(
              field.representation(parameter),
              argument,
              Some(decoding),
              level + 1
            )
          )
        // A layer of no field and of one, the naturals' and the booleans', is
        // read with no stream of field vectors between, as the codecs read it.
        // A field unread leaves the layer unread the same way.
        def layer(fields: Either[Decoded, Vector[NativeValue]]): Decoded =
          fields.fold(identity, values => Decoded.Read(built(values)))
        def appended(
            fields: Either[Decoded, Vector[NativeValue]],
            field: Decoded
        ): Either[Decoded, Vector[NativeValue]] =
          (fields, field) match
            case (Right(values), Decoded.Read(value)) => Right(values :+ value)
            case (Right(_), unread)                   => Left(unread)
            case (unread, _)                          => unread
        family.constructors(parameter)(constructor).fields.zip(arguments) match
          case Vector() => Answers.single(Decoded.Read(built(Vector.empty)))
          case Vector((field, argument)) =>
            fieldDecoded(field, argument).map(decoded =>
              layer(appended(Right(Vector.empty), decoded))
            )
          case several =>
            several
              .foldLeft(
                Answers
                  .single[ReadingState, Either[Decoded, Vector[NativeValue]]](
                    Right(Vector.empty)
                  )
              ) { case (decoded, (field, argument)) =>
                decoded.flatMap {
                  case Right(values) =>
                    fieldDecoded(field, argument).map(
                      appended(Right(values), _)
                    )
                  case unread => Answers.single(unread)
                }
              }
              .map(layer)
      case (
            Representation.ListOf(_),
            JitHead.Neutral(
              ListCase(`number`, `level`, ListConstructor.Nil),
              arguments
            )
          ) if arguments.isEmpty =>
        Answers.single(
          Decoded.Read(
            NativeValue.Listed(ListRepresentation.Items(0, Vector.empty))
          )
        )
      case (
            Representation.ListOf(element),
            JitHead.Neutral(
              ListCase(`number`, `level`, ListConstructor.Cons),
              Vector(item, tail)
            )
          ) =>
        // One layer looked at: a storage only when the cell is in the unique spelling (`StorageEncoding.cellSpelled`,
        // the item `i ∥ E` or a storage of E, the tail `t ∥ L` or a storage of the list), so that its view is the
        // member itself: an O(1) step has every layer but the outermost made already, read in no O(n) walk, and fields
        // that are all storages already are asked of the natives' specialized types, not of every single-layer ADT. Any
        // other cell is read as written,
        // the parallel (its layer is what `writtenCell` asks of it again): a cell with its fields filtered in is below the
        // member in ⊑_O and drops the meeting of the value's cons case with the type's nil case,
        // `(cons I nil ∥ list_type nat_type) I (λa b. a)` having the answer I.
        val layer = NativeValue.Listed(ListRepresentation.Cell(item, tail))
        if operations.cellSpelled(item, tail, representation) then
          Answers.single(Decoded.Read(layer))
        else Answers.single(Decoded.AsWritten(Some(layer)))
      case _ => Answers.single(Decoded.Refuted())

  /** The heads of the term the value of the representation stands for, one
    * layer, the encoding counted (encoded_head/3).
    */
  private def encodedHeads(
      representation: Representation,
      value: NativeValue
  ): Stream =
    Answers(
      countsModified(counts => counts.copy(encodings = counts.encodings + 1))
        .flatMap(_ =>
          (representation, value) match
            case (_, NativeValue.Stored(term)) =>
              val constructed = (term match
                case JitValue.Stored(storage) =>
                  StorageOf.constructed[C](storage)
                case _ => None
              ).getOrElse(
                throw IllegalStateException(
                  s"a stored declared value is no declared family's storage: $term"
                )
              )
              genericApplied(
                operations.constructorDefine(
                  representation,
                  constructed.constructor
                ),
                constructed.fields
              ).pull
            case (Representation.Data(familyIdentity, parameter), _) =>
              val family = dataFamily(familyIdentity)
              val DataLayer(constructor, fields) =
                family.layer(parameter, value)
              genericApplied(
                pureTerm(
                  facts.constructorDefine(
                    family.constructors(parameter)(constructor).native
                  )
                ),
                fieldValues(family, parameter, constructor, fields)
              ).pull
            case (
                  Representation.ListOf(_),
                  NativeValue.Listed(ListRepresentation.Items(0, _))
                ) =>
              genericApplied(pureTerm(facts.nil), Vector.empty).pull
            case (
                  Representation.ListOf(element),
                  NativeValue.Listed(ListRepresentation.Cell(item, tail))
                ) =>
              genericApplied(
                pureTerm(facts.cons),
                Vector(parallel(item, element), tail)
              ).pull
            case (
                  Representation.ArrayListOf(_),
                  listed: NativeValue.ArrayListed
                ) =>
              if listed.nil then
                genericApplied(pureTerm(facts.nil), Vector.empty).pull
              else
                genericApplied(
                  pureTerm(facts.cons),
                  arrayListFields(representation, listed)
                ).pull
            case _ =>
              throw IllegalStateException(
                s"a value of another representation than ${representation.familyIdentity.shown}"
              )
        )
    )

  /** The encoding of the value applied to the cases (elimination_encoded/4). */
  private def eliminationEncoded(
      representation: Representation,
      value: NativeValue,
      cases: Vector[JitValue]
  ): Stream =
    encodedHeads(representation, value).flatMap(headApplied(_, cases.toList))

  // ---- the readers' end of a block ----

  /** The native-bound define that heads the application spine and its
    * arguments, in order; none when no bound define heads it. The spine stops
    * at the first bound define, which may itself be an application.
    */
  @scala.annotation.tailrec
  private def boundSpine(
      value: JitValue,
      arguments: List[JitValue]
  ): Option[(Term, Vector[JitValue])] =
    value match
      case JitValue.IrTerm(define) if operations.bound(Value.of(define)) =>
        Some((define, arguments.toVector))
      case JitValue.Apply(function, argument) =>
        boundSpine(function, argument :: arguments)
      case _ => None

  /** The parallel sets the JIT hands a reader for its head
    * (jit_observed_head/2), one O(1) step on the head itself and none on its
    * fillings, which are the readers' values already, the JIT and the readers
    * holding the same objects:
    *   - a storage: its one-layer view's value `C ȳ` read to its heads, the
    *     view read with the capability and counted as an encoding;
    *     `C ȳ ∥ T ≃_O C ȳ` by the unique spelling's pattern theorem (proofs,
    *     section 23), whose premise is the backend's obligation;
    *   - an elimination of a storage and a native's application: evaluated on
    *     to their heads, as any application is;
    *   - a lambda or a neutral head: handed over as it is, its fillings
    *     unconverted;
    *   - the JIT's parallel head: each side read and their parallel sets
    *     paired;
    *   - the empty parallel set: the reader's empty parallel set.
    */
  def observed(head: JitHead): Answers[ReadingState, ParallelSet] =
    given gezi.ir.StorageAccess = configuration.storageAccess
    head match
      // A storage reached here is one the reading did not hand over whole (`NormalForms.termRead` hands those over,
      // their views not read): its one-layer view is read under this configuration, on demand, and its fields stay
      // storages or the terms it holds as written, read further only as a reading asks for them.
      case storage: RepresentedStorage[?] =>
        val value =
          Value.of((configuration.specializer: C).viewOf(storage).value)
        // The view's value `C ȳ` is read through the constructor's term, as the reader reads it: dispatched to its
        // native, `C` applied to storages would fold back into this very storage, and the reading would not end.
        boundSpine(value, Nil) match
          case Some((constructor, arguments)) =>
            Answers(
              countsModified(counts =>
                counts.copy(encodings = counts.encodings + 1)
              ).flatMap(_ =>
                genericApplied(constructor, arguments).flatMap(observed).pull
              )
            )
          case None => heads(value).flatMap(observed)
      case gezi.jit.Elimination(representation, value, cases) =>
        eliminationEncoded(representation, value, cases).flatMap(observed)
      case gezi.jit.NativeApplication(instruction, _, _, arguments) =>
        genericApplied(instruction, arguments).flatMap(observed)
      case gezi.ir.Thunk(code, holes, fillings) =>
        Answers.single(ParallelSet.single(Head.Lambda(code, holes, fillings)))
      case gezi.weakhead.Neutral(variable, arguments) =>
        Answers.single(ParallelSet.single(Head.Neutral(variable, arguments)))
      case ParallelHead(left, right) =>
        heads(left)
          .flatMap(observed)
          .distinct
          .flatMap(leftSet =>
            heads(right).flatMap(observed).distinct.map(leftSet.parallel)
          )
          .distinct
      case EmptyParallel => Answers.single(ParallelSet.bottom)
