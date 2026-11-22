package gezi.jit

import gezi.weakhead.JitState
import gezi.weakhead.AnswerSet
import gezi.weakhead.ReadingState
import gezi.weakhead.Tables
import gezi.ir.Code

/** The costs the JIT counts (jit_native_counts/2, jit_native_call_count/2,
  * jit_encoding_count/1): costs only, which no answer depends on.
  *
  * @param nativeCalls
  *   the calls of every native
  * @param callsByNative
  *   the calls of each native, by its implementation's name
  * @param decodings
  *   the decodings that applied a head to their codec's cases, which also
  *   number the decodings
  * @param encodings
  *   the layers of represented values encoded
  * @param syntaxReads
  *   the layers of terms the JIT read (`SyntaxRead`): by
  *   the machine, which also charges a step for each, and by the checks of
  *   decode points, fallback points, type-filtered constructors and natives'
  *   arguments, which charge none. It stands in for the inferences the
  *   Prolog tests measured on those checks (jit_natives.plt,
  *   a_lists_tail_is_kept_as_written_and_filtered_once).
  *
  *   A read is counted where a value that is an instruction is read one
  *   layer through `JitRules.layer` (`layerOf`, the machine's evaluation):
  *   the program's syntax, and as well a value the JIT built that equals an
  *   instruction by content, which is that instruction, one object in the
  *   pool. A value of any other layer is read with none. A check that
  *   matches a value's constructor directly, without `layer`, counts none
  *   either, whether the value is an instruction or not.
  * @param decodingCaseVisits
  *   the nodes visited to check that a field kept unread holds no case of a
  *   decoding (`JitValues.caseWalk`)
  */
final case class JitCounts(
    nativeCalls: Long,
    callsByNative: Map[NativeName, Long],
    decodings: Long,
    encodings: Long,
    syntaxReads: Long,
    decodingCaseVisits: Long
):

  /** The count of the calls of the native. */
  def callsOf(native: NativeName): Long = callsByNative.getOrElse(native, 0L)

/** No cost counted. */
object JitCounts:
  val empty: JitCounts = JitCounts(0, Map.empty, 0, 0, 0, 0)

/** A reading of a fallback point's operand in a representation, among the
  * readings in progress around a reading (jit.pl, THE READING OF AN
  * INFINITE VALUE).
  */
final case class OperandReading(representation: Representation, operand: JitValue)

/** The readings in progress around a reading, as Brent's cycle detection
  * keeps them (path_extended/3): none, or the reading at the last power of
  * two along the nested readings, the readings since and the power.
  */
enum ReadingPath:
  case Empty
  case Path(tortoise: OperandReading, steps: Int, power: Int)

  /** The path extended by the reading, or nothing when the reading is the
    * tortoise in spelling (R. P. Brent, "An improved Monte Carlo
    * factorization algorithm", BIT 20, 1980, doi:10.1007/bf01933190).
    */
  def extended(reading: OperandReading): Option[ReadingPath] = this match
    case Empty => Some(Path(reading, 1, 1))
    case Path(tortoise, steps, power) =>
      if reading == tortoise then None
      else if steps == power then Some(Path(reading, 1, 2 * power))
      else Some(Path(tortoise, steps + 1, power))

/** The JIT's part of a reading's state: what the Prolog JIT kept in the
  * process and the thread, here a value the reading threads.
  *
  * @param configuration
  *   the configuration the compiled codes were compiled under; a state of
  *   another configuration is not read (a fresh one is taken in its place)
  * @param compiled
  *   the cache: each code's compiled form the state took, by code (jit.pl,
  *   THE CACHE AND THE LINKS), compiled for it or, when its readings share
  *   their memos, found in the cache service (`CompiledCodes`); the JIT's
  *   compilation budget bounds how many
  * @param compilationOrder
  *   the codes of `compiled`, in the order the state took them
  * @param counts
  *   the costs counted
  * @param readingPath
  *   the readings of fallback points' operands in progress
  * @param instanceTables
  *   the instance table under `JitConfiguration.instanceTable`, by each
  *   instance's code and fillings (`TabledInstance`): the tables of the
  *   tabled function whose body is an instance's own reading (`Tabling`,
  *   `Jit.instanceTabling`), the complete ones being the table's young
  *   generation. Between two readings, and between the heads a reading gives
  *   outside every instance, it holds complete tables only
  *   (`Tabling.answers`)
  * @param olderInstances
  *   the table's old generation under `InstanceRetention.Generations`: the
  *   young generation's complete tables as they were when they last reached
  *   the generation's size (`Jit.instance`), so that the table holds at most
  *   twice that many entries however long the reader's JVM runs; empty under
  *   `InstanceRetention.NeverDropped`. An entry found here is
  *   completed in the young generation again, so an instance met in every
  *   generation stays. Dropping a generation changes only cost (CONTRIBUTING.md, "Tables"): a dropped instance is read again.
  * @param criteria
  *   the decoding criteria read so far, by the criterion's instruction: the
  *   representation the criterion's syntax names, or none
  *   (`JitRules.decodingCriterionRead`, a pure function of the instruction under
  *   the configuration and of the instruction's layers), so that each is read once and not at every
  *   decode point, fallback point or native argument that meets it. They are
  *   the syntax of filters written in the term, never a fact about a value.
  *   Measured on a probe (not committed, 2026-11-01): `nat_fold` of k
  *   negations of a 16-bit word, each argument a fallback point under
  *   `int16_type`, the negation a native; at k = 10, 20 and 40,
  *   `JitRules.syntaxDecoded` was called 747, 1,427 and 2,787 times before
  *   this table and 67 times at every k after it (the one read of
  *   `int16_width` and of the word's literal), with the same steps and
  *   native calls
  * @param tableCosts
  *   for each code the table has seen, how many of its instances were read
  *   into the table, the steps their readings spent, and how many were taken
  *   from it and the steps their lookups were charged (`TableCost`), so
  *   that a code whose hits save less than its lookups cost stops being
  *   tabled; costs, never a type, kept across the readings of a suite
  * @param cuts
  *   how many readings of fallback points' operands were cut so far because
  *   they recurred (`ReadingPath.extended` gave nothing): a count, never a
  *   type, that the reading itself does not read; a test reads it to tell
  *   that its programs cut (`NativeRouteCompilationTest`), the case where a
  *   check's heads are its own and the table keeps out of it
  *   (`Jit.tabledInstance`)
  * @param blockRecord
  *   the costs of the native blocks each code ran so far (`BlockRecord`,
  *   `JitRules.blockEntered`), from which the configuration's mechanism
  *   decides entries and retirements (`NativeBlockMechanism.entered`);
  *   costs, never a type
  * @param blockArtifacts
  *   the compiled form the mechanism keeps for each code it ran a block of
  *   (`BlockArtifact`, `NativeBlockMechanism.run`): a pure function of the
  *   code and of the configuration this state belongs to, never a judgment
  *   about a value
  * @param caseFree
  *   the values known to hold no case of a decoding (`CaseFreeValues`), a
  *   pure function of each value and never a fact about its type
  * @param decodedPoints
  *   the values of the decode points read to their end (`DecodedPoints`)
  */
final case class JitRunState(
    configuration: JitConfiguration,
    compiled: Map[Code, CompiledCode],
    compilationOrder: Vector[Code],
    counts: JitCounts,
    readingPath: ReadingPath,
    instanceTables: Tables[ReadingState, TabledInstance, JitHead] = Tables.empty,
    olderInstances: Map[TabledInstance, AnswerSet[JitHead]] = Map.empty,
    criteria: Map[gezi.ir.Instruction, Option[Representation]] = Map.empty,
    tableCosts: Map[Code, TableCost] = Map.empty,
    cuts: Long = 0,
    blockRecord: BlockRecord = BlockRecord.empty,
    blockArtifacts: Map[Code, BlockArtifact] = Map.empty,
    lastCheckpointSpent: Long = 0,
    caseFree: CaseFreeValues = CaseFreeValues.empty,
    decodedPoints: DecodedPoints = DecodedPoints.empty
) extends JitState:

  /** This state without the instance table's answers, its young and its old
    * generation, and the values of its decode points, all read through the
    * expansions of the URI nodes they met; the compiled codes, blocks and
    * criteria, read off syntax alone (a URI node has no layer to read,
    * `Jit.layerOf`), and the costs are kept.
    */
  def withoutAnswers: JitState =
    copy(instanceTables = Tables.empty, olderInstances = Map.empty, decodedPoints = DecodedPoints.empty)

  /** The steps spent since the last instance the table recorded
    * (`lastCheckpointSpent`, a reading's spent steps then), given the steps
    * the reading has spent now (`InstanceCheckpoints`).
    * The table is kept from one reading to the next while each reading
    * counts its steps from zero, so a reading that has spent fewer steps
    * than the last checkpoint is a later reading, and its steps are all
    * since the checkpoint.
    */
  def stepsSinceCheckpoint(spent: Long): Long =
    if spent >= lastCheckpointSpent then spent - lastCheckpointSpent else spent

/** A decode point `x ∥ C`: the representation its criterion names and the
  * term x.
  */
final case class DecodePoint(representation: Representation, term: JitValue)

/** The values of the decode points read to their end: the table of the heads
  * of the term `x ∥ C`, a pure function of the term as the instance table's
  * entries are, whose emptying changes only how many steps a later reading
  * takes (`CONTRIBUTING.md`, "Tables"). It is kept in two generations, as the
  * instance table is (`InstanceRetention`), a value found in the older
  * generation being completed in the young one again.
  */
final case class DecodedPoints(
    young: Map[DecodePoint, Vector[NativeValue]],
    older: Map[DecodePoint, Vector[NativeValue]]
):

  /** The values of the point, if it was read to its end. */
  def found(point: DecodePoint): Option[Vector[NativeValue]] = young.get(point).orElse(older.get(point))

  /** These points with the values of the point recorded. */
  def recorded(point: DecodePoint, values: Vector[NativeValue], retention: InstanceRetention): DecodedPoints =
    retention match
      case InstanceRetention.Generations(size) if young.size >= size && !young.contains(point) =>
        DecodedPoints(Map(point -> values), young)
      case InstanceRetention.Generations(_) | InstanceRetention.NeverDropped =>
        copy(young = young.updated(point, values))

object DecodedPoints:

  /** No point read. */
  val empty: DecodedPoints = DecodedPoints(Map.empty, Map.empty)

/** A code's use of the instance table: the instances read into it, the
  * steps their readings spent, the instances taken from it, the steps
  * charged for the lookups of both (their keys' nodes, `JitRules.instance`),
  * and the misses that opened a table (`missesOpened`).
  *
  * FIXME (2026-11-02): an entry is counted when its reading finishes, so https://github.com/Atry/private-overlay/issues/1941
  * the instances of one code nested in each other's readings are not judged
  * until the innermost finishes, and the cutoff does not apply to them.
  * MEASURED (a probe that is not committed, CPUs 2 and 3, the published
  * repeated_library_unshared_doublings/direct/repetitions_8 read by the JIT
  * with dispatch and the table on): one code had 38,728 entries and no hit,
  * 24,723,132 steps in all. Counting an entry when its reading starts cut
  * that code off at 64 entries (770 instances in the table, 24,606,039
  * steps), but it also cut off the longest common subsequence's cell code
  * before its first hit, which comes only when a cell's second branch meets
  * a cell the first finished: the steps a cell at n = 100 went from 157 to
  * beyond 19,605 (the budget of 2 * 10^8 steps exceeded). A candidate:
  * judge a code on its finished entries only, and count the open ones
  * against a depth bound of their own.
  */
final case class TableCost(entries: Long, entrySteps: Long, hits: Long, lookupSteps: Long, missesOpened: Long):

  /** The cost after one more instance read into the table, its lookup
    * charged the key's nodes and its reading having spent the steps.
    */
  def entered(keyNodes: Int, steps: Long): TableCost =
    assert(steps >= 0, s"a reading's spent steps never decrease: $steps")
    copy(entries = entries + 1, entrySteps = entrySteps + steps, lookupSteps = lookupSteps + keyNodes)

  /** The cost after one more miss that enters the instance table, an
    * instance found in no complete table, which opens its table or reads it
    * while it is open (an instance met again inside its own reading),
    * counted where the miss enters the table (`JitRules.tabledInstance`);
    * a miss run untabled (not recorded, or inside a fallback point's
    * check) enters no table and is not counted. `entered` counts a miss when
    * its heads end with the table complete. The instances of one code
    * nested in each other's readings all miss before the innermost
    * finishes, so a policy that must act while they are still open reads
    * this count: `missesOpened - entries` misses of the code have not
    * finished, being open or left unfinished by a stop. A miss is counted
    * before it can finish, so `missesOpened >= entries`.
    */
  def missOpened: TableCost = copy(missesOpened = missesOpened + 1)

  /** The cost after one more instance taken from the table, its lookup
    * charged the key's nodes.
    */
  def hit(keyNodes: Int): TableCost = copy(hits = hits + 1, lookupSteps = lookupSteps + keyNodes)

  /** Whether the table costs the code more than it saves, after `trial`
    * entries (`JitConfiguration.instanceTableTrial`): the hits save the
    * steps of an entry's reading each on average, fewer than the steps
    * charged for the lookups.
    */
  def unprofitable(trial: Long): Boolean =
    entries >= trial && hits * entrySteps < entries * lookupSteps

/** No use of the table yet, and the fewest entries a code is judged on.
  *
  * FIXME (2026-11-01): the test of `TableCost.unprofitable` takes a lookup's https://github.com/Atry/private-overlay/issues/1942
  * charged step to cost the wall time of a reading's step, which is not
  * measured, and `trial` is a choice. The costs persist across the readings
  * of a suite (`JitRunState.of` keeps them), so a code judged unprofitable
  * in one point is never tabled again in the run, even where its later
  * instances would be read again.
  */
object TableCost:
  val none: TableCost = TableCost(0, 0, 0, 0, 0)
  val trial: Long = 64

/** An instance of a code: the code with no hole left and its fillings, a
  * key of `JitRunState.instanceTables`. The table takes two instances with one
  * key, under one configuration, to have the same heads: a code's clauses
  * read its fillings, and the arguments are applied to its heads outside the
  * table. The JIT's state shapes heads in one place, a fallback point's
  * check in progress (`ReadingPath`), so no instance is tabled or taken from
  * the table while the path is not empty (`JitRules.instance`).
  *
  * The code and the fillings are interned terms (`gezi.ir.Interned`),
  * so two instances with equal fillings are one key however they were
  * built, and comparing two keys compares each filling by `==`, which ends
  * at `eq` or at a differing hash code; the hash, computed once when the key
  * is made, combines the fillings' hash codes, each computed when its
  * filling was made. Both cost the number of fillings, whatever their size,
  * and a lookup is charged that (`Jit.instance`). The hash codes are by
  * content, the same in every process; the table is only looked up and
  * updated, never iterated (`JitRunState.instanceTables`).
  *
  * No filling needs a key of its own. An `Evaluated` filling, the operand a
  * fallback point's check passes on with its heads, is an interned
  * constructor like every other value of the JIT (`JitLayer`): two equal
  * ones are one object, its hash code is computed when it is made, and `==`
  * compares it by its parts, each by `eq` or a differing hash code, at the
  * cost of its width as any filling.
  */
final case class TabledInstance(code: Code, fillings: Vector[JitValue]):

  /** The hash, computed once when the key is made: a key is looked up and
    * looked up in `JitRunState.instanceTables` and `JitRunState.olderInstances`
    * up to five times for one instance.
    */
  override val hashCode: Int = scala.util.hashing.MurmurHash3.productHash(this)

/** The JIT's part of a reading. */
object JitRunState:

  /** A fresh part for the configuration: an empty cache, no cost counted. */
  def fresh(configuration: JitConfiguration): JitRunState =
    JitRunState(configuration, Map.empty, Vector.empty, JitCounts.empty, ReadingPath.Empty)

  /** The JIT's part of the reading's state under the configuration, a fresh
    * one when the state holds none, or one of another configuration
    * (compared by reference: a configuration is built once and passed on).
    * A code identifier is the canonical object of its code, so a state's
    * cache holds for every later reading: this is how the tests f a, f b and
    * f c compile f's codes once (jit_strategies.pl,
    * THE TEST IS THE UNIT).
    *
    * FIXME: only the configuration is compared, while the instance tables and
    * the decode points (`instanceTables`, `olderInstances`, `decodedPoints`)
    * hold readings that depend on the state's `extremes`, which their keys
    * leave out. A state read under one set of known extremes and handed to a
    * reading under another would answer from the other's tables. No reading
    * does that today (each executor fixes its extremes); nothing enforces it.
    * Candidate fix: record the extremes in this part and give a fresh one when
    * they differ, as for another configuration.
    * https://github.com/Atry/private-overlay/issues/2086
    */
  def of(state: ReadingState, configuration: JitConfiguration): JitRunState = state.jitState match
    case found: JitRunState if found.configuration eq configuration => found
    case _                                                         => fresh(configuration)
