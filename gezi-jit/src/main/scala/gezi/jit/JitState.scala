package gezi.jit

import gezi.weakhead.JitState
import gezi.weakhead.AnswerSet
import gezi.weakhead.ReadingState
import gezi.weakhead.Tables
import gezi.ir.Code
import gezi.ir.{Configured, NativeSpecializer}

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
  *   the layers of terms the JIT read (`SyntaxRead`): by the machine, which
  *   also charges a step for each, and by the checks of decode points, fallback
  *   points, type-filtered constructors and natives' arguments, which charge
  *   none. It stands in for the inferences the Prolog tests measured on those
  *   checks (jit_natives.plt,
  *   a_lists_tail_is_kept_as_written_and_filtered_once).
  *
  * A read is counted where a value that is an instruction is read one layer
  * through `JitRules.layer` (`layerOf`, the machine's evaluation): the
  * program's syntax, and as well a value the JIT built that equals an
  * instruction by content, which is that instruction, one object in the pool. A
  * value of any other layer is read with none. A check that matches a value's
  * constructor directly, without `layer`, counts none either, whether the value
  * is an instruction or not.
  * @param decodingCaseVisits
  *   the nodes visited to check that a field kept unread holds no case of a
  *   decoding (`JitValues.caseWalk`)
  * @param fallbackChecks
  *   the checks of fallback points' operands run (`JitRules.fallbackOutcome`),
  *   a check whose heads a reading replays from `CheckedHeads` not counted
  *   again
  */
final case class JitCounts(
    nativeCalls: Long,
    callsByNative: Map[NativeName, Long],
    decodings: Long,
    encodings: Long,
    syntaxReads: Long,
    decodingCaseVisits: Long,
    fallbackChecks: Long
):

  /** The count of the calls of the native. */
  def callsOf(native: NativeName): Long = callsByNative.getOrElse(native, 0L)

/** No cost counted. */
object JitCounts:
  val empty: JitCounts = JitCounts(0, Map.empty, 0, 0, 0, 0, 0)

/** A reading of a fallback point's operand in a representation, among the
  * readings in progress around a reading (jit.pl, THE READING OF AN INFINITE
  * VALUE).
  */
final case class OperandReading[C <: NativeSpecializer & Singleton](
    representation: Representation[JitValue[C]],
    operand: JitValue[C]
)

/** The readings in progress around a reading, as Brent's cycle detection keeps
  * them (path_extended/3): none, or the reading at the last power of two along
  * the nested readings, the readings since and the power.
  */
enum ReadingPath[C <: NativeSpecializer & Singleton]:
  case Empty()
  case Path(tortoise: OperandReading[C], steps: Int, power: Int)

  /** Whether no reading is in progress. */
  def isEmpty: Boolean = this match
    case Empty()       => true
    case Path(_, _, _) => false

  /** The path extended by the reading, or nothing when the reading is the
    * tortoise in spelling (R. P. Brent, "An improved Monte Carlo factorization
    * algorithm", BIT 20, 1980, doi:10.1007/bf01933190).
    */
  def extended(reading: OperandReading[C]): Option[ReadingPath[C]] = this match
    case Empty()                      => Some(Path(reading, 1, 1))
    case Path(tortoise, steps, power) =>
      if reading == tortoise then None
      else if steps == power then Some(Path(reading, 1, 2 * power))
      else Some(Path(tortoise, steps + 1, power))

/** The JIT's part of a reading's state: what the Prolog JIT kept in the process
  * and the thread, here a value the reading threads.
  *
  * @param configuration
  *   the configuration the compiled codes were compiled under; a state of
  *   another configuration is not read (a fresh one is taken in its place)
  * @param compiled
  *   the cache: each code's compiled form the state took, by code (jit.pl, THE
  *   CACHE AND THE LINKS), compiled for it or, when its readings share their
  *   memos, found in the cache service (`CompiledCodes`); the JIT's compilation
  *   budget bounds how many
  * @param compilationOrder
  *   the codes of `compiled`, in the order the state took them
  * @param counts
  *   the costs counted
  * @param readingPath
  *   the readings of fallback points' operands in progress
  * @param instanceTables
  *   the instance table under `JitConfiguration.instanceTable`, by each
  *   instance's code and fillings (`TabledInstance`): the tables of the tabled
  *   function whose body is an instance's own reading (`Tabling`,
  *   `Jit.instanceTabling`), the complete ones being the table's young
  *   generation. Between two readings, and between the heads a reading gives
  *   outside every instance, it holds complete tables only (`Tabling.answers`)
  * @param olderInstances
  *   the table's old generation under `InstanceRetention.Generations`: the
  *   young generation's complete tables as they were when they last reached the
  *   generation's size (`Jit.instance`), so that the table holds at most twice
  *   that many entries however long the reader's JVM runs; empty under
  *   `InstanceRetention.NeverDropped`. An entry found here is completed in the
  *   young generation again, so an instance met in every generation stays.
  *   Dropping a generation changes only cost (CONTRIBUTING.md, "Tables"): a
  *   dropped instance is read again.
  * @param criteria
  *   the decoding criteria read so far, by the criterion's instruction: the
  *   representation the criterion's syntax names, or none
  *   (`JitRules.decodingCriterionRead`, a pure function of the instruction
  *   under the configuration and of the instruction's layers), so that each is
  *   read once and not at every decode point, fallback point or native argument
  *   that meets it. They are the syntax of filters written in the term, never a
  *   fact about a value. Measured on a probe (not committed, 2026-11-01):
  *   `nat_fold` of k negations of a 16-bit word, each argument a fallback point
  *   under `int16_type`, the negation a native; at k = 10, 20 and 40,
  *   `JitRules.syntaxDecoded` was called 747, 1,427 and 2,787 times before this
  *   table and 67 times at every k after it (the one read of `int16_width` and
  *   of the word's literal), with the same steps and native calls
  * @param tableCosts
  *   for each code the table has seen, how many of its instances were read into
  *   the table, the steps their readings spent, and how many were taken from it
  *   and the steps their lookups were charged (`TableCost`), so that a code
  *   whose hits save less than its lookups cost stops being tabled; costs,
  *   never a type, kept across the readings of a suite
  * @param cuts
  *   how many readings of fallback points' operands were cut so far because
  *   they recurred (`ReadingPath.extended` gave nothing): a count, never a
  *   type, that the reading itself does not read; a test reads it to tell that
  *   its programs cut (`NativeRouteCompilationTest`), the case where a check's
  *   heads are its own and the table keeps out of it (`Jit.tabledInstance`)
  * @param blockRecord
  *   the costs of the native blocks each code ran so far (`BlockRecord`,
  *   `JitRules.blockEntered`), from which the configuration's mechanism decides
  *   entries and retirements (`NativeBlockMechanism.entered`); costs, never a
  *   type
  * @param blockArtifacts
  *   the compiled form the mechanism keeps for each code it ran a block of
  *   (`BlockArtifact`, `NativeBlockMechanism.run`): a pure function of the code
  *   and of the configuration this state belongs to, never a judgment about a
  *   value
  * @param groupBlocks
  *   the group block of each thunk the group block mechanism was asked about,
  *   or none when it is no block (`GroupBlocks.compiled`): a pure function of
  *   the thunk's syntax and the configuration, carried from one reading to the
  *   next with the compiled codes, so that the later points of a family do not
  *   scan the thunk again; the young generation under the instance retention's
  *   `Generations` (`Jit`'s `groupBlockEntered`)
  * @param olderGroupBlocks
  *   the old generation of `groupBlocks`
  * @param caseFree
  *   the values known to hold no case of a decoding (`CaseFreeValues`), a pure
  *   function of each value and never a fact about its type
  * @param decodedPoints
  *   the values of the decode points read to their end (`DecodedPoints`)
  * @param checkedHeads
  *   the heads the uncut checks of fallback points found (`CheckedHeads`)
  * @param sharedTerms
  *   the closed canonical terms a slot read more than once was filled with
  *   (`SharedTerms`), each of which an evaluation reads through the instance
  *   table, always tabled
  * @param openTraces
  *   under `InstanceReuse.VerifiedAcrossVersions`, what the reading of each
  *   instance whose table is not complete read so far
  * @param verifiable
  *   under the same option, the tables completed or verified under this
  *   version, with what they read
  * @param earlierVerifiable
  *   under the same option, those of earlier versions, which answer nothing
  *   until they are verified (`Jit.verifiedOrRead`)
  * @param verifying
  *   under the same option, the instances whose tables of earlier versions are
  *   being verified now (`Jit.verificationOf`)
  * @param checkOpenings
  *   the open tables a fallback point's check opened, each with `cuts` as it
  *   was when the table opened (`checkOpened`), so that a table whose reading
  *   saw a cut is dropped when it completes (`componentCompleted`)
  * @param wastedGroupBlockSteps
  *   the steps the group blocks' entries and runs spent in this reading and
  *   gave no value for (a decoding that ran out or read no storage, a block
  *   that admitted no argument or stopped), all blocks together, which the
  *   mechanism's share of the reading's budget bounds
  *   (`Jit.groupBlockEntered`): a cost, never a type; an entry nested in
  *   another's decoding is counted again in the outer one's, which may only
  *   overcount
  * @param givenUpGroupBlocks
  *   the thunks whose group block this reading gave up, a decoding of their
  *   arguments having run out or their block stopped other than on a rejected
  *   row: a cost, never a type
  */
final case class JitRunState[C <: NativeSpecializer & Singleton](
    configuration: JitConfiguration[C],
    compiled: Map[Code, CompiledCode[C]],
    compilationOrder: Vector[Code],
    counts: JitCounts,
    readingPath: ReadingPath[C],
    instanceTables: Tables[ReadingState[C], TabledInstance[C], JitHead[C]] =
      Tables.empty[ReadingState[C], TabledInstance[C], JitHead[C]],
    olderInstances: Map[TabledInstance[C], AnswerSet[JitHead[C]]] =
      Map.empty[TabledInstance[C], AnswerSet[JitHead[C]]],
    criteria: Map[Configured[C], Option[Representation[JitValue[C]]]] =
      Map.empty[Configured[C], Option[Representation[JitValue[C]]]],
    tableCosts: Map[Code, TableCost] = Map.empty,
    cuts: Long = 0,
    blockRecord: BlockRecord = BlockRecord.empty,
    blockArtifacts: Map[Code, BlockArtifact] = Map.empty,
    groupBlocks: Map[Configured[C], Option[GroupBlockArtifact[C]]] =
      Map.empty[Configured[C], Option[GroupBlockArtifact[C]]],
    olderGroupBlocks: Map[Configured[C], Option[GroupBlockArtifact[C]]] =
      Map.empty[Configured[C], Option[GroupBlockArtifact[C]]],
    lastCheckpointSpent: Long = 0,
    caseFree: CaseFreeValues = CaseFreeValues.empty,
    decodedPoints: DecodedPoints[C] = DecodedPoints.empty[C],
    checkedHeads: CheckedHeads[C] = CheckedHeads.empty[C],
    sharedTerms: SharedTerms[C] = SharedTerms.empty[C],
    openTraces: Map[TabledInstance[C], ReadTrace[C]] =
      Map.empty[TabledInstance[C], ReadTrace[C]],
    verifiable: Map[TabledInstance[C], VerifiableTable[C]] =
      Map.empty[TabledInstance[C], VerifiableTable[C]],
    earlierVerifiable: Map[TabledInstance[C], VerifiableTable[C]] =
      Map.empty[TabledInstance[C], VerifiableTable[C]],
    verifying: Set[TabledInstance[C]] = Set.empty[TabledInstance[C]],
    checkOpenings: Map[TabledInstance[C], Long] =
      Map.empty[TabledInstance[C], Long],
    wastedGroupBlockSteps: Long = 0,
    givenUpGroupBlocks: Set[Configured[C]] = Set.empty[Configured[C]]
) extends JitState[C]:

  /** This state for a reading that starts now: the group blocks' waste and
    * give-ups, which count against one reading's budget, cleared.
    */
  def readingStarted: JitState[C] =
    copy(wastedGroupBlockSteps = 0, givenUpGroupBlocks = Set.empty)

  /** This state without the instance table's answers, its young and its old
    * generation, and the values of its decode points, all read through the
    * expansions of the URI nodes they met; the compiled codes, blocks and
    * criteria, read off syntax alone (a URI node has no layer to read,
    * `Jit.layerOf`), and the costs are kept. The verifiable tables stay, none
    * of them answering until it is verified, within the retention's size.
    */
  def withoutAnswers: JitState[C] =
    val carried = earlierVerifiable ++ verifiable
    copy(
      instanceTables = Tables.empty,
      olderInstances = Map.empty,
      decodedPoints = DecodedPoints.empty,
      checkedHeads = CheckedHeads.empty,
      sharedTerms = SharedTerms.empty,
      openTraces = Map.empty,
      verifiable = Map.empty,
      earlierVerifiable =
        if withinRetention(carried.size) then carried else verifiable,
      verifying = Set.empty,
      wastedGroupBlockSteps = 0,
      givenUpGroupBlocks = Set.empty
    )

  /** This state with the table of an earlier version, whose reads hold,
    * completed under this version; a key completed or in progress meanwhile
    * keeps its own table.
    */
  def tableVerified(
      key: TabledInstance[C],
      table: VerifiableTable[C]
  ): JitRunState[C] =
    if completeAnswers(key).isDefined || instanceTables.open.contains(key) then
      this
    else
      copy(
        instanceTables = instanceTables.copy(complete =
          instanceTables.complete.updated(key, table.answers)
        ),
        verifiable = verifiable.updated(key, table)
      )

  /** Whether the retention lets the state hold that many verifiable tables. */
  private def withinRetention(size: Int): Boolean =
    configuration.instanceRetention match
      case InstanceRetention.Generations(limit) => size <= limit
      case InstanceRetention.NeverDropped       => true

  /** This state with the read noted for the producer running innermost, if any,
    * under `InstanceReuse.VerifiedAcrossVersions`.
    */
  def readNoted(read: InstanceRead[C]): JitRunState[C] = traceChanged(
    _.read(read)
  )

  /** This state with the innermost producer's trace marked as not saying all it
    * depends on.
    */
  def traceMadeOpaque: JitRunState[C] = traceChanged(_.copy(opaque = true))

  private def traceChanged(
      change: ReadTrace[C] => ReadTrace[C]
  ): JitRunState[C] =
    if configuration.instanceReuse == InstanceReuse.WithinVersion then this
    else
      instanceTables.innermostKey.fold(this)(reader =>
        copy(openTraces =
          openTraces.updated(
            reader,
            change(openTraces.getOrElse(reader, ReadTrace.empty[C]))
          )
        )
      )

  /** This state with the reader's trace as it was, none for no reader. */
  def traceRestored(
      reader: Option[TabledInstance[C]],
      trace: Option[ReadTrace[C]]
  ): JitRunState[C] =
    reader.fold(this)(key =>
      copy(openTraces =
        trace.fold(openTraces - key)(openTraces.updated(key, _))
      )
    )

  /** This state after a stop: the trace of every instance whose table is open
    * marked as not saying all it depends on, since a reading a budget cut short
    * may have noted only part of what it read.
    */
  def openReadingsStopped: JitRunState[C] =
    if configuration.instanceReuse == InstanceReuse.WithinVersion then this
    else
      copy(openTraces =
        instanceTables.open.keysIterator.foldLeft(openTraces)((traces, key) =>
          traces.updated(
            key,
            traces.getOrElse(key, ReadTrace.empty[C]).copy(opaque = true)
          )
        )
      )

  /** This state with the table of the instance noted as opened in a fallback
    * point's check, at the cuts made so far.
    */
  def checkOpened(key: TabledInstance[C]): JitRunState[C] =
    copy(checkOpenings = checkOpenings.updated(key, cuts))

  /** This state after the component of the leader and the members completed:
    * the tables of the component that a fallback point's check opened and whose
    * reading saw a cut dropped (`cutReadingsDropped`); its traces closed, and
    * its tables verifiable when the trace says all they depend on, the
    * component did not complete inside a fallback point's check, whose cuts
    * depend on the readings around it, and every instance read outside the
    * component is complete, so that the answers it read are a table's whole
    * answers.
    */
  def componentCompleted(
      leader: TabledInstance[C],
      members: Vector[TabledInstance[C]]
  ): JitRunState[C] =
    cutReadingsDropped(members :+ leader).tracesClosed(leader, members)

  /** This state without the complete tables of the component that a fallback
    * point's check opened while a cut was made after they opened: their heads
    * may be the check's (`Jit.tabledInstance`). The cuts only grow, so a cut
    * made after a table opened and before its component completed is one its
    * reading may have seen; a cut of another reading in between drops a table
    * that could have stayed, which costs a reading again and changes no answer.
    */
  private def cutReadingsDropped(
      component: Vector[TabledInstance[C]]
  ): JitRunState[C] =
    val dropped =
      component.filter(key => checkOpenings.get(key).exists(_ < cuts))
    copy(
      instanceTables =
        instanceTables.copy(complete = instanceTables.complete -- dropped),
      checkOpenings = checkOpenings -- component
    )

  private def tracesClosed(
      leader: TabledInstance[C],
      members: Vector[TabledInstance[C]]
  ): JitRunState[C] =
    if configuration.instanceReuse == InstanceReuse.WithinVersion then this
    else
      val component = members :+ leader
      val inside = component.toSet
      val trace = component
        .flatMap(openTraces.get)
        .foldLeft(ReadTrace.empty[C])(_.joined(_))
      val held = Option
        .unless(trace.opaque || !readingPath.isEmpty)(trace.reads)
        .flatMap(reads => heldReads(reads, inside))
      val base = if withinRetention(verifiable.size + component.size) then
        verifiable
      else Map.empty[TabledInstance[C], VerifiableTable[C]]
      val kept = held.fold(verifiable)(reads =>
        component.foldLeft(base)((tables, member) =>
          completeAnswers(member).fold(tables)(answers =>
            tables.updated(member, VerifiableTable(answers, reads))
          )
        )
      )
      copy(openTraces = openTraces -- component, verifiable = kept)

  /** The reads outside the component with what they gave, none when one of the
    * instances read has no complete table.
    */
  private def heldReads(
      reads: Vector[InstanceRead[C]],
      inside: Set[TabledInstance[C]]
  ): Option[Vector[HeldRead[C]]] =
    reads.foldLeft(Option(Vector.empty[HeldRead[C]])) {
      case (None, _)                                                => None
      case (found, InstanceRead.Table(key)) if inside.contains(key) => found
      case (Some(found), InstanceRead.Table(key))                   =>
        completeAnswers(key).map(answers =>
          found :+ HeldRead.Table(key, answers)
        )
      case (Some(found), InstanceRead.Expansion(node, expansion)) =>
        Some(found :+ HeldRead.Expansion(node, expansion))
    }

  /** The answers of the key's complete table, in either generation. */
  def completeAnswers(key: TabledInstance[C]): Option[AnswerSet[JitHead[C]]] =
    instanceTables.complete.get(key).orElse(olderInstances.get(key))

  /** The steps spent since the last instance the table recorded
    * (`lastCheckpointSpent`, a reading's spent steps then), given the steps the
    * reading has spent now (`InstanceCheckpoints`). The table is kept from one
    * reading to the next while each reading counts its steps from zero, so a
    * reading that has spent fewer steps than the last checkpoint is a later
    * reading, and its steps are all since the checkpoint.
    */
  def stepsSinceCheckpoint(spent: Long): Long =
    if spent >= lastCheckpointSpent then spent - lastCheckpointSpent else spent

/** A decode point `x ∥ C`: the representation its criterion names and the term x.
  */
final case class DecodePoint[C <: NativeSpecializer & Singleton](
    representation: Representation[JitValue[C]],
    term: JitValue[C]
)

/** The values of the decode points read to their end: the table of the heads of
  * the term `x ∥ C`, a pure function of the term as the instance table's
  * entries are, whose emptying changes only how many steps a later reading
  * takes (`CONTRIBUTING.md`, "Tables"). It is kept in two generations, as the
  * instance table is (`InstanceRetention`), a value found in the older
  * generation being completed in the young one again.
  */
final case class DecodedPoints[C <: NativeSpecializer & Singleton](
    young: Map[DecodePoint[C], Vector[NativeValue[JitValue[C]]]],
    older: Map[DecodePoint[C], Vector[NativeValue[JitValue[C]]]]
):

  /** The values of the point, if it was read to its end. */
  def found(point: DecodePoint[C]): Option[Vector[NativeValue[JitValue[C]]]] =
    young.get(point).orElse(older.get(point))

  /** These points with the values of the point recorded. */
  def recorded(
      point: DecodePoint[C],
      values: Vector[NativeValue[JitValue[C]]],
      retention: InstanceRetention
  ): DecodedPoints[C] =
    retention match
      case InstanceRetention.Generations(size)
          if young.size >= size && !young.contains(point) =>
        DecodedPoints[C](Map(point -> values), young)
      case InstanceRetention.Generations(_) | InstanceRetention.NeverDropped =>
        copy(young = young.updated(point, values))

object DecodedPoints:

  /** No point read. */
  def empty[C <: NativeSpecializer & Singleton]: DecodedPoints[C] =
    DecodedPoints[C](Map.empty, Map.empty)

/** The operand of a fallback point's check, read under a dispatch mode: the key
  * of the heads the check found.
  */
final case class CheckedOperand[C <: NativeSpecializer & Singleton](
    operand: JitValue[C],
    mode: DispatchMode
)

/** The heads the uncut checks of fallback points found, by the operand and the
  * dispatch mode it was read under: the memo of a pure function of the term, as
  * the instance table's entries are, whose emptying changes only how many steps
  * a later reading takes (`CONTRIBUTING.md`, "Tables"). It holds heads only,
  * never whether they are of a type: that is read off the heads at each use. A
  * check that saw a cut is not recorded, its heads depending on the readings
  * around it. It is kept in two generations, as the instance table is
  * (`InstanceRetention`), and emptied with it when the contents of the URI
  * nodes change (`JitRunState.withoutAnswers`), the heads having been read
  * through them.
  */
final case class CheckedHeads[C <: NativeSpecializer & Singleton](
    young: Map[CheckedOperand[C], Vector[JitHead[C]]],
    older: Map[CheckedOperand[C], Vector[JitHead[C]]]
):

  /** The heads of the operand under the mode, if an uncut check found them. */
  def found(operand: CheckedOperand[C]): Option[Vector[JitHead[C]]] =
    young.get(operand).orElse(older.get(operand))

  /** These heads with the heads of the operand recorded. */
  def recorded(
      operand: CheckedOperand[C],
      heads: Vector[JitHead[C]],
      retention: InstanceRetention
  ): CheckedHeads[C] =
    retention match
      case InstanceRetention.Generations(size)
          if young.size >= size && !young.contains(operand) =>
        CheckedHeads[C](Map(operand -> heads), young)
      case InstanceRetention.Generations(_) | InstanceRetention.NeverDropped =>
        copy(young = young.updated(operand, heads))

object CheckedHeads:

  /** No check recorded. */
  def empty[C <: NativeSpecializer & Singleton]: CheckedHeads[C] =
    CheckedHeads[C](Map.empty, Map.empty)

/** The closed canonical terms a slot read more than once, at a cost, was filled
  * with (`JitRules.shared`): an evaluation of such a term reads it through the
  * instance table under the key `TabledInstance(cellCode, [term])`, always
  * tabled, so that the reads share it. A closed canonical term is never wrapped
  * in a cell, which would be a second spelling of it. Kept in two generations,
  * as the instance table is: a term dropped with the older generation is shared
  * again only once a slot is filled with it again, which costs speed, never an
  * answer; emptied with the instance table when the contents of the URI nodes
  * change.
  */
final case class SharedTerms[C <: NativeSpecializer & Singleton](
    young: Set[JitValue[C]],
    older: Set[JitValue[C]]
):

  /** Whether an evaluation of the term reads it through the instance table. */
  def contains(term: JitValue[C]): Boolean =
    young.contains(term) || older.contains(term)

  /** These terms with the term added. */
  def added(term: JitValue[C], retention: InstanceRetention): SharedTerms[C] =
    retention match
      case InstanceRetention.Generations(size)
          if young.size >= size && !young.contains(term) =>
        SharedTerms[C](Set(term), young)
      case InstanceRetention.Generations(_) | InstanceRetention.NeverDropped =>
        copy(young = young + term)

object SharedTerms:

  /** No term shared. */
  def empty[C <: NativeSpecializer & Singleton]: SharedTerms[C] =
    SharedTerms[C](Set.empty, Set.empty)

/** A code's use of the instance table: the instances read into it, the steps
  * their readings spent, the instances taken from it, the steps charged for the
  * lookups of both (their keys' nodes, `JitRules.instance`), and the misses
  * that opened a table (`missesOpened`).
  *
  * FIXME (2026-11-02): an entry is counted when its reading finishes, so
  * https://github.com/Atry/private-overlay/issues/1941 the instances of one
  * code nested in each other's readings are not judged until the innermost
  * finishes, and the cutoff does not apply to them. MEASURED (a probe that is
  * not committed, CPUs 2 and 3, the published
  * repeated_library_unshared_doublings/direct/repetitions_8 read by the JIT
  * with dispatch and the table on): one code had 38,728 entries and no hit,
  * 24,723,132 steps in all. Counting an entry when its reading starts cut that
  * code off at 64 entries (770 instances in the table, 24,606,039 steps), but
  * it also cut off the longest common subsequence's cell code before its first
  * hit, which comes only when a cell's second branch meets a cell the first
  * finished: the steps a cell at n = 100 went from 157 to beyond 19,605 (the
  * budget of 2 * 10^8 steps exceeded). A candidate: judge a code on its
  * finished entries only, and count the open ones against a depth bound of
  * their own.
  */
final case class TableCost(
    entries: Long,
    entrySteps: Long,
    hits: Long,
    lookupSteps: Long,
    missesOpened: Long
):

  /** The cost after one more instance read into the table, its lookup charged
    * the key's nodes and its reading having spent the steps.
    */
  def entered(keyNodes: Int, steps: Long): TableCost =
    assert(steps >= 0, s"a reading's spent steps never decrease: $steps")
    copy(
      entries = entries + 1,
      entrySteps = entrySteps + steps,
      lookupSteps = lookupSteps + keyNodes
    )

  /** The cost after one more miss that enters the instance table, an instance
    * found in no complete table, which opens its table or reads it while it is
    * open (an instance met again inside its own reading), counted where the
    * miss enters the table (`JitRules.tabledInstance`); a miss run untabled
    * (not recorded, or inside a fallback point's check) enters no table and is
    * not counted. `entered` counts a miss when its heads end with the table
    * complete. The instances of one code nested in each other's readings all
    * miss before the innermost finishes, so a policy that must act while they
    * are still open reads this count: `missesOpened - entries` misses of the
    * code have not finished, being open or left unfinished by a stop. A miss is
    * counted before it can finish, so `missesOpened >= entries`.
    */
  def missOpened: TableCost = copy(missesOpened = missesOpened + 1)

  /** The cost after one more instance taken from the table, its lookup charged
    * the key's nodes.
    */
  def hit(keyNodes: Int): TableCost =
    copy(hits = hits + 1, lookupSteps = lookupSteps + keyNodes)

  /** Whether the table costs the code more than it saves, after `trial` entries
    * (`JitConfiguration.instanceTableTrial`): the hits save the steps of an
    * entry's reading each on average, fewer than the steps charged for the
    * lookups.
    */
  def unprofitable(trial: Long): Boolean =
    entries >= trial && hits * entrySteps < entries * lookupSteps

/** No use of the table yet, and the fewest entries a code is judged on.
  *
  * FIXME (2026-11-01): the test of `TableCost.unprofitable` takes a lookup's
  * https://github.com/Atry/private-overlay/issues/1942 charged step to cost the
  * wall time of a reading's step, which is not measured, and `trial` is a
  * choice. The costs persist across the readings of a suite (`JitRunState.of`
  * keeps them), so a code judged unprofitable in one point is never tabled
  * again in the run, even where its later instances would be read again.
  */
object TableCost:
  val none: TableCost = TableCost(0, 0, 0, 0, 0)
  val trial: Long = 64

/** An instance of a code: the code with no hole left and its fillings, a key of
  * `JitRunState.instanceTables`. The table takes two instances with one key,
  * under one configuration, to have the same heads: a code's clauses read its
  * fillings, and the arguments are applied to its heads outside the table. The
  * JIT's state shapes heads in one place, a fallback point's check in progress
  * (`ReadingPath`), so no instance is tabled or taken from the table while the
  * path is not empty (`JitRules.instance`).
  *
  * The code and the fillings are interned terms (`gezi.ir.Interned`), so two
  * instances with equal fillings are one key however they were built, and
  * comparing two keys compares each filling by `==`, which ends at `eq` or at a
  * differing hash code; the hash, computed once when the key is made, combines
  * the fillings' hash codes, each computed when its filling was made. Both cost
  * the number of fillings, whatever their size, and a lookup is charged that
  * (`Jit.instance`). The hash codes are by content, the same in every process;
  * the table is only looked up and updated, never iterated
  * (`JitRunState.instanceTables`).
  *
  * No filling needs a key of its own: every value of the JIT is interned
  * (`JitLayer`), so two equal ones are one object, its hash code is computed
  * when it is made, and `==` compares it by its parts, each by `eq` or a
  * differing hash code, at the cost of its width as any filling.
  */
final case class TabledInstance[C <: NativeSpecializer & Singleton](
    code: Code,
    fillings: Vector[JitValue[C]]
):

  /** The hash, computed once when the key is made: a key is looked up and
    * looked up in `JitRunState.instanceTables` and `JitRunState.olderInstances`
    * up to five times for one instance.
    */
  override val hashCode: Int = scala.util.hashing.MurmurHash3.productHash(this)

/** The JIT's part of a reading. */
object JitRunState:

  /** A fresh part for the configuration: an empty cache, no cost counted. */
  def fresh[C <: NativeSpecializer & Singleton](
      configuration: JitConfiguration[C]
  ): JitRunState[C] =
    JitRunState(
      configuration,
      Map.empty,
      Vector.empty,
      JitCounts.empty,
      ReadingPath.Empty()
    )

  /** The JIT's part of the reading's state under the configuration, a fresh one
    * when the state holds none, or one of another configuration (compared by
    * reference: a configuration is built once and passed on). A code identifier
    * is the canonical object of its code, so a state's cache holds for every
    * later reading: this is how the tests f a, f b and f c compile f's codes
    * once (jit_strategies.pl, THE TEST IS THE UNIT).
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
  def of[C <: NativeSpecializer & Singleton](
      state: ReadingState[C],
      configuration: JitConfiguration[C]
  ): JitRunState[C] =
    held(state.jitState, configuration).getOrElse(fresh(configuration))

  /** The JIT's part a reading's state holds under the configuration
    * (`ReadingState.jitState`), none when it is none or one of another
    * configuration (compared by reference), as `of` reads it.
    */
  def held[C <: NativeSpecializer & Singleton](
      state: JitState[C],
      configuration: JitConfiguration[C]
  ): Option[JitRunState[C]] =
    state match
      // Registered conversion (issue 2261, section 8): a JIT state in a reading of `C` is of `C`, `JitState` being
      // covariant only so that `NoJitState` is every reading's, and no JIT state of another configuration being one
      // of `C`'s (`C` is a singleton type); the configuration it was built under, compared by reference, says it is
      // this JIT's.
      case found: (JitRunState[C] @unchecked)
          if found.configuration eq configuration =>
        Some(found)
      case _ => None
