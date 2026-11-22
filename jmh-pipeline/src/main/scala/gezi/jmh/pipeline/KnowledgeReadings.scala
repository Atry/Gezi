package gezi.jmh.pipeline

import gezi.programfamilies.FixedPointLines
import gezi.standardlibrary.LibraryBackend
import gezi.standardlibrary.StandardLibrary
import gezi.weakhead.ApplicationReading
import gezi.weakhead.Mode

/** The benchmarks' knowledge, the nine modules of `knowledgeFile`, and its
  * reading on weak-head, for the measurement of what reading the knowledge
  * written as one term costs ([[KnowledgeInLambdalattice]]).
  */
object KnowledgeReadings:

  /** The fixture whose one field is the benchmarks' knowledge, the choice of
    * the nine modules the baseline entry (deleted since) enabled when these
    * benchmarks were written (relative to the build root). Since the library
    * became files reached by paths, the benchmarks read it from this file, not from a text the host wrote, so
    * their JMH readings before that commit are not comparable without a
    * rerun.
    */
  val knowledgeFile: String = "tests/benchmark_fixtures/baseline_modules.lambdalattice"

  /** The budget of evaluator steps of one reading, far above what the
    * readings measured spend.
    */
  val stepLimit: Long = 100000000L

  /** The library of the fixture at the path relative to the build root,
    * with the backends' checks, read off the
    * tree whose visible subtree is Gezi's directory
    * (`StandardLibrary.compiledAt`).
    */
  def compiled(file: String, backends: Vector[LibraryBackend]): StandardLibrary =
    StandardLibrary.compiledAt(FixedPointLines.buildRoot, FixedPointLines.buildRoot.resolve(file), backends)

  /** The library of the benchmarks' knowledge as the current reader loads
    * it, with no backend's check.
    */
  def library(): StandardLibrary = compiled(knowledgeFile, Vector.empty)

  /** The reading of the knowledge term combined `copies` times; throws
    * `IllegalStateException` when what it reads, its repetitions dropped,
    * is not what the current reader's index holds, or when it reads each
    * lemma another number of times than the mode gives: `copies` times under
    * weak_head, which finds a head once for each copy, and once under
    * tabling(weak_head), whose heads are a set and whose copies, one term
    * by hash consing, are one key of its tables.
    */
  def checkedReading(
      library: StandardLibrary,
      mode: Mode,
      applications: ApplicationReading,
      slotReading: SlotReading,
      copies: Int
  ): KnowledgeReading =
    val index = library.index
    val knowledge = KnowledgeInLambdalattice.combined(KnowledgeInLambdalattice.term(index), copies)
    val reading =
      KnowledgeReader.read(mode, applications, slotReading, knowledge, KnowledgeInLambdalattice.slots(index), stepLimit)
    val expected = KnowledgeInLambdalattice.expected(index)
    if reading.read.distinct != expected then
      throw IllegalStateException(
        s"the weak-head reading of $copies copies under $mode, $applications, $slotReading differs from the index"
      )
    val readings = mode match
      case Mode.TablingWeakHead => 1
      case _                    => copies
    if reading.read.lemmas.size != readings * expected.lemmas.size then
      throw IllegalStateException(s"the weak-head reading of $copies copies read ${reading.read.lemmas.size} lemmas")
    reading
