package gezi.jmh.pipeline

import gezi.generatedinputs.KnowledgeGenerators
import gezi.generatedinputs.SeededSamples
import gezi.knowledgereading.KnowledgeReading
import gezi.programfamilies.FixedPointLines
import gezi.standardlibrary.KnowledgeSlot
import gezi.standardlibrary.LibraryBackend
import gezi.standardlibrary.StandardLibrary
import gezi.weakhead.ApplicationReading
import gezi.weakhead.Mode
import gezi.ir.{Configured, NativeSpecializer, NoFacts}

/** The configuration of the benchmarks' knowledge terms: no facts. */
private given knowledgeReadingsNoFacts: NoFacts.type = NoFacts

/** The benchmarks' knowledge, generated from a fixed seed
  * (`KnowledgeGenerators`, standardlibrary's generator of well-formed
  * knowledge), so that what the benchmarks time does not change with the
  * repository's knowledge; and its reading on weak-head, for the measurement
  * of what reading the knowledge written as one term costs
  * ([[KnowledgeInLambdalattice]]).
  */
object KnowledgeReadings:

  /** The seed the benchmarks' knowledge is drawn from. */
  val seed: Long = 20261031L

  /** The most members of each slot of the benchmarks' knowledge, which is
    * drawn at Hedgehog's largest size, where each slot draws from none to
    * this many members.
    */
  val maximumMembers: Int = 32

  /** The text of a knowledge of the slots drawn from `seed`, every name it
    * declares starting with the label.
    */
  def knowledgeText(label: String, slots: Vector[KnowledgeSlot]): String =
    val Vector(text) = SeededSamples.samples(KnowledgeGenerators.knowledgeText(label, slots, maximumMembers), seed, 1): @unchecked
    text

  /** The benchmarks' knowledge read by the knowledge reader, a knowledge of
    * every slot a generated knowledge fills: the library a benchmark of the
    * knowledge reading reads.
    */
  lazy val knowledgeTerm: Configured[NoFacts.type] =
    KnowledgeGenerators.term[NoFacts.type](knowledgeText("benchmark", KnowledgeGenerators.fillableSlots))

  /** The benchmarks' knowledge given to an executor: a knowledge of the slots
    * no backend interprets (`KnowledgeGenerators.slotsNoBackendInterprets`),
    * since the backend checks the natives, codecs and families of the others
    * against what it implements. None of its terms occurs in a benchmark's
    * program, each bound term holding its member's name.
    */
  lazy val executorKnowledgeTerm: Configured[NoFacts.type] =
    KnowledgeGenerators.term[NoFacts.type](knowledgeText("executor", KnowledgeGenerators.slotsNoBackendInterprets))

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

  /** The library of the knowledge term with the backends' checks, read from
    * the compilation's first state.
    */
  def compiled[C <: NativeSpecializer & Singleton](knowledge: Configured[C], backends: Vector[LibraryBackend])(using C): StandardLibrary =
    StandardLibrary.compiled(knowledge, backends, KnowledgeReading.compilationState)._1

  /** The library of the benchmarks' knowledge as the current reader loads
    * it, with no backend's check.
    */
  def library(): StandardLibrary = compiled(knowledgeTerm, Vector.empty)

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
