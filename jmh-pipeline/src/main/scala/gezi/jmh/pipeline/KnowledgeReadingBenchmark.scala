package gezi.jmh.pipeline

import gezi.ir.{ChoiceSpine, Configured, NoFacts}
import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"): the time unit of JMH's annotations, an immutable enum of the concurrency package
import gezi.standardlibrary.StandardLibrary
import gezi.weakhead
import org.openjdk.jmh.annotations.Benchmark
import org.openjdk.jmh.annotations.BenchmarkMode
import org.openjdk.jmh.annotations.Fork
import org.openjdk.jmh.annotations.Level
import org.openjdk.jmh.annotations.Measurement
import org.openjdk.jmh.annotations.Mode
import org.openjdk.jmh.annotations.OutputTimeUnit
import org.openjdk.jmh.annotations.Param
import org.openjdk.jmh.annotations.Scope
import org.openjdk.jmh.annotations.Setup
import org.openjdk.jmh.annotations.State
import org.openjdk.jmh.annotations.Warmup
import scala.compiletime.uninitialized

/** The configuration of the terms here: no facts. */
private given knowledgeReadingBenchmarkNoFacts: NoFacts.type = NoFacts

/** The input of a knowledge reading: the library of the benchmarks'
  * generated knowledge (`KnowledgeReadings.knowledgeTerm`) as the current
  * reader loads it, the knowledge term combined a number of times, and the
  * reading's mode and slot reading, each reading checked once against the
  * current reader's index in the trial's setup, outside the timed code.
  */
@State(Scope.Benchmark)
class KnowledgeInput:

  /** The number of copies combined by `+`, which JMH assigns. */
  @SuppressWarnings(Array("org.wartremover.warts.Var")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  @Param(Array("1", "2", "4", "8")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  var copies: Int = uninitialized // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")

  /** The evaluator's mode, `weak_head` or `tabling(weak_head)`, which JMH
    * assigns.
    */
  @SuppressWarnings(Array("org.wartremover.warts.Var")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  @Param(Array("weak_head", "tabling_weak_head")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  var modeName: String = uninitialized // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")

  /** How the evaluator takes applications apart
    * (`weakhead.ApplicationReading`), which JMH assigns.
    */
  @SuppressWarnings(Array("org.wartremover.warts.Var")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  @Param(Array("ByLayer", "BySpine")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  var applicationReadingName: String = uninitialized // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")

  /** How the slots are read (`SlotReading`), which JMH assigns. */
  @SuppressWarnings(Array("org.wartremover.warts.Var")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  @Param(Array("OneSlotEach", "AllSlotsAtOnce")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  var slotReadingName: String = uninitialized // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")

  /** The library of the benchmarks' knowledge. */
  lazy val library: StandardLibrary = KnowledgeReadings.library()

  /** The evaluator's mode named. */
  lazy val mode: weakhead.Mode = modeName match
    case "weak_head"         => weakhead.Mode.WeakHead
    case "tabling_weak_head" => weakhead.Mode.TablingWeakHead
    case other               => throw IllegalArgumentException(s"no mode is named $other")

  /** The option of taking applications apart named. */
  lazy val applications: weakhead.ApplicationReading = weakhead.ApplicationReading.valueOf(applicationReadingName)

  /** The slot reading named. */
  lazy val slotReading: SlotReading = SlotReading.valueOf(slotReadingName)

  /** The slots of the library's knowledge. */
  lazy val slots: Vector[KnowledgeSlot] = KnowledgeInLambdalattice.slots(library.index)

  /** The knowledge term combined `copies` times. */
  lazy val knowledge: Configured[NoFacts.type] =
    KnowledgeInLambdalattice.combined(KnowledgeInLambdalattice.term(library.index), copies)

  /** The library and the term built, and the reading checked, before the
    * trial.
    */
  @Setup(Level.Trial)
  def built(): Unit =
    val checked = KnowledgeReadings.checkedReading(library, mode, applications, slotReading, copies)
    assert(checked.spent > 0, "a reading spends steps")
    assert(knowledge == KnowledgeInLambdalattice.combined(KnowledgeInLambdalattice.term(library.index), copies))

/** The cost of reading the benchmarks' generated knowledge base
  * (`KnowledgeReadings.knowledgeTerm`) written as one term
  * ([[KnowledgeInLambdalattice]]), with the weak-head evaluator, against the current reader's
  * load of the same knowledge (`StandardLibrary.compiled` on the knowledge
  * term, with no backend's check). Both start from a term already interned,
  * and neither includes writing or parsing a text. Each
  * benchmark returns what it read, so that JMH consumes it. The mode is the
  * average time of a call; the fork has the serial collector and the heap of
  * the build's tests. The warm-up and measurement iterations are set below,
  * from the readings of the warm-up iterations.
  */
@BenchmarkMode(Array(Mode.AverageTime)) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Fork(value = 3, jvmArgsAppend = Array("-Xmx256m", "-XX:+UseSerialGC")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
class KnowledgeReadingBenchmark:

  /** The knowledge term read on weak-head: every slot and every lemma pair
    * opened.
    */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MICROSECONDS)
  def weakHeadRead(input: KnowledgeInput): KnowledgeReading =
    KnowledgeReader.read(input.mode, input.applications, input.slotReading, input.knowledge, input.slots, KnowledgeReadings.stepLimit)

/** The current reader's load of the benchmarks' generated knowledge, the
  * reference the weak-head reading is compared with. Same JMH settings as
  * `KnowledgeReadingBenchmark`.
  */
@BenchmarkMode(Array(Mode.AverageTime)) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Fork(value = 3, jvmArgsAppend = Array("-Xmx256m", "-XX:+UseSerialGC")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
class CurrentReaderBenchmark:

  /** The generated knowledge compiled by the current reader. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MICROSECONDS)
  def currentReaderLoad(): StandardLibrary = KnowledgeReadings.library()
