package gezi.jmh.pipeline

import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"): the time unit of JMH's annotations, an immutable enum of the concurrency package
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Literal
import gezi.frontend.Literals
import gezi.weakhead.Computed
import gezi.weakhead.Mode
import gezi.weakhead.ReadingState
import gezi.weakhead.Value
import gezi.weakhead.WeakHead
import org.openjdk.jmh.annotations.Benchmark
import org.openjdk.jmh.annotations.BenchmarkMode
import org.openjdk.jmh.annotations.Fork
import org.openjdk.jmh.annotations.Level
import org.openjdk.jmh.annotations.Measurement
import org.openjdk.jmh.annotations.Param
import org.openjdk.jmh.annotations.OutputTimeUnit
import org.openjdk.jmh.annotations.Scope
import org.openjdk.jmh.annotations.Setup
import org.openjdk.jmh.annotations.State
import org.openjdk.jmh.annotations.Warmup
import scala.compiletime.uninitialized

/** The look-ups of a choice of variable arguments partial functions of text
  * keys, each key's literal its CBOR text string spread into bits, read
  * under the tabled weak head that knows top, every look-up of a run in one
  * reading state (`ReadingState.nextReading` keeps the tables). The keys
  * are names that share eight prefixes, as file names do.
  */
final case class CborTrieSetting(hits: Vector[Value], rootMisses: Vector[Value], deepMisses: Vector[Value])

/** A run of look-ups: the state after the last and the number of parallel
  * sets each read.
  */
final case class CborTrieRun(state: ReadingState, answers: Vector[Int])

object CborTries:

  /** The budget of one look-up, far above what any takes. */
  val limit: Long = 3000000

  private val prefixes: Vector[String] =
    Vector("binary", "boolean", "fixpoint", "integer", "native", "prelude", "rational", "scott")

  /** The keys: names that share the prefixes above. */
  def keys(members: Int): Vector[String] =
    (0 until members).map(index => s"${prefixes(index % prefixes.size)}_${index / prefixes.size}").toVector

  /** First characters no key starts with. */
  private val missingFirst: Vector[Char] =
    (('a' to 'z') ++ ('0' to '9') :+ '_').filterNot(character => prefixes.exists(_.startsWith(character.toString))).toVector

  /** Keys that miss at the first byte after the head, each with another first character. */
  def rootMisses(members: Int): Vector[String] =
    val written = keys(members)
    missingFirst.zipWithIndex.map((first, index) => s"$first${written(index % written.size).drop(1)}")

  /** Keys that miss deep: a key with one character more, and a key whose
    * last character is changed.
    */
  def deepMisses(members: Int): Vector[String] =
    keys(members).take(32).flatMap(written => Vector(written + "_", written.dropRight(1) + "z"))

  private def chained(members: List[DeBruijnTerm]): DeBruijnTerm = members match
    case Nil           => Literals.top
    case single :: Nil => single
    case first :: rest => DeBruijnTerm.Choice(first, chained(rest))

  /** The setting of the number of members: the choice of the keys' partial
    * functions, the body of the key of index i the natural i, and the
    * queries, the choice applied to each key's bits.
    */
  def setting(members: Int): CborTrieSetting =
    val record = chained(
      keys(members).zipWithIndex.map((written, index) => Literals.partialFunction(Literal.text(written), Literals.naturalTerm(index))).toList
    )
    def queries(written: Vector[String]): Vector[Value] =
      written.map(key =>
        Defunctionalization.thunkInstruction(Literals.arguments(Literal.text(key)).foldLeft(record)(DeBruijnTerm.Apply(_, _)))
      )
    CborTrieSetting(queries(keys(members)), queries(rootMisses(members)), queries(deepMisses(members)))

  /** The tables the states may hold. MEASURED 2026-11-16 (a scratch munit
    * probe in jmh-pipeline, not committed, the limit lifted): after the
    * insertion, after the root misses and after the deep misses, 3,853,
    * 5,916 and 4,607 tables at 16 members (140 bytes of keys), 14,023, 16,356
    * and 15,049 at 64 (560 bytes), 59,553, 62,503 and 60,265 at 256 (2,416
    * bytes): about 25 tables a byte of the keys, the trie's nodes, one a
    * bit. The limit is the largest, 62,503, plus a quarter, rounded up.
    */
  val tableLimit: Int = 80000

  /** The state no look-up has read in, knowing top. */
  def fresh: ReadingState = ReadingState.knowingTop(limit).copy(tableLimit = tableLimit)

  /** The queries looked up in order, each in the state the one before left. */
  def looked(queries: Vector[Value], start: ReadingState): CborTrieRun =
    queries.foldLeft(CborTrieRun(start, Vector.empty))((run, query) =>
      WeakHead.heads(Mode.TablingWeakHead, query).collected.result(run.state.nextReading(limit)) match
        case Computed.Done(sets, after) => CborTrieRun(after, run.answers :+ sets.size)
        case Computed.Stopped(after) =>
          throw IllegalStateException(s"a look-up stopped at ${after.budget.spent} steps (${after.exhausted})")
    )

/** The input of the CBOR trie benchmarks: the setting of one number of
  * members, and the states after inserting every key and after one round of
  * root misses, built and checked before the trial.
  */
@State(Scope.Benchmark)
class CborTrieInput:

  /** The number of members, which JMH assigns. */
  @SuppressWarnings(Array("org.wartremover.warts.Var")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  @Param(Array("16", "64", "256")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  var members: Int = uninitialized // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")

  lazy val setting: CborTrieSetting = CborTries.setting(members)

  /** The state after every key was looked up once. */
  lazy val inserted: ReadingState = CborTries.looked(setting.hits, CborTries.fresh).state

  /** The state after one round of root misses besides. */
  lazy val rootMissed: ReadingState = CborTries.looked(setting.rootMisses, inserted).state

  /** The states built and the answers checked: a hit reads one parallel
    * set, a miss none.
    */
  @Setup(Level.Trial)
  def built(): Unit =
    assert(CborTries.looked(setting.hits, CborTries.fresh).answers.forall(_ == 1), "every key is found")
    assert(CborTries.looked(setting.rootMisses, inserted).answers.forall(_ == 0), "every root miss misses")
    assert(CborTries.looked(setting.deepMisses, inserted).answers.forall(_ == 0), "every deep miss misses")
    assert(rootMissed.tables.complete.nonEmpty, "the tables are kept")

/** The time of the runs of look-ups of `CborTries`, each from a state the
  * input built: inserting every key into a fresh state, every key again,
  * root misses and deep misses after the insertion, and the root misses a
  * second time. They measure three hypotheses: a hit and a repeated miss cost
  * the same whatever the number of members; the distinct root misses of one
  * run grow with the members far slower than under a byte per argument, and
  * cost no more than inserting every key; inserting every key bit by bit
  * costs no more than byte by byte. Each benchmark returns its run, so that JMH
  * consumes it.
  */
// The result is the allocation per operation (`-prof gc`), which is deterministic up to about 1 percent (two
// forks of 2026-11-16 read 4,690,616 and 4,744,912 B/op for the deep misses at 16 members), so one fork, one
// warm-up and two measurement iterations suffice (CONTRIBUTING.md, "Benchmarks with JMH (Scala)", rule 6).
// The warm-up: in the run of 2026-11-16 (two forks, three warm-up and five measurement iterations of 1 s, cores
// 8,9 loaded), the first warm-up iteration took 1.3 to 2 times the steady time (deep misses at 64 members:
// 3,182 and 3,774 us/op against 1,694 to 2,560) and the second was already within the measurement's spread.
// The heap: 768 MB held 137,910 tables at 256 members in the draft of 2026-11-16, more than twice the 62,503
// this benchmark's states hold (`CborTries.tableLimit`).
@BenchmarkMode(Array(org.openjdk.jmh.annotations.Mode.AverageTime)) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Fork(value = 1, jvmArgsAppend = Array("-Xmx768m", "-XX:+UseSerialGC")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Warmup(iterations = 1, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 2, time = 1, timeUnit = TimeUnit.SECONDS)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
class CborTrieBenchmark:

  @Benchmark
  def insertAll(input: CborTrieInput): CborTrieRun = CborTries.looked(input.setting.hits, CborTries.fresh)

  @Benchmark
  def hitsAfterInsertion(input: CborTrieInput): CborTrieRun = CborTries.looked(input.setting.hits, input.inserted)

  @Benchmark
  def rootMissesAfterInsertion(input: CborTrieInput): CborTrieRun = CborTries.looked(input.setting.rootMisses, input.inserted)

  @Benchmark
  def rootMissesRepeated(input: CborTrieInput): CborTrieRun = CborTries.looked(input.setting.rootMisses, input.rootMissed)

  @Benchmark
  def deepMissesAfterInsertion(input: CborTrieInput): CborTrieRun = CborTries.looked(input.setting.deepMisses, input.inserted)
