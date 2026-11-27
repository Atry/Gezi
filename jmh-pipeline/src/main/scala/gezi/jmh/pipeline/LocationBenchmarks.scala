package gezi.jmh.pipeline

import gezi.ir.{ChoiceSpine, Configured, NoFacts}
import java.net.URI
import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"): the time unit of JMH's annotations, an immutable enum of the concurrency package
import gezi.backendcomparison.Compiled
import gezi.frontend.Defunctionalization
import gezi.frontend.Defunctionalization.BindingsContracted
import gezi.frontend.FreeNames
import gezi.frontend.Lambdalattice
import gezi.frontend.ReadableText
import gezi.ir.Direction
import gezi.ir.LemmaIdentifier
import gezi.ir.Pattern
import gezi.programfamilies.CompiledConfiguration
import gezi.programfamilies.FixedPointLines
import gezi.programfamilies.FrontEnd
import gezi.programfamilies.Item
import gezi.programfamilies.Pipeline
import gezi.programfamilies.Saturated
import gezi.programfamilies.SizeFamily
import gezi.provenance.Provenance
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
private given locationBenchmarksNoFacts: NoFacts.type = NoFacts

/** What source locations cost: reading a text with its locations against
  * reading it without them, and computing the provenance of a saturated graph's
  * nodes against saturating it. The input of each is a program family's item
  * printed as a text (`LocatedItemInput`). The mode, collector and warm-up are
  * `PipelineBenchmarks`'; the heap is 1 GB, since the texts of the largest
  * items run to 2.9 million characters (`tuple` of 1,024), whose reading the
  * 256 MB of `PipelineBenchmarks` leaves mostly to the collector. Each reading
  * contracts the printer's bindings (`Defunctionalization.bindingsContracted`),
  * so that what is read, saturated and located is the program's own
  * instruction.
  */
@BenchmarkMode(
  Array(Mode.AverageTime)
) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Fork(
  value = 3,
  jvmArgsAppend = Array("-Xmx1g", "-XX:+UseSerialGC")
) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Warmup(iterations = 2, time = 3, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 3, time = 1, timeUnit = TimeUnit.SECONDS)
class LocationBenchmarks:

  /** The text read as a term and converted to the IR, its bindings contracted,
    * with no locations.
    */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MICROSECONDS)
  def readUnlocated(
      input: ItemTextInput
  ): Either[String, Configured[NoFacts.type]] =
    Defunctionalization.bindingsContracted(
      Lambdalattice.term(input.text, FreeNames.Rejected),
      input.printed.bindings,
      enclosingBinders = 0
    )(using gezi.ir.NoFacts)

  /** The text read with its spans and converted to the IR, its bindings
    * contracted, with the source maps of the body and of each binding's value.
    */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MICROSECONDS)
  def readLocated(input: ItemTextInput): Either[String, BindingsContracted] =
    val read = Lambdalattice.located(input.text, FreeNames.Rejected)
    Defunctionalization.locatedBindingsContracted(
      read.term,
      read.spans,
      ItemTextInput.uri,
      input.printed.bindings
    )(using gezi.ir.NoFacts)

  /** The locations of the saturated graph's nodes, from the maps of the body
    * and of each binding's value and the graph's union log.
    */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MICROSECONDS)
  def provenance(input: LocatedItemInput): Provenance =
    Provenance.of(input.saturated.graph, input.inputs, input.lemmas)

  /** The graph saturated to its End from the program's instruction, the graph
    * `provenance` reads.
    */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MICROSECONDS)
  def saturated(input: LocatedItemInput): Saturated =
    Pipeline.saturated(input.indexed)

/** A program family's item printed as a text, the input of the reading
  * benchmarks of `LocationBenchmarks`, built once before the trial: the item's
  * program after the front end, under the item's configuration as
  * `PipelineBenchmarks`' `ItemInput` builds it, printed by
  * `ReadableText.printedNameless`. The text names each shared part and binds it
  * by a let, `(λt. t λg. M) λg. …`, so that it is as long as the program's
  * graph and not its tree, which the items' sharing makes too long to write out
  * (printing the items in full, from `numeral` of 64 on, exhausted a heap of 3
  * GB on 2026-11-19). The readings contract the lets, which gives back the
  * program's own instruction; read as it is, each let stays a β-redex whose
  * code passes every name still needed to each thunk below, 133,727 fillings
  * for the 518 lets of `lists` of 256 against 1 in the program's instruction.
  */
@State(Scope.Benchmark)
class ItemTextInput:

  /** The size family's name, which JMH assigns. */
  @SuppressWarnings(
    Array("org.wartremover.warts.Var")
  ) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  @Param(
    Array(
      "numeral",
      "list",
      "chain",
      "nested",
      "tuple",
      "numerals",
      "lists",
      "folds"
    )
  ) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  var family: String =
    uninitialized // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")

  /** The size `n`, which JMH assigns, `PipelineBenchmarks`' sizes. */
  @SuppressWarnings(
    Array("org.wartremover.warts.Var")
  ) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  @Param(
    Array("64", "128", "512", "1024")
  ) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  var size: Int =
    uninitialized // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")

  /** The size family named. */
  lazy val sizeFamily: SizeFamily =
    Pipeline.sizeFamilies
      .find(_.family == family)
      .getOrElse(
        throw IllegalArgumentException(s"no size family is named $family")
      )

  /** The family's item of the size. */
  lazy val item: Item = sizeFamily.item(size)

  /** The family's configuration with its library and orientations compiled. */
  lazy val compiled: CompiledConfiguration =
    Pipeline.libraryCompiled(
      sizeFamily.configuration,
      FixedPointLines.buildRoot
    )

  /** The item's program after the front end. */
  lazy val afterFrontEnd: FrontEnd = Pipeline.frontEnd(compiled, item.program)

  /** The program after the front end printed, its shared parts named. */
  lazy val printed: ReadableText.Printed =
    ReadableText.printedNameless(afterFrontEnd.inputInstruction)

  /** The printed program's text. */
  lazy val text: String = printed.text

  /** The item and its text built before the trial. */
  @Setup(Level.Trial)
  def textBuilt(): Unit =
    assert(item.size == size.toString, s"${item.name} is not of size $size")
    assert(text.nonEmpty, s"${item.name} prints as no text")

/** The item's text read with its locations, its bindings contracted, and the
  * graph the program's instruction saturates to, the input of `provenance` and
  * `saturated`, built once before the trial.
  */
@State(Scope.Benchmark)
class LocatedItemInput extends ItemTextInput:

  /** The text read with its locations, its bindings contracted: the program's
    * instruction, its map, and the map of each binding's value. Throws
    * `IllegalStateException` when the text is no text of the printer's
    * bindings.
    */
  lazy val located: BindingsContracted =
    val read = Lambdalattice.located(text, FreeNames.Rejected)
    Defunctionalization
      .locatedBindingsContracted(
        read.term,
        read.spans,
        ItemTextInput.uri,
        printed.bindings
      )(using gezi.ir.NoFacts)
      .fold(
        reason => throw IllegalStateException(s"${item.name}'s text: $reason"),
        identity
      )

  /** The program's instruction, read from the text. */
  lazy val instruction: Configured[NoFacts.type] = located.body

  /** The inputs of the provenance: the body with its map, and each binding's
    * value with its own.
    */
  lazy val inputs: Vector[Provenance.Input] =
    Provenance.Input(located.body, located.map) +: located.bindings.map(
      binding => Provenance.Input(binding.instruction, binding.map)
    )

  /** The run input of the program's instruction, compiled by the index and the
    * closure backend.
    */
  lazy val indexed: Compiled[NoFacts.type] =
    Pipeline.indexCompiled(compiled, afterFrontEnd)

  /** The graph saturated from that run input. */
  lazy val saturated: Saturated = Pipeline.saturated(indexed)

  /** The sides of each lemma the configuration orients, its left side first,
    * which `Provenance.of` reads an instance's union by.
    */
  lazy val lemmas
      : Map[LemmaIdentifier, (Pattern[NoFacts.type], Pattern[NoFacts.type])] =
    compiled.orientations.orientations
      .map(orientation =>
        orientation.lemma -> (orientation.direction match
          case Direction.Forward  => (orientation.matched, orientation.added)
          case Direction.Backward => (orientation.added, orientation.matched))
      )
      .toMap

  /** The graph built before the trial, so that no iteration builds it. */
  @Setup(Level.Trial)
  def saturatedBuilt(): Unit =
    assert(
      instruction eq afterFrontEnd.inputInstruction,
      s"${item.name}'s text reads as another instruction than the program's"
    )
    assert(
      saturated.graph.instructionNode(instruction).isDefined,
      s"${item.name}'s instruction is not in its graph"
    )

object ItemTextInput:

  /** The URI the texts are read at. */
  val uri: URI = URI("file:///program-families/item.lambdalattice")
