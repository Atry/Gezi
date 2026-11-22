package gezi.jmh.pipeline

import java.nio.file.Path
import gezi.programfamilies.ClassicHindleyMilner
import gezi.programfamilies.CompiledConfiguration
import gezi.programfamilies.Configuration
import gezi.programfamilies.Configurations
import gezi.programfamilies.FixedPointLines
import gezi.programfamilies.FrontEnd
import gezi.programfamilies.Item
import gezi.programfamilies.Pipeline
import gezi.programfamilies.SizeFamily
import gezi.programfamilies.TypeScheme
import gezi.backendcomparison.Compiled
import org.openjdk.jmh.annotations.Level
import org.openjdk.jmh.annotations.Param
import org.openjdk.jmh.annotations.Scope
import org.openjdk.jmh.annotations.Setup
import org.openjdk.jmh.annotations.State
import scala.compiletime.uninitialized

// The JMH protocol's exception to the immutability of the Scala code
// (`CONTRIBUTING.md`, "The code is 100% immutable"): a mutable field that
// the JMH protocol requires is used where it is needed and nowhere else.
// JMH assigns a `@Param` field of a `@State` object after constructing it and
// rejects a final field, so each parameter is a `var`; a Java annotation's
// element of array type is written `Array(...)` in Scala, a constant of the
// annotation that no code changes. These lines, the two annotations of each
// benchmark class and its import of JMH's time unit, an immutable enum of
// java.util.concurrent, and no others, are suppressed with @SuppressWarnings
// where WartRemover rejects them, each carrying the user's words at its end
// (WartSuppressionTest).
// Everything derived from the parameters is a `lazy val`, written once, in
// the trial's setup.

/** The input of the library's compilation: a configuration, by name, and the
  * standard library's knowledge files.
  */
@State(Scope.Benchmark)
class LibraryInput:

  /** The configuration's name, which JMH assigns. */
  @SuppressWarnings(Array("org.wartremover.warts.Var")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  @Param(Array("hindley_milner_baseline", "cost_comparison")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  var configurationName: String = uninitialized // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")

  /** The configuration named. */
  lazy val configuration: Configuration =
    Configurations.all
      .find(_.name == configurationName)
      .getOrElse(throw IllegalArgumentException(s"no configuration is named $configurationName"))

  /** The root of Gezi's build, off which the configuration's fixture
    * file is read.
    */
  lazy val buildRoot: Path = FixedPointLines.buildRoot

  /** The configuration found before the trial, so that no iteration looks it
    * up.
    */
  @Setup(Level.Trial)
  def built(): Unit =
    val knowledgeFile = buildRoot.resolve(configuration.knowledgeFile)
    assert(knowledgeFile.toFile.isFile, s"$configurationName's fixture $knowledgeFile is no file")

/** The input of the stages after the library and of the classic reference:
  * an item of a size family, and the values the earlier stages give for it,
  * each built once before the trial.
  */
@State(Scope.Benchmark)
class ItemInput:

  /** The size family's name, which JMH assigns. */
  @SuppressWarnings(Array("org.wartremover.warts.Var")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  @Param(Array("numeral", "list", "chain", "nested", "tuple", "numerals", "lists", "folds")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  var family: String = uninitialized // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")

  /** The size `n`, which JMH assigns, `Pipeline.countedSizes`.
    */
  @SuppressWarnings(Array("org.wartremover.warts.Var")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  @Param(Array("64", "128", "512", "1024")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  var size: Int = uninitialized // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")

  /** The size family named. */
  lazy val sizeFamily: SizeFamily =
    Pipeline.sizeFamilies
      .find(_.family == family)
      .getOrElse(throw IllegalArgumentException(s"no size family is named $family"))

  /** The family's item of the size. */
  lazy val item: Item = sizeFamily.item(size)

  /** The family's configuration with its library and orientations compiled. */
  lazy val compiled: CompiledConfiguration =
    Pipeline.libraryCompiled(sizeFamily.configuration, FixedPointLines.buildRoot)

  /** The item's program after the front end. */
  lazy val afterFrontEnd: FrontEnd = Pipeline.frontEnd(compiled, item.program)

  /** The item's run input compiled by the index and the closure backend. */
  lazy val indexed: Compiled = Pipeline.indexCompiled(compiled, afterFrontEnd)

  /** Every input built before the trial, so that no iteration builds one. */
  @Setup(Level.Trial)
  def built(): Unit =
    assert(item.size == size.toString, s"${item.name} is not of size $size")
    assert(indexed.input.inputs == Vector(afterFrontEnd.inputInstruction), s"${item.name}'s run has another input")

/** The type schemes of the classic reference, read before the trial: a state
  * of its own, taken by `ClassicHindleyMilnerBenchmark` alone, so that the
  * other benchmarks of an item do not read them (their reading is broken
  * under the FIXME of `ClassicHindleyMilner.namedSchemes`, and when they were
  * part of `ItemInput` every benchmark of an item failed in its setup).
  */
@State(Scope.Benchmark)
class SchemesInput:

  /** The type schemes of the classic reference. */
  lazy val schemes: Map[String, TypeScheme] = ClassicHindleyMilner.schemes(ClassicHindleyMilner.libraryTypes)

  /** The schemes read before the trial. */
  @Setup(Level.Trial)
  def built(): Unit =
    assert(schemes.nonEmpty, "the classic reference has no type scheme")
