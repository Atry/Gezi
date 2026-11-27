package com.yang_bo.gezi.programfamilies

import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths

/** The fixed points of every item of the two configurations, one line per item
  * as `com.yang_bo.gezi.backendcomparison.FixedPoint.line` writes it (configuration, item,
  * End, classes, live nodes, the form's digest), in the order the Prolog
  * exporter's fixtures sort by path, `configuration/item.fixture`.
  */
object FixedPointLines:

  /** The root of Gezi's build, which the build passes to the forked JVM.
    */
  def buildRoot: Path = Paths.get(
    sys.props.getOrElse(
      "gezi.buildRoot",
      throw IllegalStateException(
        "the build passes gezi.buildRoot to the forked JVM"
      )
    )
  )

  /** The source tree of the library and the knowledge files. */
  def sourceTree: Path = buildRoot.resolve("corpora")

  /** Each configuration and its items, in the order of the fixtures' paths.
    */
  def itemsInFileOrder: Vector[(Configuration, Item)] =
    Configurations.all
      .flatMap(configuration =>
        configuration.items.map(item => (configuration, item))
      )
      .sortBy((configuration, item) =>
        s"${configuration.name}/${item.name}.fixture"
      )

  /** Every configuration compiled once, by name. */
  def compiledConfigurations: Map[String, CompiledConfiguration] =
    Configurations.all
      .map(configuration =>
        configuration.name -> FixedPointRuns.compiled(configuration, buildRoot)
      )
      .toMap

  /** The line of every item named `configuration/item` in the selection, or of
    * every item when the selection is empty, each printed as it is computed.
    * Throws `IllegalArgumentException` for a name no item has.
    */
  def lines(selection: Set[String]): Vector[String] =
    val known = itemsInFileOrder
      .map((configuration, item) => s"${configuration.name}/${item.name}")
      .toSet
    val unknown = selection -- known
    if unknown.nonEmpty then
      throw IllegalArgumentException(
        s"no such items: ${unknown.toVector.sorted}"
      )
    val compiled = compiledConfigurations
    itemsInFileOrder
      .filter((configuration, item) =>
        selection.isEmpty || selection.contains(
          s"${configuration.name}/${item.name}"
        )
      )
      .map { (configuration, item) =>
        val line = FixedPointRuns
          .run(compiled(configuration.name), item)
          .line(configuration.name)
        println(line)
        line
      }

/** `com.yang_bo.gezi.programfamilies.FixedPoints <output> [configuration/item ...]`: the
  * line of every item, or of the items named, written to the output file.
  */
@main def FixedPoints(arguments: String*): Unit = arguments.toList match
  case output :: selection =>
    Files.writeString(
      Paths.get(output),
      FixedPointLines.lines(selection.toSet).mkString("", "\n", "\n")
    )
  case Nil =>
    throw IllegalArgumentException(
      "usage: FixedPoints <output> [configuration/item ...]"
    )
