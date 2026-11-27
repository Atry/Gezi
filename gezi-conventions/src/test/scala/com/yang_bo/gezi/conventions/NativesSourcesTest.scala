package com.yang_bo.gezi.conventions

import java.nio.file.Files
import java.nio.file.Path
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** A natives project, a directory `gezi-contest-natives-<name>`, where an entry's
  * compiler is written as lemmas and natives rather than as Scala, holds native
  * implementations only: its Scala imports nothing of Gezi but the native
  * interface of `com.yang_bo.gezi.jit` (`NativesProvider`, `NativeBackend`, `Native`, the
  * native values, places and families), and it registers `NativesProvider` and
  * no other service. Its purpose is to catch a natives project that reads a
  * term, an e-graph, a round or a cost (a strategy in Scala under another
  * name), or that registers an entry provider of its own.
  */
class NativesSourcesTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  /** The Gezi packages a natives project may import: the JIT's native
    * interface, which holds the static block method a native implements to be
    * called from a narrow block.
    */
  private val allowed: Vector[String] = Vector("com.yang_bo.gezi.jit.")

  private def directories(root: Path): Vector[Path] =
    Using.resource(Files.list(root))(paths =>
      paths.toList.asScala.toVector.filter(path =>
        Files.isDirectory(path) && path.getFileName.toString.startsWith(
          "gezi-contest-natives-"
        )
      )
    )

  private def filesUnder(root: Path): Vector[Path] =
    directories(root).flatMap(directory =>
      Using.resource(Files.walk(directory))(paths =>
        paths.toList.asScala.toVector.filter(path =>
          Files.isRegularFile(path) && !root
            .relativize(path)
            .toString
            .split('/')
            .contains("target")
        )
      )
    )

  test("a natives project imports nothing of gezi but the native interface") {
    val root = ScalaSources.root
    val imported = filesUnder(root)
      .filter(_.toString.endsWith(".scala"))
      .flatMap(file =>
        Files
          .readString(file)
          .split('\n')
          .toVector
          .map(_.trim)
          .filter(line =>
            line.startsWith("import com.yang_bo.gezi.") && !allowed
              .exists(prefix => line.stripPrefix("import ").startsWith(prefix))
          )
          .map(line => s"${root.relativize(file)}: $line")
      )
    assertEquals(imported, Vector.empty)
  }

  test("a natives project registers NativesProvider and no other service") {
    val root = ScalaSources.root
    val services = filesUnder(root)
      .filter(_.toString.contains("META-INF/services"))
      .map(_.getFileName.toString)
      .filterNot(_ == "com.yang_bo.gezi.jit.NativesProvider")
    assertEquals(services, Vector.empty)
  }
