package gezi.standardlibrary

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import scala.jdk.CollectionConverters.*
import scala.util.Using
import snapshot4s.generated.snapshotConfig

/** The lemma declarations `LemmaSources.declared` finds in the knowledge
  * files of `corpora/compiler`, each with the text of its two sides, the
  * slices of the file at the spans it gives.
  *
  * Purpose: catch a reader that misses a declaration, decodes a name
  * otherwise than the literal the file writes, or takes a side's span from
  * another node, so that a trace's lemma would
  * point at the wrong text. The input is the corpus itself, the files the
  * traces' lemmas come from; the expected output is as complex as the files,
  * so it is a snapshot.
  */
class LemmaSourcesSnapshotTest extends gezi.generatedinputs.FailFastSuite with snapshot4s.munit.SnapshotAssertions:

  /** One test per file, so that each reads one file within the default
    * deadline: all 39 files in one test took 2.5 s to 3.0 s on cores 4-7,
    * 2026-11-17, over the 3 s deadline once.
    */
  private val files: Vector[java.nio.file.Path] =
    Using
      .resource(Files.list(LibraryFiles.buildRoot.resolve("corpora").resolve("compiler")))(_.toList.asScala.toVector)
      .filter(_.getFileName.toString.endsWith(".lambdalattice"))
      .sortBy(_.getFileName.toString)

  files.foreach(file =>
    val name = file.getFileName.toString.stripSuffix(".lambdalattice")
    test(s"the lemma declarations of corpora/compiler/$name, with their sides' text") {
      val text = Files.readString(file, StandardCharsets.UTF_8)
      // The text's code points, in which the spans count, the surrogate pairs
      // of a code point beyond the basic plane joined.
      @scala.annotation.tailrec
      def codePointsFrom(index: Int, found: Vector[Int]): Vector[Int] =
        if index >= text.length then found
        else
          val point = text.codePointAt(index)
          codePointsFrom(index + Character.charCount(point), found :+ point)
      val codePoints = codePointsFrom(0, Vector.empty)
      def slice(span: gezi.locations.Span): String =
        codePoints.slice(span.start, span.end).map(Character.toString(_)).mkString
      val lines = LemmaSources
        .declared(file, text)
        .map(found => s"${found.name}: ${slice(found.left)} = ${slice(found.right)}")
      assertFileSnapshot(lines.mkString("", "\n", "\n"), s"lemma_sources/compiler/$name.txt")
    }
  )
