package gezi.contest.entry

import java.net.URI
import java.nio.file.Files
import java.nio.file.Paths
import gezi.directorysugar.DirectoryTree
import gezi.ir.Configured
import gezi.ir.NoFacts
import scala.jdk.StreamConverters.*
import scala.util.Using

private given corporaTreeTestNoFacts: NoFacts.type = NoFacts

/** The whole-tree check of the corpora (an error of a file is raised only when
  * its URI node is expanded, so a check expands the whole tree). Its purpose is
  * to catch a file of `corpora` that does not read in its scope, a malformed
  * text or a name outside the scope, which no reading that reaches it has yet
  * met: the URI node of `corpora` and every URI node its expansions hold are
  * expanded (`DirectoryTree.expansion`), and every `.lambdalattice` file under
  * it is among the files expanded.
  */
class CorporaTreeTest extends gezi.generatedinputs.FailFastSuite:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of CorporaTreeTest, "every file of corpora reads in its scope", takes 6.153 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(10, "s")

  test("every file of corpora reads in its scope") {
    val corpora = Paths
      .get(sys.props("gezi.buildRoot"))
      .toAbsolutePath
      .normalize
      .resolve("corpora")
    val expanded = expandedFrom(NoFacts.uri(corpora.toUri))
    val files = Using
      .resource(Files.walk(corpora))(_.toScala(Vector))
      .filter(path =>
        Files.isRegularFile(path) && path.getFileName.toString.endsWith(
          DirectoryTree.fileExtension
        )
      )
      .filterNot(path =>
        val relative = corpora.relativize(path)
        (0 until relative.getNameCount).exists(index =>
          relative.getName(index).toString.startsWith(".")
        )
      )
      .map(_.toUri)
      .toSet
    assertEquals(
      expanded.filter(_.getPath.endsWith(DirectoryTree.fileExtension)),
      files
    )
  }

  /** The URIs of the URI nodes expanded: the node's and those of every URI node
    * its expansion holds, expanded in turn.
    */
  private def expandedFrom(start: Configured[NoFacts.type]): Set[URI] =
    @scala.annotation.tailrec
    def walked(
        pending: List[Configured[NoFacts.type]],
        seen: Set[Configured[NoFacts.type]],
        found: Set[URI]
    ): Set[URI] = pending match
      case Nil                                      => found
      case instruction :: rest if seen(instruction) => walked(rest, seen, found)
      case instruction :: rest                      =>
        instruction.uri match
          case Some(uri) =>
            walked(
              DirectoryTree.expansion(instruction) :: rest,
              seen + instruction,
              found + uri
            )
          case None =>
            val parts = instruction.layer match
              case gezi.ir.Apply(function, argument) => List(function, argument)
              case gezi.ir.Parallel(left, right)     => List(left, right)
              case gezi.ir.Choice(left, right)       => List(left, right)
              case gezi.ir.Thunk(_, _, fillings)     => fillings.toList
              case _                                 => Nil
            walked(parts ++ rest, seen + instruction, found)
    walked(List(start), Set.empty, Set.empty)
