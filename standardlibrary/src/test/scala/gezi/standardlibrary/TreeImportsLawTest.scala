package gezi.standardlibrary

import java.nio.file.Files
import java.nio.file.Path
import gezi.knowledgereading.KnowledgeReading
import gezi.weakhead.ContinuationReading
import gezi.weakhead.Mode
import gezi.ir.NoFacts
import gezi.ir.Value
import gezi.weakhead.WeakHead
import scala.jdk.StreamConverters.*
import scala.util.Using

/** The law that every file of `corpora` and of the fixture trees reads, by
  * projection in its tree, to a live value: at least one parallel set, never
  * top alone. A file's term is read as the host reads an entry
  * (`StandardLibrary.entryTerm`: its instance applied to a handler, its
  * imports read on the way), and its imports stand in head position on the
  * spine (`omega X "key" (λname. …)`), so a single import that reads top makes
  * the whole file read top, and the law fails on it. Its failure is a defect by
  * definition.
  *
  * Its purpose is to catch an import that names the wrong mixin, which the
  * front end does not warn of. The mechanism the law exists for is
  * shadowing: the innermost binder of a name wins, and a file or a directory
  * binds its own name over its content, so an entry named like an enclosing directory hides that
  * directory from everything under it. A fixture with a directory `corpora`
  * of its own hid the source tree's `corpora`, and a file named like its
  * fixture's directory hid the fixture: `omega corpora "library"` then read
  * the fixture's own mixin, which has no member `library`, and the import was
  * top (the case of `codec_literals`, moved in 7d566029d).
  *
  * The two fixtures whose purpose is a file that does not read are the dark
  * witnesses, and they are read dark here, so that the law does not hold
  * vacuously. `path_reaches_nothing` imports a file that is not there.
  * `recursive` has two library files that import each other, whose least
  * reading is top.
  *
  * Each file is read from a fresh compilation's state
  * (`KnowledgeReading.compilationState`) under the continuation reading the
  * in-tree contest entries choose, `ContinuationReading.Packed`,
  * as a compilation
  * reads its knowledge: its term by `StandardLibrary.entryTerm`, then its
  * parallel sets under the tabled weak head that knows top. MEASURED 2026-11-12 (a scratch
  * probe over the same files, loadavg about 2): at most 51,709 complete
  * tables after the entry's term (tests/round_fixtures/fixed_width_type_check.lambdalattice),
  * above a single read's limit of 50,000 (`ReadingState.defaultTableLimit`)
  * and within a compilation's (`KnowledgeReading.compilationTableLimit`),
  * and at most 27 steps for the parallel sets (tests/jit_fixtures/library_terms.lambdalattice),
  * hence the limit `setsLimit`. The problem tables under `problems/` are not
  * read here.
  */
class TreeImportsLawTest extends gezi.generatedinputs.FailFastSuite:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of TreeImportsLawTest, "tests/standard_library_fixtures/opacity/compiler/opacity_terms.lambdalattice reads to a live value", takes 3.979 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "s")

  private val root: Path = LibraryFiles.buildRoot

  given NoFacts.type = NoFacts

  /** The steps the parallel sets of one file's term may take: the measured
    * 27, with room for a fixture a few times larger.
    */
  private val setsLimit: Long = 1000

  /** The trees, each with the directory its files are read in: `corpora`
    * in itself, as the libraries mount it, and each fixture tree in the
    * project's directory, as `LibraryFiles` mounts the fixtures.
    */
  private val trees: Vector[(Path, Path)] =
    Vector(root.resolve("corpora") -> root.resolve("corpora")) ++
      Vector("tests/standard_library_fixtures", "tests/jit_fixtures", "tests/round_fixtures").map(tree => root -> root.resolve(tree))

  /** The files that are to read dark, each the reason. */
  private val darkWitnesses: Map[String, String] = Map(
    "tests/standard_library_fixtures/path_reaches_nothing/compiler/u.lambdalattice" -> "a path that reaches nothing",
    "tests/standard_library_fixtures/recursive/compiler/r.lambdalattice" -> "an import of a file in a cycle",
    "tests/standard_library_fixtures/recursive/library/r/a.lambdalattice" -> "a file in a cycle",
    "tests/standard_library_fixtures/recursive/library/r/b.lambdalattice" -> "a file in a cycle"
  )

  private def files(tree: Path): Vector[Path] =
    Using
      .resource(Files.walk(tree))(_.toScala(Vector))
      .filter(path => Files.isRegularFile(path) && path.getFileName.toString.endsWith(".lambdalattice"))
      .sorted

  /** The number of parallel sets the file's term reads to. */
  private def parallelSets(visible: Path, file: Path): Int =
    val StandardLibrary.EntryReading(instance, afterEntry, _, _) = StandardLibrary.entryTerm(visible, file, KnowledgeReading.compilationState.copy(continuations = ContinuationReading.Packed))
    val (sets, _) = KnowledgeReading.run(WeakHead.heads(Mode.TablingWeakHead, Value.of(instance)).collected, setsLimit, afterEntry)
    sets.size

  trees.foreach((visible, tree) =>
    files(tree).foreach(file =>
      val relative = root.relativize(file).toString
      darkWitnesses.get(relative) match
        case Some(reason) =>
          test(s"$relative reads dark: $reason") {
            assertEquals(parallelSets(visible, file), 0)
          }
        case None =>
          test(s"$relative reads to a live value") {
            assert(parallelSets(visible, file) > 0, s"$relative reads top: an import names a mixin that has no such member")
          }
    )
  )

  test("every dark witness is a file of a tree") {
    val read = trees.flatMap((_, tree) => files(tree)).map(file => root.relativize(file).toString).toSet
    assertEquals(darkWitnesses.keySet -- read, Set.empty[String])
  }
