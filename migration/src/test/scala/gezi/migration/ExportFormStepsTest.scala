package gezi.migration

import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import gezi.directorysugar.DirectoryTree
import gezi.ir.Instruction
import gezi.knowledgereading.KnowledgeReading
import gezi.knowledgereading.Reading
import gezi.weakhead.ContinuationReading
import scala.jdk.StreamConverters.*
import scala.util.Using
import snapshot4s.generated.snapshotConfig

/** The forms of a file's export and import the diamond is written in. */
enum Form(val label: String):
  case Tuple extends Form("tuple")
  case Export extends Form("export")
  case Packed extends Form("packed")
  case ExportPackedReading extends Form("export, packed reading")

/** The evaluator steps and tables of reading a file's fields, for the two
  * forms of a file's export, a third form of import that measures a fix of the export form's cost, and
  * the export form read with that fix in the evaluator, on a diamond of imports: `d_0` exports `λz. z`, and each `d_i` imports
  * `d_(i-1)` twice, on two lines of its spine, and exports `λz. a`, a the
  * first import's field. The tree has i + 1 files under `d_i`, and 2^i paths of
  * imports from `d_i` down to `d_0`.
  *
  *   - The tuple form ends the spine with `λtuple. tuple M`: the instance
  *     of a file, `omega (omega corpora "d_i")`, is a closed term in the head
  *     position of its importers, so its spine is reduced once and its table
  *     is shared.
  *   - The export form, `λexport. … export M`, has the spine under
  *     `export`: an importer applies the instance to its own continuation,
  *     a closed term of its own, so that the tabled weak head reduces the
  *     imported file's spine once for each importer, and that spine's own
  *     imports once for each of those, once per path.
  *   - The packed form keeps the export form's files and has each importer
  *     apply the instance to the closed tuple maker `λm. λt. t m` before its
  *     continuation, `f pack k`, equal to `f k` by the β rule when `f` hands
  *     its export on in tail position. `f pack` is one closed term for every
  *     importer, so its table is shared: the counts an evaluator that does
  *     this itself would reach.
  *   - The export form read under the continuation reading `Packed`, the
  *     evaluator that does this itself; every other form is read under
  *     `Substituted`.
  *
  * Its purpose: the cost of a continuation per import is a defect, since
  * the FFI is in continuation passing style and a slow continuation would
  * make it unusable, and the snapshot's diff shows a change of the evaluator's sharing that
  * moves the export form's counts from the paths towards the files. The
  * depths are the input, a count of files, as `jmh-pipeline`'s counts take
  * their copies.
  */
class ExportFormStepsTest extends gezi.generatedinputs.FailFastSuite with snapshot4s.munit.SnapshotAssertions:

  // Measured 2026-11-20 on CPUs 0-3 and 8-11 (nice 10), the 1-minute load 3.3: the test takes 3.94 s, 36 reads (four
  // forms, nine depths) each from a fresh reading state and from the tree's root (about 6,500 steps each before any
  // import), which the counts need, since a state shared between the reads would hide the cost of each. Before the
  // fourth form, 27 reads took 4.33 s on CPUs 8,9 at the load 12.8 and 5.74 s at the load 24 to 34. The bound is 1.5
  // times 4.33 s rounded up, which covers the reading with four forms.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(7, "s")

  /** The steps a read may take: the largest read below takes far fewer. */
  private val limit: Long = 2000000

  private val trees: Path = Files.createDirectories(Paths.get("target", "export-form-steps").toAbsolutePath.normalize)

  /** The text of `d_index` in the form. */
  private def moduleText(index: Int, form: Form): String =
    val imports =
      if index == 0 then ""
      else
        val instance = s"""omega (omega corpora "d_${index - 1}")"""
        val imported = if form == Form.Packed then s"$instance (λm. λt. t m)" else instance
        s"(λtuple. tuple λmixin. mixin mixin) λomega.\n$imported λa.\n$imported λb.\n"
    val member = if index == 0 then "(λz. z)" else "(λz. a)"
    if form == Form.Tuple then s"${imports}λtuple. tuple $member\n" else s"λexport. ${imports}export $member\n"

  /** The deepest file of the diamond. */
  private val deepest: Int = 8

  /** The steps and the tables of reading the fields of `d_0` to `d_deepest`
    * in the form, each from a fresh compilation state, the files written
    * once under `corpora`, so that every read sees the same directory. The
    * path is the same for every form and every run, since a read spends
    * steps on the path's URI.
    */
  private def counts(form: Form): Vector[(Long, Int)] =
    val corpora = trees.resolve("tree").resolve("corpora")
    if Files.exists(corpora.getParent) then
      Using.resource(Files.walk(corpora.getParent))(_.toScala(Vector)).reverse.foreach(Files.delete)
    Files.createDirectories(corpora)
    (0 to deepest).foreach(index =>
      val _ = Files.writeString(corpora.resolve(s"d_$index${DirectoryTree.fileExtension}"), moduleText(index, form))
    )
    val read = (0 to deepest).toVector.map(depth =>
      val instance = DirectoryTree.instance(corpora, corpora.resolve(s"d_$depth${DirectoryTree.fileExtension}"))
      val reading: Reading[Vector[Instruction]] =
        KnowledgeReading.alternative(instance, 1).map(_._2.map(KnowledgeReading.term(_, Set.empty)))
      val continuations = if form == Form.ExportPackedReading then ContinuationReading.Packed else ContinuationReading.Substituted
      val (_, after) = KnowledgeReading.run(reading, limit, KnowledgeReading.compilationState.copy(continuations = continuations))
      (after.budget.spent, after.tables.complete.size + after.tables.open.size)
    )
    Using.resource(Files.walk(corpora.getParent))(_.toScala(Vector)).reverse.foreach(Files.delete)
    read

  test("steps and tables of a diamond of imports, by export form") {
    val read = Form.values.toVector.map(form => form -> counts(form))
    val rows = (0 to deepest).toVector.flatMap(depth =>
      read.map { case (form, byDepth) =>
        val (steps, tables) = byDepth(depth)
        s"$depth\t${form.label}\t$steps\t$tables"
      }
    )
    assertFileSnapshot(rows.mkString("depth\tform\tsteps\ttables\n", "\n", "\n"), "export_form/diamond_counts.tsv")
  }
