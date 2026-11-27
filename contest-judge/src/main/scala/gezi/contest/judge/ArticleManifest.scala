package gezi.contest.judge

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.StandardOpenOption
import gezi.frontend.ExchangeText
import gezi.proofs.HolTermText
import gezi.proofs.OpentheoryArticle
import gezi.standardlibrary.StandardLibraryIndex

/** What every manifest of a pass records about the judge: the build that
  * judged (`TableFile.build`, the Gezi commit, `-dirty` when the tree
  * differs from it), the path, relative to the build root, of the
  * lambdalattice file whose member `knowledge` it compiled
  * (`--article-knowledge`, `SupervisorCommand.articleLibrary`), and that
  * library's index, against which a point's IR is encoded. The file's
  * content at a path can change, so the path names the knowledge only
  * together with the build: the manifest records both.
  */
final case class ManifestProvenance(build: String, knowledge: String, index: StandardLibraryIndex[gezi.ir.NoFacts.type])

/** The manifest of a checked point's articles: what an offline verifier needs to check them, written
  * beside the article directory as `manifest.tsv`. The judge writes it and
  * never reads it. Its lines, each a key and a value joined by a tab, the
  * value holding no tab and no newline:
  *
  *   - a comment line, `#` and what the file holds;
  *   - `point`, the point's name;
  *   - `outcome`, the point's outcome in `articles.tsv`
  *     (`ArticleOutcome.written`); only "文章已存" (articles stored) is
  *     evidence of an answer the scored pass gave;
  *   - `build`, `knowledge`, the judge's build and the path of the file of
  *     the library's knowledge as the option gave it (`ManifestProvenance`),
  *     the file read at that build;
  *   - `program`, the point's program as the points file holds it and the
  *     judge sent it, an `ExchangeText` line;
  *   - `encoded`, the point's IR, the instruction its line reads as,
  *     as the article writer encodes it (`OpentheoryArticle.termEncoded`),
  *     written as `HolTermText.sharedText` writes a HOL term: a
  *     self-contained text, every name and type in it, each shared subterm
  *     written once and referred to by its number, as large as the program
  *     as a graph; expanding the numbers gives the text `HolTermText.text`
  *     writes, which Lean's `Encoding.encode` writes alike
  *     (`OpentheoryArticleFixpointRunsTest`). The tree text was written here
  *     before, and on a point of `repeated_library_edit_distances_small` it
  *     ran the judge's 256m heap out (MEASURED 2026-11-20: 26,476,705
  *     characters on another point of the same kind, whose exchange line is
  *     7,699). An
  *     article's dictionary shares subterms by `def` and `ref`, so no
  *     fragment of an article stands alone for the term; this text does. The first article's left
  *     side is this term when the entry ran no step before its schedule,
  *     its thunk constants numbered otherwise;
  *   - `definition`, once for each thunk constant of `encoded` in the order
  *     of its number, the constant's defining term
  *     (`OpentheoryArticle.definingTermEncoded`), `LambdaJit.Code.thunkOf`
  *     of its code and holes, as `HolTermText.sharedText` writes it, as
  *     large as the code as a graph (its unary numbers shared): the constant
  *     `LambdaJit.thunk.N` of `encoded` is the thunk of the N-th, from 0;
  *   - `article`, once for each article in the order of the chain, its path
  *     relative to the manifest's directory (`article/round-1.art`, ...).
  *
  * FIXME (2026-11-09): the on-demand verifier that reads this evidence https://github.com/Atry/private-overlay/issues/1997
  * does not exist yet. Its design: Lean proofs that each round's input
  * is ≃_O to its output (Definition 14), generated from the rewrite trace
  * and checked together with the Lean library exported by lean4export, by
  * the Lean kernel or nanoda, the choice pending a measurement of the two.
  * No article is read by the Lean kernel's evaluator
  * (that reading took 73.4 s and 8.2 GB on an 8,198-line
  * contest article, and stopped with "(kernel) deep recursion detected" on
  * a 15,608-line one, while contest articles reach 50,867 lines).
  *
  * FIXME (2026-11-09): this manifest is an ad hoc TSV format, against https://github.com/Atry/private-overlay/issues/2045
  * CONTRIBUTING.md, "Configuration and data files are lambdalattice, or a framework's own format". The point's trace
  * file, a lambdalattice file, is to replace it, the judge storing the trace instead; the format stays until
  * then.
  */
object ArticleManifest:

  /** The manifest's file name in the point's directory. */
  val fileName: String = "manifest.tsv"

  /** The manifest's lines for the point, its check's outcome and its
    * articles, the paths of the articles relative to `pointDirectory`.
    * Throws `IllegalStateException` when a value holds a tab or a newline.
    */
  def lines(
      point: Point,
      outcome: ArticleOutcome,
      articles: Vector[Path],
      pointDirectory: Path,
      provenance: ManifestProvenance
  ): Vector[String] =
    val named = OpentheoryArticle.termEncoded(provenance.index, point.program)
    val Vector(encoded) = named.terms: @unchecked
    val definitions = named.definitions.map((code, holes) =>
      "definition" -> HolTermText.sharedText(OpentheoryArticle.definingTermEncoded(provenance.index, code, holes))
    )
    val fields = Vector(
      "point" -> point.name,
      "outcome" -> outcome.written,
      "build" -> provenance.build,
      "knowledge" -> provenance.knowledge,
      "program" -> point.programLine,
      "encoded" -> HolTermText.sharedText(encoded)
    ) ++ definitions ++ articles.map(article => "article" -> pointDirectory.relativize(article).toString)
    s"# the articles of one checked point (docs/design/gezi-judge.md, section 4.3)" +: fields.map { (key, value) =>
      if value.exists(character => character == '\t' || character == '\n') then
        throw IllegalStateException(s"the manifest's $key of ${point.name} holds a tab or a newline")
      s"$key\t$value"
    }

  /** The lines written to `manifest.tsv` in the point's directory, one a
    * line. The file must not exist: `CREATE_NEW` neither overwrites nor
    * follows a link left at its name.
    */
  def written(pointDirectory: Path, lines: Vector[String]): Unit =
    Files.writeString(pointDirectory.resolve(fileName), lines.mkString("", "\n", "\n"), StandardCharsets.UTF_8, StandardOpenOption.CREATE_NEW)

/** The manifests of the checked points, written by a JVM of their own
  * (`judgeArticleManifests`) and not by the supervisor: a manifest encodes
  * the point's IR and the defining terms of its thunks, which a point's
  * program makes larger than the supervisor's heap, whose points it holds as
  * their lines (`Point`). Measured 2026-11-22 by the setter's pass of the
  * MIXINv2 builtin families at the supervisor's 256 MB: the pass itself
  * held about 80 to 90 MB, and the manifest of
  * `repeated_reduction_mixin_builtin_boolean_depth_12/respelled/repetitions_1`
  * ran it out of memory. The JVM is the judge's own (its classpath, not an
  * entry's), started on the pass's placement with the round's entry heap,
  * reads the points file and the knowledge itself, and writes one manifest
  * for each request: a point's name and its directory, with its check's
  * outcome, one request a line, tab-separated, in `requestsFileName` of the
  * articles' directory.
  */
object ArticleManifests:

  /** The requests' file name in the articles' directory. */
  val requestsFileName: String = "manifest-requests.tsv"

  /** Where the knowledge of the manifests is read from: a file of the build
    * root (`--article-knowledge`, `SupervisorCommand.articleLibrary`), or an
    * entry's directory (`SupervisorCommand.entryKnowledgeLibrary`).
    */
  enum KnowledgeSource:
    case ArticleFile(path: String)
    case EntryDirectory(directory: Path)

  /** The requests' lines: each point's name, its directory and its
    * outcome's written form, tab-separated.
    */
  def requestLines(requests: Vector[(Point, ArticleOutcome, Path)]): Vector[String] =
    requests.map((point, outcome, directory) => Vector(point.name, directory.toString, outcome.written).mkString("\t"))

  /** The manifests of the requests' file written, each in its point's
    * directory, the points read from the points directory and the library
    * from the knowledge source. Throws `IllegalArgumentException` for a
    * request of another shape, a point the points file does not hold, and an
    * outcome no `ArticleOutcome` writes.
    */
  def written(requests: Path, pointsDirectory: Path, buildRoot: Path, build: String, knowledgeName: String, source: KnowledgeSource): Unit =
    val points = PointsFile.read(pointsDirectory).map(point => point.name -> point).toMap
    val library = source match
      case KnowledgeSource.ArticleFile(path)         => SupervisorCommand.articleLibrary(buildRoot, path)
      case KnowledgeSource.EntryDirectory(directory) => SupervisorCommand.entryKnowledgeLibrary(directory)
    val provenance = ManifestProvenance(build, knowledgeName, library.index)
    Files.readAllLines(requests, StandardCharsets.UTF_8).forEach(line =>
      line.split("\t", -1).toVector match
        case Vector(name, directoryText, outcomeText) =>
          val point = points.getOrElse(name, throw IllegalArgumentException(s"no point $name in $pointsDirectory"))
          val outcome = ArticleOutcome.values.find(_.written == outcomeText).getOrElse(
            throw IllegalArgumentException(s"no article outcome is written $outcomeText")
          )
          val directory = Path.of(directoryText)
          ArticleManifest.written(directory, ArticleManifest.lines(point, outcome, ArticleCheck.articleFiles(directory.resolve("article")), directory, provenance))
        case fields => throw IllegalArgumentException(s"a manifest request of ${fields.size} fields, not 3: $line")
    )

/** The manifests' JVM's main (`ArticleManifests`): `--requests`, `--points`,
  * `--build-root`, `--build`, `--knowledge-name`, and `--article-knowledge`
  * (a file of the build root) or `--entry-directory`.
  */
@main def judgeArticleManifests(arguments: String*): Unit =
  val options = SupervisorCommand.options(arguments.toVector)
  def required(name: String): String = options.getOrElse(name, throw IllegalArgumentException(s"the option --$name is required"))
  val source = (options.get("article-knowledge"), options.get("entry-directory")) match
    case (Some(file), None)      => ArticleManifests.KnowledgeSource.ArticleFile(file)
    case (None, Some(directory)) => ArticleManifests.KnowledgeSource.EntryDirectory(Path.of(directory))
    case _                       => throw IllegalArgumentException("exactly one of --article-knowledge and --entry-directory is required")
  ArticleManifests.written(
    Path.of(required("requests")),
    Path.of(required("points")),
    Path.of(required("build-root")),
    required("build"),
    required("knowledge-name"),
    source
  )
