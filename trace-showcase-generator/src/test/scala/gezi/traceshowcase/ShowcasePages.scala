package gezi.traceshowcase

import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import scala.jdk.CollectionConverters.*
import gezi.contest.corpora.reductions.ReductionGroup
import gezi.contest.corpora.reductions.RepeatedVariants
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Cells
import gezi.contest.entry.Defaults
import gezi.contest.entry.EntryData
import gezi.contest.entry.Interaction
import gezi.contest.entry.generic.GenericEntry
import gezi.contest.entry.generic.GenericEntryProvider
import gezi.ematching.closures.ClosureCompilation
import gezi.frontend.DeBruijnTerm
import gezi.frontend.DeBruijnTermOf
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.frontend.Term
import gezi.ir.Apply
import gezi.ir.BuiltInRule
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.LemmaIdentifier
import gezi.jit.NativesProvider
import gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import gezi.locations.LemmaText
import gezi.locations.Span
import gezi.proofs.OpentheoryArticle
import gezi.proofs.RewriteTrace
import gezi.rewritetrace.Trace
import gezi.rewritetrace.TraceStart
import gezi.rewritetrace.TraceText
import gezi.saturation.StopSignal
import gezi.standardlibrary.LemmaSides
import gezi.standardlibrary.LemmaSources
import gezi.standardlibrary.LibraryFiles
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.StandardLibraryIndex
import gezi.standardlibrary.TermTables
import gezi.strategies.BaselineModules
import gezi.strategies.BaselineRounds
import gezi.strategies.CountedExtractor
import gezi.strategies.ExtractionOptions
import gezi.strategies.FixpointEgraph
import gezi.strategies.FixpointVerdicts
import gezi.strategies.GraphProof
import gezi.strategies.SaturationOptions
import gezi.strategies.StandardIndexer
import gezi.strategies.StandardSaturator
import gezi.strategies.StrategyTesting
import gezi.strategies.TraceFiles
import gezi.weakhead.Expansions
import gezi.ir.{Configured, NativeSpecializer}

private given showcasePagesNoFacts: NoFacts.type = NoFacts

/** The trace player's end-to-end showcase:
  * four traces, each with its player page, an index page, and the player
  * that plays them, written into the directory `trace-showcase` of Gezi by
  * the sbt task `trace-showcase/regenerate`, which runs this program with the
  * directory, the player's linked script and the directory of its style
  * sheets. The directory is deleted and written again whole, so that nothing
  * in it is written by hand (gezi/.gitattributes marks it generated).
  *
  * The four traces:
  *   - K and the choice, and β residuals: small lemmas written here, saturated
  *     by the fixpoint e-graph, the proof of the program's output replayed;
  *   - the entry `contest-entries-wren` on the first point of calls_1000_hot's direct variant,
  *     seed 20261116, under `ArticleDestination.WrittenWithTraces`;
  *   - the HM baseline's type check of `compose boolean_not boolean_not`, the
  *     trace of the proof that its `type_of` is the type the fixture
  *     `TermTables.showcaseTerms` writes, a function from bool to bool. The
  *     type is the fixture's, not chosen here among the graph's terms: a
  *     graph that does not join the two throws.
  */
object ShowcasePages:

  given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  /** Writes the showcase: the arguments are the destination directory,
    * the player's linked `main.js` and the directory of its assets
    * (`player.css` and the webjars under `lib/`).
    */
  def main(arguments: Array[String]): Unit =
    val Array(destinationArgument, scriptArgument, assetsArgument) = arguments: @unchecked
    val destination = Paths.get(destinationArgument).toAbsolutePath.normalize
    deleted(destination)
    Files.createDirectories(destination)
    val pages = Vector(
      small(
        destination,
        "1-k-and-choice",
        Vector(
          "λa. λb. (λx. λy. x) a b" -> "λa. λb. a",
          "λa. (a + a)" -> "λa. a",
          "λa. λb. (a + b)" -> "λa. λb. (b + a)"
        ),
        "(λk. λl. k) (λa. a) (λb. b b) + (λa. a)",
        "K and the choice",
        "Lemmas: K a b = a, a + a = a, a + b = b + a."
      ),
      small(
        destination,
        "2-beta-residuals",
        Vector("λf. λa. (λu. u) (f a)" -> "λf. λa. f a"),
        "(λu. u) ((λx. λy. λz. (z (x (λc. c)) + x)) ((λu. u) ((λx. λz. z (x (λd. d d))) (λa. a))))",
        "β residuals",
        "Lemma: λf. λa. (λu. u) (f a) = λf. λa. f a, with the β rule. The β rule fills a lambda's first hole and leaves a thunk with holes left, which the trace replays in the front end's spelling."
      ),
      wren(destination),
      hindleyMilner(destination)
    )
    Files.writeString(destination.resolve("index.html"), index(pages))
    player(destination.resolve("trace-player"), Paths.get(scriptArgument), Paths.get(assetsArgument))

  /** A page of the index: its file, title, number of steps and description. */
  private final case class Page(file: String, title: String, steps: Int, description: String)

  /** The directory deleted with what it holds, nothing when it is absent. */
  private def deleted(directory: Path): Unit =
    if Files.exists(directory) then
      val paths = scala.util.Using.resource(Files.walk(directory))(_.toList.asScala.toVector)
      paths.sortBy(-_.getNameCount).foreach(Files.delete)

  private def closed[C <: NativeSpecializer & Singleton](text: String)(using C): Configured[C] = Defunctionalization.thunkInstruction[C](Lambdalattice.term(text))

  /** The page of the trace written at the file, beside its directory: the
    * player page `TraceFiles` writes, copied to `name.html`, whose relative
    * paths then reach the player's directory.
    */
  private def published(destination: Path, name: String, traceFile: Path): Unit =
    val _ = Files.copy(TraceFiles.pageFile(traceFile), destination.resolve(s"$name.html"))

  /** The lemma texts with each location's URI relative to the directory of
    * the trace that names it, `../../corpora/compiler/…` for a library file,
    * so that the showcase's files do not depend on where Gezi is checked out
    * and a location still leads to its file in the repository.
    */
  private def relativeTo[C <: NativeSpecializer & Singleton](
      directory: Path,
      texts: Map[(Configured[C], Configured[C]), LemmaText[C]]
  )(using C): Map[(Configured[C], Configured[C]), LemmaText[C]] =
    texts.map((sides, text) => sides -> text.copy(uri = relative(directory, Paths.get(text.uri))))

  /** The entry with its lemma texts relative to the directory, run on the point, its constants of no facts crossed
    * into the entry's configuration, under the stop.
    */
  private def ranWithRelativeTexts[C <: NativeSpecializer & Singleton](
      entry: GenericEntry[C],
      directory: Path,
      point: DeBruijnTermOf[Configured[NoFacts.type]],
      stop: StopSignal
  ): Unit =
    given C = entry.specializer
    val relative = entry.copy(lemmaTexts = relativeTo(directory, entry.lemmaTexts))
    val crossed = DeBruijnTerm.constantsMapped(point, (constant: Configured[NoFacts.type]) =>
      entry.specializer.crossedAllFromNoFacts(Vector(constant))(constant)
    )
    relative.run(Cells.cell(crossed), gezi.hotspot.ExpansionSource.fresh(), stop) match
      case Interaction.Finished(_, _, _) => ()

  /** The path as a relative URI from the directory, its separators `/`. */
  private def relative(directory: Path, file: Path): java.net.URI =
    java.net.URI(null, null, directory.relativize(file).toString.replace(java.io.File.separatorChar, '/'), null)

  /** The number of commands of the trace the file holds. */
  private def steps(traceFile: Path): Int =
    val text = Files.readString(traceFile)
    TraceText.read(text, TraceText.readingLimit(text)).rounds.flatten.size

  /** A small trace: the lemmas, written in a lemma file of the page's
    * directory each side on a line, the fixpoint e-graph's output of the
    * program, and the trace of the proof that the program equals it.
    */
  private def small(
      destination: Path,
      name: String,
      lemmas: Vector[(String, String)],
      program: String,
      title: String,
      lemmasDescription: String
  ): Page =
    val sides = lemmas.zipWithIndex.map { case ((left, right), number) => LemmaSides(LemmaIdentifier(number), closed(left), closed(right)) }
    val directory = destination.resolve(name)
    Files.createDirectories(directory)
    val lemmaFile = directory.resolve("lemmas.lambdalattice")
    val (texts, _) = lemmas.zip(sides).foldLeft((Map.empty[(Configured[NoFacts.type], Configured[NoFacts.type]), LemmaText], 0)) {
      case ((found, offset), ((left, right), lemma)) =>
        val leftSpan = Span(offset, offset + left.length)
        val rightSpan = Span(leftSpan.end + 1, leftSpan.end + 1 + right.length)
        (found.updated((lemma.left, lemma.right), LemmaText(relative(directory, lemmaFile), leftSpan, rightSpan, left, right, Vector.empty)), rightSpan.end + 1)
    }
    val index = StandardLibraryIndex(NoFacts, Vector.empty, sides, Vector.empty, Vector.empty)
    val modules = BaselineRounds.modules
    val strategy = FixpointEgraph(
      index,
      StandardSaturator(
        SaturationOptions(sides.map(_.lemma), BuiltInRule.beforeOptIn, 24, BaselineLemmaEncoding, ClosureCompilation, StandardIndexer, modules.orientationCompiler, gezi.egraph.MemoRetention.Kept, gezi.ir.TermConstruction(gezi.ir.NoFacts))
      ),
      CountedExtractor(ExtractionOptions(Vector("compression")), BaselineModules.table)
    )
    val input = closed(program)
    val outcome = strategy.ran(Vector(input), true, StopSignal.completedWith(scala.concurrent.Future.never)).get
    val Vector(output) = outcome.outputs: @unchecked
    val trace = RewriteTrace.trace(OpentheoryArticle.derivation(index, input, output, outcome.proof.get))
    Files.writeString(lemmaFile, lemmas.map((left, right) => s"$left\n$right\n").mkString)
    val traceFile = directory.resolve("trace.lambdalattice")
    TraceFiles.textWrittenAt(traceFile, TraceStart.written(input, Some(program)), TraceText.writtenWith(trace, texts))
    published(destination, name, traceFile)
    Page(name, title, trace.rounds.flatten.size, s"$lemmasDescription Program: $program.")

  /** The entry `contest-entries-wren` on the first point of calls_1000_hot's direct variant,
    * seed 20261116, its trace written by the entry under
    * `ArticleDestination.WrittenWithTraces`, the run stopped once it is.
    */
  private def wren(destination: Path): Page =
    val name = "3-wren-calls-1000-hot"
    val root = LibraryFiles.buildRoot
    val directory = destination.resolve(name)
    Files.createDirectories(directory)
    val (data, afterEntry) = EntryData.read(root.resolve("contest-entries-wren"), Defaults.entryDataState)
    val (library, initialized) =
      GenericEntryProvider.initializedWithLibrary(
        data,
        gezi.contest.entry.ExecutorModules.registeredFor(root.resolve("contest-entries-wren")),
        gezi.contest.entry.ExtractorModules.registeredFor(root.resolve("contest-entries-wren")),
        NativesProvider.loaded,
        ArticleDestination.WrittenWithTraces(directory),
        afterEntry,
        Defaults.caches()
      )
    val withTexts = initialized.withLemmaTexts(library, root.resolve("contest-entries-wren"))
    val group = ReductionGroup(root, Expansions.none, Defaults.caches())
    val Vector(variant) = RepeatedVariants.families
      .filter((family, _) => family == "repeated_library_hotspots_calls_1000_hot")
      .flatMap(_._2)
      .filter(_.stem.endsWith("direct")): @unchecked
    val point = variant.point(group, 20261116L, variant.nominal.repetitions.start).program.deBruijnTerm(Map.empty)
    val traceFile = directory.resolve("trace-1.lambdalattice")
    val traceWritten = new StopSignal:
      def stopRequested: Boolean = Files.exists(traceFile)
    ranWithRelativeTexts(withTexts, directory, point, traceWritten)
    if !Files.exists(traceFile) then throw IllegalStateException(s"wren's entry wrote no trace in $directory")
    published(destination, name, traceFile)
    Page(
      name,
      "wren's entry on a contest hot point",
      steps(traceFile),
      "repeated_library_hotspots_calls_1000_hot/direct, first point, seed 20261116: wren's lemma rounds from the program to the extraction, then the numerals the native blocks computed. The terms are large: this is what the compiler really does."
    )

  /** The HM baseline's type check of `compose boolean_not boolean_not`: the
    * round `prolog_backend_type_check` saturated on the program, and the
    * trace of the graph's proof that the program's `type_of` is the type the
    * fixture writes.
    */
  private def hindleyMilner(destination: Path): Page =
    val name = "4-hindley-milner"
    val root = LibraryFiles.buildRoot
    val library = LibraryFiles.compiled("tests/library_fixtures/native_route_with_prolog_backend.lambdalattice", Vector.empty)
    val round = StrategyTesting.round("prolog_backend_type_check")
    val options = BaselineRounds.saturationOptions(library, round, BuiltInRule.beforeOptIn, 6000)
    val terms = StandardLibrary.entryMembers(root, TermTables.jitLibraryTerms, Expansions.none)._1
    val showcase = StandardLibrary.entryMembers(root, TermTables.showcaseTerms, Expansions.none)._1
    val heads = FixpointVerdicts.zeroUniverseHeads
    def term(key: String): Term = Term.closed(terms(key))
    val input = StrategyTesting.programInput(library, term("compose")(term("boolean_not"))(term("boolean_not")))
    val run = FixpointEgraph.saturated(library.index, Vector(input), options, explained = true, StopSignal.completedWith(scala.concurrent.Future.never))
    val left = NoFacts.application(showcase("type_of"), input)
    val right = showcase("function_from_bool_to_bool")
    val proof = GraphProof.proof(run.graph, Vector((left, right)), FixpointEgraph.lemmas(library.index, options))
    val trace = RewriteTrace.trace(OpentheoryArticle.derivation(library.index, left, right, proof))
    val directory = destination.resolve(name)
    val texts = relativeTo(directory, LemmaSources.textsUnder(root, Vector(root.resolve("corpora")), library.index))
    val names = TraceText.namesUsed(trace, texts).map(_.swap).toMap ++
      Vector("compose", "boolean_not").map(key => terms(key) -> key) ++
      heads.map(_.swap) ++
      Map(showcase("type_of") -> "type_of")
    Files.createDirectories(directory)
    val traceFile = directory.resolve("trace.lambdalattice")
    TraceFiles.textWrittenAt(traceFile, TraceStart.written(left, None, names), TraceText.writtenWith(trace, texts))
    published(destination, name, traceFile)
    Page(
      name,
      "The HM baseline derives a type",
      trace.rounds.flatten.size,
      "Program: compose boolean_not boolean_not. Lemmas: the HM baseline's, corpora/compiler/hindley_milner_unions.lambdalattice (round prolog_backend_type_check), every step an instance of one of them. The trace proves that type_of of the program is a function from bool to bool, bool being structure (alternative no_field (alternative no_field no_alternative)). Library terms are written by name."
    )

  /** The index page: what a page shows and how to use the player, then a
    * link to each page with its steps and description.
    */
  private def index(pages: Vector[Page]): String =
    val items = pages
      .map(page =>
        s"""<li class="mb-3"><a href="${page.file}.html">${page.title}</a> (${page.steps} steps).<br>${page.description}</li>"""
      )
      .mkString("\n")
    s"""<!doctype html>
       |<html lang="en">
       |<head>
       |<meta charset="utf-8">
       |<meta name="viewport" content="width=device-width, initial-scale=1">
       |<title>gezi trace showcase</title>
       |<link rel="stylesheet" href="trace-player/lib/bootstrap/dist/css/bootstrap.min.css">
       |</head>
       |<body>
       |<main class="container py-4">
       |<h1 class="h3">gezi trace showcase</h1>
       |<p>Each page plays one trace: the program the compiler started from, then one term per step. A trace holds only the commands, and the start is written beside it; the player computes every step's term by replaying the commands from the start. Use the buttons or type a step number; the URL hash keeps the position, the view and the shared subterms inlined.</p>
       |<p>The two buttons at the right of the control bar switch between the term drawn as nested boxes and the term as its text. Both write each shared subterm once, under its name, and refer to it by that name where it occurs; a click on the name β-reduces it into its occurrences, and the button on an inlined occurrence binds it again. The node the step rewrote is highlighted.</p>
       |<ul class="list-unstyled">
       |$items
       |</ul>
       |<p class="text-body-secondary">Generated by <code>sbt trace-showcase/regenerate</code> in gezi.</p>
       |</main>
       |</body>
       |</html>
       |""".stripMargin

  /** The player's files the pages load: its linked script, its style sheet,
    * and the style sheets of Bootstrap and Bootstrap Icons with the icons'
    * fonts, at the paths the pages name (`gezi.rewritetrace.TracePageText`).
    */
  private def player(directory: Path, script: Path, assets: Path): Unit =
    val files = Vector(
      "player.css",
      "lib/bootstrap/dist/css/bootstrap.min.css",
      "lib/bootstrap-icons/font/bootstrap-icons.min.css",
      "lib/bootstrap-icons/font/fonts/bootstrap-icons.woff2",
      "lib/bootstrap-icons/font/fonts/bootstrap-icons.woff"
    )
    files.foreach(file =>
      val target = directory.resolve(file)
      Files.createDirectories(target.getParent)
      val _ = Files.copy(assets.resolve(file), target)
    )
    val _ = Files.copy(script, directory.resolve("main.js"))
