package gezi.conventions

/** The places of the main sources that name `NoFacts`, the native specializer of no facts, each listed with its reason.
  *
  * Purpose: a term of `NoFacts` holds no storage, so code that builds or reads terms under `NoFacts` where an entry's
  * configuration is meant reads a program as if its backend declared no representation: it neither builds the
  * storages the entry's facts declare nor reads those the program holds. The types keep two configurations' terms
  * apart, but nothing in the types says which configuration a piece of code should work in; this list does, and an
  * unlisted place fails.
  */
object NoFactsBoundaryCheck:

  /** The main sources allowed to name `NoFacts`, by a path prefix (a project, or a file), each with its reason. */
  val allowed: Map[String, String] =
    Map(
      "ir/src/main/" -> "the IR defines NoFacts, crosses the library from it (crossedAllFromNoFacts) and spells a thunk over placeholders of no facts",
      "frontend/src/main/" -> "the front end reads texts, which hold no storage, and formats them under no facts",
      "standardlibrary/src/main/" -> "the library is read under no facts, before the facts that come from it exist",
      "knowledge-reading/src/main/" -> "the knowledge of an entry is read under no facts, as the library is",
      "jit/src/main/scala/gezi/jit/BackendFacts.scala" -> "the facts are built from the library, read under no facts",
      "jit/src/main/scala/gezi/jit/DeclaredFamilies.scala" -> "the declared families are read off the library's facts, under no facts",
      "jit/src/main/scala/gezi/jit/BackendChecks.scala" -> "the backend's checks read the library's facts, under no facts",
      "narrow-blocks/src/main/scala/gezi/narrowblocks/groups/GroupCompilation.scala" ->
        "the group grammar reads the facts' index, whose keys are pure terms of no facts",
      "weakhead-core/src/main/scala/gezi/weakhead/ReadingState.scala" -> "the reading configuration of no facts, the reference reading's",
      "weakhead-core/src/main/scala/gezi/weakhead/ReadingExecutor.scala" -> "the reference reading's executor, the tabled weak head of no facts",
      "weakhead/src/main/scala/gezi/weakhead/oldcorpora/ScottDecoding.scala" -> "the problem corpora's decoding, under no facts",
      "contest-entry/src/main/scala/gezi/contest/entry/EntryData.scala" -> "an entry's data is read under no facts",
      "contest-entry/src/main/scala/gezi/contest/entry/Defaults.scala" -> "the state an entry's data is read in (entryDataState), of no facts",
      "contest-entry/src/main/scala/gezi/contest/entry/ModuleSelectors.scala" -> "a module's selector is a term of the entry's data",
      "contest-entry/src/main/scala/gezi/contest/entry/ExecutorModule.scala" -> "an executor module's parameters are a term of the entry's data",
      "contest-entry/src/main/scala/gezi/contest/entry/ExtractorModule.scala" -> "an extractor module's parameters are a term of the entry's data",
      "contest-entry-generic/src/main/scala/gezi/contest/entry/generic/GenericEntry.scala" ->
        "the state the entry's knowledge was read in, of no facts, before the entry's facts exist",
      "contest-modules-moore/src/main/" -> "the module reads its parameters, a term of the entry's data",
      "contest-modules-plover-families/src/main/" -> "the module reads its parameters, a term of the entry's data",
      "contest-modules-solo-extraction/src/main/" -> "the modules read their parameters, a term of the entry's data",
      "contest-modules-solo-tiering/src/main/" -> "the module reads its parameters, a term of the entry's data",
      "contest-runner/src/main/scala/gezi/contest/runner/PipeLines.scala" -> "the judge's side of the pipe reads a line's text under no facts",
      "contest-judge/src/main/" -> "the judge's reference reading and its reading of the answers' lines, under no facts",
      "contest-corpora/src/main/" -> "the problem corpora are written and read under no facts",
      "programfamilies/src/main/" -> "the generated program families of the framework's tests and benchmarks, under no facts",
      "interface-laws/src/main/" -> "the interface laws' programs of no facts",
      "jmh-pipeline/src/main/" -> "the benchmarks' programs of no facts",
      "migration/src/main/" -> "the migrations of lambdalattice texts, which hold no storage",
      "rewrite-trace/src/main/scala/gezi/rewritetrace/TraceText.scala" -> "a trace's text is read under no facts, the player's reading",
      "rewrite-trace/src/main/scala/gezi/rewritetrace/TraceStart.scala" -> "a trace's start is read under no facts, the player's reading",
      "trace-player/src/main/" -> "the trace player reads traces' texts under no facts"
    )

  private val named = """\bNoFacts\b""".r

  /** The main sources that name `NoFacts` and are not listed, each `path:number: text`. */
  def unlisted(sources: Vector[(String, String)]): Vector[String] =
    sources
      .filter((path, _) => path.contains("/src/main/") && !allowed.keys.exists(path.startsWith))
      .flatMap((path, text) =>
        val code = ScalaSources.commentsBlanked(text).split('\n').toVector
        val lines = text.split('\n').toVector
        lines.zipWithIndex.collect { case (line, index) if named.findFirstIn(code(index)).isDefined => s"$path:${index + 1}: ${line.trim}" }
      )

  /** The listed places that no main source names `NoFacts` in any longer: their entries are deleted. */
  def stale(sources: Vector[(String, String)]): Vector[String] =
    val naming = sources.filter((path, text) => path.contains("/src/main/") && named.findFirstIn(ScalaSources.commentsBlanked(text)).isDefined)
    allowed.keys.filterNot(prefix => naming.exists((path, _) => path.startsWith(prefix))).toVector.sorted

class NoFactsBoundaryTest extends gezi.generatedinputs.FailFastSuite:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => ScalaSources.texts)

  test("NoFacts stands in the main sources only where it is listed, and every listed place names it") {
    val sources = ScalaSources.texts
    assert(sources.nonEmpty, "no Scala source found")
    val unlisted = NoFactsBoundaryCheck.unlisted(sources)
    val stale = NoFactsBoundaryCheck.stale(sources)
    assert(unlisted.isEmpty && stale.isEmpty, s"unlisted:\n${unlisted.mkString("\n")}\nstale:\n${stale.mkString("\n")}")
  }
