package gezi.contest.entry.generic

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Cells
import gezi.contest.entry.CompilationPlaceOption
import gezi.contest.entry.Count
import gezi.contest.entry.Defaults
import gezi.contest.entry.Entry
import gezi.contest.entry.EntryData
import gezi.contest.entry.EntryProvider
import gezi.contest.entry.ExecutorModules
import gezi.contest.entry.ExtractorModules
import gezi.contest.entry.Interacted
import gezi.contest.entry.Interaction
import gezi.contest.entry.Judgments
import gezi.contest.entry.OutputDisplay
import gezi.contest.entry.Phase
import gezi.contest.entry.Report
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.hotspot.Budget
import gezi.hotspot.Cache
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.Executor
import gezi.hotspot.ExpansionSource
import gezi.hotspot.ForeignService
import gezi.ir.Instruction
import gezi.jit.BackendChecks
import gezi.jit.BackendFacts
import gezi.jit.Jit
import gezi.jit.NativeBackend
import gezi.jit.NativesProvider
import gezi.narrowblocks.LemmaRoundsResult
import gezi.narrowblocks.PreparedLemmaCompilation
import gezi.narrowblocks.ProgramCompilation
import gezi.lemmaencoding.EncodedLemma
import gezi.proofs.OpentheoryArticle
import gezi.proofs.RewriteTrace
import gezi.rewritetrace.TraceStart
import gezi.rewritetrace.TraceText
import gezi.saturation.End
import gezi.saturation.StopSignal
import gezi.standardlibrary.LemmaSources
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.StandardLibraryIndex
import gezi.strategies.GraphProof
import gezi.strategies.TraceFiles
import gezi.weakhead.Reading
import gezi.weakhead.ReadingState

/** The framework's entry for an entry written as data, whose compiler is
  * written with lemmas and natives and no Scala of its own: it reads the
  * entry's `entry.lambdalattice` (`EntryData`) and its natives (`NativesProvider`),
  * compiles the library with the natives' checks, builds the JIT of the
  * data's options, and prepares each lemma round once for the library's
  * index. Nothing is saturated, extracted, compiled to a block or evaluated
  * here.
  */
final class GenericEntryProvider extends EntryProvider:

  // The cache service `caches` is the dependencies of the entry's executor, which keeps the complete tables of its
  // readings there, the weak head's and the JIT's instance table's, and the JIT's compiled codes, when the entry's
  // data chooses a `table_sharing` other than `local`.
  def initial(entryDirectory: Path, caches: Cache, articles: ArticleDestination): Entry =
    val (data, afterEntry) =
      EntryData.read(entryDirectory, Defaults.entryDataState)
    val entry =
      GenericEntryProvider.initialized(
        data,
        ExecutorModules.registeredFor(entryDirectory),
        ExtractorModules.registeredFor(entryDirectory),
        NativesProvider.loaded,
        articles,
        afterEntry,
        caches
      )
    articles match
      case ArticleDestination.WrittenWithTraces(_) => GenericEntryProvider.withLemmaTexts(entry, entryDirectory)
      case _                                       => entry

object GenericEntryProvider:

  /** The entry with its lemmas' texts, for its traces only: read once, beside the library, from the knowledge files
    * under the tree's corpora and the entry's own directory, the tree read
    * off the entry directory's parent as `EntryData.read` reads it
    * (`LemmaSources.textsUnder`). `initial` reads them when traces are
    * written.
    */
  def withLemmaTexts(entry: GenericEntry, entryDirectory: Path): GenericEntry =
    val directory = entryDirectory.toAbsolutePath.normalize
    val visible = directory.getParent
    entry.copy(lemmaTexts = LemmaSources.textsUnder(visible, Vector(visible.resolve("corpora"), directory), entry.index))

  /** The entry of the data, its library the data's knowledge, one term
    * (`EntryData.knowledge`), compiled and checked against the natives, each
    * round prepared against the library's index with the round's own
    * leaves, writing its articles to the destination: what `initial` builds,
    * given its inputs as values so that a test builds it from data read by
    * `EntryData.read` or `EntryData.at`. The knowledge and each round's
    * lemmas and leaves are read under one reading state, from the state the
    * read of the data returned, so that a round's knowledge, part of the
    * knowledge read whole, is answered from the tables of that read. The
    * entry reads its programs with the executor its data chooses
    * (`Defaults.executor`), a module's looked up in the table of executor
    * modules given (`ExecutorModules.registeredFor` the entry's directory),
    * with the cache service given; a round's extraction and
    * route are those its data chooses (`Defaults.lemmaCompilation`), a
    * module's looked up in the table of extractor modules given
    * (`ExtractorModules.registeredFor` the entry's directory).
    */
  def initialized(
      data: EntryData,
      executorModules: ExecutorModules,
      extractorModules: ExtractorModules,
      natives: NativeBackend,
      articles: ArticleDestination,
      state: ReadingState,
      caches: Cache
  ): GenericEntry =
    initializedWithLibrary(data, executorModules, extractorModules, natives, articles, state, caches)._2

  /** The compiled library of `initialized`'s entry, with the entry: what the
    * verifier of the entry's articles reads the statements of its lemmas
    * from (`EntryArticleVerification`).
    */
  def initializedWithLibrary(
      data: EntryData,
      executorModules: ExecutorModules,
      extractorModules: ExtractorModules,
      natives: NativeBackend,
      articles: ArticleDestination,
      state: ReadingState,
      caches: Cache
  ): (StandardLibrary, GenericEntry) =
    // The knowledge, the lemmas and the leaves are read as the entry's reading options say a function is applied to a
    // continuation: a library whose files export through their
    // continuation reads its imports once per path under `substituted`.
    val knowledgeState = state.copy(continuations = Defaults.continuations(data.reading.continuation))
    val (library, afterKnowledge) = StandardLibrary.compiled(data.knowledge, Vector(BackendChecks(natives)), knowledgeState)
    val facts = BackendFacts.of(library, natives)
    val jit = Defaults.jit(facts, data.jit)
    val (rounds, _) = data.rounds.foldLeft((Vector.empty[PreparedLemmaCompilation], afterKnowledge)) {
      case ((prepared, before), round) =>
        val (lemmas, afterLemmas) = library.lemmas(round.knowledge, before)
        val (leaves, afterLeaves) = library.leaves(round.knowledge, afterLemmas)
        val compilation =
          Defaults
            .lemmaCompilation(lemmas, round.settings, GenericEntry.roundCap, natives, extractorModules)
            .prepared(library.index.withLeaves(leaves))
        (prepared :+ compilation, afterLeaves)
    }
    // The entry's prepared compilation, built once and the same whatever its data says of where its programs are
    // compiled: the generic entry compiles by it under `Upfront`, and an executor module is handed it under either.
    val compilation = ProgramCompilation(library.index, rounds, natives)
    library -> GenericEntry(
      compilation,
      data.compilationPlace,
      jit,
      GenericEntry.readingLimit,
      GenericEntry.judgmentLimit,
      Defaults.executor(jit, data.reading, compilation, data.executor, executorModules),
      caches,
      Vector.empty,
      Cells.initialState,
      articles,
      1,
      1,
      Map.empty
    )

/** The entry between two points: what every point shares (the prepared
  * compilation, the library's index, the prepared rounds and the natives;
  * where its programs are compiled; the JIT and the reading and judgment
  * limits, the framework's in the judge and smaller in a test) and the state
  * threaded from one point to the next (the executor, which carries the JIT's
  * state, the cache service its readings run in, the reports of the cell
  * being run, and the state after the cells run so far).
  */
final case class GenericEntry(
    compilation: ProgramCompilation,
    // Where the entry's programs are compiled by its rounds, as its data chooses (`Defaults.compilationPlace`).
    compilationPlace: CompilationPlaceOption,
    jit: Jit,
    readingLimit: Long,
    judgmentLimit: Long,
    // The executor the entry's data chooses (`Defaults.executor`), whatever its suspensions' type: the
    // framework's, whose suspensions are `ReadingSuspension`, or a module's.
    // The entry resumes no suspension, so the type is never
    // needed.
    executor: Executor[?],
    caches: Cache,
    reports: Vector[Report],
    cellState: DeBruijnTerm,
    articles: ArticleDestination,
    nextArticle: Int,
    nextTrace: Int,
    // The texts of the library's lemmas as their files write them, keyed by
    // their sides, for the traces' debug information (`LemmaSources.textsUnder`):
    // read by `initial` when traces are written,
    // empty otherwise, and never read by a choice.
    lemmaTexts: Map[(Instruction, Instruction), gezi.locations.LemmaText]
) extends Entry:

  /** The library's index, the compilation's. */
  def index: StandardLibraryIndex = compilation.index

  /** The natives, the compilation's. */
  def natives: NativeBackend = compilation.natives

  /** The prepared lemma rounds, the compilation's. */
  def rounds: Vector[PreparedLemmaCompilation] = compilation.rounds

  /** The cell's Output under the judge's cancel: a judgment `N ∥ T` judged
    * by the framework (`Judgments`); any other Output the lemma rounds in
    * order and then the framework's reading, displayed as its normal forms,
    * or not evaluated when the reading stops. Every reading of the cell runs
    * with the cache service and the expansion source given.
    */
  def run(cell: DeBruijnTerm, source: ExpansionSource, stop: StopSignal): Interaction =
    val dependencies = ExecutionDependencies(caches, source)
    val output = Cells.output(cell, cellState)
    val (after, display) = output match
      // FIXME (https://github.com/Atry/private-overlay/issues/1788): a judgment always takes the judgment route, and its
      // point is never rewritten by the entry's lemma rounds; this route choice is fixed here, the only implementation.
      // It is to become an option of one interface chosen by configuration (entry data and `Defaults`) once a second
      // one exists.
      case DeBruijnTerm.Parallel(candidate, point) =>
        val judged = Judgments.judged(executor, dependencies, candidate, point, judgmentLimit, stop)
        (copy(executor = judged.executor, reports = judged.reports), Judgments.displayed(output, candidate, judged.judgment))
      case _ =>
        val (afterAnswered, normalForms) = answered(output, dependencies, stop)
        (afterAnswered, normalForms.fold(OutputDisplay.shown(output))(Cells.displayed))
    Interaction.Finished(display, after.reports, after.copy(cellState = Cells.nextState(cell, cellState)))

  /** The FFI program of the state, as the executor the entry's data chooses
    * filters it (`Executor.foreignProgram`), compiled where the data says
    * and run by that executor with the service in its dependencies; none
    * for an executor that runs no FFI program.
    */
  override def interacted(state: Instruction, service: ForeignService, source: ExpansionSource, stop: StopSignal): Option[Interacted] =
    executor.foreignProgram(state).map { program =>
      val (routed, _) = Defaults.compilationPlace(compilationPlace, compilation, program, explained = false, stop)
      val (after, _, progress) = executor.interacted(routed, ExecutionDependencies(caches, source, service), Budget(readingLimit, countedUnits = false, stop))
      Interacted(progress.answers, progress.finished, copy(executor = after))
    }

  /** The point's normal forms, the program compiled where the entry's data
    * says (`Defaults.compilationPlace`). Under `CompilationPlaceOption.Upfront`:
    * the program through the lemma rounds on one
    * shared e-graph (`ProgramCompiler.compiledProgram`, the function of the
    * program unit's compiler: the last round's route, `NarrowBlockRoute.compiledRounds`, each round saturating the
    * graph the rounds before it left, to its fixed point under its own
    * modules and the cap; then the last round's extraction with its narrow
    * blocks computed), and what is left read by the entry's executor within
    * `readingLimit`: the program with its blocks computed, else the
    * extraction, else the program. Every program takes the same route. The
    * reports: the rounds' steps, then for each round the instances it added
    * (`lemma_saturation_instances`) and whether it stopped at the cap
    * (`lemma_saturation_capped`), then the reading's reports (its phases
    * and `reading_steps`). When the destination is a directory, the article
    * of the program equal to its extraction and the trace from the program
    * are written (`evidenceWritten`). Under `CompilationPlaceOption.ByExecutor`:
    * the program itself read by the entry's executor within `readingLimit`,
    * no round run here, the reports the reading's alone and no article or
    * trace written.
    */
  private def answered(
      point: DeBruijnTerm,
      dependencies: ExecutionDependencies,
      stop: StopSignal
  ): (GenericEntry, Option[Set[DeBruijnTerm]]) =
    val (program, defunctionalization) = Phase.timed("defunctionalization")(Defunctionalization.thunkInstruction(point))
    // The graph records the terms made only when the destination is a
    // directory (`evidenceWritten` reads its proof), so a scored reading
    // pays nothing.
    val explained = articles match
      case ArticleDestination.Written(_) | ArticleDestination.WrittenWithTraces(_) => true
      case ArticleDestination.Discarded                                           => false
    // FIXME (https://github.com/Atry/private-overlay/issues/1549):
    // under `by_executor` the entry runs no round and hands the executor the uncompiled program, so no round's
    // reports, no article and no trace are written in this mode, whatever the destination: what the executor
    // compiles, it compiles out of the entry's sight. The executor's result is to carry the compilation's evidence
    // (its rounds' reports, the program equal to its extraction) for the entry to report and write.
    val (routed, roundResult) = Defaults.compilationPlace(compilationPlace, compilation, program, explained, stop)
    val (roundReports, (articlesWritten, tracesWritten)) =
      roundResult match
        case None => (Vector.empty[Report], (0, 0))
        case Some(result) =>
          (
            result.steps.map((name, nanoseconds) => Phase(name, nanoseconds / 1e9)) ++ result.rounds.flatMap(round =>
              Vector(
                Count("lemma_saturation_instances", round.instances.toLong),
                Count("lemma_saturation_capped", round.end match
                  case End.BudgetExhausted(_) => 1L
                  case _                      => 0L)
              )
            ),
            evidenceWritten(program, result, stop)
          )
    val reading = Judgments.read(executor, dependencies, routed, readingLimit, stop)
    (
      copy(
        executor = reading.executor,
        reports = (defunctionalization +: roundReports) ++ reading.reports,
        nextArticle = nextArticle + articlesWritten,
        nextTrace = nextTrace + tracesWritten
      ),
      reading.normalForms
    )

  /** The encodings of the lemmas of every round into patterns, each once:
    * what the proofs of the rounds name their lemmas by, and what a
    * statement of a lemma is built from (`gezi.proofs.LeanStatements`).
    */
  def lemmaEncodings: Vector[EncodedLemma] = rounds.flatMap(_.saturator.lemmas(index)).distinct

  /** Writes, when the destination is a directory and the rounds gave an
    * extraction, the evidence of the program equal to its extraction under
    * every round's lemmas, read from the graph the rounds left
    * (`GraphProof`); the numbers of articles and of traces written, each 1 or
    * 0.
    *
    * The article, when the graph has no union the article writer refuses
    * (below), goes to `round-<n>.art` of the directory, n the entry's next
    * article number, with its
    * trace and the text of its start, the program, beside it
    * (`TraceFiles.textWrittenAt`). The numerals of the narrow
    * blocks are the backend's computation and are not in the article.
    *
    * Under `ArticleDestination.WrittenWithTraces` only, the trace, its
    * start and its player's page (`TraceFiles.textWrittenAt`)
    * also go to `trace-<k>.lambdalattice`, `trace-<k>.start.lambdalattice` and
    * `trace-<k>.html`, k the entry's next
    * trace number, for every point with an extraction, its graph's β
    * conversions and abstractions included, which the trace keeps as
    * `convert` and `abstraction` commands: the proof flattened
    * (`RewriteTrace.trace`) as the first round, from the program to its
    * extraction, and, when blocks were computed, a second round of `native`
    * commands that put each block's numeral in the extraction
    * (`LemmaRoundsResult.natives`), so that the trace replays to the program
    * the reading starts from. Traces are numbered apart from articles: the
    * judge reads `round-1.art` on up to the first one missing
    * (`ArticleCheck.articleFiles`), so a point with a trace and no article
    * must take no article number.
    *
    * A union by the abstraction rule (a round with opening on that wrote a
    * body back) is written as the closures' equation after the opened
    * bodies' theorem, and a union by β conversion as its conversion
    * equation (`gezi.proofs.Axiom.Conversion`); the round certificate
    * proves both (`gezi.proofs.ArticleVerification`), the Lean
    * reader `LambdaJit.Article` neither when its terms hold an
    * eigenvariable. A proof whose terms hold a URI node gets no article
    * (`OpentheoryArticle.uriFree`'s FIXME). The trace keeps a round's β https://github.com/Atry/private-overlay/issues/1978
    * conversions as `convert` commands, whose replay
    * computes the saturator's normal form by the one function both call
    * (`gezi.ir.BindingNormalForm`). A proof may cross a β residual the
    * graph keeps in another spelling than the front end's; the trace
    * replays in `gezi.rewritetrace.ReplaySpelling`, where it reads as
    * the front end's (the inlined_calls_*_hot points of `contest-entries-wren`,
    * `EntryTracesTest`).
    *
    * The evidence reads the stop signal: it
    * is built step by step, the proof, the derivation flattened, the trace's
    * text and the article's text, the signal read before each, and no file is
    * written once a stop is asked for, so that a cancel never leaves an
    * article without its trace nor half a file. The steps' costs, measured
    * 2026-11-17 on `contest-entries-solo`'s repeated_library_hotspots_calls_1000 direct point
    * (seed 20261116, 2 CPUs): the proof 0.27 s, the check for URI nodes
    * 1.31 s, the derivation 0.17 s, the trace 0.01 s, the article's text and
    * file 2.08 s and the trace's files 1.33 s; a cancel at 30 s, during these
    * steps, returned 0.53 s after it. The longest step bounds what a cancel
    * waits for; on a larger proof it can exceed the judge's grace.
    */
  private def evidenceWritten(program: Instruction, result: LemmaRoundsResult, stop: StopSignal): (Int, Int) =
    val (directory, everyTrace) = articles match
      case ArticleDestination.Discarded                    => (None, false)
      case ArticleDestination.Written(directory)           => (Some(directory), false)
      case ArticleDestination.WrittenWithTraces(directory) => (Some(directory), true)
    (directory, result.extracted) match
      case (Some(directory), Some(extracted)) =>
        val texts =
          for
            proof <- GenericEntry.unlessStopped(stop)(GraphProof.proof(result.graph, Vector((program, extracted)), lemmaEncodings))
            articled <- GenericEntry.unlessStopped(stop)(OpentheoryArticle.uriFree(proof))
            flattened <- GenericEntry.unlessStopped(stop)(
              RewriteTrace.trace(OpentheoryArticle.derivation(index, program, extracted, proof))
            )
            traceText <- GenericEntry.unlessStopped(stop)(
              TraceText.writtenWith(
                if result.natives.isEmpty then flattened else flattened.copy(rounds = flattened.rounds :+ result.natives),
                lemmaTexts
              )
            )
            articleText <- GenericEntry.unlessStopped(stop)(
              Option.when(articled)(OpentheoryArticle.text(index, program, extracted, proof))
            )
            if !stop.stopRequested
            startText <- GenericEntry.unlessStopped(stop)(
              TraceStart.written(program, None, TraceText.namesUsed(flattened, lemmaTexts).map(_.swap).toMap)
            )
          yield (articleText, startText, traceText)
        texts match
          case None => (0, 0)
          case Some((articleText, startText, traceText)) =>
            articleText.foreach { text =>
              val article = directory.resolve(s"round-$nextArticle.art")
              Files.writeString(article, text, StandardCharsets.UTF_8)
              TraceFiles.textWrittenAt(TraceFiles.traceFile(article), startText, traceText)
            }
            if everyTrace then TraceFiles.textWrittenAt(directory.resolve(s"trace-$nextTrace.lambdalattice"), startText, traceText)
            (if articleText.isDefined then 1 else 0, if everyTrace then 1 else 0)
      case _ => (0, 0)

object GenericEntry:

  /** The value, computed only while the signal asks for no stop. */
  private def unlessStopped[A](stop: StopSignal)(value: => A): Option[A] = Option.unless(stop.stopRequested)(value)

  /** The safety cap of a lemma round: the instances a round may add before
    * it is stopped, the same for every entry.
    * It is no fuel: a
    * round is meant to reach its fixed point, and a round that hits the cap
    * is reported (`lemma_saturation_capped`).
    *
    * The value is about 110 times the largest round measured (91
    * instances, the one round of `contest-entries-solo` on a published points file),
    * and no round reached it.
    *
    * The hot ladder's rungs are measured (2026-11-07, the points of seed
    * 2907862446; the inlined shape from practice passes on main,
    * the nested shape from a probe that saturates and extracts
    * without evaluating, on main d327dab67): the four-round entry reads 3,
    * 3, 8 and 12 instances on the inlined shape and 3, 15, 4 and 0 on the
    * nested shape, at 10^4, 10^5 and 10^6, direct and respelled alike, none
    * capped. The count does not grow with the rung, which changes only the
    * numeral a loop is applied to, not the program's shape.
    *
    * FIXME (2026-11-07): that points file's 18 stopped points are unmeasured; their https://github.com/Atry/private-overlay/issues/1995
    * count 0 is a hypothesis. Revise the value from their readings.
    */
  val roundCap: Int = 10000

  /** The steps a reading of normal forms may take: the framework's, the
    * same for every entry.
    */
  val readingLimit: Long = Reading.budgetSteps(60)

  /** The steps a judgment's reading may take: the framework's. */
  val judgmentLimit: Long = Reading.budgetSteps(5)
