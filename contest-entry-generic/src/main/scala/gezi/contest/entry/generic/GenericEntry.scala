package gezi.contest.entry.generic

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Cells
import gezi.contest.entry.CompilationPlaceOption
import gezi.contest.entry.OccurrenceTaggingOption
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
import gezi.frontend.DeBruijnTermOf
import gezi.frontend.Defunctionalization
import gezi.hotspot.Budget
import gezi.hotspot.Cache
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.Executor
import gezi.hotspot.ExpansionSource
import gezi.hotspot.ForeignService
import gezi.jit.BackendChecks
import gezi.jit.BackendFacts
import gezi.jit.StorageEncoding
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
import gezi.weakhead.Mode
import gezi.weakhead.Reading
import gezi.weakhead.ReadingConfiguration
import gezi.weakhead.ReadingState
import gezi.weakhead.ScottADTChoices
import gezi.ir.{Closed, Configured, NativeSpecializer, NoFacts, StorageAccess}

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
  def initial(entryDirectory: Path, caches: Cache, articles: ArticleDestination): Entry[?] =
    val (data, afterEntry) =
      EntryData.read(entryDirectory, Defaults.entryDataState)
    val (library, entry) =
      GenericEntryProvider.initializedWithLibrary(
        data,
        ExecutorModules.registeredFor(entryDirectory),
        ExtractorModules.registeredFor(entryDirectory),
        NativesProvider.loaded,
        articles,
        afterEntry,
        caches
      )
    articles match
      case ArticleDestination.WrittenWithTraces(_) => entry.withLemmaTexts(library, entryDirectory)
      case _                                       => entry

object GenericEntryProvider:


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
      state: ReadingState[NoFacts.type],
      caches: Cache
  ): GenericEntry[?] =
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
      state: ReadingState[NoFacts.type],
      caches: Cache
  ): (StandardLibrary, GenericEntry[?]) =
    // The knowledge, the lemmas and the leaves are read as the entry's reading options say a function is applied to a
    // continuation: a library whose files export through their
    // continuation reads its imports once per path under `substituted`.
    val knowledgeState = state.copy(continuations = Defaults.continuations(data.reading.continuation))
    val (library, afterKnowledge) = StandardLibrary.compiled(data.knowledge, Vector(BackendChecks(natives)), knowledgeState)
    // The library is read under no facts, and the facts are built once from it (the entry's one facts, one encoding);
    // the entry's configuration is that encoding's singleton type, in which the rest of the entry is typed.
    val encoding = BackendFacts.of(library, natives).storageEncoding
    library -> initializedIn[encoding.type](encoding, data, library, executorModules, extractorModules, natives, articles, afterKnowledge, caches)

  /** The entry of the configuration `C` of the encoding of the library's facts: its index crossed into the
    * encoding once (`StandardLibraryIndex.crossed`, read here as `encoding.operations.index`), each round prepared
    * against it with the round's own leaves, and the JIT built over the encoding.
    */
  private def initializedIn[C <: NativeSpecializer & Singleton](
      encoding: StorageEncoding & C,
      data: EntryData,
      library: StandardLibrary,
      executorModules: ExecutorModules,
      extractorModules: ExtractorModules,
      natives: NativeBackend,
      articles: ArticleDestination,
      afterKnowledge: ReadingState[NoFacts.type],
      caches: Cache
  ): GenericEntry[C] =
    val operations: gezi.jit.StorageEncodingOperations[C] = encoding.operations
    val index = operations.index
    // The one capability of the entry's readings, granted where the entry is set up.
    val jit = Defaults.jit[C](encoding, data.jit, data.groupBlocks, StorageAccess.granted())
    val construction = gezi.jit.ConvertedTermConstruction[C](encoding)(jit.configuration.storageAccess)
    val (rounds, _) = data.rounds.foldLeft((Vector.empty[PreparedLemmaCompilation[C]], afterKnowledge)) {
      case ((prepared, before), round) =>
        val (lemmas, afterLemmas) = library.lemmas(round.knowledge, before)
        val (leaves, afterLeaves) = library.leaves(round.knowledge, afterLemmas)
        val compilation =
          Defaults
            // The rounds write back through the facts' native specializer, as the entry's JIT builds, so that a term has one
            // object in both.
            .lemmaCompilation[C](
              lemmas,
              round.settings,
              GenericEntry.roundCap,
              natives,
              extractorModules,
              construction,
              jit.readingConfiguration
            )
            .prepared(index.withLeaves(leaves.map(Configured.fromPure[C](encoding))))
            .scaledBy(GenericEntry.roundInstancesPerNode)
        (prepared :+ compilation, afterLeaves)
    }
    // The entry's prepared compilation, built once and the same whatever its data says of where its programs are
    // compiled: the generic entry compiles by it under `Upfront`, and an executor module is handed it under either.
    val compilation = ProgramCompilation(index, rounds, natives, encoding)
    GenericEntry[C](
      compilation,
      data.compilationPlace,
      data.occurrenceTagging,
      jit,
      GenericEntry.readingLimit,
      GenericEntry.judgmentLimit,
      Defaults.executor[C](jit, data.reading, compilation, data.executor, executorModules),
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
final case class GenericEntry[C <: NativeSpecializer & Singleton](
    compilation: ProgramCompilation[C],
    // Where the entry's programs are compiled by its rounds, as its data chooses (`Defaults.compilationPlace`).
    compilationPlace: CompilationPlaceOption,
    // How the entry's programs are tagged as occurrences before its rounds, as its data chooses
    // (`Defaults.occurrencesTagged`).
    occurrenceTagging: OccurrenceTaggingOption,
    jit: Jit[C],
    readingLimit: Long,
    judgmentLimit: Long,
    // The executor the entry's data chooses (`Defaults.executor`), whatever its suspensions' type: the
    // framework's, whose suspensions are `ReadingSuspension`, or a module's.
    // The entry resumes no suspension, so the type is never
    // needed.
    executor: Executor[C, ?],
    caches: Cache,
    reports: Vector[Report],
    cellState: DeBruijnTermOf[Configured[C]],
    articles: ArticleDestination,
    nextArticle: Int,
    nextTrace: Int,
    // The texts of the library's lemmas as their files write them, keyed by
    // their sides, for the traces' debug information (`LemmaSources.textsUnder`):
    // read by `initial` when traces are written,
    // empty otherwise, and never read by a choice.
    lemmaTexts: Map[(Configured[C], Configured[C]), gezi.locations.LemmaText[C]]
) extends Entry[C]:

  /** The native specializer of the entry's configuration, the JIT's. */
  def specializer: C = jit.configuration.specializer

  /** The entry's specializer as its backend facts' storage encoding. */
  def encoding: StorageEncoding & C = jit.configuration.specializer

  /** The capability to read a storage's view, the JIT's. */
  private def storageAccess: StorageAccess = jit.configuration.storageAccess

  /** The library's index, the compilation's. */
  def index: StandardLibraryIndex[C] = compilation.index

  /** The natives, the compilation's. */
  def natives: NativeBackend = compilation.natives

  /** The prepared lemma rounds, the compilation's. */
  def rounds: Vector[PreparedLemmaCompilation[C]] = compilation.rounds

  /** The cell's Output under the judge's cancel: a judgment `N ∥ T` judged
    * by the framework (`Judgments`); any other Output the lemma rounds in
    * order and then the framework's reading, displayed as its normal forms,
    * or not evaluated when the reading stops. Every reading of the cell runs
    * with the cache service and the expansion source given.
    */
  def run(cell: DeBruijnTermOf[Configured[C]], source: ExpansionSource, stop: StopSignal): Interaction[C] =
    given C = specializer
    given StorageAccess = storageAccess
    val dependencies = ExecutionDependencies(caches, source)
    val output = Cells.output(cell, cellState)
    val (after, display) = output match
      // FIXME (https://github.com/Atry/private-overlay/issues/1788): a judgment always takes the judgment route, and its
      // point is never rewritten by the entry's lemma rounds; this route choice is fixed here, the only implementation.
      // It is to become an option of one interface chosen by configuration (entry data and `Defaults`) once a second
      // one exists.
      case DeBruijnTerm.Parallel(candidate, point) =>
        val judged = Judgments.judged(executor, dependencies, candidate, point, judgmentLimit, stop, jit.readingConfiguration)
        (copy(executor = judged.executor, reports = judged.reports), judged.display)
      case _ =>
        val (afterAnswered, scottADTValues) = answered(output, dependencies, stop)
        (afterAnswered, scottADTValues.fold(OutputDisplay.remainder[C](output))(read => OutputDisplay.Values(read.choices)))
    Interaction.Finished(display, after.reports, after.copy(cellState = Cells.nextState(cell, cellState)))

  /** The display of one value an FFI program gave: its Scott ADT values, read under the entry's JIT configuration
    * within the reading limit (`Judgments.scottADTValuesOf`). A reading the limit or the stop ends is displayed as
    * the value's term when it is one.
    *
    * FIXME (https://github.com/Atry/private-overlay/issues/2266): the value is read under a fresh state of the entry's
    * configuration, not with the executor's tables and JIT state, which the generic `Executor` interface does not give: the Scott ADT values read are the same (a table
    * saves steps only), but a value that needs the executor's tables to finish within the limit stops here, and is
    * displayed as its term, or as no Scott ADT value when it is no term (it holds a suspension), which says less than
    * the truth (not evaluated): `OutputDisplay` has no case for it. Candidates: an `Executor` method that reads a
    * value's Scott ADT values in its own state; a case of `OutputDisplay` for a reading that did not finish.
    */
  def displayed(value: Closed[C], source: ExpansionSource, stop: StopSignal): (Entry[C], OutputDisplay[C]) =
    given C = specializer
    val display = Judgments.scottADTValuesOf(Mode.Jit, Closed.value(value), readingLimit, stop, jit.readingConfiguration) match
      case Some(read) => OutputDisplay.Values(read.choices)
      case None       => Closed.configured(Closed.value(value)).fold(OutputDisplay.noScottADTValue[C])(OutputDisplay.Remainder(_))
    (this, display)

  /** The FFI program of the state, as the executor the entry's data chooses
    * filters it (`Executor.foreignProgram`), compiled where the data says
    * and run by that executor with the service in its dependencies; none
    * for an executor that runs no FFI program.
    */
  override def interacted(state: Configured[C], service: ForeignService, source: ExpansionSource, stop: StopSignal): Option[Interacted[C]] =
    given C = specializer
    executor.foreignProgram(state).map { program =>
      val dependencies = ExecutionDependencies(caches, source, service)
      val (routed, _) = Defaults.compilationPlace(compilationPlace, compilation, program, dependencies, explained = false, stop)
      val (after, _, progress) = executor.interacted(routed, dependencies, Budget(readingLimit, countedUnits = false, stop))
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
      point: DeBruijnTermOf[Configured[C]],
      dependencies: ExecutionDependencies,
      stop: StopSignal
  )(using C, StorageAccess): (GenericEntry[C], Option[ScottADTChoices.Read[C]]) =
    val (program, defunctionalization) = Phase.timed("defunctionalization")(
      Defaults.occurrencesTagged(occurrenceTagging, compilation.index, Defunctionalization.thunkInstruction[C](point))
    )
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
    val (routed, roundResult) = Defaults.compilationPlace(compilationPlace, compilation, program, dependencies, explained, stop)
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
            ) ++ Option.when(result.units.nonEmpty)(Count("closure_units_kept", result.units.count(_.kept).toLong)),
            evidenceWritten(program, result, stop)
          )
    val reading = Judgments.read(executor, dependencies, routed, readingLimit, stop, jit.readingConfiguration)
    (
      copy(
        executor = reading.executor,
        reports = (defunctionalization +: roundReports) ++ reading.reports,
        nextArticle = nextArticle + articlesWritten,
        nextTrace = nextTrace + tracesWritten
      ),
      reading.read
    )

  /** The encodings of the lemmas of every round into patterns, each once:
    * what the proofs of the rounds name their lemmas by, and what a
    * statement of a lemma is built from (`gezi.proofs.LeanStatements`).
    */
  def lemmaEncodings: Vector[EncodedLemma[C]] = rounds.flatMap(_.saturator.lemmas(index)).distinct

  /** The entry with its lemmas' texts, for its traces only: read once, beside the library, from the knowledge files
    * under the tree's corpora and the entry's own directory, the tree read
    * off the entry directory's parent as `EntryData.read` reads it
    * (`LemmaSources.textsUnder`, against the library's index of no facts), and crossed into the entry's configuration
    * as the library's terms are (`NativeSpecializer.crossedAllFromNoFacts`), so that a text is keyed by the entry's
    * sides of its lemma and its names' values are the entry's terms. `GenericEntryProvider.initial` reads them when traces are written.
    */
  def withLemmaTexts(library: StandardLibrary, entryDirectory: Path): GenericEntry[C] =
    val directory = entryDirectory.toAbsolutePath.normalize
    val visible = directory.getParent
    val texts = LemmaSources.textsUnder(visible, Vector(visible.resolve("corpora"), directory), library.index)
    val crossed = (specializer: C).crossedAllFromNoFacts(
      texts.toVector.flatMap { case ((left, right), text) => Vector(left, right) ++ text.names.map(_._2) }
    )
    copy(lemmaTexts = texts.map { case ((left, right), text) =>
      (crossed(left), crossed(right)) -> text.copy(names = text.names.map((name, value) => (name, crossed(value))))
    })

  /** The Lean module of the statements of the lemmas named, as the entry's articles import them: from the entry's
    * index and lemma encodings, in its configuration, a storage written as its view
    * (`gezi.proofs.LeanStatements.selectedText`), each lemma's proof from the library.
    */
  def leanStatementsText(library: gezi.standardlibrary.StandardLibrary, repository: java.nio.file.Path, lemmaNames: Vector[String]): String =
    given StorageAccess = storageAccess
    gezi.proofs.LeanStatements.selectedText(library, index, lemmaEncodings, repository, lemmaNames)

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
  private def evidenceWritten(program: Configured[C], result: LemmaRoundsResult[C], stop: StopSignal): (Int, Int) =
    val (directory, everyTrace) = articles match
      case ArticleDestination.Discarded                    => (None, false)
      case ArticleDestination.Written(directory)           => (Some(directory), false)
      case ArticleDestination.WrittenWithTraces(directory) => (Some(directory), true)
    (directory, result.extracted) match
      case (Some(directory), Some(extracted)) =>
        // The proof's terms are the graph's, read with the capability its construction holds.
        given gezi.ir.StorageAccess = result.graph.store.storageAccess
        given C = specializer
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

  /** The least safety cap of a lemma round: the instances a round may add
    * before it is stopped are this many, or `roundInstancesPerNode`
    * for each node of the program's IR graph when that is more
    * (`PreparedLemmaCompilation.budgetFor`), the same for every entry.
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
    */
  val roundCap: Int = 10000

  /** The instances a lemma round may add for each node of the IR graph of the
    * program it saturates (`PreparedLemmaCompilation.graphNodes`),
    * above `roundCap`: a round that types a program
    * walks it, adding instances in proportion to its instructions, so a cap
    * fixed whatever the program cuts a large one's typing short.
    *
    * Measured 2026-11-22 under the rounds of `contest-entries-fixture`
    * (closure_application, the Prolog backend's type check and
    * occurrence_erasure) with the occurrence tagging `names_and_closures`,
    * the cap raised for the readings, every round reaching its fixed point;
    * the nodes are the tagged program's (its distinct instructions and the
    * nodes of their thunks' codes, `PreparedLemmaCompilation.graphNodes`),
    * and the type check is the round with the most instances on every point:
    *
    *   - on main 42ce7fc04, one evaluation point of each family of the
    *     public seed 885189454962688 (the hot ladders at their 10^4 rung,
    *     both spellings), 31 points: the type check reads from 1.35
    *     instances per node (`repeated_closures`) to 19.10
    *     (`repeated_reduction_meanings/repetitions_12`, 40,357 on 2,113
    *     nodes), then 17.75 (`repeated_reduction_interpreter/repetitions_4`,
    *     15,712 on 885), 14.93 and 14.44 (the inlined hot calls), 13.51
    *     (`repeated_reduction_problems_products/repetitions_4`); the list
    *     families read 1.8 to 2.8 (`repeated_library_edit_distances/direct/repetitions_1`,
    *     49,372 on 24,879);
    *   - on main 865a410be, the point
    *     `repeated_speculative_untabling_weighted_paths_recurring_nodes_10000_steps_9999/direct/repetitions_1`
    *     of seed 20261031, 6.01 (531,108 on 88,431), whose type check and
    *     erasure stopped under the cap of 10,000 alone.
    *
    * The ratio is no constant of the type check, so the value is about 2.6
    * times the largest measured, 19.10; a cap of 16 per node cut the
    * type check of the two largest short.
    */
  val roundInstancesPerNode: Int = 50

  /** The steps a reading of normal forms may take: the framework's, the
    * same for every entry.
    */
  val readingLimit: Long = Reading.budgetSteps(60)

  /** The steps a judgment's reading may take: the framework's. */
  val judgmentLimit: Long = Reading.budgetSteps(5)
