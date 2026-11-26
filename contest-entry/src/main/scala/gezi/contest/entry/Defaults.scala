package gezi.contest.entry

import gezi.egraph.MemoRetention
import gezi.ematching.Backend
import gezi.ematching.closures.ClosureCompilation
import gezi.hotspot.CacheProvider
import gezi.hotspot.Executor
import gezi.hotspot.LifecycleEvent
import gezi.hotspot.baselines.BaselineCaches
import gezi.jit.StorageEncoding
import gezi.jit.ClosureBackend
import gezi.jit.DispatchMode
import gezi.jit.Jit
import gezi.knowledgereading.KnowledgeReading
import gezi.jit.JitConfiguration
import gezi.jit.EveryStepsCheckpoints
import gezi.jit.InstanceLookahead
import gezi.jit.InstanceRetention
import gezi.jit.InstanceReuse
import gezi.jit.NoNativeBlocks
import gezi.jit.ProfitableCheckpoints
import gezi.hotspot.Retention
import gezi.weakhead.ApplicationReading
import gezi.weakhead.ContinuationReading
import gezi.weakhead.ParallelReading
import gezi.weakhead.Mode
import gezi.weakhead.NoJitState
import gezi.weakhead.ReadingExecutor
import gezi.weakhead.ReadingState
import gezi.weakhead.TableRetention
import gezi.jit.PredicatePerCode
import gezi.lemmaencoding.LemmaEncoding
import gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import gezi.ematching.bytecode.BytecodeCompilation
import gezi.ematching.interpretation.Interpretation
import gezi.ir.LemmaIdentifier
import gezi.jit.NativeBackend
import gezi.narrowblocks.LemmaCompilation
import gezi.narrowblocks.LemmaRoute
import gezi.narrowblocks.NarrowBlockExtractor
import gezi.narrowblocks.NarrowBlockRoute
import gezi.narrowblocks.LemmaRoundsResult
import gezi.narrowblocks.ProgramCompilation
import gezi.narrowblocks.ProgramCompiler
import gezi.frontend.ProgramOccurrences
import gezi.standardlibrary.StandardLibraryIndex
import gezi.saturation.OpeningCriterionChoice
import gezi.saturation.StopSignal
import gezi.orientation.OrientationCompiler
import gezi.orientation.StandardOrientationCompiler
import gezi.strategies.DispatchStrategies
import gezi.strategies.Extractor
import gezi.strategies.HigherOrderSaturator
import gezi.strategies.Indexer
import gezi.strategies.JointReading
import gezi.strategies.NormalityModule
import gezi.strategies.SaturationOptions
import gezi.strategies.SpellingRetention
import gezi.strategies.StandardIndexer
import gezi.ir.{Apply, Choice, Configured, NativeSpecializer, NoFacts, Parallel, StorageAccess, TermConstruction, Thunk}
import gezi.weakhead.ReadingConfiguration

/** The one place the framework's default implementation of each replaceable
  * interface is chosen. The framework's generic entry
  * (`gezi.contest.entry.generic.GenericEntry`) takes from here every
  * implementation an entry's data does not choose, so that retiring a
  * default module for a replacement changes one line of this
  * object. An entry written in Scala names its own implementations instead,
  * so that a later change of a default does not change it.
  */
object Defaults:

  /** The JIT of an entry's options over the backend facts, the one
    * construction of the framework's JIT:
    * each option's published case mapped to its implementation, with the capability to read storages that the entry's
    * setup grants.
    */
  def jit[C <: NativeSpecializer & Singleton](
      specializer: StorageEncoding & C,
      options: JitOptions,
      groupBlocks: GroupBlocksOption,
      storageAccess: StorageAccess
  ): Jit[C] =
    val facts = specializer.facts
    Jit(
      JitConfiguration[C](
        specializer,
        options.budget,
        options.granularity match { case GranularityOption.PredicatePerCode => PredicatePerCode },
        options.implementation match { case BackendOption.Closure => ClosureBackend },
        options.dispatch match { case DispatchOption.Fallback => DispatchMode.Dispatch(DispatchStrategies.fallback) },
        instanceTable = options.instanceTable,
        instanceTableTrial = options.instanceTableTrial,
        instanceRetention = instanceRetention(options.instanceRetention),
        nativeBlocks = options.nativeBlocks match { case NativeBlocksOption.None => NoNativeBlocks },
        instanceCheckpoints = options.checkpoints match {
          case CheckpointOption.Profitable           => ProfitableCheckpoints
          case CheckpointOption.EverySteps(interval) => EveryStepsCheckpoints(interval)
        },
        instanceLookahead = options.lookahead match {
          case LookaheadOption.Lazily             => InstanceLookahead.Lazy
          case LookaheadOption.WithinSteps(steps) => InstanceLookahead.WithinSteps(steps)
        },
        instanceReuse = options.instanceReuse match {
          case InstanceReuseOption.WithinVersion          => InstanceReuse.WithinVersion
          case InstanceReuseOption.VerifiedAcrossVersions => InstanceReuse.VerifiedAcrossVersions
        },
        groupBlocks = groupBlocks match {
          case GroupBlocksOption.None => gezi.jit.NoGroupBlocks
          case GroupBlocksOption.Enabled(sharePercent, denseCells, backend) =>
            gezi.narrowblocks.groups.GroupBlockMechanism(
              gezi.narrowblocks.groups.GroupCompilation(facts),
              facts,
              backend match {
                case GroupBackendOption.Scalar   => gezi.narrowblocks.groups.ScalarGroupBackend
                case GroupBackendOption.JvmArray => gezi.narrowblocks.groups.JvmArrayGroupBackend
              },
              gezi.jit.BudgetShare(sharePercent.toLong, 100),
              if denseCells > 0 then gezi.narrowblocks.groups.GroupMemoOption.Dense(denseCells) else gezi.narrowblocks.groups.GroupMemoOption.Mapped
            )
        },
        storageAccess = storageAccess
      )
    )

  /** How the JIT's state keeps the instance table's complete tables, as the
    * entry's options choose.
    */
  def instanceRetention(option: InstanceRetentionOption): InstanceRetention =
    option match
      case InstanceRetentionOption.Generations(size) => InstanceRetention.Generations(size)
      case InstanceRetentionOption.NeverDropped      => InstanceRetention.NeverDropped

  /** The framework's executor, the one an entry whose data writes the
    * executor `jit` reads its programs with, over its JIT: the JIT
    * as a reading executor, starting with no JIT state, the instances the
    * JIT tabled carried from one reading to the next, its applications taken
    * apart, its tables carried to the next reading and its complete weak-head
    * tables kept in the cache service as the reading options say.
    * What it keeps holds for the version of the contents
    * the URI nodes expand to that each call's dependencies give (`gezi.hotspot.ExecutionDependencies.source`), which the
    * adapter gives with each cell (`Entry.run`).
    */
  def executor[C <: NativeSpecializer & Singleton](jit: Jit[C], reading: ReadingOptions): ReadingExecutor[C] =
    ReadingExecutor(
      Mode.Jit,
      jit.readingConfiguration,
      NoJitState,
      sharedRetention(reading.tableSharing),
      None,
      applications(reading.application),
      tableRetention(reading.tableRetention),
      continuations = continuations(reading.continuation),
      parallels = parallels(reading.parallel)
    )

  /** The executor an entry's data chooses (`ExecutorOption`):
    * the framework's,
    * the JIT as a reading executor (`executor` of the JIT and the reading
    * options), or the executor of the module registered under the selector
    * the data writes, built from the parameters the data writes and the JIT,
    * the reading options and the entry's prepared compilation
    * (`ExecutorModuleInputs`). Its suspensions are those of the executor chosen,
    * so the type leaves them unknown. Throws `EntryDataError` for a selector
    * no module of the table gives (`ExecutorModules.chosen`).
    */
  def executor[C <: NativeSpecializer & Singleton](
      jit: Jit[C],
      reading: ReadingOptions,
      compilation: ProgramCompilation[C],
      chosen: ExecutorOption,
      modules: ExecutorModules
  ): Executor[C, ?] =
    chosen match
      case ExecutorOption.Jit => executor(jit, reading)
      case ExecutorOption.Module(selector, parameters) =>
        modules.chosen(selector).executor[C](parameters, ExecutorModuleInputs(jit, reading, compilation))

  /** The program an entry's executor reads, with what the entry's rounds
    * gave, as the place its data chooses says
    * (`CompilationPlaceOption`):
    * `Upfront(WholeProgram)`, the
    * program through the prepared compilation's rounds
    * (`ProgramCompiler.compiledProgram`, the program compiler's function
    * called rather than its `compiled`, since the entry reports what the
    * rounds gave and writes their evidence, which an artifact does not
    * carry), the graph recording the terms made when `explained`;
    * `Upfront(LetBoundClosure)`, the program's closure unit compiled once per
    * configuration in the cache service of the dependencies and replaced by
    * its artifact (`ClosureUnits.compiledProgram`);
    * `ByExecutor`, the program itself and nothing, no round run, the
    * executor holding the compilation (`ExecutorModuleInputs.compilation`).
    */
  def compilationPlace[C <: NativeSpecializer & Singleton](
      chosen: CompilationPlaceOption,
      compilation: ProgramCompilation[C],
      program: Configured[C],
      dependencies: gezi.hotspot.ExecutionDependencies,
      explained: Boolean,
      stop: StopSignal
  )(using C): (Configured[C], Option[LemmaRoundsResult[C]]) =
    chosen match
      case CompilationPlaceOption.Upfront(UnitSelectionOption.WholeProgram) =>
        ProgramCompiler.compiledProgram(compilation, program, explained, stop)
      case CompilationPlaceOption.Upfront(UnitSelectionOption.LetBoundClosure) =>
        gezi.narrowblocks.ClosureUnits.compiledProgram(compilation, program, dependencies, explained, stop)
      case CompilationPlaceOption.ByExecutor => (program, None)

  /** The program tagged as occurrences as the entry's data chooses:
    * `Untagged`, the program itself; `NamesAndClosures`, the program's lambda
    * chains and shared parts tagged with the library's occurrence markers
    * (`ProgramOccurrences.tagged`), every instruction the library knows by
    * its handle left untagged inside: those a lemma's side mentions, those a
    * native is bound to and those with a combinator property. Throws
    * `IllegalArgumentException` for a tagging asked of a library that
    * declares no occurrence markers.
    */
  def occurrencesTagged[C <: NativeSpecializer & Singleton](chosen: OccurrenceTaggingOption, index: StandardLibraryIndex[C], program: Configured[C])(using
      C,
      StorageAccess
  ): Configured[C] =
    chosen match
      case OccurrenceTaggingOption.Untagged => program
      case OccurrenceTaggingOption.NamesAndClosures =>
        val markers = index.occurrenceMarkers.getOrElse(
          throw IllegalArgumentException("the entry tags its programs' occurrences, and its library declares no occurrence markers")
        )
        ProgramOccurrences.tagged(program, libraryHandles(index), markers)

  /** The instructions the library knows by their handles: every instruction
    * under a lemma's side (a closed part of a side is what the lemma matches
    * by its handle), those a native is bound to and those with a combinator
    * property.
    */
  private def libraryHandles[C <: NativeSpecializer & Singleton](index: StandardLibraryIndex[C])(using C): Set[Configured[C]] =
    @scala.annotation.tailrec
    def under(pending: List[Configured[C]], found: Set[Configured[C]]): Set[Configured[C]] = pending match
      case Nil => found
      case term :: rest if found.contains(term) || term.opaque => under(rest, found + term)
      case term :: rest =>
        val parts = term.layer match
          case Apply(function, argument)    => List(function, argument)
          case Choice(left, right)          => List(left, right)
          case Parallel(left, right)        => List(left, right)
          case Thunk(_, _, fillings)        => fillings.toList
          case _                            => Nil
        under(parts ++ rest, found + term)
    under(index.lemmaSides.flatMap(sides => List(sides.left, sides.right)).toList, Set.empty) ++
      index.nativeBound.map(bound => Configured.fromPure(index.specializer)(bound.instruction)) ++
      index.combinatorProperties.map(property => Configured.fromPure(index.specializer)(property.instruction))

  /** Which tables an entry's reading leaves for its next, as the reading
    * options choose.
    */
  def tableRetention(option: TableRetentionOption): TableRetention =
    option match
      case TableRetentionOption.KeptAll                   => TableRetention.KeptAll
      case TableRetentionOption.NoneKept                  => TableRetention.NoneKept
      case TableRetentionOption.DroppedAtPercent(percent) => TableRetention.DroppedAtPercent(percent)

  /** The retention of the cache service's complete tables a reading's
    * options choose, none for tables kept in the reading's state alone.
    */
  def sharedRetention(option: TableSharingOption): Option[Retention] =
    option match
      case TableSharingOption.Local      => None
      case TableSharingOption.Strong     => Some(Retention.Strong)
      case TableSharingOption.SoftValues => Some(Retention.SoftValues)
      case TableSharingOption.WeakKeys   => Some(Retention.WeakKeys)

  /** How the weak-head machines take an application apart, as a reading's
    * options choose.
    */
  def applications(option: ApplicationOption): ApplicationReading =
    option match
      case ApplicationOption.ByLayer        => ApplicationReading.ByLayer
      case ApplicationOption.BySpine        => ApplicationReading.BySpine
      case ApplicationOption.BySharedPrefix => ApplicationReading.BySharedPrefix

  /** How the tabled weak head applies a function to a continuation, as a
    * reading's options choose.
    */
  def continuations(option: ContinuationOption): ContinuationReading =
    option match
      case ContinuationOption.Substituted => ContinuationReading.Substituted
      case ContinuationOption.Packed      => ContinuationReading.Packed

  /** How the tabled weak head reads a parallel, as a reading's options
    * choose.
    */
  def parallels(option: ParallelOption): ParallelReading =
    option match
      case ParallelOption.BothSides        => ParallelReading.BothSides
      case ParallelOption.HeadsMet => ParallelReading.HeadsMet

  /** The reading state the framework reads an entry's data under, before the
    * data has chosen its options: `KnowledgeReading.compilationState` with
    * the continuation reading `Packed`, the framework's choice for its own
    * reads of configuration. `KnowledgeReading` cannot depend on this project, so its state keeps
    * the field's default. MEASURED 2026-11-20 by a scratch munit probe in
    * contest-entry-generic, not committed, on main with the export through the first binder
    * merged: `EntryData.read` of contest-entries-solo left 72,100 tables
    * under `Substituted` and 48,706 under `Packed` (25,457 steps under
    * both), and the knowledge read after it, under `Packed`, ended at 88,799
    * tables, below `KnowledgeReading.compilationTableLimit`; after the read
    * under `Substituted` it met that limit.
    */
  val entryDataState: ReadingState[NoFacts.type] = KnowledgeReading.compilationState.copy(continuations = ContinuationReading.Packed)

  /** The lemma compilation of a round of an entry's data over the lemmas
    * read from its knowledge and the entry's natives, each implementation
    * its settings choose mapped to the framework's or to a module's of the
    * table given: its saturation under the budget given, its extraction, and
    * the narrow blocks' route its extractor chooses (`route`), whose modules
    * spell the saturation's write-backs as well; the rounds write back through the construction given, the entry's
    * facts'.
    */
  def lemmaCompilation[C <: NativeSpecializer & Singleton](
      lemmas: Vector[LemmaIdentifier],
      settings: RoundSettings,
      budget: Int,
      natives: NativeBackend,
      modules: ExtractorModules,
      construction: TermConstruction[C],
      configuration: ReadingConfiguration[C]
  ): LemmaCompilation[C] =
    val chosenRoute = route(settings.extractor, modules)
    LemmaCompilation(
      saturator(
        settings.saturator,
        SaturationOptions(
          lemmas,
          settings.builtInRules,
          budget,
          lemmaEncoding(settings.lemmaEncoding),
          ematchingBackend(settings.ematching),
          indexer[C](settings.indexer),
          orientationCompiler(settings.orientationCompiler),
          memoRetention(settings.respellings),
          construction,
          constantStorageStop = settings.constantStorageStop
        ),
        settings.opening,
        spellingRetention(settings.writeBackSpellings),
        openingCriterion(settings.openingCriterion),
        chosenRoute.extractorModules(natives, configuration)
      ),
      extractor(settings.extractor, natives, modules, configuration),
      chosenRoute
    )

  /** The saturation a round's data chooses, under the round's options, its
    * write-backs spelled by `modules`.
    */
  def saturator[C <: NativeSpecializer & Singleton](
      implementation: SaturatorImplementation,
      options: SaturationOptions[C],
      opening: Boolean,
      writeBackSpellings: SpellingRetention,
      openingChoice: OpeningCriterionChoice,
      modules: Vector[NormalityModule[C]]
  ): HigherOrderSaturator[C] =
    implementation match
      case SaturatorImplementation.HigherOrder => LemmaCompilation.higherOrderSaturator(options, opening, writeBackSpellings, modules, openingChoice)

  /** The opening criterion a round's data chooses. */
  def openingCriterion(option: OpeningCriterionOption): OpeningCriterionChoice =
    option match
      case OpeningCriterionOption.CallsAHead                       => OpeningCriterionChoice.CallsAHead
      case OpeningCriterionOption.CallsAHeadWithMatchingArguments => OpeningCriterionChoice.CallsAHeadWithMatchingArguments

  /** Whether a memo of a round's implementation keeps what it computed, as
    * the round's data chooses.
    */
  def memoRetention(option: MemoRetentionOption): MemoRetention =
    option match
      case MemoRetentionOption.Kept    => MemoRetention.Kept
      case MemoRetentionOption.NotKept => MemoRetention.NotKept

  /** How long a round's write-backs keep their spellings, as the round's
    * data chooses.
    */
  def spellingRetention(option: WriteBackSpellingsOption): SpellingRetention =
    option match
      case WriteBackSpellingsOption.KeptWithinAPass  => SpellingRetention.KeptWithinAPass
      case WriteBackSpellingsOption.NotKept          => SpellingRetention.NotKept
      case WriteBackSpellingsOption.KeptAcrossPasses => SpellingRetention.KeptAcrossPasses

  /** The narrow blocks a round's extractor data chooses: the default
    * (`gezi.narrowblocks.LemmaRoute`), the opt-in copy with lists and
    * booleans (`gezi.narrowblocks.lists.LemmaRoute`), or the route of the
    * module registered under the selector the data writes, built from the
    * parameters the data writes. Throws `EntryDataError` for a selector no
    * module of the table gives (`ExtractorModules.chosen`).
    */
  def route(implementation: ExtractorImplementation, modules: ExtractorModules): NarrowBlockRoute =
    implementation match
      case ExtractorImplementation.NarrowBlock(_, _)     => LemmaRoute
      case ExtractorImplementation.NarrowListBlock(_, _) => gezi.narrowblocks.lists.LemmaRoute
      case ExtractorImplementation.Module(selector, parameters) =>
        modules.chosen(selector).route(parameters)

  /** The extraction a round's data chooses, over the entry's natives: with
    * the bounds it writes, the narrow blocks' extraction under the modules of
    * the route it chooses (`route`); or the extraction of the module
    * registered under the selector the data writes, built from the
    * parameters the data writes and the entry's natives
    * (`ExtractorModuleInputs`). Throws `EntryDataError` for a selector no
    * module of the table gives (`ExtractorModules.chosen`).
    */
  def extractor[C <: NativeSpecializer & Singleton](
      implementation: ExtractorImplementation,
      natives: NativeBackend,
      modules: ExtractorModules,
      configuration: ReadingConfiguration[C]
  ): Extractor[C] =
    implementation match
      case ExtractorImplementation.NarrowBlock(enumerationBound, wholeFoldBound) =>
        NarrowBlockExtractor(route(implementation, modules).extractorModules(natives, configuration), JointReading(enumerationBound, wholeFoldBound))
      case ExtractorImplementation.NarrowListBlock(enumerationBound, wholeFoldBound) =>
        NarrowBlockExtractor(route(implementation, modules).extractorModules(natives, configuration), JointReading(enumerationBound, wholeFoldBound))
      case ExtractorImplementation.Module(selector, parameters) =>
        modules.chosen(selector).extractor[C](parameters, ExtractorModuleInputs(natives, configuration))

  /** The indexer a round's data chooses, which compiles the round's
    * orientations and codes.
    */
  def indexer[C <: NativeSpecializer & Singleton](implementation: IndexerImplementation): Indexer[C] =
    implementation match
      case IndexerImplementation.Standard => StandardIndexer.of[C]

  /** The orientation compiler a round's data chooses, which compiles its
    * lemmas' patterns into the orientations its indexer files.
    */
  def orientationCompiler(implementation: OrientationCompilerImplementation): OrientationCompiler =
    implementation match
      case OrientationCompilerImplementation.Standard => StandardOrientationCompiler

  /** The e-matching backend a round's data chooses, which runs its
    * saturation's program.
    */
  def ematchingBackend(implementation: EmatchingImplementation): Backend =
    implementation match
      case EmatchingImplementation.Closures       => ClosureCompilation
      case EmatchingImplementation.Interpretation => Interpretation
      case EmatchingImplementation.Bytecode       => BytecodeCompilation

  /** The encoding of a lemma's two closed terms into patterns a round's data
    * chooses.
    */
  def lemmaEncoding(implementation: LemmaEncodingImplementation): LemmaEncoding =
    implementation match
      case LemmaEncodingImplementation.Baseline => BaselineLemmaEncoding

  /** A new cache provider with nothing written, the one the judge's runner
    * builds for an entry's JVM.
    */
  def caches(): CacheProvider = BaselineCaches.provider()

  /** A new cache provider with nothing written, cleared at the lifecycle
    * events given and never when there are none: an adapter whose run is not
    * a contest's round chooses its own.
    */
  def caches(clearedAt: Set[LifecycleEvent]): CacheProvider = BaselineCaches.provider(clearedAt)
