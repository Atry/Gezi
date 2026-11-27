package com.yang_bo.gezi.contest.entry

import java.nio.file.Paths
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.frontend.Lambdalattice
import com.yang_bo.gezi.frontend.Literals
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.jit.NativeBackend
import com.yang_bo.gezi.weakhead.ReadingConfiguration
import com.yang_bo.gezi.narrowblocks.LemmaRoute
import com.yang_bo.gezi.narrowblocks.NarrowBlockRoute
import com.yang_bo.gezi.strategies.Extractor

/** The laws of choosing an extractor module by the identity of its selector
  * (`ExtractorModules`, `Defaults.route`, `Defaults.extractor`), with the
  * module of these tests (`TestExtractorModule`), registered with
  * `java.util.ServiceLoader` in the tests' resources. Their purpose is to catch
  * a lookup that finds a module by anything but its selector's term, a module
  * whose extraction or route does not get the parameters the entry wrote or the
  * framework's inputs, a round that pairs a module's extraction with another
  * route than the module's, a selector the entry imports that is another
  * instruction than the one the module registers, a selector no module gives
  * that is answered by some module or by the framework's extraction, and two
  * modules that give one selector answered by either.
  */
class ExtractorModuleLawTest extends GeneratedProperties:

  private val buildRoot =
    Paths.get(sys.props("gezi.buildRoot")).toAbsolutePath.normalize

  /** The modules the tests' class path registers, read off the tree whose
    * visible subtree is Gezi's directory.
    */
  private lazy val modules: ExtractorModules =
    ExtractorModules.registered(buildRoot)

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => modules)

  /** The natives a module's extraction and route are built over. */
  private val natives: NativeBackend = NativeBackend.standard

  /** The test module's selector written out, the term its selector file
    * tests/extractor_module_fixtures/test_extractor gives: α-equivalent terms
    * are one term.
    */
  private val testSelector: String =
    "((λ\"$extraction\". λx. x) \"$extraction\")"

  /** The text of the library's Scott integer of the value. */
  private def number(value: BigInt): String =
    s"(${Lambdalattice.text(Literals.integerTerm(value), Map.empty)})"

  /** The settings of a round, their extractor the one given, the rest the
    * fixture entry's (contest-entries-fixture).
    */
  private def settings(extractor: ExtractorImplementation): RoundSettings =
    RoundSettings(
      opening = false,
      builtInRules = Set.empty,
      IndexerImplementation.Standard,
      OrientationCompilerImplementation.Standard,
      SaturatorImplementation.HigherOrder,
      extractor,
      LemmaEncodingImplementation.Baseline,
      EmatchingImplementation.Closures,
      MemoRetentionOption.Kept,
      WriteBackSpellingsOption.KeptWithinAPass,
      OpeningCriterionOption.CallsAHead
    )

  /** An entry of one round of no knowledge whose extractor is the text given,
    * its other settings those of `settings`, and of a backend of no knowledge
    * read by the framework's JIT.
    */
  private def entryText(extractor: String): String =
    val roundSettings = EntryText
      .roundSlots(settings(ExtractorImplementation.NarrowBlock(1, 0)))
      .map(slot =>
        if slot.group == 0 && slot.slot == 3 then slot.copy(value = extractor)
        else slot
      )
    EntryText.entry(
      Vector(
        EntryText.round(
          Vector.empty,
          Vector(
            EntryText.contribution(EntryData.roundGroupWidths, roundSettings)
          )
        )
      ),
      Vector.empty,
      Vector(
        EntryText.contribution(
          EntryData.backendGroupWidths,
          EntryText.backendSlots(
            JitOptions(
              DispatchOption.Fallback,
              BackendOption.Closure,
              GranularityOption.PredicatePerCode,
              instanceTable = false,
              instanceTableTrial = 1L,
              instanceRetention = InstanceRetentionOption.NeverDropped,
              budget = 0,
              checkpoints = CheckpointOption.Profitable,
              nativeBlocks = NativeBlocksOption.None,
              lookahead = LookaheadOption.Lazily,
              instanceReuse = InstanceReuseOption.WithinVersion
            ),
            ReadingOptions(
              ApplicationOption.ByLayer,
              TableSharingOption.Local,
              TableRetentionOption.NoneKept,
              ContinuationOption.Substituted,
              ParallelOption.BothSides
            ),
            EntryText.jitExecutor,
            CompilationPlaceOption.Upfront(UnitSelectionOption.WholeProgram),
            OccurrenceTaggingOption.Untagged
          )
        )
      )
    )

  /** The classes of an extraction and a route chosen, what a failure reports:
    * their fields hold the natives, too long to print.
    */
  private def classesOf(
      extractor: Extractor[NoFacts.type],
      route: NarrowBlockRoute
  ): String =
    s"${extractor.getClass.getName} and ${route.getClass.getName}"

  /** The one round's extractor of the entry the text writes. */
  private def extractorRead(text: String): ExtractorImplementation =
    val Vector(round) = (EntryData.lambdalatticeRead(text).rounds: @unchecked)
    round.settings.extractor

  property(
    "aRoundSelectingTheTestModuleGetsItsExtractionAndRouteWithTheParametersItWrote"
  ) {
    for parameter <- Gen
        .long(Range.linearFrom(0L, Long.MinValue, Long.MaxValue))
        .map(BigInt(_))
        .forAll
    yield
      val chosen = extractorRead(
        entryText(
          EntryText.moduleExtractor(testSelector, s"λs. s ${number(parameter)}")
        )
      )
      val compilation = Defaults.lemmaCompilation(
        Vector.empty,
        settings(chosen),
        0,
        natives,
        modules,
        com.yang_bo.gezi.ir.TermConstruction(com.yang_bo.gezi.ir.NoFacts),
        ReadingConfiguration.withoutFacts
      )
      val inputs =
        ExtractorModuleInputs(natives, ReadingConfiguration.withoutFacts)
      (compilation.extractor, compilation.route) match
        case (
              ParameterCarryingExtractor(extracted, extractorInputs, _),
              ParameterCarryingRoute(routed, framework)
            ) =>
          Result
            .diff(extracted, parameter)(_ == _)
            .and(Result.diff(routed, parameter)(_ == _))
            .and(Result.diff(extractorInputs, inputs)(_ == _))
            .and(Result.assert(framework eq LemmaRoute))
        case (extractor, route) =>
          Result.failure.log(
            s"the extraction and route chosen are ${classesOf(extractor, route)}"
          )
  }

  /** Its purpose is to catch a selector the entry imports from the module's
    * selector file that reads as another instruction than the module's: the one
    * round of the entry of
    * tests/extractor_module_fixtures/entry_with_test_extractor, read through
    * the tree as the generic entry reads one, gets the test module's extraction
    * and route with its parameter, 7.
    */
  test("anEntryImportingTheSelectorFileGetsTheTestModule") {
    val (data, _) = EntryData.at(
      buildRoot,
      buildRoot.resolve(
        "tests/extractor_module_fixtures/entry_with_test_extractor.lambdalattice"
      ),
      Defaults.entryDataState
    )
    val Vector(round) = (data.rounds: @unchecked)
    val inputs =
      ExtractorModuleInputs(natives, ReadingConfiguration.withoutFacts)
    (
      Defaults.extractor(
        round.settings.extractor,
        natives,
        modules,
        ReadingConfiguration.withoutFacts
      ),
      Defaults.route(round.settings.extractor, modules)
    ) match
      case (
            ParameterCarryingExtractor(extracted, _, _),
            ParameterCarryingRoute(routed, _)
          ) =>
        assertEquals((extracted, routed), (BigInt(7), BigInt(7)))
      case (extractor, route) =>
        fail(
          s"the extraction and route chosen are ${classesOf(extractor, route)}"
        )
  }

  property("aSelectorNoModuleGivesIsRefused") {
    for count <- Gen.int(Range.linear(0, 6)).forAll
    yield
      val selector = s"(λa. λb. a${" b" * count})"
      val chosen = extractorRead(
        entryText(EntryText.moduleExtractor(selector, s"λs. s ${number(1)}"))
      )
      def refused(computed: => Any): Boolean =
        scala.util.Try(computed).failed.toOption.exists {
          case _: EntryDataError => true
          case _                 => false
        }
      Result
        .assert(
          refused(
            Defaults.extractor(
              chosen,
              natives,
              modules,
              ReadingConfiguration.withoutFacts
            )
          )
        )
        .and(Result.assert(refused(Defaults.route(chosen, modules))))
  }

  /** Its purpose is to catch a table that keeps one of two modules whose
    * selector files give one term: the test module registered twice is refused.
    */
  test("twoModulesGivingOneSelectorAreRefused") {
    intercept[EntryDataError](
      ExtractorModules.registered(
        buildRoot,
        Vector(TestExtractorModule(), TestExtractorModule())
      )
    )
  }
