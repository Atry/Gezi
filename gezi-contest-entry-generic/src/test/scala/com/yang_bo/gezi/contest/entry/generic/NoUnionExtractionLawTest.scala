package com.yang_bo.gezi.contest.entry.generic

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Paths
import com.yang_bo.gezi.contest.entry.ArticleDestination
import com.yang_bo.gezi.contest.entry.Defaults
import com.yang_bo.gezi.contest.entry.EntryData
import com.yang_bo.gezi.contest.entry.ExecutorModules
import com.yang_bo.gezi.contest.entry.ExtractorModules
import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NativeSpecializer
import com.yang_bo.gezi.jit.NativesProvider
import com.yang_bo.gezi.narrowblocks.LemmaRoute
import com.yang_bo.gezi.narrowblocks.PreparedLemmaCompilation
import com.yang_bo.gezi.saturation.StopSignal

/** The law the lemma route's shortcut rests on (`LemmaRoute.compiledRounds`):
  * when the shared rounds leave a graph with no union at all, the last round's
  * extraction is the program itself, so that handing the program on without
  * extracting changes no output. Checked with the framework's fixture entry's
  * rounds, each with its own settings (extraction, e-matching, built-in rules)
  * and no lemma, whose knowledge would union its library terms in every graph,
  * on generated programs in which neither a β-redex nor an η-redex is written,
  * so that the graphs have no union. Its purpose is to catch an extraction that
  * spells a graph with no union otherwise than the program, which the shortcut
  * would hide.
  */
class NoUnionExtractionLawTest extends GeneratedProperties:

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  /** The fixture entry's rounds, each with the settings the entry's data gives
    * it and no lemma, prepared for the entry's library's index, in the entry's
    * configuration.
    */
  private lazy val rounds: Rounds[?] =
    val entryDirectory = buildRoot.resolve("gezi-contest-entries-fixture")
    val (data, afterEntry) =
      EntryData.read(entryDirectory, Defaults.entryDataState)
    val entry = GenericEntryProvider.initialized(
      data,
      ExecutorModules.registeredFor(entryDirectory),
      ExtractorModules.registeredFor(entryDirectory),
      NativesProvider.loaded,
      ArticleDestination.Discarded,
      afterEntry,
      Defaults.caches()
    )
    Rounds.of(entry, data, ExtractorModules.registeredFor(entryDirectory))

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => rounds)

  /** A term of about `size` nodes under `bound` abstractions with neither a
    * β-redex nor an η-redex written: abstractions, variables applied to
    * abstractions, choices and parallels.
    */
  private def term(size: Int, bound: Int): Gen[DeBruijnTerm] =
    val leaf: Gen[DeBruijnTerm] =
      if bound == 0 then
        Gen.constant(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0)))
      else Gen.int(Range.constant(0, bound - 1)).map(DeBruijnTerm.Variable(_))
    if size <= 1 then leaf
    else
      Gen.int(Range.constant(1, 10)).flatMap { kind =>
        val smaller = size - 1
        if kind <= 4 then term(smaller, bound + 1).map(DeBruijnTerm.Lambda(_))
        else if kind <= 7 && bound > 0 then
          for
            variable <- Gen.int(Range.constant(0, bound - 1))
            argument <- term(smaller, bound + 1)
          yield DeBruijnTerm.Apply(
            DeBruijnTerm.Variable(variable),
            DeBruijnTerm.Lambda(argument)
          )
        else if kind <= 8 then
          for
            left <- term(1.max(smaller / 2), bound)
            right <- term(1.max(smaller / 2), bound)
          yield DeBruijnTerm.nestedChoice(Vector(left, right))
        else if kind <= 9 then
          for
            left <- term(1.max(smaller / 2), bound)
            right <- term(1.max(smaller / 2), bound)
          yield DeBruijnTerm.Parallel(left, right)
        else leaf
      }

  private val program: Gen[DeBruijnTerm] =
    Gen.int(Range.linear(1, 30)).flatMap(term(_, 0))

  stoppableProperty(
    "the last round extracts a graph with no union to the program"
  ) { stopped =>
    for root <- program.forAll
    yield rounds.extractedAlike(root, StopSignal.completedWith(stopped))
  }

  /** The rounds, prepared in the entry's configuration `C`. */
  private final case class Rounds[C <: NativeSpecializer & Singleton](
      prepared: Vector[PreparedLemmaCompilation[C]]
  )(using C):

    /** The law on one program, translated in `C`, whose parallels the entry's
      * specializer converts as its rounds do.
      */
    def extractedAlike(written: DeBruijnTerm, stop: StopSignal): Result =
      val root = Defunctionalization.thunkInstruction[C](written)
      val (run, _, _) = LemmaRoute.saturatedRounds(prepared, root, false, stop)
      if run.graph.unionCount == 0 then
        Result
          .assert(
            Configured.same(prepared.last.extracted(root, run, stop), root)
          )
          .log("the extraction and the program")
      else Result.success.log(s"${run.graph.unionCount} unions, not checked")

  private object Rounds:

    /** The entry's rounds with no lemma, written back through the entry's
      * construction as its own rounds are (`GenericEntryProvider.initialized`).
      */
    def of[C <: NativeSpecializer & Singleton](
        entry: GenericEntry[C],
        data: EntryData,
        modules: ExtractorModules
    ): Rounds[C] =
      given C = entry.specializer
      val construction = com.yang_bo.gezi.jit.ConvertedTermConstruction[C](entry.encoding)(
        entry.jit.configuration.storageAccess
      )
      Rounds(
        data.rounds.map(round =>
          Defaults
            .lemmaCompilation[C](
              Vector.empty,
              round.settings,
              GenericEntry.roundCap,
              entry.natives,
              modules,
              construction,
              entry.jit.readingConfiguration
            )
            .prepared(entry.index)
        )
      )
