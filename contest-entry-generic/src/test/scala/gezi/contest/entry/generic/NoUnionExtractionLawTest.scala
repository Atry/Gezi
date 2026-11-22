package gezi.contest.entry.generic

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Paths
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Defaults
import gezi.contest.entry.EntryData
import gezi.contest.entry.ExecutorModules
import gezi.contest.entry.ExtractorModules
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Instruction
import gezi.jit.NativesProvider
import gezi.narrowblocks.LemmaRoute
import gezi.narrowblocks.PreparedLemmaCompilation
import gezi.saturation.StopSignal

/** The law the lemma route's shortcut rests on
  * (`LemmaRoute.compiledRounds`):
  * when the shared rounds leave a graph with no union at all, the last
  * round's extraction is the program itself, so that handing the program on
  * without extracting changes no output. Checked with the framework's
  * fixture entry's rounds, each with its own settings (extraction,
  * e-matching, built-in rules) and no lemma, whose knowledge would union its
  * library terms in every graph, on generated programs in which neither a
  * β-redex nor an η-redex is written, so that the graphs have no union.
  * Its purpose is to catch an extraction that spells a graph with no union
  * otherwise than the program, which the shortcut would hide.
  */
class NoUnionExtractionLawTest extends GeneratedProperties:

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  /** The fixture entry's rounds, each with the settings the entry's data
    * gives it and no lemma, prepared for the entry's library's index.
    */
  private lazy val rounds: Vector[PreparedLemmaCompilation] =
    val entryDirectory = buildRoot.resolve("contest-entries-fixture")
    val (data, afterEntry) = EntryData.read(entryDirectory, Defaults.entryDataState)
    val entry = GenericEntryProvider.initialized(
      data,
      ExecutorModules.registeredFor(entryDirectory),
      ExtractorModules.registeredFor(entryDirectory),
      NativesProvider.loaded,
      ArticleDestination.Discarded,
      afterEntry,
      Defaults.caches()
    )
    data.rounds.map(round =>
      Defaults
        .lemmaCompilation(Vector.empty, round.settings, GenericEntry.roundCap, entry.natives, ExtractorModules.registeredFor(entryDirectory))
        .prepared(entry.index)
    )

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => rounds)

  /** A term of about `size` nodes under `bound` abstractions with neither a
    * β-redex nor an η-redex written: abstractions, variables applied to
    * abstractions, choices and parallels.
    */
  private def term(size: Int, bound: Int): Gen[DeBruijnTerm] =
    val leaf: Gen[DeBruijnTerm] =
      if bound == 0 then Gen.constant(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0)))
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
          yield DeBruijnTerm.Apply(DeBruijnTerm.Variable(variable), DeBruijnTerm.Lambda(argument))
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

  private val program: Gen[Instruction] =
    Gen.int(Range.linear(1, 30)).flatMap(term(_, 0)).map(Defunctionalization.thunkInstruction)

  stoppableProperty("the last round extracts a graph with no union to the program") { stopped =>
    for root <- program.forAll
    yield
      val stop = StopSignal.completedWith(stopped)
      val (run, _, _) = LemmaRoute.saturatedRounds(rounds, root, false, stop)
      if run.graph.unionCount == 0 then
        Result.diff(rounds.last.extracted(root, run, stop), root)(_ == _).log("the extraction and the program")
      else Result.success.log(s"${run.graph.unionCount} unions, not checked")
  }
