package gezi.contest.judge

import java.nio.file.Paths
import gezi.contest.corpora.reductions
import gezi.contest.corpora.reductions.ReductionGroup
import gezi.contest.corpora.reductions.ReductionProblem
import gezi.weakhead.Expansions

/** The reduction problems of the problem corpora as evaluation sources of a
  * points file, by corpus name: the name of the corpus file a family's
  * generator was ported from (the 23 families of the corpus files
  * jit.plt loaded and eight hidden subtasks), or of the
  * directory whose point tables it reads (`problems/mixin_builtin`'s two), or of a CSES
  * problem's point table (`problems/cses/<problem>/<problem>_point`, whose
  * rows carry their references), or of the point table of a problem built
  * as a CSES problem is (`problems/speculative_untabling/weighted_paths_point`).
  */
object CorpusSources:

  /** The points of each corpus name. */
  val families: Map[String, ReductionGroup => Vector[reductions.CorpusPoint]] = Map(
    "contest_reduction_problems" -> problems(reductions.ReductionProblems.problems),
    "contest_reduction_meanings" -> problems(reductions.ReductionMeanings.problems),
    "contest_reduction_non_canonical" -> problems(reductions.ReductionNonCanonical.problems),
    "contest_reduction_interpreter" -> problems(reductions.ReductionInterpreter.problems),
    "contest_reduction_mixins" -> problems(reductions.ReductionMixins.problems),
    "contest_reduction_mixin_binary" -> problems(reductions.ReductionMixinBinary.problems),
    "contest_reduction_mixin_fibonacci" -> problems(reductions.ReductionMixinFibonacci.problems),
    "contest_reduction_mixin_grid" -> problems(reductions.ReductionMixinGrid.problems),
    "contest_reduction_mixin_library" -> problems(reductions.ReductionMixinLibrary.problems),
    "contest_reduction_mixin_theorems" -> problems(reductions.ReductionMixinTheorems.problems),
    "contest_mixin_builtin_binary" -> problems(reductions.MixinBuiltinPoints.binary),
    "contest_mixin_builtin_natural" -> problems(reductions.MixinBuiltinPoints.natural),
    "contest_set_free_arithmetic" -> problems(reductions.SetFreeArithmetic.problems),
    "contest_set_free_dynamic" -> problems(reductions.SetFreeDynamic.problems),
    "contest_set_free_empty_search" -> problems(reductions.SetFreeEmptySearch.problems),
    "contest_set_free_search" -> problems(reductions.SetFreeSearch.problems),
    "contest_set_free_list_laws" -> problems(reductions.SetFreeListLaws.problems),
    "contest_set_free_premises" -> problems(reductions.SetFreePremises.problems),
    "contest_set_free_scope" -> problems(reductions.SetFreeScope.problems),
    "contest_collect_keys" -> problems(reductions.CollectKeys.problems),
    "contest_path_lengths" -> problems(reductions.PathLengths.problems),
    "contest_reachable_set" -> problems(reductions.ReachableSet.problems),
    "contest_shortest_superstring" -> problems(reductions.ShortestSuperstring.problems),
    "contest_smallest_team" -> problems(reductions.SmallestTeam.problems),
    "contest_two_coloring" -> problems(reductions.TwoColoring.problems),
    "contest_hidden_37_billboard" -> problems(reductions.Hidden37Billboard.problems),
    "contest_hidden_37_concatenation" -> problems(reductions.Hidden37Concatenation.problems),
    "contest_hidden_37_courses" -> problems(reductions.Hidden37Courses.problems),
    "contest_hidden_37_edits" -> problems(reductions.Hidden37Edits.problems),
    "contest_hidden_37_obstacles" -> problems(reductions.Hidden37Obstacles.problems),
    "contest_hidden_37_segments" -> problems(reductions.Hidden37Segments.problems),
    "contest_hidden_37_visit_all" -> problems(reductions.Hidden37VisitAll.problems),
    "contest_hidden_37_workers" -> problems(reductions.Hidden37Workers.problems),
    reductions.CsesPoints.diceCombinations.corpus -> reductions.CsesPoints.diceCombinations.points,
    reductions.CsesPoints.minimizingCoins.corpus -> reductions.CsesPoints.minimizingCoins.points,
    reductions.CsesPoints.messageRoute.corpus -> reductions.CsesPoints.messageRoute.points,
    reductions.CsesPoints.countingRooms.corpus -> reductions.CsesPoints.countingRooms.points,
    reductions.CsesPoints.exponentiation.corpus -> reductions.CsesPoints.exponentiation.points,
    reductions.CsesPoints.coinCombinationsOrdered.corpus -> reductions.CsesPoints.coinCombinationsOrdered.points,
    reductions.CsesPoints.coinCombinationsUnordered.corpus -> reductions.CsesPoints.coinCombinationsUnordered.points,
    reductions.CsesPoints.removingDigits.corpus -> reductions.CsesPoints.removingDigits.points,
    reductions.CsesPoints.gridPaths.corpus -> reductions.CsesPoints.gridPaths.points,
    reductions.CsesPoints.bookShop.corpus -> reductions.CsesPoints.bookShop.points,
    reductions.CsesPoints.shortestRoutesSingleSource.corpus -> reductions.CsesPoints.shortestRoutesSingleSource.points,
    reductions.CsesPoints.shortestRoutesQueries.corpus -> reductions.CsesPoints.shortestRoutesQueries.points,
    reductions.CsesPoints.countingDivisors.corpus -> reductions.CsesPoints.countingDivisors.points,
    reductions.CsesPoints.binomialCoefficients.corpus -> reductions.CsesPoints.binomialCoefficients.points,
    reductions.CsesPoints.distinctNumbers.corpus -> reductions.CsesPoints.distinctNumbers.points,
    reductions.CsesPoints.moneySums.corpus -> reductions.CsesPoints.moneySums.points,
    reductions.CsesPoints.rectangleCutting.corpus -> reductions.CsesPoints.rectangleCutting.points,
    reductions.CsesPoints.increasingSubsequence.corpus -> reductions.CsesPoints.increasingSubsequence.points,
    reductions.CsesPoints.arrayDescription.corpus -> reductions.CsesPoints.arrayDescription.points,
    reductions.CsesPoints.buildingRoads.corpus -> reductions.CsesPoints.buildingRoads.points,
    reductions.CsesPoints.roadReparation.corpus -> reductions.CsesPoints.roadReparation.points,
    reductions.CsesPoints.gameRoutes.corpus -> reductions.CsesPoints.gameRoutes.points,
    reductions.CsesPoints.staticRangeSums.corpus -> reductions.CsesPoints.staticRangeSums.points,
    reductions.CsesPoints.trailingZeros.corpus -> reductions.CsesPoints.trailingZeros.points,
    reductions.CsesPoints.sumOfDivisors.corpus -> reductions.CsesPoints.sumOfDivisors.points,
    reductions.CsesPoints.exponentiationTwo.corpus -> reductions.CsesPoints.exponentiationTwo.points,
    reductions.CsesPoints.ferrisWheel.corpus -> reductions.CsesPoints.ferrisWheel.points,
    reductions.CsesPoints.missingNumber.corpus -> reductions.CsesPoints.missingNumber.points,
    reductions.CsesPoints.repetitions.corpus -> reductions.CsesPoints.repetitions.points,
    reductions.CsesPoints.staticRangeMinimums.corpus -> reductions.CsesPoints.staticRangeMinimums.points,
    reductions.CsesPoints.stringMatching.corpus -> reductions.CsesPoints.stringMatching.points,
    reductions.CsesPoints.subarraySums.corpus -> reductions.CsesPoints.subarraySums.points,
    reductions.CsesPoints.sumOfTwoValues.corpus -> reductions.CsesPoints.sumOfTwoValues.points,
    reductions.CsesPoints.treeDiameter.corpus -> reductions.CsesPoints.treeDiameter.points,
    reductions.CsesPoints.treeMatching.corpus -> reductions.CsesPoints.treeMatching.points,
    reductions.CsesPoints.weightedPaths.corpus -> reductions.CsesPoints.weightedPaths.points
  )

  /** The points of a generator of reduction problems, each read by
    * tabling(weak_head) (`ReductionProblem.corpusPoint`).
    */
  private def problems(generator: ReductionGroup => Vector[ReductionProblem]): ReductionGroup => Vector[reductions.CorpusPoint] =
    group => generator(group).map(_.corpusPoint)

  /** The problems of the corpus named, generated in the caller's group (one
    * per run, as for `seededSources`), as evaluation sources of the stage and
    * the weight, the family the corpus name, each with the reference and the
    * trap candidates its point carries. Throws `IllegalArgumentException`
    * for a name no family has.
    */
  def sources(group: ReductionGroup, corpus: String, stage: String, weight: BigDecimal): Vector[PointSource] =
    families
      .getOrElse(corpus, throw IllegalArgumentException(s"$corpus names no reduction family"))(group)
      .map(found => PointSource.EvaluationSource(found.point, stage, corpus, weight, found.drawn.program, found.drawn.reference, found.drawn.trapCandidates))

  /** The repeated families a seed draws, by family name, with their
    * variants (`reductions.RepeatedVariants`).
    */
  val seededFamilies: Map[String, Vector[reductions.RepeatedVariant]] = reductions.RepeatedVariants.families.toMap

  /** The points of the repeated family named, drawn from the seed: for each
    * variant and each R of the repetitions, the program of R sites, named
    * `stem/repetitions_R` by the variant's stem (`family` or
    * `family/spelling`), never by the seed; the points in order of variant,
    * then of R. Throws
    * `IllegalArgumentException` for a name no repeated family has and for
    * an R outside a variant's nominal range. The group is the caller's,
    * made once per run: a group reads the library and the attractors'
    * tables once, through the evaluator, so a group made per call would read
    * them again for every family (`SeededSourcesLawTest`, 2026-11-12: 68.89 s
    * for its twenty cases, against a 30 s limit).
    */
  def seededSources(
      group: ReductionGroup,
      family: String,
      seed: Long,
      repetitions: Vector[Int],
      stage: String,
      weight: BigDecimal
  ): Vector[PointSource] =
    variantSources(
      group,
      family,
      seededFamilies.getOrElse(family, throw IllegalArgumentException(s"$family names no repeated family")),
      seed,
      repetitions,
      stage,
      weight
    )

  /** The points of the variants given for the family named, drawn as
    * `seededSources` draws them, each with the trap candidates its variant
    * computed (`DrawnPoint.trapCandidates`); the judge's laws give the
    * workload families' variants at their small ranges here, since the
    * points' ranges are of contest size.
    */
  def variantSources(
      group: ReductionGroup,
      family: String,
      variants: Vector[reductions.RepeatedVariant],
      seed: Long,
      repetitions: Vector[Int],
      stage: String,
      weight: BigDecimal
  ): Vector[PointSource] =
    for
      variant <- variants
      count <- repetitions.sorted.distinct
    yield
      val point = variant.point(group, seed, count)
      PointSource.EvaluationSource(
        s"${variant.stem}/repetitions_$count",
        stage,
        family,
        weight,
        point.program,
        point.reference,
        point.trapCandidates
      )

/** The command that writes a points file from corpora, options of
  * the form `--name value`: `--root` (default the property
  * `gezi.buildRoot`), `--corpora` (comma-separated), `--stage`,
  * `--weight`, `--budget` (the steps of tabling(weak_head), the reference
  * reading of `PointsFile.written`) and `--output` (the
  * directory). With a seed and `--repetitions` (comma-separated R values),
  * `--corpora` names the repeated families of
  * `CorpusSources.seededFamilies` instead, each R one point of the family;
  * the seed is `--seed` (a number, for tests and public runs) or
  * `--seed-file` (a file whose first line is the number, for a round), not
  * both (`SupervisorCommand.seed`).
  *
  * With `--member-judgments` (a weight), each evaluation point written is
  * followed by its judgment points of that weight (`PointsFile.written`),
  * named `<point>/candidate_<k>`: one per member of its reference, and,
  * with `--trap-seed-file` (a seed file, read as `--seed-file` is) and
  * `--trap-judgments` (a count), up to that many traps: the candidates the
  * point's family computed for it, or, when none of them is outside its
  * reference, normal forms drawn from a second instance of the same
  * repeated families and R values from the trap seed (`PointsFile.written`);
  * with traps, a point that gets none gets no judgment point at all.
  * The flag `--judgments-only`, which takes no value, writes the judgment
  * points without the evaluation rows. Throws `IllegalArgumentException`
  * when `--judgments-only`, `--trap-seed-file` or `--trap-judgments` is
  * given without `--member-judgments`, when one of the two trap options is
  * given without the other, when traps are asked without a seed and
  * `--repetitions`, and when the trap seed is the points' seed. It prints
  * each source not written and why, with traps each evaluation point
  * written with its traps, and each point whose reference its family
  * computed (`Reference.Computed`) with the test that checks it. Those
  * points are also written to `computed-references.tsv` in the output
  * directory (`ComputedReferences`), since the points file has no column
  * for where a reference came from.
  */
@main def judgePointsFile(arguments: String*): Unit =
  val judgmentsOnlyFlag = "--judgments-only"
  val judgmentsOnly = arguments.contains(judgmentsOnlyFlag)
  val options = SupervisorCommand.options(arguments.toVector.filterNot(_ == judgmentsOnlyFlag))
  def required(name: String): String = options.getOrElse(name, throw IllegalArgumentException(s"the option --$name is required"))
  val memberJudgmentWeight = options.get("member-judgments").map(BigDecimal(_))
  val trapOptions = (options.get("trap-seed-file"), options.get("trap-judgments")) match
    case (Some(path), Some(count)) => Some((path, count.toInt))
    case (None, None)              => None
    case _                         => throw IllegalArgumentException("give the options --trap-seed-file and --trap-judgments together")
  if memberJudgmentWeight.isEmpty then
    if judgmentsOnly then throw IllegalArgumentException(s"$judgmentsOnlyFlag needs --member-judgments")
    if trapOptions.nonEmpty then throw IllegalArgumentException("--trap-seed-file and --trap-judgments need --member-judgments")
  val root = Paths.get(options.getOrElse("root", sys.props.getOrElse("gezi.buildRoot", required("root"))))
  val stage = required("stage")
  val weight = BigDecimal(required("weight"))
  val corpora = required("corpora").split(',').toVector
  val seed = SupervisorCommand.seed(options)
  lazy val group = ReductionGroup(root, Expansions.none, gezi.contest.entry.Defaults.caches())
  def seededSources(drawnSeed: Long): Vector[PointSource] =
    val repetitions = required("repetitions").split(',').toVector.map(_.toInt)
    corpora.flatMap(CorpusSources.seededSources(group, _, drawnSeed, repetitions, stage, weight))
  val sources = seed match
    case Some(pointsSeed) => seededSources(pointsSeed)
    case None =>
      if options.contains("repetitions") then throw IllegalArgumentException("--repetitions needs --seed or --seed-file")
      corpora.flatMap(CorpusSources.sources(group, _, stage, weight))
  val trapDraw = trapOptions.map((path, count) =>
    val pointsSeed = seed.getOrElse(throw IllegalArgumentException("traps need --seed or --seed-file and --repetitions"))
    val trapSeed = SupervisorCommand.seed(Map("seed-file" -> path)) match
      case Some(read) => read
      case None       => throw IllegalStateException("a seed file gave no seed")
    if trapSeed == pointsSeed then throw IllegalArgumentException("the trap seed is the points' seed, so no point would get a trap")
    TrapDraw(seededSources(trapSeed), count)
  )
  val judgments = memberJudgmentWeight.map(JudgmentPoints(_, judgmentsOnly, trapDraw))
  val writtenFile = PointsFile.written(Paths.get(required("output")), sources, required("budget").toLong, judgments)
  writtenFile.unwritten.foreach(unwritten => System.err.println(s"not written: ${unwritten.name}: ${unwritten.reading}"))
  writtenFile.traps.foreach((name, outcome) => System.err.println(s"traps: $name: ${outcome.reported}"))
  ComputedReferences
    .written(Paths.get(required("output")), sources)
    .foreach(row => System.err.println(s"reference computed: ${row.point}: checked by ${row.claim}"))
