package gezi.contest.corpora.reductions

import gezi.ir.{Configured, NoFacts}
import scala.annotation.tailrec
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Term

/** `value steps root` of `problems/speculative_untabling/weighted_paths`,
  * built as a CSES family is (`CsesFamily`), each rung in both spellings: the value of the
  * root of a directed acyclic graph whose nodes carry seeds, the value of a
  * node being its weight, its seed after K steps of x ↦ x² + 1 modulo
  * 10^9 + 7, plus the values of its successors, modulo 10^9 + 7.
  *
  * The family has two subfamilies of one program, which differ in their
  * seeds only (`WeightedPaths.Seeds`): in `distinct` every node draws its
  * own seed, and in `recurring` the nodes of a site draw theirs from three
  * values drawn for the site, so that the same weights recur at many nodes.
  * A site is a graph of n nodes and K, n and K drawn from the rung's
  * parameters `nodes` and `steps` (`WeightedPaths.graph`).
  *
  * The answer (`solved`) is the problem's definition computed with one
  * value per node, by the native reference solution
  * (`CsesSolutions.weightedPaths`). The trap (`wrongAnswers`): the
  * answer when every node's weight is taken to be the root's, what a cache
  * of the weights keyed by the number of steps alone, not by the seed,
  * gives; it is a trap candidate only where it differs from the answer at
  * some site (`CsesFamily.trapCandidates`).
  */
final class WeightedPaths(spelling: Spelling, rung: CsesRung, val seeds: WeightedPaths.Seeds)
    extends CsesFamily[WeightedPaths.Site](spelling, rung):

  val problem: String = WeightedPaths.problem

  override def directory: String = WeightedPaths.directory

  override def corpus: String = s"contest_${WeightedPaths.directory}_${WeightedPaths.problem}"

  override def family: String = s"repeated_${WeightedPaths.directory}_${WeightedPaths.problem}_${WeightedPaths.seedsName(seeds)}_${rung.name}"

  val claim: String = seeds match
    case WeightedPaths.Seeds.Distinct  => "gezi.contest.corpora.reductions.WeightedPathsDistinctReferenceTest"
    case WeightedPaths.Seeds.Recurring => "gezi.contest.corpora.reductions.WeightedPathsRecurringReferenceTest"

  /** The definition with one value per node (`WeightedPaths.answer`). */
  def solved(drawn: CsesFamily.Drawn[WeightedPaths.Site]): Vector[NativeValue] = drawn.sites.map(WeightedPaths.answer)

  protected def site(draws: Draws): (WeightedPaths.Site, Draws) = WeightedPaths.site(draws, nominal, seeds)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] = problems.weightedPaths

  def arguments(problems: CsesProblems, site: WeightedPaths.Site): Vector[ProblemTerm] = WeightedPaths.arguments(site)

  /** The answer when every node's weight is the root's. */
  def wrongAnswers(site: WeightedPaths.Site, answer: NativeValue): Vector[NativeValue] = Vector(WeightedPaths.rootWeightAnswer(site))

/** The sites, the draws, the answers and the ladders of `WeightedPaths`. */
object WeightedPaths:

  /** The problem's file and point table, `weighted_paths`. */
  val problem: String = "weighted_paths"

  /** The directory of the problem under `problems`. */
  val directory: String = "speculative_untabling"

  /** The modulus of the steps and the values, 10^9 + 7, the one the
    * program's file writes (`modulus` there).
    */
  val modulus: Int = CsesFamily.modulus

  /** How a site's nodes draw their seeds. */
  enum Seeds:

    /** Each node's seed drawn uniformly from 0 to 10^9 + 6. */
    case Distinct

    /** Three distinct seeds drawn uniformly for the site, each node's seed
      * one of them.
      */
    case Recurring

  /** The subfamily's name in a family name. */
  def seedsName(seeds: Seeds): String = seeds match
    case Seeds.Distinct  => "distinct"
    case Seeds.Recurring => "recurring"

  /** The number of seeds of a recurring site. */
  val recurringValues: Int = 3

  /** A site: K, the seed of each node, and the successors of each node,
    * node 0 the root and every successor a later node.
    */
  final case class Site(steps: Int, seeds: Vector[Int], successors: Vector[Vector[Int]]):
    require(seeds.size == successors.size && seeds.nonEmpty, s"${seeds.size} seeds for ${successors.size} nodes")

    /** The edges of the graph. */
    def edges: Int = successors.map(_.size).sum

  /** A rung of n and K drawn from the ranges and R from the repetitions. */
  private def rung(nodes: Range.Inclusive, steps: Range.Inclusive, repetitions: Range.Inclusive): CsesRung =
    CsesRung(
      s"nodes_${nodes.end}_steps_${steps.end}",
      NominalRanges(repetitions, Vector(NominalParameter("nodes", nodes), NominalParameter("steps", steps)))
    )

  // THE SIZES. Each subfamily's ladder, the bottom rung first, which the suites read with the reference reading
  // (`WeightedPathsDistinctReferenceTest`, `WeightedPathsRecurringReferenceTest`), then the rungs to be sized after the
  // ablation, the last of them the top rung (`CsesFamilies.atConstraints`); every rung is one call of `rung`.
  //
  // MEASURED 2026-11-21 by a scratch probe in contest-corpora's tests (CPUs 8 and 9 of contest.slice, nice 10, a 2 GB
  // test heap, the 1-minute load 5 to 9), tabling(weak_head) knowing top within 20,000,000 steps and 400,000 tables, the
  // single program of a site of distinct seeds (drawn uniformly below the modulus, so about 30 bits each), each reading
  // one normal form unless it stopped:
  //   n = 1: K = 0 13,549 steps and 5,634 tables, K = 1 76,443 and 32,530, K = 2 118,599 and 50,405, K = 10 685,534
  //          and 292,829, K = 30 stopped at the 400,000 tables;
  //   n = 2 (1 edge): K = 0 22,771 and 9,364, K = 1 147,640 and 62,464, K = 2 296,126 and 126,063;
  //   n = 3 (3 edges): K = 0 41,752 and 17,217, K = 1 234,178 and 99,472, K = 2 439,142 and 187,185;
  //   n = 5 (7 to 9 edges): K = 0 75,452 and 31,204, K = 1 410,918 and 174,438, K = 2 712,022 and 302,326;
  //   n = 10 (19 edges): K = 0 139,421 and 57,214; n = 20 (35 edges): K = 0 280,102 and 114,555;
  //   n = 5, 10 and 20 at K = 10, 30 and 100: every reading stopped at the 400,000 tables.
  // A step of x ↦ x² + 1 on a seed of about 30 bits costs about 60,000 steps and 27,000 tables, and a node about 13,500
  // and 5,700 at K = 0, so the reference reading's 50,000 tables (`ReadingState.defaultTableLimit`) hold n · (K + 1) of
  // about 2 to 8. The bottom rung is sized to that: n of 1 to 3 at K = 0, the steps tested by the point table's rows
  // (`CsesPoints.weightedPaths`, seeds of 1 to 7 and one of 999,999,999). The second rung is the target the family was
  // specified with, n of 10 to 20 and K of 10 to 100, which the reference reading does not answer within those
  // tables; its points' references are computed (`solved`) and need no reading.
  //
  // The top rungs are sized by what the judge can read, not by a programming contest's n. MEASURED 2026-11-21 by the
  // judge's points-file writer (`judgePointsFile`, seed 20261031, R 1 and 4, both spellings, CPUs 6 and 7 at nice 10, a
  // 2 GB heap, the 1-minute load 16 to 18), at the sizes first chosen: the recurring top rung of n 5 · 10^4 to 10^5 gave
  // a 67 MB file, about 670 bytes a node, and the distinct top rung of n 5,000 to 10^4 one of 36 MB, about 3.6 KB a
  // node (each node's own 30-bit seed); the judge's supervisor, at its 256 MB heap, ran out of memory parsing the
  // recurring file at start (`PointsFile.read`, in `Lambdalattice.parse`). Most of those bytes are input, which the
  // native time does not include and the work the family measures does not need: that work is the K steps of each
  // distinct seed and one value per node. So the top rungs keep K and take n of 1,000 to 2,000 (distinct) and 5,000 to
  // 10^4 (recurring), files of about 7 MB.

  /** The ladder of `distinct`: the bottom rung, read by the reference
    * reading; n of 10 to 20 and K of 10 to 100; and the top rung, n of
    * 1,000 to 2,000 and K of 500 to 10^3, at most four sites.
    */
  val distinctRungs: Vector[CsesRung] = Vector(
    rung(1 to 3, 0 to 0, Repetition.repetitions),
    rung(10 to 20, 10 to 100, Repetition.repetitions),
    rung(1000 to 2000, 500 to 1000, 1 to 4)
  )

  /** The ladder of `recurring`: the two lower rungs of `distinct`, and the
    * top rung, n of 5,000 to 10^4 and K of 5,000 to 9,999, at most four
    * sites.
    */
  val recurringRungs: Vector[CsesRung] = Vector(
    rung(1 to 3, 0 to 0, Repetition.repetitions),
    rung(10 to 20, 10 to 100, Repetition.repetitions),
    rung(5000 to 10000, 5000 to 9999, 1 to 4)
  )

  /** Each rung's family of `distinct` in both spellings. */
  val distinctFamilies: Vector[Vector[WeightedPaths]] = CsesFamily.families(distinctRungs, WeightedPaths(_, _, Seeds.Distinct))

  /** Each rung's family of `recurring` in both spellings. */
  val recurringFamilies: Vector[Vector[WeightedPaths]] = CsesFamily.families(recurringRungs, WeightedPaths(_, _, Seeds.Recurring))

  /** A site drawn from the ranges: n, K, the graph, then the seeds. */
  def site(draws: Draws, nominal: NominalRanges, seeds: Seeds): (Site, Draws) =
    val (nodes, afterNodes) = CsesFamily.drawnParameter(draws, nominal, "nodes")
    val (steps, afterSteps) = CsesFamily.drawnParameter(afterNodes, nominal, "steps")
    val (successors, afterGraph) = graph(nodes, afterSteps)
    val (drawnSeeds, afterSeeds) = seeds match
      case Seeds.Distinct => CsesFamily.drawnValues(nodes, afterGraph)(belowModulus)
      case Seeds.Recurring =>
        val (values, afterValues) = afterGraph.distinct(recurringValues)(belowModulus)
        CsesFamily.drawnValues(nodes, afterValues)(_.chosen(values))
    (Site(steps, drawnSeeds, successors), afterSeeds)

  /** A number from 0 to 10^9 + 6, uniformly: 30 bits from two draws of 15
    * (`Draws.number`), drawn again when they are the modulus or above.
    */
  @tailrec
  def belowModulus(draws: Draws): (Int, Draws) =
    val (high, afterHigh) = draws.number(0 to Draws.highBitsCount - 1)
    val (low, afterLow) = afterHigh.number(0 to Draws.highBitsCount - 1)
    val value = (high << 15) | low
    if value < modulus then (value, afterLow) else belowModulus(afterLow)

  /** The successors of each of n nodes, every edge from a node to a later
    * one, so that the numbering is a topological order, and every node
    * reachable from node 0, the root. Each node but the last draws its
    * out-degree, 1 to 3 and at most the nodes after it; then each node from
    * 1 on is the successor of a node before it whose out-degree is not yet
    * reached, drawn uniformly, which makes it reachable from the root, by
    * induction; then each node's remaining successors are drawn uniformly
    * from the later nodes it does not reach by an edge yet. Such a node
    * before node j always remains: the j nodes before it have out-degrees
    * of at least 1 each, and the nodes 1 to j - 1 took j - 1 of them.
    */
  def graph(nodes: Int, draws: Draws): (Vector[Vector[Int]], Draws) =
    require(nodes >= 1, s"no graph of $nodes nodes")
    val (drawnDegrees, afterDegrees) = CsesFamily.drawnValues(nodes - 1, draws)(CsesFamily.between(_, 1 to 3))
    val degrees = drawnDegrees.zipWithIndex.map((degree, node) => math.min(degree, nodes - 1 - node)) :+ 0
    val (spanning, open, afterSpanning) = (1 until nodes).foldLeft((Vector.fill(nodes)(Vector.empty[Int]), Vector.empty[Int], afterDegrees)) {
      case ((found, before, current), node) =>
        val opened = before :+ (node - 1)
        val (chosen, afterChosen) = CsesFamily.between(current, 0 to opened.size - 1)
        val parent = opened(chosen)
        val grown = found.updated(parent, found(parent) :+ node)
        val stillOpen =
          if grown(parent).size < degrees(parent) then opened
          else opened.updated(chosen, opened.last).dropRight(1)
        (grown, stillOpen, afterChosen)
    }
    (0 until nodes).foldLeft((spanning, afterSpanning)) { case ((found, current), node) =>
      val (filled, afterFilled) = filledSuccessors(node, nodes, degrees(node), found(node), current)
      (found.updated(node, filled), afterFilled)
    }

  /** The successors of the node grown to the out-degree, each added one
    * drawn uniformly from the later nodes not among them, drawn again when
    * it is among them.
    */
  @tailrec
  private def filledSuccessors(node: Int, nodes: Int, degree: Int, successors: Vector[Int], draws: Draws): (Vector[Int], Draws) =
    if successors.size >= degree then (successors, draws)
    else
      val (drawn, after) = CsesFamily.between(draws, node + 1 to nodes - 1)
      filledSuccessors(node, nodes, degree, if successors.contains(drawn) then successors else successors :+ drawn, after)

  /** The answer of the site, by the native reference solution
    * (`CsesSolutions.weightedPaths`).
    */
  def answer(site: Site): NativeValue = NativeValue.natural(CsesSolutions.weightedPaths(site.steps, site.seeds, site.successors))

  /** The value of the root when every node's weight is the root's: the
    * solution on the site with every seed the root's.
    */
  def rootWeightAnswer(site: Site): NativeValue =
    NativeValue.natural(CsesSolutions.weightedPaths(site.steps, Vector.fill(site.seeds.size)(site.seeds(0)), site.successors))

  /** The site's data as the program's header gives it: K a binary natural,
    * and the root, each node `λk. k seed successors`, the seed a binary
    * natural and the successors a Scott list of nodes.
    *
    * Each node is a closed term, so each is converted once, from the last
    * node to the root, into a closed instruction (`Defunctionalization`) whose
    * successors are the instructions of the later nodes, held as constants:
    * the instructions are interned, so a node is one instruction however
    * many paths reach it, the program's IR has a layer for each node, each
    * edge and each distinct seed, and its exchange line binds each repeated
    * instruction once (`ExchangeText`), linear in the edges.
    *
    * The point table binds each node once by an abstraction applied to its
    * definition, which β-reduces to these instructions. Written so, as a
    * HOAS term, a site was not linear: each thunk of the chain of
    * abstractions captures every bound node a later definition reads, and
    * random successors make that up to all of them. MEASURED 2026-11-21 by
    * a scratch probe in contest-corpora's tests (CPUs 8 and 9 of
    * contest.slice, nice 10, a 2 GB test heap, the 1-minute load about 9):
    * the conversion of the program (`Reduction.programRoot`) of a site of
    * distinct seeds and K = 10 took 0.6 s at 250 nodes, 2.2 s at 500, 4.3 s
    * at 1,000 and 12.0 s at 2,000, and at 4,000 ran the heap out after
    * 298 s.
    */
  def arguments(site: Site): Vector[ProblemTerm] =
    val seedInstructions = site.seeds.distinct.map(seed => seed -> Defunctionalization.thunkInstruction(StandardLibraryNormalForms.binary(BigInt(seed)))(using gezi.ir.NoFacts)).toMap
    val nil = DeBruijnTerm.Constant(Defunctionalization.thunkInstruction(StandardLibraryNormalForms.list(Vector.empty))(using gezi.ir.NoFacts))
    def list(elements: Vector[ProblemDeBruijnTerm]): ProblemDeBruijnTerm =
      elements.foldRight(nil)((head, tail) =>
        DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), head), tail)))
      )
    val nodes = (site.seeds.size - 1 to 0 by -1).foldLeft(Map.empty[Int, Configured[NoFacts.type]])((converted, node) =>
      val definition = DeBruijnTerm.Lambda(
        DeBruijnTerm.Apply(
          DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), DeBruijnTerm.Constant(seedInstructions(site.seeds(node)))),
          list(site.successors(node).map(successor => DeBruijnTerm.Constant(converted(successor))))
        )
      )
      converted.updated(node, Defunctionalization.thunkInstruction(definition)(using gezi.ir.NoFacts))
    )
    Vector(CsesEncodings.natural(site.steps), Term.closed(nodes(0)))
