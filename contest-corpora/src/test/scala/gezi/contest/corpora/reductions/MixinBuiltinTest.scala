package gezi.contest.corpora.reductions

import hedgehog.Gen
import hedgehog.Result
import gezi.directorysugar.DirectoryTree
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import gezi.weakhead.Computed
import gezi.weakhead.Mode
import gezi.weakhead.NormalForms
import gezi.weakhead.ReadingState
import snapshot4s.generated.snapshotConfig

/** The small ranges the laws of the mixin_builtin families draw from; the
  * construction of a program does not depend on the ranges, and the
  * snapshots show the points' own.
  */
object MixinBuiltinRanges:

  /** Operands of one or two binary digits. */
  val binary: NominalRanges = NominalRanges(Repetition.repetitionsWithin(16), Vector(NominalParameter("digits", 1 to 2)))

  /** Operands from 0 to 2. */
  val natural: NominalRanges = NominalRanges(Repetition.repetitionsWithin(18), Vector(NominalParameter("operand", 0 to 2)))

  /** Siblings of depth 0 or 1. */
  val boolean: NominalRanges = NominalRanges(Repetition.repetitionsWithin(16), Vector(NominalParameter("sibling_depth", 0 to 1)))

  /** The depth of the laws' Boolean trees. */
  val booleanDepth: Int = 2

/** The tests of a mixin_builtin family (`MixinBuiltinFamily`), at the
  * small ranges of `MixinBuiltinRanges`, its twins `direct` and
  * `respelled`.
  *
  * Their readings are tabling(weak_head)'s within `Decoding.limit`,
  * 20,000,000 steps, and a table limit of `tableLimit`, above the reference
  * reading's 50,000 (`ReadingState.defaultTableLimit`), for the reason
  * `MixinBuiltinFamilySuite.tableLimit` gives. A reading that stops fails
  * the law.
  *
  *   - The reference law, the check the families' claims name (each family
  *     names its subclass), whose purpose is to catch a computed reference
  *     that is not the reading of the program (a number written with a
  *     digit wrong, an operation written with another's members, a site
  *     read off another member than `_check`) and a respelling that changes
  *     a program's meaning (a label renamed in the library and not in the
  *     class, two labels renamed to one name, a shuffle that drops a
  *     member): on generated seeds and R of 1 or 2, each twin's repeated
  *     program reads its computed reference, so the respelled twin reads
  *     what the direct twin reads, and the twins' programs are two terms.
  *   - The single law, whose purpose is to catch single programs that are
  *     not the sites of the repeated one: each single program of each twin
  *     reads its site's Boolean.
  *   - The tree law, whose purpose is to catch a library term that is not
  *     the directory tree's (an entry missing or under another key, a file
  *     read in another scope, a directory composed otherwise than the tree
  *     composes it): the direct single program of a generated site over the
  *     library the points carry and over the tree's own mixin of
  *     `problems/mixin_builtin` (`DirectoryTree.mixin`, its URI nodes
  *     expanded by the reading) read the same one normal form.
  *   - The snapshots, whose purpose is to show in review any change of what
  *     a seed draws or of the program built from it: the draws and the
  *     program's text, its literals written as literals
  *     (`ReductionTesting.form`), for the seed 20261031 and R = 3, of each
  *     twin at the points' ranges.
  */
abstract class MixinBuiltinFamilySuite[Site](
    direct: MixinBuiltinFamily[Site],
    respelled: MixinBuiltinFamily[Site],
    pointVariants: Vector[MixinBuiltinFamily[?]],
    snapshotName: String
) extends GeneratedProperties
    with snapshot4s.munit.SnapshotAssertions:

  // Measured 2026-11-21 on 2 CPUs (contest.slice, CPUs 0,1, nice 10), the machine's 1-minute load 28 to 44 over the run (other
  // sessions' unpinned processes), the three subclasses in one test JVM on 328176555: the slowest test, the reference law of the
  // suite that ran first (MixinBuiltinBinaryReferenceTest's "each twin's program reads its computed reference", its seed log
  // 5:56:09 to 5:56:27), took 18 s, the JVM's warm-up included; the other reference laws 5 and 7 s, the single laws about 4 s
  // and the tree laws up to 14 s with the snapshots after them. The bound is 1.5 times the slowest rounded up to 5 s, which
  // held at loads up to 51 in the runs before it. The reason it exceeds the 3 s default: the smallest program of these
  // families reads about 37,000 steps and 17,000 tables of the library's look-ups, the cost of the encoding the families
  // measure (`MixinBuiltinBinary.nominal`), and a law reads up to six programs.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(30, "s")

  // The fixtures, the attractors' fixpoint and the direct library, took 7.0 s and 2.5 s at a load of about 25 and 12.7 s and
  // 4.2 s at about 30 (a scratch probe of the same day), past the default 15 s at the run's load of 51; the bound is 1.5 times
  // their sum at that load rounded up to 5 s.
  override val fixtureTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(30, "s")

  private val group = ReductionTesting.group

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => group.attractors.fixpoint, _ => group.mixinBuiltin.directMixin)

  /** The tables the laws' readings may hold. */
  private val tableLimit: Int = MixinBuiltinFamilySuite.tableLimit

  private def normalForms(program: Term): Either[String, Set[DeBruijnTerm]] =
    NormalForms
      .normalForms(Mode.TablingWeakHead, Reduction.programRoot(program))
      .result(ReadingState.knowingTop(Decoding.limit).copy(tableLimit = tableLimit)) match
      case Computed.Done(forms, _) => Right(forms.map(Defunctionalization.instructionTerm).toSet)
      case Computed.Stopped(after) => Left(s"the reading stopped: ${after.exhausted}, ${after.budget.spent} steps, ${after.tables.held} tables")

  private def readAs(program: Term, expected: Set[DeBruijnTerm]): Result = normalForms(program) match
    case Right(forms) => Result.diff(forms, expected)(_ == _)
    case Left(stop)   => Result.failure.log(stop)

  private def seeds: Gen[Long] = Gen.long(hedgehog.Range.constant(0L, (1L << 31) - 1))

  property("each twin's program reads its computed reference", _.copy(testLimit = 2, shrinkLimit = hedgehog.core.ShrinkLimit(2))) {
    for
      seed <- seeds.forAll
      repetitions <- Gen.int(hedgehog.Range.constant(1, 2)).forAll
    yield
      val points = Vector(direct, respelled).map(_.point(group, seed, repetitions))
      val twoTerms = Result
        .assert(points.map(point => Encodings.deBruijn(point.program)).distinct.size == 2)
        .log("the twins' programs are two terms")
      val read = points.map(point =>
        point.reference match
          case Reference.Computed(forms, claim) =>
            Result.diff(claim, getClass.getName)(_ == _).log("the claim names this suite").and(readAs(point.program, forms.toSet))
          case Reference.Read => Result.failure.log("the reference is not computed")
      )
      Result.all((twoTerms +: read).toList).log(direct.drawnText(group, seed, repetitions))
  }

  property("each single program reads its site's Boolean", _.copy(testLimit = 1, shrinkLimit = hedgehog.core.ShrinkLimit(2))) {
    for seed <- seeds.forAll
    yield Result.all(Vector(direct, respelled).toList.map(twin =>
      val answers = twin.solved(twin.drawnAt(group, seed, 1))
      Result.all(twin.singlePrograms(group, seed, 1).zip(answers).toList.map((program, answer) => readAs(program, Set(answer.normalForm))))
        .log(twin.stem)
    )).log(direct.drawnText(group, seed, 1))
  }

  /** The tree's own mixin of the directory `mixin_builtin`. */
  private def treeMixin: Term =
    Term.closed(DirectoryTree.mixin(ReductionTesting.root, ReductionTesting.root.resolve("problems").resolve(MixinBuiltinLibrary.family)))

  property("the library the points carry reads as the directory tree's", _.copy(testLimit = 1, shrinkLimit = hedgehog.core.ShrinkLimit(2))) {
    for seed <- seeds.forAll
    yield
      val (site, _) = direct.drawnSite(Draws.fromSeed(seed))
      (normalForms(direct.directProgram(group, site)), normalForms(direct.directProgramOver(treeMixin, site))) match
        case (Right(carried), Right(tree)) =>
          Result.assert(carried.size == 1).log("one normal form").and(Result.diff(carried, tree)(_ == _)).log(site.toString)
        case (carried, tree) => Result.failure.log(s"carried: $carried, tree: $tree, $site")
  }

  pointVariants.foreach(variant =>
    val spelling = Repetition.spellingName(variant.spelling)
    test(s"the $spelling program of the seed 20261031 and three repetitions") {
      val seed = 20261031L
      assertFileSnapshot(
        s"seed $seed, 3 repetitions\n${variant.drawnText(group, seed, 3)}\n=>\n${ReductionTesting.form(variant.program(group, seed, 3))}\n",
        s"repeated/${snapshotName}_$spelling.txt"
      )
    }
  )

/** The table limit of the laws' readings. */
object MixinBuiltinFamilySuite:

  /** 200,000 tables, above the reference reading's 50,000
    * (`ReadingState.defaultTableLimit`), which a program of these families
    * passes at R = 2 even at the small ranges: the tables are the
    * encoding's cost, about 38,000 for one site of one or two binary digits
    * or of operands up to 2 and about R times that for R sites (measured
    * 2026-11-21, `MixinBuiltinBinary.nominal`), so two sites take about
    * 76,000; the limit leaves a margin of more than two.
    */
  val tableLimit: Int = 200000

class MixinBuiltinBinaryReferenceTest
    extends MixinBuiltinFamilySuite(
      MixinBuiltinBinary(Spelling.Direct, MixinBuiltinRanges.binary),
      MixinBuiltinBinary(Spelling.Respelled, MixinBuiltinRanges.binary),
      MixinBuiltinBinary.variants,
      "mixin_builtin_binary"
    )

class MixinBuiltinNaturalReferenceTest
    extends MixinBuiltinFamilySuite(
      MixinBuiltinNatural(Spelling.Direct, MixinBuiltinRanges.natural),
      MixinBuiltinNatural(Spelling.Respelled, MixinBuiltinRanges.natural),
      MixinBuiltinNatural.variants,
      "mixin_builtin_natural"
    )

/** The Boolean families' tests at a small depth; the snapshot is of the
  * ladder's first depth, the others differing in the depth alone.
  */
class MixinBuiltinBooleanReferenceTest
    extends MixinBuiltinFamilySuite(
      MixinBuiltinBoolean(Spelling.Direct, MixinBuiltinRanges.boolean, MixinBuiltinRanges.booleanDepth),
      MixinBuiltinBoolean(Spelling.Respelled, MixinBuiltinRanges.boolean, MixinBuiltinRanges.booleanDepth),
      MixinBuiltinBoolean.families.headOption.getOrElse(throw IllegalStateException("no Boolean depth")),
      "mixin_builtin_boolean"
    )
