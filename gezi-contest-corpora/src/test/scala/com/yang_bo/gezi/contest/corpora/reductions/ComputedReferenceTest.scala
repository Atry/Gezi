package com.yang_bo.gezi.contest.corpora.reductions

import hedgehog.Gen
import hedgehog.Result
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import scala.annotation.tailrec

/** The parameters of a natively solved family fixed, its data left to generate:
  * `point` builds the point of these parameters over data drawn from the draws
  * it is given (`NativelySolved.drawnPoint`).
  */
final case class ParameterDraws(
    parameters: String,
    point: (ReductionGroup, Draws) => DrawnPoint
)

/** The check a computed reference's claim names (`Reference.Computed`).
  *
  * Both laws have the purpose of catching a family whose computed reference is
  * not tabling(weak_head)'s reading of its program (a wrong parity, the sites
  * out of order, a Boolean or a list encoded otherwise than the reading reads
  * it back, a library function computed wrongly). In each, a point's normal
  * forms must be the set tabling(weak_head) (`mode`) reads of its program
  * within `Decoding.limit`, 20,000,000 steps, and a reading it stops fails the
  * law.
  *
  *   - The drawn law: on generated seeds and repetitions R from 1 to 6, the
  *     point of each of `variants` (each at the ranges its suite gives) has a
  *     computed reference whose claim names this suite. Seeds and R are drawn
  *     uniformly, `draws` of them (30 unless a suite says why fewer); a failure
  *     is shrunk at most 8 times.
  *   - The parameter law, for a suite that gives `parameters`: every parameter
  *     set the family's seeds draw from (each define of the pool, each
  *     function, loop, transformer or operation, both spellings, each count of
  *     times), enumerated, with its data generated from a uniformly drawn seed,
  *     5 seeds. A seed draws one parameter set per point, so the drawn law
  *     alone may leave one untested in a run.
  */
abstract class ComputedReferenceSuite(
    variants: Vector[RepeatedVariant],
    parameters: Vector[ParameterDraws] = Vector.empty,
    draws: Int = 30
) extends GeneratedProperties:

  // Measured 2026-11-16 on 2 CPUs (contest.slice, CPUs 0,1, nice 10), the 1-minute load 5.0 to 7.1 over the run, one run of all 31
  // subclasses in one test JVM at these deadlines, the shared fixtures forced first: the slowest subclass is
  // ReductionProblemsFibonacciReferenceTest, 5.362 s for the whole suite (its shared fixture, the group's arithmetic, about 4 s,
  // included, so its test takes less), then RepeatedGeneralCompositionsReferenceTest 4.328 s and
  // ReductionProblemsGridsReferenceTest 3.227 s (6 draws, see its Scaladoc); the bound keeps 1.5 times the slowest's measured
  // length, rounded up to 5 s. Grids at 30 draws took 9.8 s with these fixtures (one run, deadlines raised, load 4.9 to 7.0)
  // and 19.9 s on main 607eb67f5 without them, which missed this deadline.
  // FIXME: this suite exceeds the 3 s default: its draws are weak_head readings of up to 3.3M steps each (Grids), and https://github.com/Atry/private-overlay/issues/1925
  // Fibonacci's suite pays the group's arithmetic fixture, about 4 s. Its slow tests are still to be made fast.
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(10, "s")

  private val group = ReductionTesting.group

  /** The group and every program a variant or a parameter set builds from it,
    * built once before the first test and not charged to it (FailFastSuite): a
    * family's first point reads the library terms it is built of, which are the
    * group's lazy members (for the grids, `group.arithmetic`, about 4 s: 41
    * knowledge readings of 176,825 steps, measured 2026-11-16 on 607eb67f5),
    * and is setup, not the law.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(
      _ => group,
      _ => variants.map(_.point(group, 0L, 1)),
      _ => parameters.map(_.point(group, Draws.fromSeed(0L)))
    )

  /** The reading the references are checked against: tabling(weak_head). */
  private def mode: Mode = Mode.TablingWeakHead

  /** Whether the point's normal forms are the mode's reading. */
  private def read(
      point: DrawnPoint,
      normalForms: Vector[com.yang_bo.gezi.frontend.DeBruijnTerm]
  ): Result =
    Reduction.answeredNormalForms(mode, point.program, Decoding.limit) match
      case NormalFormReading.Finished(read) =>
        Result.diff(normalForms.toSet, read.toSet)(_ == _)
      case stopped => Result.failure.log(s"the reading stopped: $stopped")

  property(
    "the computed reference is tabling(weak_head)'s reading of the program",
    _.copy(
      testLimit = hedgehog.core.SuccessCount(draws),
      shrinkLimit = hedgehog.core.ShrinkLimit(8)
    )
  ) {
    for
      seed <- Gen.long(hedgehog.Range.constant(0L, (1L << 31) - 1)).forAll
      repetitions <- Gen.int(hedgehog.Range.constant(1, 6)).forAll
    yield Result.all(variants.toList.map(variant =>
      val point = variant.point(group, seed, repetitions)
      val law = point.reference match
        case Reference.Computed(normalForms, claim) =>
          Result
            .diff(claim, getClass.getName)(_ == _)
            .log("the claim names this suite")
            .and(read(point, normalForms))
        case Reference.Read =>
          Result.failure.log("the reference is not computed")
      law.log(
        s"${variant.stem}: ${variant.drawnText(group, seed, repetitions)}"
      )
    ))
  }

  if parameters.nonEmpty then
    property(
      "at every parameter set, the computed reference is tabling(weak_head)'s reading of the program",
      _.copy(testLimit = 5, shrinkLimit = hedgehog.core.ShrinkLimit(4))
    ) {
      for seed <- Gen.long(hedgehog.Range.constant(0L, (1L << 31) - 1)).forAll
      yield Result.all(parameters.toList.map(parameterDraws =>
        val point = parameterDraws.point(group, Draws.fromSeed(seed))
        val law = point.reference match
          case Reference.Computed(normalForms, _) => read(point, normalForms)
          case Reference.Read                     =>
            Result.failure.log("the reference is not computed")
        law.log(parameterDraws.parameters)
      ))
    }

/** The parameter sets the families' seeds draw from, enumerated, each over two
  * sites of data drawn from the family's ranges.
  */
object ParameterSets:

  /** The count of sites of each point. */
  private val sites: Int = 2

  /** The rebuild, the complement, the unit law and its near miss, in both
    * spellings, at every count of times, so both parities of the complement's.
    */
  val premises: Vector[ParameterDraws] =
    val family = SetFreePremisesRepeated
    for
      function <- family.functions
      spelling <- Repetition.spellings
      times <- Repetition.range(family.nominal, "times")
    yield ParameterDraws(
      s"$function, $spelling, $times times",
      (group, draws) =>
        val numbers = draws
          .distinct(sites)(Repetition.drawnNumber(_, family.nominal, "number"))
          ._1
        family.drawnPoint(
          group,
          SetFreePremisesRepeated.Drawn(function, spelling, times, numbers)
        )
    )

  /** Fibonacci and its doubling near miss in both spellings, over the steps of
    * the variant's ranges.
    */
  def scope(family: SetFreeScopeRepeatedVariant): Vector[ParameterDraws] =
    for
      loop <- SetFreeScopeRepeatedVariant.loops
      spelling <- Repetition.spellings
    yield ParameterDraws(
      s"$loop, $spelling",
      (group, draws) =>
        val steps = draws
          .distinct(sites)(Repetition.drawnNumber(_, family.nominal, "steps"))
          ._1
        family.drawnPoint(
          group,
          SetFreeScopeRepeatedVariant.Drawn(loop, spelling, steps)
        )
    )

  /** Map and its filter near miss in both spellings, over the doublings of the
    * variant's ranges.
    */
  def listLaws(family: SetFreeListLawsRepeatedVariant): Vector[ParameterDraws] =
    for
      transformer <- SetFreeListLawsRepeatedVariant.transformers
      spelling <- Repetition.spellings
    yield ParameterDraws(
      s"$transformer, $spelling",
      (group, draws) =>
        val doublings = draws
          .distinct(sites)(
            Repetition.drawnNumber(_, family.nominal, "doublings")
          )
          ._1
        family.drawnPoint(
          group,
          SetFreeListLawsRepeatedVariant.Drawn(transformer, spelling, doublings)
        )
    )

  /** The sum and the product. */
  val mixinBinary: Vector[ParameterDraws] =
    val family = ReductionMixinBinaryRepeated
    family.operations.map(operation =>
      ParameterDraws(
        operation,
        (group, draws) =>
          val equations =
            draws.distinct(sites)(family.equation(operation, _))._1
          family.drawnPoint(
            group,
            ReductionMixinBinaryRepeated.Drawn(operation, equations)
          )
      )
    )

  /** The sum, the product and the product's near miss, in both spellings. */
  val arithmetic: Vector[ParameterDraws] =
    val family = SetFreeArithmeticRepeated
    for
      operation <- family.operations
      spelling <- Repetition.spellings
    yield ParameterDraws(
      s"$operation, $spelling",
      (group, draws) =>
        val pairs = draws.distinct(sites)(family.pair(family.nominal))._1
        family.drawnPoint(
          group,
          SetFreeArithmeticRepeated.Drawn(operation, spelling, pairs)
        )
    )

  /** Each define of the pool, in both spellings. */
  val libraryCompositions: Vector[ParameterDraws] =
    for
      family <- RepeatedLibraryCompositions.variants
      (define, inputs) <- family.defines(ReductionTesting.group)
    yield ParameterDraws(
      s"$define, ${family.spelling}",
      (group, draws) =>
        val data = draws
          .distinct(sites)(CompositionLibrary.data(_, family.nominal, inputs))
          ._1
        family.drawnPoint(
          group,
          RepeatedLibraryCompositions.Drawn(define, data)
        )
    )

  /** The producers of a type: the functions of one input whose input is a
    * site's datum and whose answer has the type.
    */
  private def producers(output: SiteDataType): Vector[UnaryFunction] =
    CompositionLibrary.unaryFunctions.filter(function =>
      CompositionLibrary.dataTypes.contains(
        function.input
      ) && function.output == output
    )

  /** The first producer of a type, in the pool's order. */
  private def firstProducer(output: SiteDataType): UnaryFunction =
    producers(output).headOption.getOrElse(
      throw IllegalStateException(s"no producer answers $output")
    )

  /** Every general composition a seed may draw whose g is each function of two
    * inputs, or whose h is each producer, the other functions the first that
    * fit, in both spellings: so every function a stage one family's composition
    * may call is called, those that are no define included (the constructor
    * successor, and the functions of Booleans).
    */
  val generalCompositions: Vector[ParameterDraws] =
    val byOuter = CompositionLibrary.binaryFunctions.map(outer =>
      GeneralComposition(
        outer,
        firstProducer(outer.left),
        firstProducer(outer.right)
      )
    )
    val byLeft = CompositionLibrary.unaryFunctions
      .filter(function => CompositionLibrary.dataTypes.contains(function.input))
      .map(left =>
        val outer = CompositionLibrary.binaryFunctions
          .find(_.left == left.output)
          .getOrElse(
            throw IllegalStateException(
              s"no function of two inputs takes ${left.output} first"
            )
          )
        GeneralComposition(outer, left, firstProducer(outer.right))
      )
    for
      family <- RepeatedGeneralCompositions.variants
      composition <- (byOuter ++ byLeft).distinct
    yield ParameterDraws(
      s"$composition, ${family.spelling}",
      (group, draws) =>
        val data = draws
          .distinct(sites)(
            CompositionLibrary.data(_, family.nominal, composition.inputs)
          )
          ._1
        family.drawnPoint(
          group,
          RepeatedGeneralCompositions.Drawn(composition, data)
        )
    )

  /** Every pair of the lengths of the small ranges, both spellings, so that
    * each end of either string, empty strings included, is read; over one site
    * each, since two empty strings are one pair only.
    */
  val editDistances: Vector[ParameterDraws] =
    val nominal = StandardLibraryFamilyRanges.editDistances
    for
      spelling <- Repetition.spellings
      firstLength <- Repetition.range(nominal, "length")
      secondLength <- Repetition.range(nominal, "length")
    yield ParameterDraws(
      s"$spelling, lengths $firstLength and $secondLength",
      (group, draws) =>
        LibraryEditDistances(spelling, nominal, LibraryEditDistances.name)
          .drawnPoint(
            group,
            LibraryEditDistances.drawnOfLengths(
              nominal,
              draws,
              1,
              firstLength,
              secondLength
            )
          )
    )

  /** A member site and a trap site, both spellings, over one site each. The
    * drawn law draws each site's kind with probability one half, and a trap
    * site needs rods that leave a height from 1 to S / 2 unreached, which the
    * small ranges' rods often do not, so a run of it may read no trap; here a
    * trap site's rods are drawn again until they leave one.
    */
  val billboards: Vector[ParameterDraws] =
    val nominal = StandardLibraryFamilyRanges.billboards
    for
      spelling <- Repetition.spellings
      kind <- LibraryBillboards.Kind.values.toVector
    yield ParameterDraws(
      s"$spelling, a $kind site",
      (group, draws) =>
        LibraryBillboards(spelling, nominal, LibraryBillboards.name)
          .drawnPoint(
            group,
            LibraryBillboards.Drawn(Vector(billboardSite(nominal, kind, draws)))
          )
    )

  /** A site of the kind: its rods drawn, then drawn again while the kind is a
    * trap and the rods reach every height a trap may take, so that the site
    * falls back to a member.
    */
  @tailrec
  private def billboardSite(
      nominal: NominalRanges,
      kind: LibraryBillboards.Kind,
      draws: Draws
  ): LibraryBillboards.Site =
    val (rods, afterRods) = LibraryBillboards.rods(nominal)(draws)
    val (site, afterSite) = LibraryBillboards.site(rods, kind, afterRods)
    val (member, _) =
      LibraryBillboards.site(rods, LibraryBillboards.Kind.Member, afterRods)
    if kind == LibraryBillboards.Kind.Member || site != member then site
    else billboardSite(nominal, kind, afterSite)

  /** Every count of skills and of people of the small ranges, both spellings,
    * over one site each: at one skill and one person only two teams exist, so
    * two distinct sites are not always there.
    */
  val smallestTeams: Vector[ParameterDraws] =
    val nominal = StandardLibraryFamilyRanges.smallestTeams
    for
      spelling <- Repetition.spellings
      skills <- Repetition.range(nominal, "skills")
      people <- Repetition.range(nominal, "people")
    yield ParameterDraws(
      s"$spelling, $skills skills, $people people",
      (group, draws) =>
        LibrarySmallestTeams(spelling, nominal, LibrarySmallestTeams.name)
          .drawnPoint(
            group,
            LibrarySmallestTeams.drawnOfCounts(
              nominal,
              draws,
              1,
              skills,
              people
            )
          )
    )

class LibraryUnsharedDoublingsReferenceTest
    extends ComputedReferenceSuite(
      Repetition.spellings.map(
        LibraryUnsharedDoublings(
          _,
          StandardLibraryFamilyRanges.unsharedDoublings,
          LibraryUnsharedDoublings.name,
          LibraryUnsharedDoublings.claim
        )
      )
    )

class LibraryUnsharedBinaryReferenceTest
    extends ComputedReferenceSuite(
      Repetition.spellings.map(
        LibraryUnsharedBinary(
          _,
          StandardLibraryFamilyRanges.unsharedBinary,
          StandardLibraryFamilyRanges.unsharedBinarySuffix,
          LibraryUnsharedBinary.name,
          LibraryUnsharedBinary.claim
        )
      )
    )

class LibraryUnsharedDoublingsLargeReferenceTest
    extends ComputedReferenceSuite(
      Repetition.spellings.map(
        StandardLibraryFamilyRanges.unsharedDoublingsLarge
      )
    )

class LibraryUnsharedBinaryLargeReferenceTest
    extends ComputedReferenceSuite(
      Repetition.spellings.map(StandardLibraryFamilyRanges.unsharedBinaryLarge)
    )

/** The binary domain traps' computed reference, by the defines' semantics on
  * trees, against tabling(weak_head)'s reading at the small ranges of
  * `StandardLibraryFamilyRanges.binaryDomainTraps`: it would catch a tree
  * semantics that differs from the defines' (a sum that drops the leading zeros
  * as the integers do, a comparison by value), which would make the family's
  * traps answer what an unchecked integer reading answers.
  */
class LibraryBinaryDomainTrapsReferenceTest
    extends ComputedReferenceSuite(
      Repetition.spellings.map(
        LibraryBinaryDomainTraps(
          _,
          StandardLibraryFamilyRanges.binaryDomainTraps
        )
      )
    )

class LibraryLongestCommonSubsequencesReferenceTest
    extends ComputedReferenceSuite(
      Repetition.spellings.map(
        LibraryLongestCommonSubsequences(
          _,
          StandardLibraryFamilyRanges.longestCommonSubsequences,
          LibraryLongestCommonSubsequences.name
        )
      )
    )

/** The billboards' computed reference, the targets or no normal form, against
  * tabling(weak_head)'s reading: it would catch a native solver that misses or
  * invents a height, a target drawn as a trap that the rods reach, or a
  * parallel read otherwise than the reference assumes. The parameter law reads
  * a member site and a trap site in both spellings on every run.
  */
class LibraryBillboardsReferenceTest
    extends ComputedReferenceSuite(
      Repetition.spellings.map(
        LibraryBillboards(
          _,
          StandardLibraryFamilyRanges.billboards,
          LibraryBillboards.name
        )
      ),
      ParameterSets.billboards
    )

class LibraryEditDistancesReferenceTest
    extends ComputedReferenceSuite(
      Repetition.spellings.map(
        LibraryEditDistances(
          _,
          StandardLibraryFamilyRanges.editDistances,
          LibraryEditDistances.name
        )
      ),
      ParameterSets.editDistances
    )

class LibrarySmallestTeamsReferenceTest
    extends ComputedReferenceSuite(
      Repetition.spellings.map(
        LibrarySmallestTeams(
          _,
          StandardLibraryFamilyRanges.smallestTeams,
          LibrarySmallestTeams.name
        )
      ),
      ParameterSets.smallestTeams
    )

/** The hotspots' rung and its cold and hot calibration variants, whose
  * references the same native solver computes.
  */
class LibraryHotspotsReferenceTest
    extends ComputedReferenceSuite(
      for
        calibration <- LibraryHotspots.Calibration.values.toVector
        spelling <- Repetition.spellings
      yield StandardLibraryFamilyRanges.hotspotsVariant(spelling, calibration)
    )

/** The inlined shape of the hot ladder, whose reference the iterated shape's
  * native solver computes: it would catch a loop that applies a function other
  * than its count of times (a digit read the wrong way, the odd case's
  * application dropped or doubled) or that applies another function than the
  * site's.
  */
class LibraryHotspotsInlinedReferenceTest
    extends ComputedReferenceSuite(
      Repetition.spellings.map(
        StandardLibraryFamilyRanges
          .hotspotsShapedVariant(_, LibraryHotspots.Shape.Inlined)
      )
    )

/** The nested shape of the hot ladder, whose reference the iterated shape's
  * native solver computes: it would catch a split whose product is not the
  * count, or inner and outer loops wired so that the function runs another
  * number of times.
  */
class LibraryHotspotsNestedReferenceTest
    extends ComputedReferenceSuite(
      Repetition.spellings.map(
        StandardLibraryFamilyRanges
          .hotspotsShapedVariant(_, LibraryHotspots.Shape.Nested)
      )
    )

class LibraryUnsharedWordPowersReferenceTest
    extends ComputedReferenceSuite(
      Repetition.spellings.map(
        LibraryUnsharedWordPowers(
          _,
          StandardLibraryFamilyRanges.unsharedWordPowers
        )
      )
    )

class ReductionMeaningsReferenceTest
    extends ComputedReferenceSuite(Vector(ReductionMeaningsRepeated))

class ReductionInterpreterReferenceTest
    extends ComputedReferenceSuite(Vector(ReductionInterpreterRepeated))

class SetFreePremisesReferenceTest
    extends ComputedReferenceSuite(
      Vector(SetFreePremisesRepeated),
      ParameterSets.premises
    )

/** Steps from 0 to 20, the range of `SetFreeScopeRepeatedTest`'s law, for the
  * reason given there.
  */
class SetFreeScopeReferenceTest
    extends ComputedReferenceSuite(
      Vector(SetFreeScopeReferenceTest.variant),
      ParameterSets.scope(SetFreeScopeReferenceTest.variant)
    )

/** The scope loop over steps from 0 to 20. */
object SetFreeScopeReferenceTest:

  /** The variant both laws read. */
  val variant: SetFreeScopeRepeatedVariant =
    SetFreeScopeRepeatedVariant(
      NominalRanges(
        Repetition.repetitionsWithin(21),
        Vector(NominalParameter("steps", 0 to 20))
      )
    )

/** Doublings from 0 to 6, the range of `SetFreeListLawsRepeatedTest`'s law, for
  * the reason given there.
  */
class SetFreeListLawsReferenceTest
    extends ComputedReferenceSuite(
      Vector(SetFreeListLawsReferenceTest.variant),
      ParameterSets.listLaws(SetFreeListLawsReferenceTest.variant)
    )

/** The list law over doublings from 0 to 6. */
object SetFreeListLawsReferenceTest:

  /** The variant both laws read. */
  val variant: SetFreeListLawsRepeatedVariant =
    SetFreeListLawsRepeatedVariant(
      NominalRanges(
        Repetition.repetitionsWithin(7),
        Vector(NominalParameter("doublings", 0 to 6))
      )
    )

class ReductionProblemsFibonacciReferenceTest
    extends ComputedReferenceSuite(Vector(ReductionProblemsRepeated.Fibonacci))

class ReductionProblemsProductsReferenceTest
    extends ComputedReferenceSuite(Vector(ReductionProblemsRepeated.Products))

/** Sides from 0 to 8, the range of `ReductionProblemsGridsRepeatedTest`'s law,
  * for the reason given there, on 6 draws, not 30: every draw can be the
  * heaviest, whose weak_head reading takes 3,271,378 steps and 0.72 to 1.07 s
  * (measured 2026-11-16 on 607eb67f5 and 4f79cb45e, cores 0-1, the 1-minute
  * load 4 to 7, five runs in fresh JVMs), so 6 draws take at most about 6.4 s
  * whatever the seeds, two thirds of the 10 s deadline (the margin of 1.5 times
  * this build's deadlines keep over their measured length). Thirty took 9.8 s
  * with the suite's shared fixtures (the same day, load 4.9 to 7.0) and 19.9 s
  * on main 607eb67f5 without them. The side range is unchanged, so every side
  * stays reachable; the law says the same thing on fewer samples.
  */
class ReductionProblemsGridsReferenceTest
    extends ComputedReferenceSuite(
      Vector(
        ReductionProblemsRepeated.GridsVariant(
          NominalRanges(
            Repetition.repetitionsWithin(9),
            Vector(NominalParameter("side", 0 to 8))
          )
        )
      ),
      draws = 6
    )

class ReductionProblemsSumsReferenceTest
    extends ComputedReferenceSuite(Vector(ReductionProblemsRepeated.Sums))

class ReductionMixinBinaryReferenceTest
    extends ComputedReferenceSuite(
      Vector(ReductionMixinBinaryRepeated),
      ParameterSets.mixinBinary
    )

class SetFreeArithmeticReferenceTest
    extends ComputedReferenceSuite(
      Vector(SetFreeArithmeticRepeated),
      ParameterSets.arithmetic
    )

class LibraryDoublingParitiesReferenceTest
    extends ComputedReferenceSuite(
      Repetition.spellings.map(
        LibraryDoublingParities(_, StandardLibraryFamilyRanges.doublingParities)
      )
    )

class LibraryBinaryParitiesReferenceTest
    extends ComputedReferenceSuite(
      Repetition.spellings.map(
        LibraryBinaryParities(_, StandardLibraryFamilyRanges.binaryParities)
      )
    )

class RepeatedIdenticalSubtermsReferenceTest
    extends ComputedReferenceSuite(RepeatedIdenticalSubterms.variants)

class RepeatedClosuresReferenceTest
    extends ComputedReferenceSuite(RepeatedClosures.variants)

class RepeatedLibraryCompositionsReferenceTest
    extends ComputedReferenceSuite(
      RepeatedLibraryCompositions.variants,
      ParameterSets.libraryCompositions
    )

class RepeatedGeneralCompositionsReferenceTest
    extends ComputedReferenceSuite(
      RepeatedGeneralCompositions.variants,
      ParameterSets.generalCompositions
    )

class RepeatedNestedCompositionsReferenceTest
    extends ComputedReferenceSuite(RepeatedNestedCompositions.variants)
