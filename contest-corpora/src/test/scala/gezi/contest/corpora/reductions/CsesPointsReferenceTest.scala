package gezi.contest.corpora.reductions

import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.generatedinputs.FailFastSuite
import gezi.weakhead.Computed
import gezi.weakhead.Mode
import gezi.weakhead.NormalForms
import gezi.weakhead.ReadingState
import snapshot4s.generated.snapshotConfig

/** The tests of the CSES point tables (`CsesPoints`), the check their
  * computed references name (`CsesPoints.claim`). Their inputs are the
  * rows of the tables, the data under test, not generated.
  *
  *   - The rows' snapshots, whose purpose is to show in review what each row
  *     reads as, and to catch a row that no longer reads (a field of
  *     another encoding, a row of another width): every row of every table,
  *     its name, its site and its Result, one snapshot for each batch.
  *   - The definition law, whose purpose is to catch a Result of the second
  *     or the third batch's tables that is not the problem's answer by its
  *     statement, independently of the native solver: each row's Result is
  *     the definition's computed in the test (`CsesSecondBatchDefinitions`,
  *     `CsesThirdBatchDefinitions`).
  *   - The solver law, whose purpose is to catch a Result that is not the
  *     problem's answer at the row's inputs, or inputs decoded otherwise than
  *     the table writes them: each row's Result is the native solver's
  *     (`CsesSolutions`, through the family's `solved`).
  *   - The reading law, whose purpose is to catch a point whose program does
  *     not answer its reference (inputs encoded otherwise than the problem's
  *     header gives them, another problem's function): each point's
  *     reference is the row's Result, its claim this suite, and the
  *     program's reading by the reference reading, tabling(weak_head)
  *     knowing top within `CsesPointsReferenceTest.stepLimit` steps and the
  *     reference reading's 50,000 tables (`ReadingState.defaultTableLimit`),
  *     is that Result alone.
  */
class CsesPointsReferenceTest extends FailFastSuite with snapshot4s.munit.SnapshotAssertions:

  given gezi.ir.NoFacts.type = gezi.ir.NoFacts

  private val group = ReductionTesting.group

  /** The library's expansions, and each table's points: its file's rows
    * decoded and its problem's function read, both kept by the group, so
    * that a test is timed by its own work. MEASURED 2026-11-22 (CPUs 4 and 5
    * of contest.slice, nice 10, the 1-minute load about 20): with only the
    * dice function a fixture, the third batch's rows test, which decodes its
    * ten files, took 3.022 s and the rectangle_cutting reading test, which
    * reads its function first, 3.005 s, past their 3 s; in two runs before
    * that both had passed.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector[scala.concurrent.Future[Unit] => Any](_ => group.problems.sharedExpansions) ++
      CsesPoints.all.map(table => (_: scala.concurrent.Future[Unit]) => table.points(group))

  private def normalForms(program: Term): Either[String, Set[gezi.frontend.DeBruijnTermOf[gezi.ir.Configured[gezi.ir.NoFacts.type]]]] =
    NormalForms
      .normalForms(Mode.TablingWeakHead, Reduction.programRoot(program))
      .result(ReadingState.knowingTop(CsesPointsReferenceTest.stepLimit, gezi.weakhead.ReadingConfiguration.withoutFacts)) match
      case Computed.Done(forms, _) => Right(forms.map(form => Defunctionalization.instructionTerm[gezi.ir.NoFacts.type](form)).toSet)
      case Computed.Stopped(after) => Left(s"the reading stopped: ${after.exhausted}, ${after.budget.spent} steps, ${after.tables.held} tables")

  /** A Result as the tables write it: a natural in decimal, an option `none`
    * or `some k`, a list `[a, b]`.
    */
  private def shown(value: NativeValue): String = value match
    case NativeValue.Binary(digits)        => CsesFamily.naturalOf(digits).toString
    case NativeValue.Optional(None)        => "none"
    case NativeValue.Optional(Some(found)) => s"some ${shown(found)}"
    case NativeValue.Elements(values)      => values.map(shown).mkString("[", ", ", "]")
    case other                             => fail(s"no Result of a CSES table: $other")

  /** Every row of the tables, its name, its site and its Result. */
  private def rowsText(tables: Vector[CsesPointTable[?]]): String =
    tables
      .map(table => (table.table +: table.rows(group).map(row => s"  ${row.point}: ${row.site} => ${shown(row.result)}")).mkString("\n"))
      .mkString("", "\n", "\n")

  test("every row of every table of the first batch reads") {
    assertFileSnapshot(rowsText(CsesPoints.firstBatch), "cses/points.txt")
  }

  test("every row of every table of the second batch reads") {
    assertFileSnapshot(rowsText(CsesPoints.secondBatch), "cses/points_second_batch.txt")
  }

  test("every row of every table of the third batch reads") {
    assertFileSnapshot(rowsText(CsesPoints.thirdBatch), "cses/points_third_batch.txt")
  }

  test("every row of every table of the fourth batch reads") {
    assertFileSnapshot(rowsText(CsesPoints.fourthBatch), "cses/points_fourth_batch.txt")
  }

  (CsesPointsReferenceTest.secondBatchDefinitions ++ CsesPointsReferenceTest.thirdBatchDefinitions ++
    CsesPointsReferenceTest.fourthBatchDefinitions).foreach(defined =>
    test(s"${defined.table.table}: each row's Result is the problem's definition's") {
      def checked[Site](of: CsesPointsReferenceTest.Defined[Site]): Unit =
        of.table.rows(group).foreach(row => assertEquals(row.result, of.definition(row.site), row.point))
      checked(defined)
    }
  )

  CsesPoints.all.foreach(table =>
    test(s"${table.table}: each row's Result is the native solver's") {
      def solved[Site](of: CsesPointTable[Site]): Vector[(String, NativeValue, NativeValue)] =
        of.rows(group).map(row =>
          val answer = of.family.solved(CsesFamily.Drawn(Vector(row.site), 0L)) match
            case Vector(single) => single
            case other          => fail(s"${other.size} answers for one site")
          (row.point, row.result, answer)
        )
      solved(table).foreach((point, result, answer) => assertEquals(result, answer, point))
    }

    test(s"${table.table}: each program reads its row's Result") {
      def checked[Site](of: CsesPointTable[Site]): Vector[(String, NativeValue, Reference, Either[String, Set[gezi.frontend.DeBruijnTermOf[gezi.ir.Configured[gezi.ir.NoFacts.type]]]])] =
        of.rows(group).zip(of.points(group)).map((row, point) =>
          assertEquals(point.point, row.point)
          (row.point, row.result, point.drawn.reference, normalForms(point.drawn.program))
        )
      checked(table).foreach((point, result, reference, reading) =>
        assertEquals(reference, Reference.Computed(Vector(result.normalForm), getClass.getName), point)
        reading match
          case Right(forms) => assertEquals(forms, Set(result.normalForm), point)
          case Left(stop)   => fail(s"$point: $stop")
      )
    }
  )

/** The budget of the reading law, and the definitions of the second and the
  * third batch's problems the tables' Results are checked against.
  */
object CsesPointsReferenceTest:

  /** A table of the second or the third batch and its problem's definition
    * (`CsesSecondBatchDefinitions`, `CsesThirdBatchDefinitions`).
    */
  final case class Defined[Site](table: CsesPointTable[Site], definition: Site => NativeValue)

  /** The second batch's tables, each with its problem's definition, in the
    * order of `CsesPoints.secondBatch`.
    */
  val secondBatchDefinitions: Vector[Defined[?]] = Vector(
    Defined(CsesPoints.coinCombinationsOrdered, CsesSecondBatchDefinitions.coinCombinationsOrdered),
    Defined(CsesPoints.coinCombinationsUnordered, CsesSecondBatchDefinitions.coinCombinationsUnordered),
    Defined(CsesPoints.removingDigits, CsesSecondBatchDefinitions.removingDigits),
    Defined(CsesPoints.gridPaths, CsesSecondBatchDefinitions.gridPaths),
    Defined(CsesPoints.bookShop, CsesSecondBatchDefinitions.bookShop),
    Defined(CsesPoints.shortestRoutesSingleSource, CsesSecondBatchDefinitions.shortestRoutesSingleSource),
    Defined(CsesPoints.shortestRoutesQueries, CsesSecondBatchDefinitions.shortestRoutesQueries),
    Defined(CsesPoints.countingDivisors, CsesSecondBatchDefinitions.countingDivisors),
    Defined(CsesPoints.binomialCoefficients, CsesSecondBatchDefinitions.binomialCoefficients),
    Defined(CsesPoints.distinctNumbers, CsesSecondBatchDefinitions.distinctNumbers)
  )

  /** The third batch's tables, each with its problem's definition, in the
    * order of `CsesPoints.thirdBatch`.
    */
  val thirdBatchDefinitions: Vector[Defined[?]] = Vector(
    Defined(CsesPoints.moneySums, CsesThirdBatchDefinitions.moneySums),
    Defined(CsesPoints.rectangleCutting, CsesThirdBatchDefinitions.rectangleCutting),
    Defined(CsesPoints.increasingSubsequence, CsesThirdBatchDefinitions.increasingSubsequence),
    Defined(CsesPoints.arrayDescription, CsesThirdBatchDefinitions.arrayDescription),
    Defined(CsesPoints.buildingRoads, CsesThirdBatchDefinitions.buildingRoads),
    Defined(CsesPoints.roadReparation, CsesThirdBatchDefinitions.roadReparation),
    Defined(CsesPoints.gameRoutes, CsesThirdBatchDefinitions.gameRoutes),
    Defined(CsesPoints.staticRangeSums, CsesThirdBatchDefinitions.staticRangeSums),
    Defined(CsesPoints.trailingZeros, CsesThirdBatchDefinitions.trailingZeros),
    Defined(CsesPoints.sumOfDivisors, CsesThirdBatchDefinitions.sumOfDivisors)
  )

  /** The fourth batch's tables, each with its problem's definition, in the
    * order of `CsesPoints.fourthBatch`.
    */
  val fourthBatchDefinitions: Vector[Defined[?]] = Vector(
    Defined(CsesPoints.exponentiationTwo, CsesFourthBatchDefinitions.exponentiationTwo),
    Defined(CsesPoints.ferrisWheel, CsesFourthBatchDefinitions.ferrisWheel),
    Defined(CsesPoints.missingNumber, CsesFourthBatchDefinitions.missingNumber),
    Defined(CsesPoints.repetitions, CsesFourthBatchDefinitions.repetitions),
    Defined(CsesPoints.staticRangeMinimums, CsesFourthBatchDefinitions.staticRangeMinimums),
    Defined(CsesPoints.stringMatching, CsesFourthBatchDefinitions.stringMatching),
    Defined(CsesPoints.subarraySums, CsesFourthBatchDefinitions.subarraySums),
    Defined(CsesPoints.sumOfTwoValues, CsesFourthBatchDefinitions.sumOfTwoValues),
    Defined(CsesPoints.treeDiameter, CsesFourthBatchDefinitions.treeDiameter),
    Defined(CsesPoints.treeMatching, CsesFourthBatchDefinitions.treeMatching)
  )

  /** The steps of the reading law's readings: 150,000, twice the largest
    * reading of the tables' rows. MEASURED 2026-11-21 on 9a1e7944f by a
    * scratch test in this suite (CPUs 0 to 3 of contest.slice, nice 10, the
    * 1-minute load about 8), tabling(weak_head) knowing top, each row's
    * program read to its one normal form: the largest,
    * cses_counting_rooms_all_floor (a map of 4 × 4 floor squares), 74,936
    * steps and 29,597 tables; then cses_dice_combinations_sum_six 32,947 and
    * 14,089, cses_counting_rooms_two_rooms 26,420 and 10,692 and
    * cses_exponentiation_seven_to_eight 16,402 and 7,131; every other row at
    * most 10,501 steps and 4,629 tables. The second batch's rows, MEASURED
    * 2026-11-21 on 236b88682 by a scratch test in this project (CPUs 0 to 3
    * of contest.slice, nice 10, the 1-minute load about 9), the same
    * reading within 20,000,000 steps: the largest,
    * cses_counting_divisors_highly_composite (36 and 30), 57,034 steps and
    * 24,177 tables; then cses_binomial_coefficients_central_of_ten 30,929
    * and 13,195 and cses_counting_divisors_single_prime_square 21,327 and
    * 9,237; every other row at most 20,784 steps and 9,161 tables. Every row
    * is within the reference reading's 50,000 tables
    * (`ReadingState.defaultTableLimit`).
    */
  val stepLimit: Long = 150000
