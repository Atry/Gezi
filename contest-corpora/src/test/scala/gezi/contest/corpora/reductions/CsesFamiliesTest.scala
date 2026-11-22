package gezi.contest.corpora.reductions

import hedgehog.Gen
import hedgehog.Result
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import gezi.weakhead.Computed
import gezi.weakhead.Mode
import gezi.weakhead.NormalForms
import gezi.weakhead.ReadingState
import snapshot4s.generated.snapshotConfig

/** The answers of the CSES problems by their definitions, computed in the
  * tests at the small sizes of the families' bottom rungs: the reference
  * the families' suites read the programs against while the families'
  * native solvers (`CsesFamily`) are not written. Each
  * follows the problem's statement as its file's header words it, not the
  * best known algorithm: the dice sequences and the coin sequences counted
  * by their running sum, the shortest route by the walks of each length, the
  * rooms by the floor squares that no earlier one reaches, and the power by
  * `BigInt.modPow`.
  */
object CsesDefinitions:

  private val modulus: BigInt = BigInt(CsesFamily.modulus)

  /** The sequences of faces 1 to 6 that sum to n, modulo 10^9 + 7. */
  def diceCombinations(site: DiceCombinations.Site): NativeValue =
    def from(sum: Int): BigInt = if sum == site.sum then 1 else (1 to 6).filter(sum + _ <= site.sum).map(face => from(sum + face)).sum
    NativeValue.natural(from(0) % modulus)

  /** The fewest coins that sum to x, or none. */
  def minimizingCoins(site: MinimizingCoins.Site): NativeValue =
    def from(sum: Int): Option[Int] =
      if sum == site.target then Some(0)
      else site.coins.filter(sum + _ <= site.target).flatMap(coin => from(sum + coin).map(_ + 1)).minOption
    NativeValue.Optional(from(0).map(count => NativeValue.natural(count)))

  /** The fewest computers on a route from 1 to n, or none: the least k
    * below n such that n is among the computers k connections from 1, plus
    * one.
    */
  def messageRoute(site: MessageRoute.Site): NativeValue =
    def next(computers: Set[Int]): Set[Int] =
      site.connections.flatMap((from, to) =>
        (if computers.contains(from) then Vector(to) else Vector.empty) ++ (if computers.contains(to) then Vector(from) else Vector.empty)
      ).toSet
    val walks = Vector.iterate(Set(1), site.computers)(next)
    NativeValue.Optional(walks.indexWhere(_.contains(site.computers)) match
      case -1    => None
      case steps => Some(NativeValue.natural(steps + 1))
    )

  /** The rooms: the floor squares, in reading order, that no earlier floor
    * square reaches by steps over floor.
    */
  def countingRooms(site: CountingRooms.Site): NativeValue =
    val floors = for
      (row, rowIndex) <- site.rows.zipWithIndex
      (floor, columnIndex) <- row.zipWithIndex
      if floor
    yield (rowIndex, columnIndex)
    val floorSet = floors.toSet
    @scala.annotation.tailrec
    def grown(found: Set[(Int, Int)]): Set[(Int, Int)] =
      val next = found ++ found.flatMap((row, column) => Vector((row + 1, column), (row - 1, column), (row, column + 1), (row, column - 1))).filter(floorSet.contains)
      if next == found then found else grown(next)
    def reached(from: (Int, Int)): Set[(Int, Int)] = grown(Set(from))
    val rooms = floors.indices.count(index => !floors.take(index).exists(earlier => reached(earlier).contains(floors(index))))
    NativeValue.natural(rooms)

  /** a^b modulo 10^9 + 7, 0^0 being 1. */
  def exponentiation(site: Exponentiation.Site): NativeValue =
    NativeValue.natural(BigInt(site.base).modPow(site.exponent, modulus))

/** The tests of a CSES family (`CsesFamily`), at the small ranges given,
  * its twins `direct` and `respelled`.
  *
  * Their readings are tabling(weak_head)'s, the reference reading, within
  * `Decoding.limit`, 20,000,000 steps, and `CsesFamilySuite.tableLimit`
  * tables. A reading that stops fails the law. The reference the laws read
  * against is the problem's definition computed in the test
  * (`CsesDefinitions`), not the families' native solvers (`CsesSolutions`),
  * which the solver law checks against it.
  *
  *   - The reference law, whose purpose is to catch a site whose data is
  *     not written as the problem's header gives its encoding (a number
  *     written with another bit order, the coins or the connections in
  *     another shape, a map's rows transposed, computers counted from 0)
  *     and a respelling that changes the function's meaning (a β-expansion
  *     that captures a variable or drops a subterm): on generated seeds and
  *     R of 1 or 2, each twin's repeated program reads the list of the
  *     definition's answers at its sites, so the respelled twin reads what
  *     the direct twin reads, and the twins' programs are two terms.
  *   - The single law, whose purpose is to catch single programs that are
  *     not the sites of the repeated one: each single program of each twin
  *     reads its site's answer.
  *   - The solver law, whose purpose is to catch a native solver
  *     (`CsesSolutions`) that answers otherwise than the
  *     problem's definition, at the bottom rung's sizes: on generated seeds
  *     and R up to the rung's repetitions, `solved` gives the definition's
  *     answers at every site.
  *   - The snapshots, whose purpose is to show in review any change of what
  *     a seed draws, of the program built from it or of the traps drawn for
  *     it: the draws, the trap candidates computed from the definition's
  *     answers (`CsesFamily.trapCandidates`) and the program's text, its
  *     literals written as literals (`ReductionTesting.form`), for the seed
  *     20261031 and R = 3, of each twin of the bottom rung.
  */
abstract class CsesFamilySuite[Site](
    direct: CsesFamily[Site],
    respelled: CsesFamily[Site],
    definition: Site => NativeValue,
    snapshotName: String
) extends GeneratedProperties
    with snapshot4s.munit.SnapshotAssertions:

  private val group = ReductionTesting.group

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => direct.program(group, 0L, 1))

  private def normalForms(program: Term): Either[String, Set[DeBruijnTerm]] =
    NormalForms
      .normalForms(Mode.TablingWeakHead, Reduction.programRoot(program))
      .result(ReadingState.knowingTop(Decoding.limit).copy(tableLimit = CsesFamilySuite.tableLimit)) match
      case Computed.Done(forms, _) => Right(forms.map(Defunctionalization.instructionTerm).toSet)
      case Computed.Stopped(after) => Left(s"the reading stopped: ${after.exhausted}, ${after.budget.spent} steps, ${after.tables.held} tables")

  private def readAs(program: Term, expected: NativeValue): Result = normalForms(program) match
    case Right(forms) => Result.diff(forms, Set(expected.normalForm))(_ == _)
    case Left(stop)   => Result.failure.log(stop)

  private def seeds: Gen[Long] = Gen.long(hedgehog.Range.constant(0L, (1L << 31) - 1))

  property("each twin's program reads the definition's answers", _.copy(testLimit = 2, shrinkLimit = hedgehog.core.ShrinkLimit(2))) {
    for
      seed <- seeds.forAll
      repetitions <- Gen.int(hedgehog.Range.constant(1, 2)).forAll
    yield
      val programs = Vector(direct, respelled).map(_.program(group, seed, repetitions))
      val twoTerms = Result.assert(programs.map(Encodings.deBruijn).distinct.size == 2).log("the twins' programs are two terms")
      val answers = direct.drawnAt(group, seed, repetitions).sites.map(definition)
      val read = programs.map(readAs(_, NativeValue.Elements(answers)))
      Result.all((twoTerms +: read).toList).log(direct.drawnText(group, seed, repetitions))
  }

  property("the native solver gives the definition's answers", _.copy(testLimit = 50)) {
    for
      seed <- seeds.forAll
      repetitions <- Gen.int(hedgehog.Range.constant(1, direct.nominal.repetitions.end)).forAll
    yield
      val drawn = direct.drawnAt(group, seed, repetitions)
      Result.diff(direct.solved(drawn), drawn.sites.map(definition))(_ == _).log(direct.drawnText(group, seed, repetitions))
  }

  property("each single program reads its site's answer", _.copy(testLimit = 1, shrinkLimit = hedgehog.core.ShrinkLimit(2))) {
    for seed <- seeds.forAll
    yield Result.all(Vector(direct, respelled).toList.map(twin =>
      val answers = twin.drawnAt(group, seed, 1).sites.map(definition)
      Result.all(twin.singlePrograms(group, seed, 1).zip(answers).toList.map(readAs.tupled)).log(twin.stem)
    )).log(direct.drawnText(group, seed, 1))
  }

  Vector(direct, respelled).foreach(variant =>
    val spelling = Repetition.spellingName(variant.spelling)
    test(s"the $spelling program of the seed 20261031 and three repetitions") {
      val seed = 20261031L
      val drawn = variant.drawnAt(group, seed, 3)
      val traps = variant.trapCandidates(drawn, drawn.sites.map(definition)).map(Lambdalattice.textWithLiterals(_, Map.empty))
      assertFileSnapshot(
        s"seed $seed, 3 repetitions\n$drawn\ntraps:\n${traps.mkString("\n")}\n=>\n${ReductionTesting.form(variant.program(group, seed, 3))}\n",
        s"repeated/${snapshotName}_$spelling.txt"
      )
    }
  )

/** The table limit of the laws' readings. */
object CsesFamilySuite:

  /** The reference reading's 50,000 tables (`ReadingState.defaultTableLimit`). */
  val tableLimit: Int = ReadingState.defaultTableLimit

class DiceCombinationsReferenceTest
    extends CsesFamilySuite(
      DiceCombinations(Spelling.Direct, DiceCombinations.rungs.head),
      DiceCombinations(Spelling.Respelled, DiceCombinations.rungs.head),
      CsesDefinitions.diceCombinations,
      "cses_dice_combinations"
    )

class MinimizingCoinsReferenceTest
    extends CsesFamilySuite(
      MinimizingCoins(Spelling.Direct, MinimizingCoins.rungs.head),
      MinimizingCoins(Spelling.Respelled, MinimizingCoins.rungs.head),
      CsesDefinitions.minimizingCoins,
      "cses_minimizing_coins"
    )

class MessageRouteReferenceTest
    extends CsesFamilySuite(
      MessageRoute(Spelling.Direct, MessageRoute.rungs.head),
      MessageRoute(Spelling.Respelled, MessageRoute.rungs.head),
      CsesDefinitions.messageRoute,
      "cses_message_route"
    )

class CountingRoomsReferenceTest
    extends CsesFamilySuite(
      CountingRooms(Spelling.Direct, CountingRooms.rungs.head),
      CountingRooms(Spelling.Respelled, CountingRooms.rungs.head),
      CsesDefinitions.countingRooms,
      "cses_counting_rooms"
    )

class ExponentiationReferenceTest
    extends CsesFamilySuite(
      Exponentiation(Spelling.Direct, Exponentiation.rungs.head),
      Exponentiation(Spelling.Respelled, Exponentiation.rungs.head),
      CsesDefinitions.exponentiation,
      "cses_exponentiation"
    )
