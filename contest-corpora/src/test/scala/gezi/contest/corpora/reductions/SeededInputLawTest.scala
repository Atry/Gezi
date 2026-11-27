package gezi.contest.corpora.reductions

import hedgehog.Gen
import hedgehog.Result
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import gezi.weakhead.Computed
import gezi.weakhead.Mode
import gezi.weakhead.NormalForms
import gezi.weakhead.ReadingState

/** The law that each generator of the seeded top rungs and its native mirror
  * agree: on generated seeds and small sizes, the normal forms
  * tabling(weak_head) reads of a generator's call
  * (`problems/cses/common/seeded_input`) are those of the data its mirror
  * (`SeededInput`) generates, written out as a rung below the top writes its
  * data. Its purpose is to catch the two departing, which would give a seeded
  * top rung's points references and traps computed on another input than the
  * program's: the top rungs are left out of the families' own laws
  * (`CsesFamilies.atConstraints`), so this law is what ties their native
  * answers to their programs.
  */
class SeededInputLawTest extends GeneratedProperties:

  given gezi.ir.NoFacts.type = gezi.ir.NoFacts

  private val group = ReductionTesting.group
  // Measured 2026-11-22 on 4 CPUs (contest.slice, CPUs 4 to 7, nice 10), the 1-minute load about 8 to 9: the suite
  // took 10.7, 10.9 and 11.6 s over three runs, its 24 cases of up to three draws each over the fifteen generators;
  // the bound is 1.5 times the slowest rounded up to 5 s. The suite cannot meet the 3 s default: a draw is a state
  // step of 31-bit modular arithmetic on the library's binary naturals, about 25,000 tables under the reference
  // reading (`SeededInputLawTest.tableLimit`), and a case needs two draws to check that a mirror chains the states.
  override val munitTimeout = scala.concurrent.duration.Duration(20, "s")

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(
      _ => group.cses.seededInput,
      _ => group.cses.seededShapes,
      _ => group.cses.append
    )

  private def normalForms(program: Term): Either[String, Set[
    gezi.frontend.DeBruijnTermOf[gezi.ir.Configured[gezi.ir.NoFacts.type]]
  ]] =
    NormalForms
      .normalForms(Mode.TablingWeakHead, Reduction.programRoot(program))
      .result(
        ReadingState
          .knowingTop(
            Decoding.limit,
            gezi.weakhead.ReadingConfiguration.withoutFacts
          )
          .copy(tableLimit = SeededInputLawTest.tableLimit)
      ) match
      case Computed.Done(forms, _) =>
        Right(
          forms
            .map(form =>
              Defunctionalization.instructionTerm[gezi.ir.NoFacts.type](form)
            )
            .toSet
        )
      case Computed.Stopped(after) =>
        Left(
          s"the reading stopped: ${after.exhausted}, ${after.budget.spent} steps, ${after.tables.held} tables"
        )

  /** A generator with its data written out as a written rung writes them. */
  private final case class Case(
      generator: SeededInput.Generator[Any],
      written: Term
  )

  private def pairs(values: Vector[(Int, Int)]): Term =
    val naturals = CsesEncodings.naturals(
      values.flatMap((left, right) => Vector(left, right))
    )
    CsesEncodings.list(
      values.map((left, right) =>
        CsesEncodings.pair(naturals(left), naturals(right))
      )
    )

  private def triples(values: Vector[(Int, Int, Long)]): Term =
    val naturals = CsesEncodings.naturals(
      values.flatMap((from, to, cost) =>
        Vector(from, to, Math.toIntExact(cost))
      )
    )
    CsesEncodings.list(
      values.map((from, to, cost) =>
        CsesEncodings.triple(naturals, from, to, Math.toIntExact(cost))
      )
    )

  private val seeds: Gen[Int] =
    Gen.int(hedgehog.Range.constant(1, Int.MaxValue - 1))

  private def small(low: Int, high: Int): Gen[Int] =
    Gen.int(hedgehog.Range.constant(low, high))

  // Each case makes at most three draws (`SeededInputLawTest.tableLimit`): two already check that a mirror chains the
  // states and draws in the generator's order.
  private val cases: Gen[Case] = Gen.choice1(
    for
      seed <- seeds; count <- small(0, 3); low <- small(0, 20);
      width <- small(0, 20)
    yield
      val generator = SeededInput.Numbers(seed, count, low, low + width)
      Case(generator, CsesFamily.writtenNumbers(generator.data))
    ,
    for
      seed <- seeds; count <- small(0, 1); low <- small(0, 5);
      width <- small(0, 5)
    yield
      val generator = SeededInput.Pairs(seed, count, low, low + width)
      Case(generator, pairs(generator.data))
    ,
    for
      seed <- seeds; count <- small(0, 1); high <- small(1, 4);
      costLow <- small(1, 3); costWidth <- small(0, 3)
    yield
      val generator =
        SeededInput.Triples(seed, count, 1, high, costLow, costLow + costWidth)
      Case(generator, triples(generator.data))
    ,
    for
      seed <- seeds
      (rows, columns) <- Gen
        .element1((0, 0), (1, 0), (0, 2), (1, 1), (1, 3), (2, 1), (3, 1))
      odds <- small(1, 3)
      corner <- Gen.element1(
        SeededInput.Corner.Neither,
        SeededInput.Corner.First,
        SeededInput.Corner.Last
      )
    yield
      val generator = SeededInput.Grid(seed, rows, columns, odds, corner)
      Case(generator, CsesFamily.writtenGrid(generator.data))
    ,
    for seed <- seeds; count <- small(0, 1); computers <- small(2, 4)
    yield
      val generator = SeededInput.Connections(seed, count, computers)
      Case(generator, pairs(generator.data))
    ,
    for
      treeSeed <- seeds
      flightSeed <- seeds
      (cities, extra) <- Gen.element1((1, 0), (1, 1), (2, 0))
      costLow <- small(1, 2)
      costWidth <- small(0, 2)
    yield
      val generator = SeededInput.Flights(
        treeSeed,
        flightSeed,
        cities,
        extra,
        costLow,
        costLow + costWidth
      )
      Case(generator, triples(generator.data))
    ,
    for seed <- seeds; count <- small(0, 1); high <- small(0, 6)
    yield
      val generator = SeededInput.BinomialQueries(seed, count, high)
      Case(generator, pairs(generator.data))
    ,
    for
      seed <- seeds; count <- small(0, 1); low <- small(0, 5);
      width <- small(0, 5)
    yield
      val generator = SeededInput.Ranges(seed, count, low, low + width)
      Case(generator, pairs(generator.data))
    ,
    for seed <- seeds; count <- small(0, 1); computers <- small(2, 4)
    yield
      val generator = SeededInput.OrderedConnections(seed, count, computers)
      Case(generator, pairs(generator.data))
    ,
    for seed <- seeds; nodes <- small(1, 2)
    yield
      val generator = SeededInput.TreeEdges(seed, nodes)
      Case(generator, pairs(generator.data))
    ,
    for seed <- seeds; count <- small(0, 1); bound <- small(1, 3)
    yield
      val generator = SeededInput.Walk(seed, count, bound)
      Case(generator, CsesFamily.writtenNumbers(generator.data))
    ,
    for seed <- seeds; count <- small(1, 3)
    yield
      val generator = SeededInput.Rotation(seed, count)
      Case(generator, CsesFamily.writtenNumbers(generator.data))
  )

  property(
    "each generator's call reads the data its native mirror generates",
    _.copy(testLimit = 24)
  ) {
    for found <- cases.forAll
    yield (
      normalForms(found.generator.argument(group.cses)),
      normalForms(found.written)
    ) match
      case (Right(generated), Right(written)) =>
        Result.diff(generated, written)(_ == _).log(found.generator.toString)
      case (generated, written) =>
        Result.failure.log(
          s"${found.generator}: generated $generated, written $written"
        )
  }

/** The table limit of the law's readings. */
object SeededInputLawTest:

  /** 100,000 tables: a draw reads one state step, 48271 · s mod (2^31 − 1) on
    * the library's binary naturals, under tabling(weak_head). MEASURED
    * 2026-11-22 by a scratch test of `seeded_numbers seed count 0 20` (CPUs 0,
    * 1, 4 and 5 of contest.slice, nice 10, the 1-minute load about 10): one
    * draw took 6,284 to 25,886 tables (seeds 7, 12,345 and 2,147,480,000, the
    * larger states the costlier), three 42,204 to 71,382 and four 66,106 to
    * 95,529, about linear; a case makes at most three, so the reference
    * reading's 50,000 (`CsesFamilySuite.tableLimit`) stopped two draws of a
    * large state.
    */
  val tableLimit: Int = 100000
