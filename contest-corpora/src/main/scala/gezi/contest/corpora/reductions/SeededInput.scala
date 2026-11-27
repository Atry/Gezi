package gezi.contest.corpora.reductions

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.ir.{Configured, NoFacts}

/** The corpora are read under no facts. */
private given seededInputNoFacts: NoFacts.type = NoFacts

/** The seeded inputs of the CSES families' top rungs: a site's data written
  * into its program as a call of a generator of
  * `problems/cses/common/seeded_input` on a seed and sizes
  * (`RungInput.Seeded`), so that the program's size does not grow with its
  * input, and the same data generated natively here, for the native
  * solutions (`solved`) and the traps (`wrongAnswers`).
  *
  * Every generator draws from one stream of Park–Miller states, s_0 the
  * seed and s_k = `CsesSolutions.nextSeededState` s_(k-1), the k-th draw
  * from [low, high] being low + s_k mod (high − low + 1), each generator's
  * draws in the order its file's header names them. Each mirror here makes
  * the draws in that order. `SeededInputLawTest` checks every generator's
  * program against its mirror on generated arguments.
  */
object SeededInput:

  /** A stream of the generators' states. */
  final case class Stream(state: Long):

    /** The next draw from [low, high], and the stream after it. */
    def drawn(low: Int, high: Int): (Int, Stream) =
      require(low <= high, s"no draw from $low to $high")
      val next = CsesSolutions.nextSeededState(state)
      (Math.toIntExact(low + next % (high.toLong - low + 1)), Stream(next))

  /** `count` values of the draw, in the order drawn. */
  def drawnValues[Drawn](count: Int, stream: Stream)(draw: Stream => (Drawn, Stream)): (Vector[Drawn], Stream) =
    (1 to count).foldLeft((Vector.empty[Drawn], stream)) { case ((found, current), _) =>
      val (value, after) = draw(current)
      (found :+ value, after)
    }

  /** A call of a generator, and the data it generates. */
  trait Generator[+Data]:

    /** The data, as the program computes them. */
    def data: Data

    /** The call, the program's argument. */
    def argument(problems: CsesProblems): ProblemTerm

  /** A site's datum: written out, or generated from a seed. Two seeded data
    * are equal by their generators' seeds and sizes, so that drawing
    * distinct sites does not generate their data.
    */
  enum Input[+Data]:
    case Written(written: Data)
    case Seeded(generator: Generator[Data])

    /** The datum. */
    def data: Data = this match
      case Written(written) => written
      case Seeded(generator) => generator.data

    /** The argument: the datum written by `write`, or the generator's call. */
    def argument(problems: CsesProblems, write: Data => ProblemTerm): ProblemTerm = this match
      case Written(written) => write(written)
      case Seeded(generator) => generator.argument(problems)

    /** The datum as the written site printed it, or the generator. */
    def described(written: Data => String): String = this match
      case Written(data)     => written(data)
      case Seeded(generator) => generator.toString

  private def call(generator: Configured[NoFacts.type], arguments: Vector[Int]): ProblemTerm =
    applied(Term.closed(generator), arguments.map(CsesEncodings.natural(_)))

  /** `seeded_numbers seed count low high`: count draws from [low, high]. */
  final case class Numbers(seed: Int, count: Int, low: Int, high: Int) extends Generator[Vector[Int]]:
    lazy val data: Vector[Int] = CsesSolutions.seededNumbers(seed.toLong, count, low.toLong, high.toLong).toVector.map(Math.toIntExact)
    def argument(problems: CsesProblems): ProblemTerm = call(problems.seededNumbers, Vector(seed, count, low, high))

  /** `seeded_pairs seed count low high`: count pairs, x then y drawn from [low, high]. */
  final case class Pairs(seed: Int, count: Int, low: Int, high: Int) extends Generator[Vector[(Int, Int)]]:
    lazy val data: Vector[(Int, Int)] =
      drawnValues(count, Stream(seed.toLong))(stream =>
        val (x, afterX) = stream.drawn(low, high)
        val (y, afterY) = afterX.drawn(low, high)
        ((x, y), afterY)
      )._1
    def argument(problems: CsesProblems): ProblemTerm = call(problems.seededPairs, Vector(seed, count, low, high))

  /** `seeded_triples seed count low high cost_low cost_high`: count triples,
    * x and y drawn from [low, high], then c from [cost_low, cost_high].
    */
  final case class Triples(seed: Int, count: Int, low: Int, high: Int, costLow: Int, costHigh: Int) extends Generator[Vector[(Int, Int, Long)]]:
    lazy val data: Vector[(Int, Int, Long)] = triples(Stream(seed.toLong), count, low, high, costLow, costHigh)._1
    def argument(problems: CsesProblems): ProblemTerm = call(problems.seededTriples, Vector(seed, count, low, high, costLow, costHigh))

  private def triples(stream: Stream, count: Int, low: Int, high: Int, costLow: Int, costHigh: Int): (Vector[(Int, Int, Long)], Stream) =
    drawnValues(count, stream)(current =>
      val (x, afterX) = current.drawn(low, high)
      val (y, afterY) = afterX.drawn(low, high)
      val (cost, afterCost) = afterY.drawn(costLow, costHigh)
      ((x, y, cost.toLong), afterCost)
    )

  /** Which corner square of a grid a site makes a trap. */
  enum Corner:

    /** Neither. */
    case Neither

    /** The first square of the first row (`trapped_first`). */
    case First

    /** The last square of the last row (`trapped_last`). */
    case Last

  /** `seeded_grid seed rows columns odds`, its corner made a trap by
    * `trapped_first` or `trapped_last`: rows of columns squares each, row by
    * row, each a draw d from [1, odds], true when d is not 1.
    */
  final case class Grid(seed: Int, rows: Int, columns: Int, odds: Int, corner: Corner) extends Generator[Vector[Vector[Boolean]]]:
    lazy val data: Vector[Vector[Boolean]] =
      val drawn = drawnValues(rows, Stream(seed.toLong))(beforeRow =>
        drawnValues(columns, beforeRow)(current =>
          val (square, after) = current.drawn(1, odds)
          (square != 1, after)
        )
      )._1
      corner match
        case Corner.Neither => drawn
        case Corner.First   => drawn.headOption.filter(_.nonEmpty).fold(drawn)(row => drawn.updated(0, row.updated(0, false)))
        case Corner.Last    => drawn.lastOption.filter(_.nonEmpty).fold(drawn)(row => drawn.updated(drawn.size - 1, row.updated(row.size - 1, false)))
    def argument(problems: CsesProblems): ProblemTerm =
      val grid = call(problems.seededGrid, Vector(seed, rows, columns, odds))
      corner match
        case Corner.Neither => grid
        case Corner.First   => applied(Term.closed(problems.trappedFirst), Vector(grid))
        case Corner.Last    => applied(Term.closed(problems.trappedLast), Vector(grid))

  /** `seeded_connections seed count n`, n ≥ 2: count pairs a, b, a drawn
    * from [1, n], then d from [1, n − 1], and b = 1 + ((a − 1 + d) mod n), so
    * that b is not a.
    */
  final case class Connections(seed: Int, count: Int, computers: Int) extends Generator[Vector[(Int, Int)]]:
    require(computers >= 2, s"no connection between distinct computers of $computers")
    lazy val data: Vector[(Int, Int)] =
      drawnValues(count, Stream(seed.toLong))(stream =>
        val (from, afterFrom) = stream.drawn(1, computers)
        val (distance, afterDistance) = afterFrom.drawn(1, computers - 1)
        ((from, 1 + (from - 1 + distance) % computers), afterDistance)
      )._1
    def argument(problems: CsesProblems): ProblemTerm = call(problems.seededConnections, Vector(seed, count, computers))

  /** `append (seeded_tree tree_seed n cost_low cost_high) (seeded_triples
    * flight_seed extra 1 n cost_low cost_high)`: a flight to each city k from
    * 2 to n from a parent p drawn from [1, k − 1], then its cost drawn, so
    * that every city is reached from city 1, then `extra` flights drawn as
    * `Triples` draws them.
    */
  final case class Flights(treeSeed: Int, flightSeed: Int, cities: Int, extra: Int, costLow: Int, costHigh: Int)
      extends Generator[Vector[(Int, Int, Long)]]:
    lazy val data: Vector[(Int, Int, Long)] =
      tree(treeSeed, cities, costLow, costHigh) ++ triples(Stream(flightSeed.toLong), extra, 1, cities, costLow, costHigh)._1
    def argument(problems: CsesProblems): ProblemTerm =
      applied(
        Term.closed(problems.append),
        Vector(
          call(problems.seededTree, Vector(treeSeed, cities, costLow, costHigh)),
          call(problems.seededTriples, Vector(flightSeed, extra, 1, cities, costLow, costHigh))
        )
      )

  /** `seeded_tree seed n cost_low cost_high`: for each city k from 2 to n a
    * parent p drawn from [1, k − 1], then a cost drawn, the edge (p, k, cost).
    */
  private def tree(seed: Int, cities: Int, costLow: Int, costHigh: Int): Vector[(Int, Int, Long)] =
    (2 to cities).foldLeft((Vector.empty[(Int, Int, Long)], Stream(seed.toLong))) { case ((found, current), city) =>
      val (parent, afterParent) = current.drawn(1, city - 1)
      val (cost, afterCost) = afterParent.drawn(costLow, costHigh)
      (found :+ (parent, city, cost.toLong), afterCost)
    }._1

  /** `seeded_binomial_queries seed count high`: count pairs a, b, x then y
    * drawn from [0, high], a the larger and b the smaller.
    */
  final case class BinomialQueries(seed: Int, count: Int, high: Int) extends Generator[Vector[(Int, Int)]]:
    lazy val data: Vector[(Int, Int)] =
      drawnValues(count, Stream(seed.toLong))(stream =>
        val (x, afterX) = stream.drawn(0, high)
        val (y, afterY) = afterX.drawn(0, high)
        ((math.max(x, y), math.min(x, y)), afterY)
      )._1
    def argument(problems: CsesProblems): ProblemTerm = call(problems.seededBinomialQueries, Vector(seed, count, high))

  // The shapes of `problems/cses/common/seeded_shapes`, each built on a generator above and drawing as it does.

  /** `seeded_ranges seed count low high`: the pairs of `Pairs`, each as
    * (smaller, larger).
    */
  final case class Ranges(seed: Int, count: Int, low: Int, high: Int) extends Generator[Vector[(Int, Int)]]:
    lazy val data: Vector[(Int, Int)] = Pairs(seed, count, low, high).data.map((x, y) => (math.min(x, y), math.max(x, y)))
    def argument(problems: CsesProblems): ProblemTerm = call(problems.seededRanges, Vector(seed, count, low, high))

  /** `seeded_ordered_connections seed count n`, n ≥ 2: the pairs of
    * `Connections`, each as (smaller, larger), so that a flight never leads
    * back.
    */
  final case class OrderedConnections(seed: Int, count: Int, computers: Int) extends Generator[Vector[(Int, Int)]]:
    lazy val data: Vector[(Int, Int)] = Connections(seed, count, computers).data.map((a, b) => (math.min(a, b), math.max(a, b)))
    def argument(problems: CsesProblems): ProblemTerm = call(problems.seededOrderedConnections, Vector(seed, count, computers))

  /** `seeded_tree_edges seed n`: the edges of `seeded_tree seed n 1 1`
    * without their costs, each cost still drawn.
    */
  final case class TreeEdges(seed: Int, nodes: Int) extends Generator[Vector[(Int, Int)]]:
    lazy val data: Vector[(Int, Int)] = tree(seed, nodes, 1, 1).map((parent, node, _) => (parent, node))
    def argument(problems: CsesProblems): ProblemTerm = call(problems.seededTreeEdges, Vector(seed, nodes))

  /** `seeded_walk seed count bound`, bound ≥ 1: from the pairs d, h of
    * `Pairs(seed, count, 0, 2)`, v_0 = 1 and v_k = min(bound, max(1,
    * v_(k−1) + d − 1)), the k-th entry 0 when h = 0 and v_k otherwise.
    */
  final case class Walk(seed: Int, count: Int, bound: Int) extends Generator[Vector[Int]]:
    require(bound >= 1, s"no walk within $bound")
    lazy val data: Vector[Int] =
      Pairs(seed, count, 0, 2).data.foldLeft((Vector.empty[Int], 1)) { case ((found, before), (step, shown)) =>
        val value = math.min(bound, math.max(1, before + step - 1))
        (found :+ (if shown == 0 then 0 else value), value)
      }._1
    def argument(problems: CsesProblems): ProblemTerm = call(problems.seededWalk, Vector(seed, count, bound))

  /** `seeded_rotation seed n`, n ≥ 1: from the one pair missing, start of
    * `Pairs(seed, 1, 1, n)`, the numbers 1 + ((start − 1 + t) mod n) for t
    * from 0 to n − 1, without missing.
    */
  final case class Rotation(seed: Int, count: Int) extends Generator[Vector[Int]]:
    require(count >= 1, s"no rotation of $count numbers")
    lazy val data: Vector[Int] =
      val (missing, start) = Pairs(seed, 1, 1, count).data match
        case Vector(drawn) => drawn
        case other         => throw IllegalStateException(s"one pair drawn, not $other")
      (0 until count).toVector.map(offset => 1 + (start - 1 + offset) % count).filter(_ != missing)
    def argument(problems: CsesProblems): ProblemTerm = call(problems.seededRotation, Vector(seed, count))
