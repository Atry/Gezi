package gezi.contest.modules.solo.extraction

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.extraction.Entry
import gezi.extraction.Shape
import gezi.extraction.StatelessCostModel
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Apply
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.saturation.StopSignal

private given rememberingCostModelLawTestNoFacts: NoFacts.type = NoFacts

/** The laws of `RememberingCostModel` over a stateless model whose cost of
  * an application is a weight of its node plus its children's costs, read
  * by parity. On a generated sequence of calls, each a node among a few, two
  * children's options drawn from a few entries and either call, the memo
  * threaded from call to call, the arguments drawn from a few so that they
  * repeat, and each call's options drawn from one of two pools of equal
  * entries that are different objects: (1) every call gives the candidates
  * the stateless model gives for its arguments, and every candidate's child
  * entries are the objects of this call's options, and (2) under a requested stop
  * no call is remembered. Their purpose is to catch a memo whose key misses
  * an input (the node, a child's options, or which call it is), so that a
  * call is answered with another call's candidates; a memo that answers a
  * call with the candidates of an equal call over other objects, which the
  * extraction's pass at cost would drop since it finds a child entry by
  * reference; and a memo that keeps a
  * call made once a stop was requested, whose candidates the contract of
  * `gezi.extraction.CostModel.Memo` leaves out.
  */
class RememberingCostModelLawTest extends GeneratedProperties:

  /** The cost of an application: its node's weight plus its children's
    * costs; two costs of one parity are of one reading.
    */
  private final class Weighted(weights: Vector[Int]) extends StatelessCostModel[Int]:
    def cost(shape: Shape, childCosts: Vector[Int]): Int = shape match
      case Shape.Node(node, _) => weights(node % weights.size) + childCosts.sum
      case _                   => 1 + childCosts.sum
    val ordering: Ordering[Int] = Ordering.Int
    override def sameReading(left: Int, right: Int): Boolean = left % 2 == right % 2
    def pricedChildren(shape: Shape): Vector[Boolean] = shape.children.map(_ => true)

  /** A leaf entry of the cost given: a name, which has no children. */
  private def leaf(cost: Int, name: Int): Entry[Int] = Entry(cost, Shape.Name(NoFacts.opaque(s"leaf$name")), Vector.empty)

  /** A call: the node of the application, its two children's options as
    * indices into the pool of entries, and whether it is the least call.
    */
  private final case class Call(node: Int, functionOptions: Vector[Int], argumentOptions: Vector[Int], least: Boolean, copied: Boolean)

  /** A node and its two children's options. */
  private val argumentTuple: Gen[(Int, Vector[Int], Vector[Int])] =
    val options = Gen.int(Range.linear(0, 4)).list(Range.linear(1, 3)).map(_.toVector)
    for
      node <- Gen.int(Range.linear(0, 2))
      functionOptions <- options
      argumentOptions <- options
    yield (node, functionOptions, argumentOptions)

  /** A sequence of calls whose arguments are drawn from one to three
    * argument tuples, so that calls repeat their arguments, with either call
    * each time.
    */
  private val calls: Gen[List[Call]] =
    for
      tuples <- argumentTuple.list(Range.linear(1, 3)).map(_.toVector)
      picks <- (for
        position <- Gen.int(Range.linear(0, 2))
        least <- Gen.boolean
        copied <- Gen.boolean
      yield (position, least, copied)).list(Range.linear(0, 30))
    yield picks.map((position, least, copied) =>
      val (node, functionOptions, argumentOptions) = tuples(position % tuples.size)
      Call(node, functionOptions, argumentOptions, least, copied)
    )

  /** The entries the options are drawn from, and a second pool of entries
    * equal to them that are other objects, so that two calls may have equal
    * options over different objects.
    */
  private val pool: Vector[Entry[Int]] = Vector.tabulate(5)(position => leaf(position, 10 + position))
  private val copies: Vector[Entry[Int]] = Vector.tabulate(5)(position => leaf(position, 10 + position))

  private def arguments(call: Call): (Shape, Vector[Vector[Entry[Int]]]) =
    val drawn = if call.copied then copies else pool
    (Shape.Node(call.node, Apply(0, 1)), Vector(call.functionOptions.map(drawn), call.argumentOptions.map(drawn)))

  stoppableProperty("every remembered call gives the stateless model's candidates for its arguments") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for
      weights <- Gen.int(Range.linear(0, 3)).list(Range.singleton(3)).map(_.toVector).forAll
      drawn <- calls.forAll
      (node, functionOptions, argumentOptions) <- argumentTuple.forAll
      leastCopied <- Gen.boolean.forAll
      allCopied <- Gen.boolean.forAll
    yield
      // The case the law must reach, by construction every iteration: one
      // node and options called with both calls, after the drawn sequence.
      val sequence = drawn ++ List(
        Call(node, functionOptions, argumentOptions, least = true, copied = leastCopied),
        Call(node, functionOptions, argumentOptions, least = false, copied = allCopied)
      )
      val base = Weighted(weights)
      val model = RememberingCostModel(base, stop)
      val (results, _) = sequence.foldLeft((Vector.empty[Result], model.emptyMemo)) { case ((found, memo), call) =>
        val (shape, options) = arguments(call)
        val (answered, after) =
          if call.least then model.memoizedLeastCandidates(shape, options, memo) else model.memoizedCandidates(shape, options, memo)
        val expected = if call.least then base.leastCandidates(shape, options) else base.candidates(shape, options)
        val ownObjects = answered.forall(candidate =>
          candidate.childEntries.lazyZip(options).forall((child, childOptions) => childOptions.exists(_ eq child))
        )
        (found :+ Result.diff(answered, expected)(_ == _).and(Result.assert(ownObjects)).log(s"call $call"), after)
      }
      Result.all(results.toList)
  }

  property("no call is remembered once a stop is requested") {
    for
      weights <- Gen.int(Range.linear(0, 3)).list(Range.singleton(3)).map(_.toVector).forAll
      sequence <- calls.forAll
    yield
      val model = RememberingCostModel(Weighted(weights), StopSignal.completedWith(scala.concurrent.Future.successful(())))
      val memo = sequence.foldLeft(model.emptyMemo) { (memo, call) =>
        val (shape, options) = arguments(call)
        (if call.least then model.memoizedLeastCandidates(shape, options, memo) else model.memoizedCandidates(shape, options, memo))._2
      }
      Result.assert(memo.isEmpty).log(s"remembered under a stop: ${memo.keys}")
  }
