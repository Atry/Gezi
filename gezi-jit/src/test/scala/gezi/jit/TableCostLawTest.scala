package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.jit.JitTesting.*
import gezi.weakhead.Bounded
import gezi.weakhead.EvaluatorTesting
import gezi.weakhead.Mode
import gezi.weakhead.NoJitState
import gezi.frontend.DeBruijnTerm
import gezi.ir.Code
import gezi.ir.Configured

/** The law of the instance table's miss count (`TableCost.missesOpened`):
  * on a random closed term with choices and parallels whose reading under
  * the table finishes, every code's misses are at least its entries, since a
  * miss is counted where it enters the table and an entry when its heads end
  * with the table complete. Its purpose is to catch a miss counted in the
  * wrong place: after the heads were pulled, on a hit, or on one branch of
  * the lookup and not the other, which a policy that judges a code by its
  * open misses (`missesOpened - entries`) would read as fewer open tables
  * than there are. Every iteration checks the law also on
  * `(λx. x x) (λy. y)`, whose β step reads the body `x x` as an instance of
  * its code under the filling `λy. y`, which the empty table misses, and
  * which finishes at `λy. y`; that it finished with a miss is asserted, so
  * that the law always has a reading to check.
  */
class TableCostLawTest extends GeneratedProperties:

  private val encoding = JitTesting.noFactsEncoding

  private given encoding.type = encoding

  private val configuration: JitConfiguration[encoding.type] =
    JitConfiguration[encoding.type](
      encoding,
      JitConfiguration.defaultBudget,
      PredicatePerCode,
      ClosureBackend,
      DispatchMode.NoDispatch,
      instanceTable = true,
      storageAccess = gezi.ir.StorageAccess.granted()
    )

  private val limit: Long = 200000

  /** A drawn term and its reading under the table. */
  private val readings =
    for
      seed <- Gen.long(Range.linear(0L, Long.MaxValue))
      size <- Gen.int(Range.linear(4, 24))
    yield
      val term = EvaluatorTesting.draws(1, seed)(random => randomLatticeApplication(size, random)) match
        case Vector(only) => only
        case other        => throw IllegalStateException(s"one term drawn, not ${other.size}")
      (term, readUnderTheTable(term))

  /** The term's reading under the table. */
  private def readUnderTheTable(term: DeBruijnTerm): Spent[encoding.type, Vector[Configured[encoding.type]]] =
    val value = valuesOf(Vector(instructionOf(term))) match
      case Vector(only) => only
      case other        => throw IllegalStateException(s"one value per term, not ${other.size}")
    NativesTesting.normalFormsSpent(Jit(configuration), value, limit, NoJitState)

  /** `(λx. x x) (λy. y)`: the instance of `x x` under `λy. y` is missed. */
  private val selfApplied: DeBruijnTerm =
    DeBruijnTerm.Apply(
      DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), DeBruijnTerm.Variable(0))),
      DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0))
    )

  /** The law on one reading. */
  private def missesAtLeastEntries(term: DeBruijnTerm, read: Spent[encoding.type, Vector[Configured[encoding.type]]]): Result =
    finishedCosts(read) match
      case Some(costs) =>
        val fewer = costs.toVector.filter((_, cost) => cost.missesOpened < cost.entries)
        Result.assert(fewer.isEmpty).log(s"term $term, codes with fewer misses than entries: $fewer")
      case None => Result.success

  /** The codes' costs of a reading that finished, none for another. */
  private def finishedCosts(read: Spent[encoding.type, Vector[Configured[encoding.type]]]): Option[Map[Code, TableCost]] =
    (read.outcome, read.jitState) match
      case (Bounded.Finished(_), run: JitRunState[?]) => Some(run.tableCosts)
      case _                                      => None

  property("every code's misses that entered the instance table are at least its entries, wherever the reading finishes") {
    for (term, read) <- readings.forAll
    yield
      val selfRead = readUnderTheTable(selfApplied)
      missesAtLeastEntries(term, read)
        .and(missesAtLeastEntries(selfApplied, selfRead))
        .and(
          Result
            .assert(finishedCosts(selfRead).exists(_.values.exists(_.missesOpened > 0)))
            .log(s"(λx. x x) (λy. y) did not finish with a miss: ${selfRead.outcome}")
        )
  }
