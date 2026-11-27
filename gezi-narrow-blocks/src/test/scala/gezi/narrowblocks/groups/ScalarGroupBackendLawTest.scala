package gezi.narrowblocks.groups

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import gezi.generatedinputs.GeneratedProperties
import gezi.jit.StaticBlockMethod
import gezi.jit.StaticBlockResult

/** The static methods the laws call: a sum, and a half that has no answer
  * on an odd natural.
  */
object ScalarGroupBackendLawMethods:

  def summed(left: BigInteger, right: BigInteger): BigInteger = left.add(right)

  def halved(value: BigInteger): BigInteger = if value.testBit(0) then null else value.shiftRight(1)

private object SummedMethod extends StaticBlockMethod:
  val className: String = classOf[ScalarGroupBackendLawMethods.type].getName.stripSuffix("$")
  val methodName: String = "summed"

private object HalvedMethod extends StaticBlockMethod:
  val className: String = classOf[ScalarGroupBackendLawMethods.type].getName.stripSuffix("$")
  val methodName: String = "halved"
  override val result: StaticBlockResult = StaticBlockResult.NaturalOrNoAnswer

/** The laws of the JVM scalar group backend (`ScalarGroupBackend`), each a
  * statement about rows checked on generated tables, against the backend's
  * own work on columns: the product's rows are the pairs of rows, the left's
  * outer; a concatenation's are the left's then the right's; `unique` gives
  * the distinct rows in the canonical order and is idempotent; `selected`
  * splits the rows by the mask; `called` gives each row with the method's
  * value appended, a row on which a `NaturalOrNoAnswer` method has no answer
  * dropped. Their purpose is to catch columns misaligned by an operation,
  * a lost or repeated row, and a no answer taken for a value.
  */
class ScalarGroupBackendLawTest extends GeneratedProperties:

  private val backend = ScalarGroupBackend

  private val natural: Gen[GroupValue] = Gen.long(Range.linear(0L, 20L)).map(value => GroupValue.Natural(BigInteger.valueOf(value)))

  private val truth: Gen[GroupValue] = Gen.boolean.map(GroupValue.Truth(_))

  /** A table of the given numbers of columns of naturals and of truth
    * values, the truths last, of up to five rows.
    */
  private def generatedTable(naturals: Int, truths: Int): Gen[GroupTable[backend.Column]] =
    for
      rowCount <- Gen.int(Range.linear(0, 5))
      naturalColumns <- natural.list(Range.singleton(rowCount)).list(Range.singleton(naturals))
      truthColumns <- truth.list(Range.singleton(rowCount)).list(Range.singleton(truths))
    yield backend.table((naturalColumns ++ truthColumns).map(column => backend.column(column.toVector)).toVector, rowCount)

  property("the product's rows are the pairs of rows, the left's outer") {
    for
      left <- generatedTable(2, 0).forAll
      right <- generatedTable(1, 1).forAll
    yield Result.diff(
      backend.rows(backend.product(left, right)),
      for
        first <- backend.rows(left)
        second <- backend.rows(right)
      yield first ++ second
    )(_ == _)
  }

  property("a concatenation's rows are the left's then the right's") {
    for
      left <- generatedTable(2, 1).forAll
      right <- generatedTable(2, 1).forAll
    yield Result.diff(backend.rows(backend.concatenated(left, right)), backend.rows(left) ++ backend.rows(right))(_ == _)
  }

  property("unique gives the distinct rows in the canonical order, and is idempotent") {
    for table <- generatedTable(2, 1).forAll
    yield
      val once = backend.unique(table)
      Result
        .diff(backend.rows(once), backend.rows(table).distinct.sorted(using GroupBackend.rowOrdering))(_ == _)
        .and(Result.diff(backend.rows(backend.unique(once)), backend.rows(once))(_ == _))
  }

  property("selected splits the rows by the mask") {
    for table <- generatedTable(2, 1).forAll
    yield
      val (chosen, others) = backend.selected(table, 2)
      val (expectedChosen, expectedOthers) = backend.rows(table).partition(_(2) == GroupValue.Truth(true))
      Result.diff((backend.rows(chosen), backend.rows(others)), (expectedChosen, expectedOthers))(_ == _)
  }

  property("called appends the method's value to each row, and drops a row with no answer") {
    for table <- generatedTable(2, 0).forAll
    yield
      def natural(value: GroupValue): BigInteger = value match
        case GroupValue.Natural(number) => number
        case other                      => throw IllegalStateException(s"a natural column holds $other")
      val summed = backend.rows(backend.called(table, GroupMethod(gezi.jit.NativeName.Function("scalar_group_backend_law_summed"), SummedMethod, Vector(GroupPlace.Natural, GroupPlace.Natural)), Vector(0, 1)))
      val halved = backend.rows(backend.called(table, GroupMethod(gezi.jit.NativeName.Function("scalar_group_backend_law_halved"), HalvedMethod, Vector(GroupPlace.Natural)), Vector(1)))
      Result
        .diff(summed, backend.rows(table).map(row => row :+ GroupValue.Natural(natural(row(0)).add(natural(row(1))))))(_ == _)
        .and(
          Result.diff(
            halved,
            backend.rows(table).filterNot(row => natural(row(1)).testBit(0)).map(row => row :+ GroupValue.Natural(natural(row(1)).shiftRight(1)))
          )(_ == _)
        )
  }
