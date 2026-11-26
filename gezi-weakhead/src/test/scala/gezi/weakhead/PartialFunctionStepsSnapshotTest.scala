package gezi.weakhead

import hedgehog.Gen
import hedgehog.Range
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.frontend.Literals
import gezi.generatedinputs.SeededSnapshots
import gezi.knowledgereading.KnowledgeReading
import snapshot4s.generated.snapshotConfig

/** The evaluator steps of looking keys up in generated records of partial
  * functions of literals, two records deep, under the tabled evaluator that
  * knows top (`KnowledgeReading.knownExtremes`), the one reader of data,
  * recorded as a seeded snapshot: the steps are a function of the encodings
  * and of the evaluator's rules with no concise law. Its purpose is to show,
  * as a diff beside the records, any change of what matching a partial
  * function costs and of the values read. A reading that does not know top is
  * not one: the top a miss leaves is then a head beside the data's, which the
  * reader refuses (`KnowledgeReading.dataHeads`). Each record is read under
  * `ByLayer`, which tables every prefix of a key, and `BySharedPrefix`, which
  * tables the prefixes where keys part (`ApplicationReading`), so that
  * the steps and tables each costs on the binary trie of the keys show side
  * by side.
  */
class PartialFunctionStepsSnapshotTest extends gezi.generatedinputs.FailFastSuite with SeededSnapshots:

  /** A budget far above what the readings take and far below what would
    * make the snapshot slow to compute.
    */
  private val stepLimit = 2000000L

  /** A record two levels deep: the outer keys, and under each the inner
    * keys with an integer each.
    */
  private final case class Nested(outer: Vector[(String, Vector[(String, Int)])])

  private val key: Gen[String] = Gen.string(Gen.lower, Range.linear(1, 8))

  /** One to six fields of distinct keys, an integer each. */
  private val inner: Gen[Vector[(String, Int)]] =
    (for
      name <- key
      value <- Gen.int(Range.linear(0, 1000))
    yield (name, value)).list(Range.linear(1, 6)).map(_.toVector.distinctBy(_._1))

  /** Records whose inner records each have keys of their own. */
  private val ownKeys: Gen[Nested] =
    (for
      name <- key
      fields <- inner
    yield (name, fields)).list(Range.linear(1, 6)).map(found => Nested(found.toVector.distinctBy(_._1)))

  /** Records whose inner records all have the keys of one schema, as the
    * entries of one kind of a configuration have.
    */
  private val oneSchema: Gen[Nested] =
    for
      schema <- key.list(Range.linear(1, 6)).map(_.toVector.distinct)
      outerKeys <- key.list(Range.linear(2, 8)).map(_.toVector.distinct)
      values <- Gen.int(Range.linear(0, 1000)).list(Range.singleton(schema.size * outerKeys.size))
    yield Nested(outerKeys.zipWithIndex.map((name, index) =>
      (name, schema.zipWithIndex.map((field, position) => (field, values(index * schema.size + position))))
    ))

  private val nested: Gen[Nested] = Gen.choice1(ownKeys, oneSchema)

  private def recordText(fields: Vector[(String, String)]): String =
    fields.map((name, value) => s"(λ\"$name\". $value)").mkString(" + ")

  /** The record's text, each integer written as the library's Scott integer
    * (`Literals.integerTerm`): a literal is never a value of its own.
    */
  private def text(record: Nested): String =
    recordText(record.outer.map((name, inner) =>
      (name, s"(${recordText(inner.map((key, value) => (key, s"(${Lambdalattice.text(Literals.integerTerm(BigInt(value)), Map.empty)})")))})")
    ))

  /** The record as the snapshot shows it: each key with its value. */
  private def described(record: Nested): String =
    record.outer
      .map((name, inner) => s"$name = (${inner.map((key, value) => s"$key = $value").mkString(", ")})")
      .mkString(" + ")

  /** The partial function applied to the elements the key's string literal
    * spreads into (`Literals.arguments`), `R k1 … \0`. Nothing is evaluated.
    */
  private def keyApplied(partialFunction: Value, key: String): Value =
    Literals
      .arguments(gezi.frontend.Literal.text(key))
      .foldLeft(partialFunction)((function, element) => Value.Apply(function, Defunctionalization.thunkInstruction(element)))

  /** The integers of every inner key under every outer key, and of one key
    * no record writes under each, read in one reading, and the steps it
    * took, from the state.
    */
  private def read(record: Nested, state: ReadingState): String =
    val root = Defunctionalization.thunkInstruction(Lambdalattice.term(text(record)))
    val reading = Computation.traversed(record.outer)((outerKey, inner) =>
      val under = keyApplied(root, outerKey)
      Computation.traversed(inner.map(_._1) :+ "0")(innerKey =>
        KnowledgeReading.integerWritten(keyApplied(under, innerKey))
      )
    )
    reading.result(state) match
      case Computed.Done(values, after) =>
        s"${values.map(_.map(_.fold("absent")(_.toString)).mkString(" ")).mkString(" ; ")} in ${after.budget.spent} steps, ${after.tables.complete.size} tables"
      case Computed.Stopped(after) => s"stopped after ${after.budget.spent} steps (${after.exhausted})"

  test("the steps of looking keys up in records of partial functions of literals") {
    assertSeededSnapshot(nested, 20261111L, 12, "partial_functions/lookup_steps.txt")(
      described,
      identity[String]
    )(record =>
      Vector(ApplicationReading.ByLayer, ApplicationReading.BySharedPrefix)
        .map(applications =>
          s"$applications: ${read(record, ReadingState.knowing(stepLimit, KnowledgeReading.knownExtremes).copy(applications = applications))}"
        )
        .mkString("knowing top, ", "; ", "")
    )
  }
