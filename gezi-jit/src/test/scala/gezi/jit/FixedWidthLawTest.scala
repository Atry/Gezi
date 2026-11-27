package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import gezi.weakhead.Bounded
import gezi.weakhead.Mode
import gezi.standardlibrary.LibraryFiles
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTables
import gezi.weakhead.Expansions
import gezi.ir.{Configured, NoFacts}
import gezi.frontend.TermOf
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties

/** The law of the fixed-width integers (corpora/library/fixed_width): at a
  * width w and words x and y written as their bits, the reference's normal form
  * of each operation applied to w, x and y is the normal form of the result
  * that the JVM's `Long` arithmetic gives, masked to w bits (signed, for the
  * comparison). Its purpose is to catch a library term whose bits, carries,
  * wrap or sign differ from two's complement arithmetic at the width; the eight
  * thin operations at 16 and 32 are checked the same way, to_natural on small
  * values and of_natural on small naturals, whose readings are linear in the
  * natural. The oracle is independent: the JVM's arithmetic, not a second
  * implementation of the library's terms. The operations are members of the
  * fixture `TermTables.fixedWidthTerms`, the naturals, booleans and word
  * constructors members of `JitTesting.libraryTermsFile`, each read by
  * projection, so no name is resolved.
  */
class FixedWidthLawTest extends GeneratedProperties:

  private given NoFacts.type = NoFacts

  private type Operand = TermOf[Configured[NoFacts.type]]

  private lazy val operations: Map[String, Configured[NoFacts.type]] =
    StandardLibrary
      .entryMembers(
        LibraryFiles.buildRoot,
        TermTables.fixedWidthTerms,
        Expansions.none
      )
      ._1

  /** The operations and the library terms the words are built from, forced
    * before the first test and not charged to it (FailFastSuite).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => operations, _ => JitTesting.libraryTerms)

  private def operation(key: String): Operand =
    Term.closed(
      operations.getOrElse(
        key,
        throw IllegalArgumentException(
          s"${TermTables.fixedWidthTerms.file} has no member $key"
        )
      )
    )

  private def term(key: String): Operand =
    JitTesting.libraryTerm[NoFacts.type](key)

  private def numeral(value: Long): Operand =
    (1L to value).foldLeft(term("zero"))((below, _) => term("successor")(below))

  private def boolean(value: Boolean): Operand = term(
    if value then "true" else "false"
  )

  /** The word of width w whose bits are the w low bits of the value, the least
    * significant first.
    */
  private def word(width: Int, value: Long): Operand =
    (0 until width).foldRight(term("word_end"))((position, above) =>
      term("word_cell")(boolean(((value >> position) & 1L) == 1L))(above)
    )

  private def masked(width: Int, value: Long): Long =
    value & ((1L << width) - 1L)

  private def signed(width: Int, value: Long): Long =
    val low = masked(width, value)
    if (low >> (width - 1)) == 1L then low - (1L << width) else low

  /** The reference's normal forms of the closed term, within the natives' limit
    * of steps.
    */
  private def normalForms(
      closed: Operand
  ): Bounded[Vector[Configured[NoFacts.type]]] =
    NativesTesting
      .normalFormsSpent(
        Mode.TablingWeakHead,
        gezi.weakhead.ReadingConfiguration.withoutFacts,
        JitTesting.termValue(closed),
        NativesTesting.normalFormLimit
      )
      .outcome

  private def agrees(read: Operand, expected: Operand): Result =
    normalForms(read) match
      case finished @ Bounded.Finished(_) =>
        Result
          .assert(JitTesting.sameOutcomes(finished, normalForms(expected)))
          .log(s"$finished against ${normalForms(expected)}")
      case other => Result.failure.log(s"the reading did not finish: $other")

  private val widthAndWords: Gen[(Int, Long, Long)] =
    for
      width <- Gen.int(Range.linear(1, 8))
      left <- Gen.long(Range.linear(0L, (1L << width) - 1L))
      right <- Gen.long(Range.linear(0L, (1L << width) - 1L))
    yield (width, left, right)

  private def applied(key: String, width: Int, operands: Operand*): Operand =
    operands.foldLeft(operation(key)(numeral(width)))((applying, operand) =>
      applying(operand)
    )

  property(
    "each operation reads as two's complement arithmetic at the width",
    _.copy(testLimit = SuccessCount(40))
  ) {
    for (width, left, right) <- widthAndWords.forAll
    yield
      val x = word(width, left)
      val y = word(width, right)
      Result.all(
        List(
          agrees(applied("word_add", width, x, y), word(width, left + right)),
          agrees(
            applied("word_subtract", width, x, y),
            word(width, left - right)
          ),
          agrees(
            applied("word_multiply", width, x, y),
            word(width, left * right)
          ),
          agrees(applied("word_negate", width, x), word(width, -left)),
          agrees(applied("word_equal", width, x, y), boolean(left == right)),
          agrees(
            applied("word_less_than", width, x, y),
            boolean(signed(width, left) < signed(width, right))
          ),
          agrees(applied("word_to_natural", width, x), numeral(left))
        )
      )
  }

  property(
    "word_of_natural wraps a natural to the width",
    _.copy(testLimit = SuccessCount(20))
  ) {
    for
      width <- Gen.int(Range.linear(1, 5)).forAll
      natural <- Gen.long(Range.linear(0L, 40L)).forAll
    yield agrees(
      applied("word_of_natural", width, numeral(natural)),
      word(width, natural)
    )
  }

  property(
    "the thin operations at 16 and 32 are the operations at their widths",
    _.copy(testLimit = SuccessCount(10))
  ) {
    for
      wide <- Gen.boolean.forAll
      left <- Gen
        .long(Range.linear(Int.MinValue.toLong, Int.MaxValue.toLong))
        .forAll
      right <- Gen
        .long(Range.linear(Int.MinValue.toLong, Int.MaxValue.toLong))
        .forAll
      small <- Gen.long(Range.linear(0L, 40L)).forAll
    yield
      val (width, prefix) = if wide then (32, "int32") else (16, "int16")
      val x = word(width, left)
      val y = word(width, right)
      Result.all(
        List(
          agrees(operation(s"${prefix}_add")(x)(y), word(width, left + right)),
          agrees(
            operation(s"${prefix}_subtract")(x)(y),
            word(width, left - right)
          ),
          agrees(
            operation(s"${prefix}_multiply")(x)(y),
            word(width, left * right)
          ),
          agrees(operation(s"${prefix}_negate")(x), word(width, -left)),
          agrees(
            operation(s"${prefix}_equal")(x)(y),
            boolean(masked(width, left) == masked(width, right))
          ),
          agrees(
            operation(s"${prefix}_less_than")(x)(y),
            boolean(signed(width, left) < signed(width, right))
          ),
          agrees(
            operation(s"${prefix}_to_natural")(word(width, small)),
            numeral(small)
          ),
          agrees(
            operation(s"${prefix}_of_natural")(numeral(small)),
            word(width, small)
          )
        )
      )
  }
