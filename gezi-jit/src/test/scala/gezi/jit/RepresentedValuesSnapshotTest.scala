package gezi.jit

import gezi.frontend.ReadableText
import gezi.frontend.Term
import gezi.frontend.TermOf
import gezi.ir.Configured
import gezi.standardlibrary.SplitMix
import gezi.weakhead.Bounded
import gezi.weakhead.EvaluatorTesting
import gezi.weakhead.Mode
import snapshot4s.generated.snapshotConfig

/** The JIT's readings of 40 programs over filtered naturals, booleans and
  * lists, generated from the fixed seed 20261123 and read with the natives on
  * (`NativesTesting.nativesOn`): for each program, its spelling, its normal
  * forms, the steps of its reading, its native calls by native and its
  * decodings. The programs apply the natives `double` and `even`, `boolean_not`
  * and the codecs' constructors to values under decode points (`x ∥ nat_type`,
  * `x ∥ boolean_type`, `x ∥ list_type nat_type`), so that the JIT holds values
  * of representations and calls natives on them. A decode point of a list reads
  * one layer, its tail filtered and unread, so a program that takes a list's
  * head reads that layer only. Its purpose is to catch a change in the answers,
  * the steps or the native calls of these readings.
  */
class RepresentedValuesSnapshotTest
    extends gezi.generatedinputs.FailFastSuite
    with snapshot4s.munit.SnapshotAssertions:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => NativesTesting.nativesOn, _ => encoding, _ => evaluator)

  /** The encoding of the natives' library, whose singleton type is the
    * configuration of the programs.
    */
  private lazy val encoding: StorageEncoding = NativesTesting.nativesOnEncoding

  private given encoding.type = encoding

  /** The capability to read a storage's view, for the text of the normal forms.
    */
  private given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  /** A closed HOAS term over the library's terms of the configuration. */
  private type Hoas = TermOf[Configured[encoding.type]]

  private lazy val evaluator = Jit(NativesTesting.configurationOf(encoding))

  /** The same configuration with the conversion at construction sites selected
    * (`StorageConstruction.Converted`).
    */
  private lazy val convertingEvaluator =
    val plain = NativesTesting.configurationOf(encoding)
    Jit(
      JitConfiguration[encoding.type](
        encoding,
        plain.budget,
        plain.strategy,
        plain.backend,
        plain.dispatch,
        plain.instanceTable,
        storageAccess = gezi.ir.StorageAccess.granted()
      )
    )

  private lazy val zero = JitTesting.libraryTerm[encoding.type]("zero")
  private lazy val successor =
    JitTesting.libraryTerm[encoding.type]("successor")
  private lazy val natType = JitTesting.libraryTerm[encoding.type]("nat_type")
  private lazy val double = JitTesting.libraryTerm[encoding.type]("double")
  private lazy val even = JitTesting.libraryTerm[encoding.type]("even")
  private lazy val trueTerm = JitTesting.libraryTerm[encoding.type]("true")
  private lazy val falseTerm = JitTesting.libraryTerm[encoding.type]("false")
  private lazy val booleanType =
    JitTesting.libraryTerm[encoding.type]("boolean_type")
  private lazy val booleanNot =
    JitTesting.libraryTerm[encoding.type]("boolean_not")
  private lazy val nil = JitTesting.libraryTerm[encoding.type]("nil")
  private lazy val cons = JitTesting.libraryTerm[encoding.type]("cons")
  private lazy val listType = JitTesting.libraryTerm[encoding.type]("list_type")

  /** The steps a reading may take; the programs are small. */
  private val limit: Long = 200000

  private def numeral(value: Int): Hoas =
    (1 to value).foldLeft(zero)((inner, _) => successor(inner))

  /** A natural: a numeral filtered or not, or `double` or `successor` of a
    * smaller one.
    */
  private def natural(depth: Int, random: SplitMix): (Hoas, SplitMix) =
    val (kind, afterKind) = random.between(0, if depth <= 0 then 1 else 3)
    val (value, afterValue) = afterKind.between(0, 4)
    kind match
      case 0 => (numeral(value) ∥ natType, afterValue)
      case 1 => (numeral(value), afterValue)
      case 2 =>
        val (inner, afterInner) = natural(depth - 1, afterValue)
        (double(inner), afterInner)
      case _ =>
        val (inner, afterInner) = natural(depth - 1, afterValue)
        (successor(inner), afterInner)

  /** A boolean: a constant filtered or not, `even` of a natural, or
    * `boolean_not` of a smaller one.
    */
  private def boolean(depth: Int, random: SplitMix): (Hoas, SplitMix) =
    val (kind, afterKind) = random.between(0, if depth <= 0 then 1 else 3)
    kind match
      case 0 =>
        val (truth, afterTruth) = afterKind.between(0, 1)
        (if truth == 0 then trueTerm ∥ booleanType else falseTerm, afterTruth)
      case 1 =>
        val (inner, afterInner) = natural(depth, afterKind)
        (even(inner), afterInner)
      case 2 =>
        val (inner, afterInner) = natural(depth - 1, afterKind)
        (even(inner) ∥ booleanType, afterInner)
      case _ =>
        val (inner, afterInner) = boolean(depth - 1, afterKind)
        (booleanNot(inner), afterInner)

  /** A list of up to three naturals, filtered by the lists of naturals, its
    * cells filtered again at random.
    */
  private def list(random: SplitMix): (Hoas, SplitMix) =
    val (length, afterLength) = random.between(0, 3)
    val (items, afterItems) =
      (1 to length).foldLeft((Vector.empty[Hoas], afterLength)) {
        case ((found, current), _) =>
          val (item, after) = natural(2, current)
          (found :+ item, after)
      }
    val (filtered, afterFiltered) = afterItems.between(0, 1)
    val cells = items.foldRight(nil)((item, rest) =>
      cons(item)(if filtered == 0 then rest else rest ∥ listType(natType))
    )
    (cells ∥ listType(natType), afterFiltered)

  /** A program: a natural, a boolean, or a list applied to its two cases, the
    * cons case taking the head.
    */
  private def program(random: SplitMix): (Hoas, SplitMix) =
    val (kind, afterKind) = random.between(0, 2)
    kind match
      case 0 => natural(3, afterKind)
      case 1 => boolean(3, afterKind)
      case _ =>
        val (cells, afterCells) = list(afterKind)
        (cells(zero)(Term.λ(head => Term.λ(_ => head))), afterCells)

  private lazy val programs: Vector[Hoas] =
    EvaluatorTesting.draws(40, 20261123L)(program)

  private def line(program: Hoas, index: Int): String =
    val instruction = JitTesting.termInstruction[encoding.type](program)
    val read = NativesTesting.normalFormsSpent(
      evaluator,
      JitTesting.termValue[encoding.type](program),
      limit
    )
    val outcome = read.outcome match
      case Bounded.Finished(normalForms) =>
        normalForms
          .map(found => ReadableText.printedNameless(found).text)
          .mkString("finished[", " | ", "]")
      case other => other.productPrefix
    val counts = JitTesting.counts(read.jitState)
    val calls = counts.callsByNative.toVector
      .map((native, count) => s"$native=$count")
      .sorted
      .mkString(",")
    Vector(
      index.toString,
      ReadableText.printedNameless(instruction).text,
      outcome,
      s"steps=${read.steps}",
      s"nativeCalls=${counts.nativeCalls}",
      s"byNative=[$calls]",
      s"decodings=${counts.decodings}"
    ).mkString("\t")

  test("theJitReadingsOfGeneratedProgramsOverRepresentedValues") {
    assertFileSnapshot(
      programs.zipWithIndex.map(line).mkString("\n") + "\n",
      "represented-values/generated-programs.txt"
    )
  }

  // Its purpose is to catch an answer the conversion adds or loses, and the
  // conversion is sound when a parallel it makes a storage equals the storage
  // (#2163 B1): with the conversion selected, each program reads the normal
  // forms it reads as written.
  test("theConversionReadsTheSameNormalFormsAsWritten") {
    programs.zipWithIndex.foreach((program, index) =>
      val asWritten = NativesTesting
        .normalFormsSpent(
          evaluator,
          JitTesting.termValue[encoding.type](program),
          limit
        )
        .outcome
      val converted = NativesTesting
        .normalFormsSpent(
          convertingEvaluator,
          JitTesting.termValue[encoding.type](program),
          limit
        )
        .outcome
      assert(JitTesting.sameOutcomes(converted, asWritten), s"program $index")
    )
  }
