package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.weakhead.Mode
import gezi.weakhead.Value
import gezi.weakhead.Values
import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.standardlibrary.LibraryFiles
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTables
import gezi.weakhead.Expansions
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.{Apply, Choice, Parallel}

/** The law of a literal of a family that has a codec and whose constructor
  * natives are at the family's parameter (binary_natural, word), so
  * that a literal that is not type-filtered is decoded by its syntax: a native that takes the family's
  * representation, applied to a fallback point `[x, x ∥ T]` whose operand x
  * is a literal written with the family's constructors and whose criterion
  * T names the representation, is called once on the literal, decoded by
  * its syntax (`JitRules.codecLiteralOutcome`), and the JIT reads the normal
  * forms tabling(weak_head) reads of the function applied to x alone, which the
  * fallback point equals since x is in T. The natives are the test's, bound
  * by the fixture `codec_literals`: `merge_binary_increment` to
  * `test_binary_increment` at the canonical binary naturals,
  * `int16_negate` to `test_int16_negate` at the words of width 16, and the
  * binary defines of two arguments to the natives `binaryOperations` lists
  * beside them. Its
  * purpose is to catch a literal of such a family that never becomes ready,
  * so that the native taking it is never called (the defect witnessed
  * on 2026-11-01: no decoding and no native call on binary literals), and a
  * syntax decoding that changes the value. The nested properties write a
  * fallback point at every level of the literal, as the refinement does
  * (the defect witnessed on 2026-11-01: the criterion read, and
  * still no decoding, since a field was a fallback point).
  */
class CodecLiteralLawTest extends GeneratedProperties:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of CodecLiteralLawTest, "a native is called on a canonical binary literal under binary_set true, and reads as tabling(weak_head)", takes 3.165 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(5, "s")

  private val canonicalBinary: Representation = Representation.Data(BinaryNaturalFamily.identity, Some(NativeValue.Truth(true)))

  private val wordWidth: Int = 16

  private val sixteenBitWord: Representation = Representation.Data(WordFamily.identity, Some(NativeValue.Natural(wordWidth)))

  /** A native of two canonical binary naturals with the result at the
    * representation.
    */
  private def binaryOperation(operation: (BigInt, BigInt) => NativeValue, result: Representation): Native =
    Native(Vector(NativePlace.Fixed(canonicalBinary), NativePlace.Fixed(canonicalBinary)), NativePlace.Fixed(result), {
      case Vector(NativeArgument.Represented(BinaryNatural(left)), NativeArgument.Represented(BinaryNatural(right))) =>
        operation(left, right)
      case other => Native.outsidePlaces("a test binary operation", other)
    })

  private val testNatives: NativeBackend = NativeBackend.standard.extended(
    NativeBackend.functions(
      Map(
        "test_binary_increment" -> Native(Vector(NativePlace.Fixed(canonicalBinary)), NativePlace.Fixed(canonicalBinary), {
          case Vector(NativeArgument.Represented(BinaryNatural(value))) => BinaryNatural(value + 1)
          case other                                                    => Native.outsidePlaces("test_binary_increment", other)
        }),
        "test_int16_negate" -> Native(Vector(NativePlace.Fixed(sixteenBitWord)), NativePlace.Fixed(sixteenBitWord), {
          case Vector(NativeArgument.Represented(Word(width, bits))) => Word(width, ((BigInt(1) << width.toInt) - bits).mod(BigInt(1) << width.toInt))
          case other                                                 => Native.outsidePlaces("test_int16_negate", other)
        }),
        "test_binary_plus" -> binaryOperation((left, right) => BinaryNatural(left + right), canonicalBinary),
        "test_binary_times" -> binaryOperation((left, right) => BinaryNatural(left * right), canonicalBinary),
        "test_binary_maximum" -> binaryOperation((left, right) => BinaryNatural(left.max(right)), canonicalBinary),
        "test_binary_less_than" -> binaryOperation((left, right) => NativeValue.Truth(left < right), Representation.Truth),
        "test_binary_equality" -> binaryOperation((left, right) => NativeValue.Truth(left == right), Representation.Truth)
      ),
      Vector.empty
    )
  )

  /** The library of the standard knowledge files the literals need and the
    * fixture `codec_literals`'s natives, the one field of
    * tests/library_fixtures/codec_literals.lambdalattice, read off the tree
    * whose visible subtree is Gezi's directory (`LibraryFiles.compiled`),
    * with the backend's checks on the test's natives.
    */
  private lazy val library: StandardLibrary =
    LibraryFiles.compiled("tests/library_fixtures/codec_literals.lambdalattice", Vector(BackendChecks(testNatives)))

  /** The file of the library terms the literals and programs are built
    * from (`TermTables.codecTerms`).
    */
  private val termsFile: String = TermTables.codecTerms.file

  /** The members of `termsFile`, each a closed instruction read by
    * projection (`StandardLibrary.entryMembers`).
    */
  private lazy val terms: Map[String, Instruction] =
    StandardLibrary.entryMembers(LibraryFiles.buildRoot, TermTables.codecTerms, Expansions.none)._1

  /** The library with the test's natives and the terms of `termsFile`, forced before the first test and not charged to it (FailFastSuite). */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => library, _ => terms)

  private def define(key: String): Instruction = terms.getOrElse(key, throw IllegalArgumentException(s"$termsFile has no member $key"))

  private def name(key: String): Term = Term.closed(define(key))

  /** The canonical numeral of the natural: binary_zero, or binary_even or
    * binary_odd over the half, so that an even numeral's half is positive.
    */
  private def binary(value: BigInt): Term =
    if value == 0 then name("binary_zero")
    else if value.testBit(0) then name("binary_odd")(binary(value >> 1))
    else name("binary_even")(binary(value >> 1))

  /** The word of the bits, the least significant first. */
  private def word(bits: List[Boolean]): Term =
    bits.foldRight(name("word_end"))((bit, above) => name("word_cell")(name(if bit then "true" else "false"))(above))

  /** The term compiled to one thunk, the instructions of `terms` kept as
    * references, so that a filter by a criterion the backend binds reaches
    * the JIT as that instruction.
    */
  private def termValue(term: Term): Value =
    Values.ofInstruction(Defunctionalization.thunkInstruction(term.deBruijnTerm(Map.empty)), terms.values.toSet)

  /** A term spelled in interned layers, as the refinement's output is: a
    * subterm written twice is one instruction. A fallback point doubles its
    * operand, so a literal with one at every level, written as a `Term`, is
    * a tree exponential in its depth.
    */
  private final case class Layers():
    def layer(found: Layer[Instruction]): (Layers, Instruction) = (this, Instruction(found))

    def applied(function: Instruction, arguments: Instruction*): (Layers, Instruction) =
      arguments.foldLeft((this, function)) { case ((current, applying), argument) => current.layer(Apply(applying, argument)) }

    /** `operand + (operand ∥ criterion)`, a fallback point as the
      * refinement writes one.
      */
    def fallback(operand: Instruction, criterion: Instruction): (Layers, Instruction) =
      val (afterFiltered, filtered) = layer(Parallel(operand, criterion))
      afterFiltered.layer(Choice(operand, filtered))

  /** The canonical numeral of the natural with a fallback point on every
    * field, each by `binary_set p`, p generated per level (`parameters`,
    * the least significant level first, cycled): true at every level, as
    * the witness of 2026-11-01 writes, or false. A choice `x + (x ∥ T)`
    * equals x whatever T is, by equation (6) of the formal definition,
    * M + (M ∥ N) = M, so the value is the numeral's either way.
    */
  private def nestedBinary(value: BigInt, parameters: List[Boolean])(start: Layers): (Layers, Instruction) =
    def level(current: Layers, remaining: BigInt, depth: Int): (Layers, Instruction) =
      if remaining == 0 then (current, define("binary_zero"))
      else
        val (afterField, field) = level(current, remaining >> 1, depth + 1)
        val parameter = if parameters(depth % parameters.size) then "true" else "false"
        val (afterCriterion, criterion) = afterField.applied(define("binary_set"), define(parameter))
        val (afterPoint, point) = afterCriterion.fallback(field, criterion)
        afterPoint.applied(define(if remaining.testBit(0) then "binary_odd" else "binary_even"), point)
    level(start, value, 0)

  /** The natural written out with successor and zero, as int16_width is. */
  private def numeral(value: Int)(start: Layers): (Layers, Instruction) =
    (1 to value).foldLeft((start, define("zero"))) { case ((current, below), _) => current.applied(define("successor"), below) }

  /** The word of the bits with a fallback point on every field: each
    * boolean by boolean_type, and each word of width w by `word_type w`, w
    * written out.
    */
  private def nestedWord(bits: List[Boolean])(start: Layers): (Layers, Instruction) =
    def cells(current: Layers, remaining: List[Boolean]): (Layers, Instruction) = remaining match
      case Nil => (current, define("word_end"))
      case bit :: above =>
        val (afterAbove, aboveWord) = cells(current, above)
        val (afterWidth, width) = numeral(above.size)(afterAbove)
        val (afterType, wordType) = afterWidth.applied(define("word_type"), width)
        val (afterAbovePoint, abovePoint) = afterType.fallback(aboveWord, wordType)
        val (afterBitPoint, bitPoint) = afterAbovePoint.fallback(define(if bit then "true" else "false"), define("boolean_type"))
        afterBitPoint.applied(define("word_cell"), bitPoint, abovePoint)
    cells(start, bits)

  /** The function applied to a fallback point over each literal under the
    * criterion, in interned layers, as a reference.
    */
  private def layered(function: String, literals: Vector[Layers => (Layers, Instruction)], criterion: Layers => (Layers, Instruction)): Value =
    val (after, program) = literals.foldLeft((Layers(), define(function))) { case ((current, applying), literal) =>
      val (afterLiteral, literalInstruction) = literal(current)
      val (afterCriterion, criterionInstruction) = criterion(afterLiteral)
      val (afterPoint, point) = afterCriterion.fallback(literalInstruction, criterionInstruction)
      afterPoint.applied(applying, point)
    }
    program

  /** The JIT's reading of the filtered program, a function applied to
    * fallback points over literals, against tabling(weak_head)'s of the plain
    * program, the function applied to the same numerals with no fallback
    * point anywhere, which the filtered program equals by equation (6); and
    * the native called once.
    */
  private def agreement(filteredProgram: Value, plainProgram: Term, native: String): Result =
    val filtered = filteredProgram
    val plain = termValue(plainProgram)
    val jit = NativesTesting.normalFormsSpent(
      Mode.Jit(Jit(JitTesting.configured(BackendFacts.of(library, testNatives), JitConfiguration.defaultBudget))),
      filtered,
      NativesTesting.normalFormLimit
    )
    val reference = NativesTesting.normalFormsSpent(Mode.TablingWeakHead, plain, NativesTesting.normalFormLimit)
    val counts = JitTesting.counts(jit.jitState)
    Result.all(
      List(
        Result.assert(jit.outcome.finished).log(s"the JIT's reading: ${jit.outcome}"),
        Result.diff(jit.outcome, reference.outcome)(_ == _),
        Result.diff(counts.callsOf(NativeName.Function(native)), 1L)(_ == _).log(s"counts: $counts")
      )
    )

  private val canonicalCriterion: Layers => (Layers, Instruction) = _.applied(define("binary_set"), define("true"))

  property("a native is called on a canonical binary literal under binary_set true, and reads as tabling(weak_head)") {
    for value <- Gen.long(Range.linear(0L, 1L << 20)).forAll
    yield
      val literal = binary(BigInt(value))
      agreement(
        termValue(name("merge_binary_increment")(Term.choice(literal, literal ∥ name("binary_set")(name("true"))))),
        name("merge_binary_increment")(literal),
        "test_binary_increment"
      )
  }

  property("a native is called on a word literal of width 16 under int16_type, and reads as tabling(weak_head)") {
    for bits <- Gen.list(Gen.boolean, Range.singleton(wordWidth)).forAll
    yield
      val literal = word(bits)
      agreement(termValue(name("int16_negate")(Term.choice(literal, literal ∥ name("int16_type")))), name("int16_negate")(literal), "test_int16_negate")
  }

  property("a native is called on a canonical binary literal with a fallback point at every level, and reads as tabling(weak_head)") {
    for
      value <- Gen.long(Range.linear(0L, 1L << 20)).forAll
      parameters <- Gen.list(Gen.boolean, Range.linear(1, 4)).forAll
    yield agreement(
      layered("merge_binary_increment", Vector(nestedBinary(BigInt(value), parameters)), canonicalCriterion),
      name("merge_binary_increment")(binary(BigInt(value))),
      "test_binary_increment"
    )
  }

  property("a native is called on a word literal of width 16 with a fallback point at every level, and reads as tabling(weak_head)") {
    for bits <- Gen.list(Gen.boolean, Range.singleton(wordWidth)).forAll
    yield agreement(
      layered("int16_negate", Vector(nestedWord(bits)), current => (current, define("int16_type"))),
      name("int16_negate")(word(bits)),
      "test_int16_negate"
    )
  }

  /** The binary defines of two arguments bound to the test's natives by the
    * fixture, each with its native.
    */
  private val binaryOperations: Vector[(String, String)] = Vector(
    "merge_binary_plus" -> "test_binary_plus",
    "merge_binary_times" -> "test_binary_times",
    "binary_maximum" -> "test_binary_maximum",
    "binary_less_than" -> "test_binary_less_than",
    "merge_binary_equality" -> "test_binary_equality"
  )

  property("a binary define of two arguments is called natively on literals with a fallback point at every level, and reads as tabling(weak_head)") {
    for
      (function, native) <- Gen.elementUnsafe(binaryOperations.toList).forAll
      left <- Gen.long(Range.linear(0L, 1L << 10)).forAll
      right <- Gen.long(Range.linear(0L, 1L << 10)).forAll
      parameters <- Gen.list(Gen.boolean, Range.linear(1, 4)).forAll
    yield agreement(
      layered(function, Vector(nestedBinary(BigInt(left), parameters), nestedBinary(BigInt(right), parameters.reverse)), canonicalCriterion),
      name(function)(binary(BigInt(left)))(binary(BigInt(right))),
      native
    )
  }

  /** Ω, a term with no head. */
  private val omega: Term = Term.λ(a => a(a))(Term.λ(b => b(b)))

  /** The natural written out with successor and zero. */
  private def unary(value: Int): Term = (1 to value).foldLeft(name("zero"))((below, _) => name("successor")(below))

  private def wordType(width: Int): Term = name("word_type")(unary(width))

  private def binarySet(parameter: Boolean): Term = name("binary_set")(name(if parameter then "true" else "false"))

  /** The heads of the term under the JIT with the test's natives, under the
    * JIT with no native (an empty set, so no decode point either), and under
    * tabling(weak_head), each within a million steps.
    */
  private def headsAgree(term: Term): Result =
    val value = termValue(term)
    def jitHeads(natives: NativeBackend) =
      JitTesting.headsRead(
        Mode.Jit(Jit(JitTesting.configured(BackendFacts.of(library, natives), JitConfiguration.defaultBudget))),
        value,
        1000000
      ).outcome
    val reference = JitTesting.headsRead(Mode.TablingWeakHead, value, 1000000).outcome
    Result.all(
      List(
        Result.assert(reference.finished).log(s"tabling(weak_head) did not finish on $term"),
        Result.diff(jitHeads(testNatives), reference)(_ == _).log(s"natives on: $term"),
        Result.diff(jitHeads(NativeBackend(Map.empty, Vector.empty)), reference)(_ == _).log(s"natives off: $term")
      )
    )

  /** The JIT's normal forms, with the test's natives, of the literal under
    * the criterion: tabling(weak_head)'s of the literal alone when the literal is in
    * the criterion (equation: x ∥ T = x for x in T), and none when it is
    * not, as a filter on a value of another width or parameter decodes into
    * nothing (`JitNativesTest`, aFilterOnANonNumberGivesNoAnswerWithNatives).
    */
  private def filterReads(literal: Term, criterion: Term, member: Boolean): Result =
    val jit = NativesTesting.normalFormsSpent(
      Mode.Jit(Jit(JitTesting.configured(BackendFacts.of(library, testNatives), JitConfiguration.defaultBudget))),
      termValue(literal ∥ criterion),
      NativesTesting.normalFormLimit
    ).outcome
    val expected =
      if member then NativesTesting.normalFormsSpent(Mode.TablingWeakHead, termValue(literal), NativesTesting.normalFormLimit).outcome
      else gezi.weakhead.Bounded.Finished(Vector.empty)
    Result.diff(jit, expected)(_ == _).log(s"${literal ∥ criterion}, member: $member")

  // The purpose: catch a constructor native at the family's parameter
  // that changes a head the reference reads, forces a field the term
  // never reads (`word_cell @ true @ (Ω ∥ word_type w)` keeps word_cell's
  // head), or changes what a filter reads, where the decoding fails (a
  // literal under a criterion of another width or parameter) as where it
  // succeeds. A filter at the top is a decode point the JIT reads and a
  // head tabling(weak_head) stops at, so it is compared by normal forms.
  property("generated words in and under constructors read alike with natives on, natives off and tabling(weak_head)") {
    for
      bits <- Gen.list(Gen.boolean, Range.linear(0, 8)).forAll
      bit <- Gen.boolean.forAll
      criterionWidth <- Gen.int(Range.linear(0, 9)).forAll
      context <- Gen.int(Range.linear(0, 3)).forAll
    yield
      val literal = word(bits)
      val bitTerm = name(if bit then "true" else "false")
      context match
        case 0 => headsAgree(literal)
        case 1 => filterReads(literal, wordType(criterionWidth), bits.size == criterionWidth)
        case 2 => headsAgree(name("word_cell")(bitTerm)(omega ∥ wordType(criterionWidth)))
        case _ => headsAgree(name("word_cell")(bitTerm)(literal ∥ wordType(criterionWidth)))
  }

  property("generated binary naturals in and under constructors read alike with natives on, natives off and tabling(weak_head)") {
    for
      value <- Gen.long(Range.linear(0L, 1L << 12)).forAll
      parameter <- Gen.boolean.forAll
      constructor <- Gen.element1("binary_even", "binary_odd").forAll
      context <- Gen.int(Range.linear(0, 3)).forAll
    yield
      val literal = binary(BigInt(value))
      context match
        case 0 => headsAgree(literal)
        case 1 => filterReads(literal, binarySet(parameter), parameter || value > 0)
        case 2 => headsAgree(name(constructor)(omega ∥ binarySet(parameter)))
        case _ => headsAgree(name(constructor)(literal ∥ binarySet(parameter)))
  }

  /** The value rebuilt by the family's constructor natives from the layers
    * the codec takes it apart into, each native's result parameter checked:
    * a word's is the width the layer was taken at, a binary natural's is
    * the canonical naturals' (true) at either parameter (the FIXME at
    * `BinaryNaturalFamily.builtParameter`).
    */
  private def rebuilt(family: DataFamily, parameter: Option[NativeValue], value: NativeValue): Either[String, NativeValue] =
    val layer = family.taken(parameter, value)
    val constructor = family.constructors(parameter)(layer.constructor)
    val fields = layer.fields.zip(constructor.fields).foldLeft(Right(Vector.empty): Either[String, Vector[NativeValue]]) {
      case (found, (field, declared)) =>
        found.flatMap(sofar =>
          declared.representation(parameter) match
            case Representation.Data(fieldFamily, fieldParameter) if fieldFamily == family.identity =>
              rebuilt(family, fieldParameter, field).map(sofar :+ _)
            case _ => Right(sofar :+ field)
        )
    }
    fields.flatMap(values =>
      val native = NativeBackend.standard.natives(constructor.native)
      val built = native.implementation(values.map(NativeArgument.Represented(_)))
      native.resultParameter(values) match
        case Some(found) if found == resultParameterExpected(family, parameter) => Right(built)
        case other => Left(s"${constructor.native} over $values gives the parameter $other at $parameter")
    )

  private def resultParameterExpected(family: DataFamily, parameter: Option[NativeValue]): Option[NativeValue] =
    if family.identity == BinaryNaturalFamily.identity then Some(NativeValue.Truth(true)) else parameter

  // The purpose: catch a constructor native whose value or result parameter
  // differs from the codec's (`DataFamily.built`, `taken`), which the JIT
  // would then plant as the literal's value.
  property("the constructor natives of words and binary naturals rebuild every value the codec takes apart") {
    for
      width <- Gen.int(Range.linear(0, 40)).forAll
      bits <- Gen.long(Range.linear(0L, Long.MaxValue)).forAll
      natural <- Gen.long(Range.linear(0L, Long.MaxValue)).forAll
    yield
      val wordValue = Word(width, BigInt(bits) & ((BigInt(1) << width) - 1))
      val binaryValue = BinaryNatural(BigInt(natural))
      Result.all(
        List(
          Result.diff(rebuilt(WordFamily, Some(NativeValue.Natural(width)), wordValue), Right(wordValue))(_ == _),
          Result.diff(rebuilt(BinaryNaturalFamily, Some(NativeValue.Truth(true)), binaryValue), Right(binaryValue))(_ == _)
        )
      )
  }
