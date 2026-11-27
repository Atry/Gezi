package com.yang_bo.gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.standardlibrary.LibraryFiles
import com.yang_bo.gezi.weakhead.BooleanCodec
import com.yang_bo.gezi.weakhead.Computed
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.NormalForms
import com.yang_bo.gezi.weakhead.ReadingState
import com.yang_bo.gezi.ir.Value

/** The law that a storage's view is exactly the term it stands for (#2163 B1's
  * soundness obligation), against an oracle independent of the backend's codecs
  * (`DataFamily.layer`, `built`, `taken`): a storage made directly from a
  * generated native value is applied to selectors written here, and the
  * reference reading (tabled weak head, no native backend) must read the part
  * of the value the library's own encoding puts there, computed here from the
  * native value by the encoding the library's files document:
  *   - a JVM bit tuple of width w (`java_ffi/bits`): w booleans, high bit
  *     first, read by the projection of each position;
  *   - a word of width w (`fixed_width/word_representation`): `word_cell b
  *     above`, the least significant bit first, ending in `word_end`, read by
  *     walking the cells;
  *   - a binary natural (`binary/natural`): `binary_zero`, `binary_even h` for
  *     2h, `binary_odd h` for 2h + 1, low bit outermost, read layer by layer;
  *   - a natural (`native_types/natural`): zero or the successor of the natural
  *     below, read layer by layer, the reading taking the reader's storage
  *     option so that it does not read the naturals' criterion as a fold over
  *     every natural;
  *   - a boolean: true or false, by its two cases;
  *   - a list (`native_types/list`): `nil` or `cons item rest`, read cell by
  *     cell with the reader's storage option, each item a natural's storage
  *     read as the plain natural (an item written plainly sits in the view as
  *     `i ∥ nat_type`, whose criterion the reference reading reads as a fold
  *     over every natural, past any limit). A selector's cases are distinct
  *     closed markers. And in the other direction, a bit tuple written in the
  *     unique spelling from the bits of the native value, its fields the
  *     storages of the booleans, is converted to the same object as the storage
  *     made from the value. Its purpose is to catch a codec whose bit order,
  *     sign or layer order differs from the library's, which a round trip
  *     through the codec itself (decode then encode) does not see, and on which
  *     a native would compute on the wrong number. The values of the fixed
  *     widths are drawn with their top bit set half the time.
  */
class StorageViewOracleLawTest extends GeneratedProperties:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(
      _ => bitsKit,
      _ => wordKit,
      _ => binaryKit,
      _ => naturalKit,
      _ => bitsKit.markers,
      _ => wordKit.markers,
      _ => binaryKit.markers,
      _ => naturalKit.markers
    )

  private lazy val bitsEncoding: StorageEncoding = NativesTesting.encodingOf(
    LibraryFiles.compiled(
      "tests/library_fixtures/java_ffi_backend.lambdalattice",
      Vector(BackendChecks)
    )
  )
  private lazy val wordEncoding: StorageEncoding = NativesTesting.encodingOf(
    LibraryFiles.compiled(
      "tests/library_fixtures/word_backend.lambdalattice",
      Vector(BackendChecks)
    )
  )
  private lazy val binaryEncoding: StorageEncoding = NativesTesting.encodingOf(
    LibraryFiles.compiled(
      "tests/library_fixtures/binary_natural_backend.lambdalattice",
      Vector(BackendChecks)
    )
  )
  private lazy val naturalEncoding: StorageEncoding =
    NativesTesting.nativesOnEncoding

  private lazy val bitsKit = Kit(bitsEncoding)
  private lazy val wordKit = Kit(wordEncoding)
  private lazy val binaryKit = Kit(binaryEncoding)
  private lazy val naturalKit = Kit(naturalEncoding)

  private val limit: Long = 200000

  /** The marker of the index among three of distinct normal forms: λa b c. a, …
    * b, … c.
    */
  private def markerTerm(index: Int): Term =
    Term.λ(a => Term.λ(b => Term.λ(c => Vector(a, b, c)(index))))

  /** The readings of the law under one encoding, the configuration of the facts
    * whose storages they read.
    */
  private final class Kit[E <: StorageEncoding & Singleton](val encoding: E):

    private given E = encoding

    /** The storage of the value in the representation under the encoding, as a
      * value.
      */
    def stored(
        representation: Representation[JitValue[E]],
        value: NativeValue[JitValue[E]]
    ): Value[E] =
      JitTesting.valueOfNative(encoding)(representation, value)

    def termValue(term: Term): Value[E] = JitTesting.termValue[E](term)

    /** The library's term of the key, a value. */
    def library(key: String): Value[E] =
      Value.of(JitTesting.libraryInstruction[E](key))

    def apply(function: Value[E], argument: Value[E]): Value[E] =
      Value.Apply(function, argument)

    def parallel(left: Value[E], right: Value[E]): Value[E] =
      JitTesting.parallelOfValues(encoding)(left, right)

    def criterion(representation: Representation[JitValue[E]]): Value[E] =
      JitTesting.criterionOf(encoding)(representation)

    /** The define bound to the native, a value. */
    def constructorTerm(native: NativeName): Value[E] =
      encoding.operations.constructorTerm(native)

    lazy val markers: Vector[Value[E]] =
      Vector(0, 1, 2).map(index => termValue(markerTerm(index)))

    /** The function that ignores its argument and gives the marker. */
    def constant(index: Int): Value[E] = termValue(
      Term.λ(_ => markerTerm(index))
    )

    /** The closed term λx1 … λxn. x(index + 1). */
    def projection(arity: Int, index: Int): Value[E] =
      def bound(sofar: Vector[Term]): Term =
        if sofar.size == arity then sofar(index)
        else Term.λ(variable => bound(sofar :+ variable))
      termValue(bound(Vector.empty))

    def applied(function: Value[E], arguments: Value[E]*): Value[E] =
      arguments.foldLeft(function)(Value.Apply(_, _))

    /** The reader's storage option under the encoding. */
    def option: StorageReadingOfFacts[E] = StorageReadingOfFacts[E](encoding)

    def fresh: ReadingState[E] =
      ReadingState.fresh(limit, JitTesting.plainConfiguration(encoding))

    def normalForms(
        value: Value[E],
        state: ReadingState[E]
    ): Vector[Configured[E]] =
      NormalForms.normalForms(Mode.TablingWeakHead, value).result(state) match
        case Computed.Done(found, _) =>
          found.sorted(com.yang_bo.gezi.ir.ContentComparison.ordering)
        case Computed.Stopped(_) => Vector.empty

    def read(value: Value[E]): Vector[Configured[E]] = normalForms(value, fresh)

    /** A Scott boolean's normal form, as the facts bind true and false. */
    def booleanNormalForm(truth: Boolean): Vector[Configured[E]] =
      read(
        constructorTerm(
          NativeName.Constructor(
            BooleanFamily.identity,
            BooleanCodec.position(truth)
          )
        )
      )

    def marker(index: Int): Vector[Configured[E]] = read(markers(index))

    def same(
        left: Vector[Configured[E]],
        right: Vector[Configured[E]]
    ): Boolean = JitTesting.sameTerms(left, right)

    def sameValue(left: Value[E], right: Value[E]): Boolean =
      Value.same(left, right)

  /** A value of the width, its top bit set when asked. */
  private def bitsOf(width: Int, topSet: Boolean): Gen[BigInt] =
    Gen
      .long(Range.linear(0L, Long.MaxValue))
      .map(drawn =>
        val low = BigInt(drawn) & ((BigInt(1) << (width - 1)) - 1)
        if topSet then low | (BigInt(1) << (width - 1)) else low
      )

  property("a JVM bit tuple's view holds the value's bits, high bit first") {
    for
      family <- Gen
        .element1(JvmBitsFamily.all.head, JvmBitsFamily.all.tail*)
        .forAll
      topSet <- Gen.boolean.forAll
      bits <- bitsOf(family.width, topSet).forAll
      position <- Gen.int(Range.linear(0, family.width - 1)).forAll
    yield
      val kit = bitsKit
      val value = JvmBitsFamily.masked(family.width, bits.toLong)
      val storage =
        kit.stored(Representation.Data(family.identity, None), value)
      val expected = kit.booleanNormalForm(
        ((bits >> (family.width - 1 - position)) & 1) == 1
      )
      Result
        .assert(
          kit.same(
            kit.read(
              kit.applied(storage, kit.projection(family.width, position))
            ),
            expected
          )
        )
        .log(s"$value at $position")
  }

  property(
    "a JVM bit tuple written in the unique spelling from its bits converts to the storage of its value"
  ) {
    for
      family <- Gen
        .element1(JvmBitsFamily.all.head, JvmBitsFamily.all.tail*)
        .forAll
      topSet <- Gen.boolean.forAll
      bits <- bitsOf(family.width, topSet).forAll
    yield
      val kit = bitsKit
      val representation = Representation.Data(family.identity, None)
      val booleanCriterion = kit.criterion(Representation.Truth)
      val fields = (family.width - 1 to 0 by -1).toVector.map(bit =>
        kit.parallel(
          kit.constructorTerm(
            NativeName.Constructor(
              BooleanFamily.identity,
              BooleanCodec.position(((bits >> bit) & 1) == 1)
            )
          ),
          booleanCriterion
        )
      )
      val spelled = kit.applied(
        kit.constructorTerm(NativeName.Constructor(family.identity, 0)),
        fields*
      )
      val converted = kit.parallel(spelled, kit.criterion(representation))
      val made = kit.stored(
        representation,
        JvmBitsFamily.masked(family.width, bits.toLong)
      )
      Result.assert(kit.sameValue(converted, made)).log(s"$converted, $made")
  }

  property(
    "a word's view holds the value's bits, the least significant first"
  ) {
    for
      width <- Gen.int(Range.linear(1, 66)).forAll
      topSet <- Gen.boolean.forAll
      bits <- bitsOf(width, topSet).forAll
      position <- Gen.int(Range.linear(0, width - 1)).forAll
    yield
      val kit = wordKit
      val storage = kit.stored(
        Representation.Data(WordFamily.identity, Some(WordWidth(width))),
        Word(width, bits)
      )
      val above = kit.projection(2, 1)
      val walked = (0 until position).foldLeft(storage)((word, _) =>
        kit.applied(word, above)
      )
      val expected = kit.booleanNormalForm(((bits >> position) & 1) == 1)
      Result
        .assert(
          kit
            .same(kit.read(kit.applied(walked, kit.projection(2, 0))), expected)
        )
        .log(s"word $width $bits at $position")
  }

  property("a binary natural's view holds its layers, the low bit outermost") {
    for
      canonical <- Gen.boolean.forAll
      drawn <- Gen.long(Range.linear(0L, 1L << 40)).forAll
      layer <- Gen.int(Range.linear(0, 41)).forAll
    yield
      val kit = binaryKit
      val number = BigInt(if canonical then drawn else drawn + 1)
      val storage = kit.stored(
        Representation.Data(
          BinaryNaturalFamily.identity,
          Some(BinaryCanonicity(canonical))
        ),
        BinaryNatural(number)
      )
      val half = kit.termValue(Term.λ(h => h))
      val depth = math.min(layer, number.bitLength)
      val walked = (0 until depth).foldLeft(storage)((natural, _) =>
        kit.applied(natural, kit.markers(0), half, half)
      )
      val atLayer = number >> depth
      val expected = if atLayer == 0 then kit.marker(0)
      else if atLayer % 2 == 0 then kit.marker(1)
      else kit.marker(2)
      Result
        .assert(
          kit.same(
            kit.read(
              kit.applied(
                walked,
                kit.markers(0),
                kit.constant(1),
                kit.constant(2)
              )
            ),
            expected
          )
        )
        .log(s"$number at layer $depth")
  }

  property("a natural's view holds its layers") {
    for
      number <- Gen.int(Range.linear(0, 30)).forAll
      layer <- Gen.int(Range.linear(0, 30)).forAll
    yield
      val kit = naturalKit
      val depth = math.min(layer, number)
      val storage = kit.stored(
        Representation.BigInteger,
        NativeValue.Natural(BigInt(number))
      )
      val predecessor = kit.termValue(Term.λ(p => p))
      val walked = (0 until depth).foldLeft(storage)((natural, _) =>
        kit.applied(natural, kit.markers(0), predecessor)
      )
      val expected = if depth == number then kit.marker(0) else kit.marker(1)
      val successorCase = kit.constant(1)
      val state = kit.fresh.copy(storages = Some(kit.option))
      Result
        .assert(
          kit.same(
            kit.normalForms(
              kit.applied(walked, kit.markers(0), successorCase),
              state
            ),
            expected
          )
        )
        .log(s"$number at layer $depth")
  }

  property("a list's view holds its cells in order and its items") {
    for
      items <- Gen.int(Range.linear(0, 8)).list(Range.linear(0, 6)).forAll
      layer <- Gen.int(Range.linear(0, 6)).forAll
      takeItem <- Gen.boolean.forAll
    yield
      val kit = naturalKit
      val zero = kit.library("zero")
      val successor = kit.library("successor")
      val plain = (count: Int) =>
        (1 to count).foldLeft(zero)((inner, _) => kit.apply(successor, inner))
      val storage = kit.stored(
        Representation.ListOf(kit.library("nat_type")),
        NativeValue.Listed(
          com.yang_bo.gezi.weakhead.ListRepresentation.Items(
            items.size,
            items.toVector.map(item =>
              kit.stored(
                Representation.BigInteger,
                NativeValue.Natural(BigInt(item))
              )
            )
          )
        )
      )
      val depth = math.min(layer, items.size)
      val rest = kit.projection(2, 1)
      val walked = (0 until depth).foldLeft(storage)((list, _) =>
        kit.applied(list, kit.markers(0), rest)
      )
      val state = kit.fresh.copy(storages = Some(kit.option))
      val (cons, expected) =
        if depth == items.size then (kit.constant(1), kit.marker(0))
        else if takeItem then
          (kit.projection(2, 0), kit.read(plain(items(depth))))
        else
          (
            kit.termValue(Term.λ(_ => Term.λ(_ => markerTerm(1)))),
            kit.marker(1)
          )
      Result
        .assert(
          kit.same(
            kit.normalForms(kit.applied(walked, kit.markers(0), cons), state),
            expected
          )
        )
        .log(s"$items at layer $depth")
  }

  property("a boolean's view is its case") {
    for truth <- Gen.boolean.forAll
    yield
      val kit = naturalKit
      val storage = kit.stored(Representation.Truth, NativeValue.Truth(truth))
      Result.assert(
        kit.same(
          kit.read(kit.applied(storage, kit.markers(0), kit.markers(1))),
          kit.marker(if truth then 0 else 1)
        )
      )
  }
