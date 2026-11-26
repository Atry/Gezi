package gezi.standardlibrary

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import io.bullet.borer.Dom
import io.bullet.borer.Tag
import java.nio.charset.StandardCharsets
import java.nio.file.Path
import gezi.directorysugar.DirectoryTree
import gezi.frontend.Defunctionalization
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Literal
import gezi.frontend.Literals
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Instruction
import gezi.knowledgereading.KnowledgeReading
import gezi.weakhead.Computed
import gezi.weakhead.Mode
import gezi.weakhead.ReadingState
import gezi.weakhead.Value
import gezi.weakhead.Values
import gezi.weakhead.WeakHead

/** The laws of the library's `from_cbor` and `to_cbor`: for each module, the binary naturals
  * (`binary/cbor`), the integers (`integer/cbor`), the texts (`text/cbor`),
  * the byte strings (`bytes/cbor`), the rationals (`rational/cbor`), the
  * booleans (`native_types/boolean_cbor`) and the lists of integers
  * (`prelude/list_cbor` over `integer/cbor`), on generated values. The
  * oracle is the front end: the literal of a value is the bytes borer writes
  * for the value's data item in its preferred serialization
  * (`Literal.integerElement`, `Literal.text`, borer's `Dom`), and its bits
  * reach the library only as the variable arguments and the variable
  * arguments partial function of that literal (`Literals.arguments`,
  * `Literals.partialFunction`), whose bits come from that one encoding.
  *
  * A probe is a closed term whose abstractions bind the tuples of the
  * library files it opens (`instances`, each the Scott tuple `λt. t f1 … fn`
  * of the file's fields, read once off its instance), applied to those
  * tuples, the tree's visible subtree being `corpora/library`; it opens a
  * file as `instance (λfrom_cbor. λto_cbor. λ_ … λ_. body)`. The library's
  * values are the Scott data the host builds (`Literals.naturalTerm` and the
  * others), and the booleans and the cells of a list are the library's own
  * (`native_types/boolean`, `prelude/list`). The bits `to_cbor` folds are
  * collected with `f = λb. λrest. λp. rest (p b)` and `z = λp. p`, so that
  * `to_cbor v f z P` is `P b1 … bn`. A reading is the tabled weak head that
  * knows top (`KnowledgeReading.knownExtremes`), its answer the set of parallel
  * sets read back to the IR, top reading as none. `marker` is a closed term
  * that no module gives, its own reading one parallel set.
  */
class CborCodecLawTest extends GeneratedProperties:

  // FIXME: not yet measured. The step limit of each reading is https://github.com/Atry/private-overlay/issues/1962
  // DirectoryTreeLawTest's (2,000,000), taken without a run of this suite
  // (written 2026-11-16 while no sbt server could be started); measure the
  // readings' steps and the suite's time at its first gate, set the limit
  // and, if a test needs more than the 3 s default, `munitTimeout` from the
  // measurement.
  private val limit: Long = 2000000

  /** The visible subtree: the library's directory, whose files import one
    * another through `corpora "library"`, `corpora` the one directory above
    * it they name.
    */
  private val visible: Path = LibraryFiles.sourceTree.resolve("library")

  /** The library files a probe opens: the path under `library` without its
    * extension and the number of fields of the tuple it returns.
    */
  private enum LibraryFile(val path: String, val fields: Int):
    case NaturalCodec extends LibraryFile("binary/cbor", 6)
    case IntegerCodec extends LibraryFile("integer/cbor", 2)
    case TextCodec extends LibraryFile("text/cbor", 4)
    case BytesCodec extends LibraryFile("bytes/cbor", 2)
    case RationalCodec extends LibraryFile("rational/cbor", 2)
    case BooleanCodec extends LibraryFile("native_types/boolean_cbor", 2)
    case ListCodec extends LibraryFile("prelude/list_cbor", 4)
    case Booleans extends LibraryFile("native_types/boolean", 4)
    case Lists extends LibraryFile("prelude/list", 5)

  /** The tuple of each library file, in the order of `LibraryFile`, read
    * once as the host reads an entry (`KnowledgeReading.tuplesTerm` of its
    * instance), so that its imports are read once and every probe shares
    * the result. A probe that applied the instance itself to its own
    * continuation would read the file's imports again for each probe, the
    * cost that `ExportFormStepsTest` records, which this suite does not test.
    */
  private val instances: Vector[(LibraryFile, Instruction)] =
    LibraryFile.values.toVector.map(file =>
      val instance = DirectoryTree.instance(visible, visible.resolve(file.path + DirectoryTree.fileExtension))
      file -> KnowledgeReading.run(KnowledgeReading.tuplesTerm(instance), limit, ReadingState.knowing(limit, KnowledgeReading.knownExtremes))._1
    )

  /** The CBOR item a literal is, as far as the modules tell items apart. */
  private enum ItemClass:
    case UnsignedIntegerItem, NegativeIntegerItem, TextStringItem, ByteStringItem, RationalItem, BooleanItem, ArrayItem

  /** A generated value of one module. */
  private enum Sample:
    case NaturalNumber(value: BigInt)
    case SignedInteger(value: BigInt)
    case TextString(value: String)
    case ByteString(value: Vector[Int])
    case RationalNumber(numerator: BigInt, denominator: BigInt)
    case BooleanValue(value: Boolean)
    case IntegerList(value: Vector[BigInt])

  import Sample.*
  import ItemClass.*

  /** The bytes of the values, each 0 to 255, as a byte array a JDK call
    * returns.
    */
  private def byteArray(values: Vector[Int]): Array[Byte] =
    java.util.HexFormat.of().parseHex(values.map(value => f"$value%02x").mkString)

  /** The literal of the sample: the bytes of its data item in its preferred
    * serialization, a rational as tag 30 over the array of its numerator and
    * denominator.
    */
  private def literal(sample: Sample): Literal = sample match
    case NaturalNumber(value)  => Literal.of(Literal.integerElement(value))
    case SignedInteger(value)  => Literal.of(Literal.integerElement(value))
    case TextString(value)     => Literal.text(value)
    case ByteString(value)     => Literal.of(Dom.ByteArrayElem(byteArray(value)))
    case RationalNumber(numerator, denominator) =>
      Literal.of(
        Dom.TaggedElem(Tag.Other(30), Dom.ArrayElem.Sized(Vector(Literal.integerElement(numerator), Literal.integerElement(denominator))))
      )
    case BooleanValue(value) => Literal.of(Dom.BooleanElem(value))
    case IntegerList(value)  => Literal.of(Dom.ArrayElem.Sized(value.map(Literal.integerElement)))

  private def itemClass(sample: Sample): ItemClass = sample match
    case NaturalNumber(_)       => UnsignedIntegerItem
    case SignedInteger(value)   => if value >= 0 then UnsignedIntegerItem else NegativeIntegerItem
    case TextString(_)          => TextStringItem
    case ByteString(_)          => ByteStringItem
    case RationalNumber(_, _)   => RationalItem
    case BooleanValue(_)        => BooleanItem
    case IntegerList(_)         => ArrayItem

  /** The items the module of the sample reads: an integer's module reads a
    * natural's item as well.
    */
  private def readItems(sample: Sample): Set[ItemClass] = sample match
    case SignedInteger(_) => Set(UnsignedIntegerItem, NegativeIntegerItem)
    case other            => Set(itemClass(other))

  /** A value of the sample's module other than the sample's, one more in
    * the last place: the argument after the sample's, an extra character, an
    * extra byte, a rational one greater, the other boolean, an extra
    * element.
    */
  private def neighbour(sample: Sample): Sample = sample match
    case NaturalNumber(value)                   => NaturalNumber(value + 1)
    case SignedInteger(value)                   => SignedInteger(value + 1)
    case TextString(value)                      => TextString(value + "a")
    case ByteString(value)                      => ByteString(value :+ 0)
    case RationalNumber(numerator, denominator) => RationalNumber(numerator + denominator, denominator)
    case BooleanValue(value)                    => BooleanValue(!value)
    case IntegerList(value)                     => IntegerList(value :+ BigInt(0))

  /** The term of the closed de Bruijn term. */
  private def closed(term: DeBruijnTerm): Term = Term.closed(Defunctionalization.thunkInstruction(term))

  /** The instance's first two fields handed to the body, the others unused:
    * `instance (λfirst. λsecond. λ_ … λ_. body)`.
    */
  private def firstTwo(instance: Term, fields: Int)(body: (Term, Term) => Term): Term =
    def unused(count: Int, inner: Term): Term = if count == 0 then inner else λ(_ => unused(count - 1, inner))
    instance(λ(first => λ(second => unused(fields - 2, body(first, second)))))

  /** The library value of the sample, under the instances. */
  private def libraryValue(sample: Sample, opened: Map[LibraryFile, Term]): Term = sample match
    case NaturalNumber(value) => closed(Literals.naturalTerm(value))
    case SignedInteger(value) => closed(Literals.integerTerm(value))
    case TextString(value) =>
      closed(Literals.textTerm(IArray.unsafeFromArray(value.getBytes(StandardCharsets.UTF_8))))
    case ByteString(value)                      => closed(Literals.textTerm(IArray.unsafeFromArray(byteArray(value))))
    case RationalNumber(numerator, denominator) => closed(Literals.rationalTerm(numerator, denominator))
    case BooleanValue(value) =>
      firstTwo(opened(LibraryFile.Booleans), LibraryFile.Booleans.fields)((truth, falsity) => if value then truth else falsity)
    case IntegerList(value) =>
      firstTwo(opened(LibraryFile.Lists), LibraryFile.Lists.fields)((nil, cons) =>
        value.foldRight(nil)((element, tail) => cons(closed(Literals.integerTerm(element)))(tail))
      )

  /** The `from_cbor` and `to_cbor` of the sample's module handed to the
    * body; for a list of integers, the list module's applied to the integer
    * module's.
    */
  private def codec(sample: Sample, opened: Map[LibraryFile, Term])(body: (Term, Term) => Term): Term =
    def of(file: LibraryFile): Term = firstTwo(opened(file), file.fields)(body)
    sample match
      case NaturalNumber(_)     => of(LibraryFile.NaturalCodec)
      case SignedInteger(_)     => of(LibraryFile.IntegerCodec)
      case TextString(_)        => of(LibraryFile.TextCodec)
      case ByteString(_)        => of(LibraryFile.BytesCodec)
      case RationalNumber(_, _) => of(LibraryFile.RationalCodec)
      case BooleanValue(_)      => of(LibraryFile.BooleanCodec)
      case IntegerList(_) =>
        firstTwo(opened(LibraryFile.IntegerCodec), LibraryFile.IntegerCodec.fields)((elementFrom, elementTo) =>
          firstTwo(opened(LibraryFile.ListCodec), LibraryFile.ListCodec.fields)((listFrom, listTo) =>
            body(listFrom(elementFrom), listTo(elementTo))
          )
        )

  /** `λx. x x`, the marker: a closed term no module gives. */
  private val markerTerm: DeBruijnTerm = λ(x => x(x)).deBruijnTerm(Map.empty)

  private val marker: Instruction = Defunctionalization.thunkInstruction(markerTerm)

  /** `λb. λrest. λp. rest (p b)`: the step of the fold that collects bits. */
  private val collected: Term = λ(bit => λ(rest => λ(applied => rest(applied(bit)))))

  /** `λp. p`: the end of the fold that collects bits. */
  private val collectedEnd: Term = λ(applied => applied)

  /** The variable arguments partial function of the literal, the marker its
    * body.
    */
  private def partialFunction(key: Literal): Term = closed(Literals.partialFunction(key, markerTerm))

  /** The term applied to the bits of the literal. */
  private def appliedToBits(function: Term, bits: Literal): Term =
    Literals.arguments(bits).foldLeft(function)((applied, bit) => applied(closed(bit)))

  /** The reading of the probe: its body under abstractions that bind the
    * library files' instances, applied to them.
    */
  private def probe(body: Map[LibraryFile, Term] => Term): Value =
    def bound(files: List[LibraryFile], opened: Map[LibraryFile, Term]): Term = files match
      case Nil          => body(opened)
      case file :: rest => λ(instance => bound(rest, opened.updated(file, instance)))
    val term = Defunctionalization.thunkInstruction(bound(instances.map(_._1).toList, Map.empty).deBruijnTerm(Map.empty))
    instances.foldLeft(term: Value) { case (function, (_, instance)) => Value.Apply(function, instance) }

  /** `to_cbor v f z` applied to the partial function of the key. */
  private def written(sample: Sample, key: Literal): Value =
    probe(opened => codec(sample, opened)((_, toCbor) => toCbor(libraryValue(sample, opened))(collected)(collectedEnd)(partialFunction(key))))

  /** `(from_cbor λx. to_cbor x f z) b1 … bn`, the bits of the sample's
    * literal, applied to the partial function of that literal.
    */
  private def roundTrip(sample: Sample): Value =
    probe(opened =>
      codec(sample, opened)((fromCbor, toCbor) =>
        appliedToBits(fromCbor(λ(read => toCbor(read)(collected)(collectedEnd))), literal(sample))(partialFunction(literal(sample)))
      )
    )

  /** `(from_cbor λx. marker) b1 … bn` of the reader's module, the bits of
    * the other sample's literal.
    */
  private def readAs(reader: Sample, other: Sample): Value =
    probe(opened => codec(reader, opened)((fromCbor, _) => appliedToBits(fromCbor(λ(_ => Term.closed(marker))), literal(other))))

  /** The answers of the reading read back to the IR under the state, and
    * the state after it; nothing when the budget stops it.
    */
  private def answersFrom(reading: Value, state: ReadingState): (Option[Set[Set[Instruction]]], ReadingState) =
    WeakHead.heads(Mode.TablingWeakHead, reading).collected.result(state) match
      case Computed.Done(sets, after) =>
        (
          Some(
            WeakHead
              .headsExpanded(Mode.TablingWeakHead, sets)
              .map(_.heads.map(head => Values.instruction(head.value)).toSet)
              .toSet
          ),
          after.nextReading(limit)
        )
      case Computed.Stopped(after) => (None, after.nextReading(limit))

  /** The readings in order under one state, each with a fresh budget, and
    * the state after them.
    */
  private def readInOrder(readings: Vector[Value], start: ReadingState): (Vector[Option[Set[Set[Instruction]]]], ReadingState) =
    readings.foldLeft((Vector.empty[Option[Set[Set[Instruction]]]], start)) { case ((found, state), reading) =>
      val (read, after) = answersFrom(reading, state)
      (found :+ read, after)
    }

  /** One sample of each module, at the smallest values. */
  private val smallest: Vector[Sample] =
    Vector(
      NaturalNumber(0),
      SignedInteger(-1),
      TextString(""),
      ByteString(Vector(0)),
      RationalNumber(0, 1),
      BooleanValue(true),
      IntegerList(Vector(BigInt(0)))
    )

  /** The state every input starts from: the readings of `written` and
    * `roundTrip` of the smallest sample of each module done, so that the
    * projection of the tree's root to the library, the expansions of the
    * files and the tables they share are read once, outside the tests'
    * time.
    */
  private lazy val warmed: ReadingState =
    readInOrder(
      smallest.flatMap(sample => Vector(written(sample, literal(sample)), roundTrip(sample))) :+ (marker: Value),
      ReadingState.knowing(limit, KnowledgeReading.knownExtremes)
    )._2

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => warmed)

  /** Naturals in the shapes of their heads: inline (below 24), one, two,
    * four and eight bytes, the bounds between them, and beyond 2^64, a tag 2
    * over a byte string.
    */
  private val magnitude: Gen[BigInt] =
    Gen.frequency1(
      3 -> Gen.long(Range.linear(0L, 30L)).map(BigInt(_)),
      2 -> Gen.element1(
        BigInt(23),
        BigInt(24),
        BigInt(255),
        BigInt(256),
        BigInt(65535),
        BigInt(65536),
        (BigInt(1) << 32) - 1,
        BigInt(1) << 32,
        (BigInt(1) << 64) - 1,
        BigInt(1) << 64
      ),
      2 -> Gen.long(Range.linear(0L, Long.MaxValue)).map(BigInt(_)),
      1 -> Gen.long(Range.linear(0L, Long.MaxValue)).map(low => (BigInt(1) << 63) + low),
      2 -> (for
        shift <- Gen.int(Range.linear(64, 80))
        low <- Gen.long(Range.linear(0L, Long.MaxValue))
      yield (BigInt(1) << shift) + low)
    )

  private val integer: Gen[BigInt] =
    for
      size <- magnitude
      negative <- Gen.boolean
    yield if negative then -size - 1 else size

  private val naturalSample: Gen[Sample] = magnitude.map(NaturalNumber(_))

  private val integerSample: Gen[Sample] = integer.map(SignedInteger(_))

  /** Texts of a few characters, of one to three UTF-8 bytes each, and
    * texts of 20 to 26 ASCII characters, whose lengths cross the 24 of an
    * inline length.
    */
  private val textSample: Gen[Sample] =
    Gen
      .frequency1(
        3 -> Gen.string(Gen.unicode, Range.linear(0, 3)),
        1 -> Gen.string(Gen.alphaNum, Range.linear(20, 26))
      )
      .map(TextString(_))

  /** Byte strings of up to four bytes, the byte 0 frequent among them. */
  private val bytesSample: Gen[Sample] =
    Gen
      .frequency1(1 -> Gen.constant(0), 3 -> Gen.int(Range.linear(0, 255)))
      .list(Range.linear(0, 4))
      .map(values => ByteString(values.toVector))

  /** Rationals in lowest terms with a positive denominator. */
  private val rationalSample: Gen[Sample] =
    for
      numerator <- integer
      denominator <- magnitude.map(_ + 1)
    yield
      val divisor = numerator.gcd(denominator)
      RationalNumber(numerator / divisor, denominator / divisor)

  private val booleanSample: Gen[Sample] = Gen.boolean.map(BooleanValue(_))

  private val listSample: Gen[Sample] = integer.list(Range.linear(0, 3)).map(values => IntegerList(values.toVector))

  /** One sample of each module, each with another sample of its module
    * whose literal differs: a second draw, or the first's neighbour when the
    * second draw has its literal.
    */
  private val samples: Gen[Vector[(Sample, Sample)]] =
    Vector(naturalSample, integerSample, textSample, bytesSample, rationalSample, booleanSample, listSample)
      .foldLeft(Gen.constant(Vector.empty[(Sample, Sample)])) { (drawn, generator) =>
        for
          before <- drawn
          sample <- generator
          second <- generator
        yield before :+ ((sample, if literal(second) == literal(sample) then neighbour(sample) else second))
      }

  /** Catches a `to_cbor` whose bits are not the front end's encoding of the
    * value: a head with the wrong major type or a non-shortest argument, a
    * big-endian number written low byte first or with a leading zero byte, a
    * length or a count that is not the payload's, a tag 2 or 3 written below
    * 2^64, a negative integer written as −n instead of −1 − n, a bit order
    * reversed within a byte, a rational's tag or array head wrong, a boolean
    * swapped. The value's `to_cbor` applied to the partial function of the
    * value's literal reads what the marker reads, one parallel set; applied
    * to the partial function of another value's literal of the same module,
    * nothing.
    */
  property("to_cbor writes the front end's encoding of the value", _.copy(testLimit = 8)) {
    for drawn <- samples.forAll
    yield
      val (markerRead, start) = answersFrom(marker, warmed)
      val (results, _) = drawn.foldLeft((List.empty[Result], start)) { case ((done, state), (sample, other)) =>
        val (matched, afterMatched) = answersFrom(written(sample, literal(sample)), state)
        val (missed, afterMissed) = answersFrom(written(sample, literal(other)), afterMatched)
        val result = Result
          .all(
            List(
              Result.diff(matched, markerRead)(_ == _),
              Result.assert(missed.exists(_.isEmpty)).log(s"against ${literal(other)}: $missed")
            )
          )
          .log(s"$sample, ${literal(sample)}")
        (done :+ result, afterMissed)
      }
      Result.all(Result.assert(markerRead.exists(_.size == 1)).log(s"the marker: $markerRead") :: results)
  }

  /** Catches a `from_cbor` that does not read back what `to_cbor` writes, or
    * reads the front end's literal into another value: a byte or an item
    * read too many or too few (counts by halves), a big-endian number
    * accumulated in the wrong order or with an even over zero left at its
    * top, a negative integer read as −n, a list's elements or a text's bytes
    * reversed. `from_cbor` of the bits of the value's literal, continued
    * with `to_cbor`, applied to the partial function of that literal, reads
    * what the marker reads.
    */
  property("from_cbor of a literal is read back by to_cbor", _.copy(testLimit = 8)) {
    for drawn <- samples.forAll
    yield
      val (markerRead, start) = answersFrom(marker, warmed)
      val (reads, _) = readInOrder(drawn.map((sample, _) => roundTrip(sample)), start)
      Result.all(
        Result.assert(markerRead.exists(_.size == 1)).log(s"the marker: $markerRead") ::
          drawn.zip(reads).toList.map { case ((sample, _), read) =>
            Result.diff(read, markerRead)(_ == _).log(s"$sample, ${literal(sample)}")
          }
      )
  }

  /** Catches a `from_cbor` that takes an item of another kind for its own:
    * a major type or a tag whose bits are dispatched wrongly, a simple value
    * read as an integer, a byte string as a text. Each module's `from_cbor`,
    * continued with the marker, applied to the bits of the literal of a
    * sample whose item it does not read (an integer's module reads a
    * natural's item, so that pair is left out), reads nothing.
    */
  property("from_cbor reads nothing of another kind's literal", _.copy(testLimit = 8)) {
    for drawn <- samples.forAll
    yield
      val pairs = for
        (reader, _) <- drawn
        (other, _) <- drawn
        if !readItems(reader).contains(itemClass(other))
      yield (reader, other)
      val (reads, _) = readInOrder(pairs.map((reader, other) => readAs(reader, other)), warmed)
      Result.all(pairs.zip(reads).toList.map { case ((reader, other), read) =>
        Result.assert(read.exists(_.isEmpty)).log(s"$reader reading ${literal(other)}: $read")
      })
  }
