package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.weakhead.Shape
import gezi.generatedinputs.GeneratedProperties

/** The law of the family `word` (`WordFamily`):
  * at every width w, 64 and
  * above included, and every word of that width, `built` after `taken` is
  * the identity, and the layer `taken` gives has the fields its one
  * constructor at w declares, the word above it at the parameter w - 1 that
  * the field gives. Its purpose is to catch a codec that loses or moves a
  * bit, and one whose field parameters disagree with the values it hands
  * out. The shape check at the family's two parameters accepts the library's
  * word_cell and word_end, read as members of `JitTesting.libraryTermsFile`,
  * and rejects either in the other's place, so a wrong term for word_cell or
  * word_end fails it.
  */
class WordFamilyLawTest extends GeneratedProperties:

  /** The library terms word_cell and word_end are read from, forced before the first test and not charged to it (FailFastSuite). */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => JitTesting.libraryTerms)

  private val word: Gen[Word] =
    for
      width <- Gen.int(Range.linear(0, 200))
      bits <- Gen.list(Gen.boolean, Range.singleton(width))
    yield Word(width, bits.zipWithIndex.foldLeft(BigInt(0)) { case (sum, (set, position)) => if set then sum.setBit(position) else sum })

  property("built after taken is the identity at each width, with the fields the constructor declares") {
    for value <- word.forAll
    yield
      val parameter = Some(NativeValue.Natural(value.width))
      val layer = WordFamily.taken(parameter, value)
      val constructor = WordFamily.constructors(parameter)(layer.constructor)
      val declared = constructor.fields.map(field =>
        field.representation(parameter) match
          case Representation.Data(family, fieldParameter) => (family, fieldParameter)
          case other                                       => (other.familyIdentity, None)
      )
      val found = layer.fields.map {
        case Word(width, _)       => (WordFamily.identity, Some(NativeValue.Natural(width)))
        case NativeValue.Truth(_) => (BooleanFamily.identity, None)
        case other                => (FamilyIdentity.Codec("unknown"), Some(other))
      }
      Result.all(
        List(
          Result.diff(WordFamily.built(parameter, layer), value)(_ == _),
          Result.diff(found, declared)(_ == _),
          Result.diff(WordFamily.constructors(parameter).size, 1)(_ == _)
        )
      )
  }

  test("the shape check accepts fixed_width's constructors and rejects either in the other's place") {
    val end = JitTesting.libraryTerms("word_end")
    val cell = JitTesting.libraryTerms("word_cell")
    val atZero = Some(NativeValue.Natural(0))
    val atOne = Some(NativeValue.Natural(1))
    assertEquals(WordFamily.constructorsShape(atZero, Vector(end)), Shape.Fits)
    assertEquals(WordFamily.constructorsShape(atOne, Vector(cell)), Shape.Fits)
    assertNotEquals(WordFamily.constructorsShape(atOne, Vector(end)), Shape.Fits)
    assertNotEquals(WordFamily.constructorsShape(atZero, Vector(cell)), Shape.Fits)
  }
