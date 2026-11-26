package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Configured
import gezi.ir.NativeSpecializer.*
import gezi.ir.NoFacts
import gezi.ir.NonEmptyHoles
import gezi.ir.StorageAccess

/** The law of a long list in the exchange format: a list of thousands of cells
  * whose elements each occur twice, so that the printer binds each of them,
  * is written and read back as itself within the deadline. Its purpose is to
  * catch a readback whose cost is quadratic in a list's length, as joining the
  * maps of the shared terms along the right spine was.
  */
class ExchangeTextLongListLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts
  given StorageAccess = StorageAccess.granted()

  private type NoFactsTerm = Configured[NoFacts.type]

  private def thunkOf(code: Code, holes: Vector[Hole]): NoFactsTerm =
    NoFacts.thunk(code, NonEmptyHoles.of(holes).getOrElse(throw IllegalArgumentException("a thunk of no hole")), Vector.empty)

  // Measured on 2 CPUs under load 8 to 15: at 24,000 cells, after the JVM warmed up, the line
  // takes 1.6 s and reading it back 3.1 s, and with the quadratic join the line alone took
  // 46 s. The whole test in a fresh test JVM took 8.8 s.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(20, "s")

  /** The cells of the list, the elements being half as many. */
  private val cells: Int = 24000

  /** λn c. n. */
  private val nil: NoFactsTerm = thunkOf(Code.Slot(0), Vector(Hole.Bound(0), Hole.Ignored))

  /** λh t n c. c h t. */
  private val cons: NoFactsTerm = thunkOf(
    Code.Apply(Code.Apply(Code.Slot(0), Code.Slot(1)), Code.Slot(2)),
    Vector(Hole.Bound(1), Hole.Bound(2), Hole.Ignored, Hole.Bound(0))
  )

  /** λh x y. x h. */
  private val zeroBit: NoFactsTerm =
    thunkOf(Code.Apply(Code.Slot(0), Code.Slot(1)), Vector(Hole.Bound(1), Hole.Bound(0), Hole.Ignored))

  /** λh x y. y h. */
  private val oneBit: NoFactsTerm =
    thunkOf(Code.Apply(Code.Slot(0), Code.Slot(1)), Vector(Hole.Bound(1), Hole.Ignored, Hole.Bound(0)))

  /** A closed term of the value's bits, different for different values. */
  private def element(value: Int): NoFactsTerm =
    (0 until 14).foldLeft(nil)((rest, bit) => NoFacts.application(if ((value >> bit) & 1) == 1 then oneBit else zeroBit, rest))

  /** The list whose cell at each place holds the element that the odd
    * multiplier sends the place to, each element occurring twice.
    */
  private def list(multiplier: Int): NoFactsTerm =
    val elements = cells / 2
    val shared = Vector.tabulate(elements)(element)
    (0 until cells).foldRight(nil)((place, tail) =>
      NoFacts.application(NoFacts.application(cons, shared(((place.toLong * multiplier) % elements).toInt)), tail)
    )

  property("a long list of shared elements is written and read back as itself", _.copy(testLimit = 1)) {
    for multiplier <- Gen.int(Range.constant(0, 1000)).map(_ * 2 + 1).forAll
    yield
      val written = list(multiplier)
      Result.diff(ExchangeText.term[NoFacts.type](ExchangeText.line(written)).map(Configured.same(_, written)), Right(true))(_ == _)
  }
