package gezi.weakhead

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import io.bullet.borer.Dom
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Literal
import gezi.frontend.Literals
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.weakhead.EvaluatorTesting.*

/** The law of the variable arguments partial function of a literal
  * (`Literals.partialFunction`), on generated literals and generated closed bodies,
  * under `weak_head` and `tabling(weak_head)`: `(λL. M) L′`, L′ spread into
  * the bits of its bytes (`Literals.arguments`), reads what M reads when L′
  * is L, and reads ∅ when L′ is another literal, since the first bit that
  * differs gives top, top applied to the bits left is top, and no CBOR item's
  * encoding is a proper prefix of another's. The literals are drawn from few
  * values of several kinds mixed (text strings, integers of both signs, byte
  * strings, arrays), so that equal and distinct pairs both occur, of equal
  * and of different lengths. Its purpose is to catch a partial function that
  * takes a literal for another (a bit tested in the wrong sense or skipped, a
  * key taken for its prefix), one that misses the literal it was built for,
  * or one whose body's free variables point at the wrong binder after the
  * bits put it under their abstractions.
  */
class LiteralPartialFunctionLawTest extends GeneratedProperties:

  private val modes = Vector(Mode.WeakHead, Mode.TablingWeakHead)

  private val limit: Long = 20000

  private val closed = HoasGenerators.closedTerm

  private val text: Gen[Literal] =
    Gen.element1('a', 'b', 'é').list(Range.constant(0, 2)).map(characters => Literal.text(characters.mkString))

  private val integer: Gen[Literal] =
    Gen.int(Range.constant(-3, 3)).map(value => Literal.of(Dom.LongElem(value.toLong)))

  private val byteString: Gen[Literal] =
    Gen.element1("", "00", "61", "ff").map(hexadecimal => Literal.of(Dom.ByteArrayElem(java.util.HexFormat.of().parseHex(hexadecimal))))

  private val array: Gen[Literal] =
    Gen.int(Range.constant(0, 2)).list(Range.constant(0, 2)).map(items =>
      Literal.of(Dom.ArrayElem.Sized(items.map(item => Dom.LongElem(item.toLong): Dom.Element).toVector))
    )

  private val literals: Gen[Literal] = Gen.choice1(text, integer, byteString, array)

  private def valueOfTerm(term: DeBruijnTerm): Value =
    Values.ofInstruction(Defunctionalization.thunkInstruction(term), Set.empty)

  property("the partial function of a literal answers its literal only") {
    for
      key <- literals.forAll
      argument <- literals.forAll
      body <- closed.forAll
    yield
      val bodyTerm = lambdaTerm(body)
      val applied =
        Literals.arguments(argument).foldLeft(Literals.partialFunction(key, bodyTerm))(DeBruijnTerm.Apply(_, _))
      Result.all(modes.toList.map(mode =>
        normalFormsWithin(mode, valueOfTerm(bodyTerm), limit) match
          case Bounded.Finished(alone) =>
            val expected = if key == argument then alone.toSet else Set.empty
            normalFormsWithin(mode, valueOfTerm(applied), 4 * limit) match
              case Bounded.Finished(read) => Result.diff(read.toSet, expected)(_ == _).log(s"under $mode")
              case other                  => Result.failure.log(s"under $mode the application did not finish: $other")
          case _ => Result.success
      ))
  }
