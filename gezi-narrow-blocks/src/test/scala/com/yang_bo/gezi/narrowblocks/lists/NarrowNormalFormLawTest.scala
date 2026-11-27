package com.yang_bo.gezi.narrowblocks
package lists

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts

private given narrowNormalFormLawTestNoFacts: NoFacts.type = NoFacts

/** The law of a literal written as its constructors' normal forms: a natural or
  * a filtered list decodes to the same value whichever spelling each of its
  * cells has, the constructor applied to its fields or the normal form that
  * application reduces to, and a term outside the family is refused in both
  * spellings. Its purpose is to catch a field read from the wrong filling, a
  * cell of one constructor read as another, a non-canonical numeral or an
  * unreduced field let through by the normal form's route, and a list decoded
  * with no filter at its root. The library is `NarrowListLibrary`'s.
  */
class NarrowNormalFormLawTest extends GeneratedProperties:

  import NarrowListLibrary.*

  /** A natural up to six bits. */
  private val number: Gen[Int] = Gen.int(Range.constant(0, 63))

  /** Which spelling each cell takes, read in turn and repeated. */
  private val spellings: Gen[Vector[Boolean]] =
    Gen.list(Gen.boolean, Range.linear(1, 8)).map(_.toVector)

  /** The spelling of the cell at the place. */
  private def spelledAsNormalForm(
      chosen: Vector[Boolean],
      place: Int
  ): Boolean = chosen(place % chosen.size)

  /** The canonical numeral of the value, each cell in the chosen spelling. */
  private def mixedNumeral(
      value: Int,
      chosen: Vector[Boolean],
      place: Int
  ): Configured[NoFacts.type] =
    if value == 0 then zero
    else
      val field = mixedNumeral(value >> 1, chosen, place + 1)
      ((value & 1) == 1, spelledAsNormalForm(chosen, place)) match
        case (true, true)   => oddNormalForm(field)
        case (true, false)  => NoFacts.application(odd, field)
        case (false, true)  => evenNormalForm(field)
        case (false, false) => NoFacts.application(even, field)

  /** The list of the values, each cell and element in the chosen spelling. */
  private def mixedList(
      values: Vector[Int],
      chosen: Vector[Boolean]
  ): Configured[NoFacts.type] =
    values.indices.foldRight(nil)((place, tail) =>
      val element = mixedNumeral(values(place), chosen, place)
      if spelledAsNormalForm(chosen, place) then consNormalForm(element, tail)
      else NoFacts.application(NoFacts.application(cons, element), tail)
    )

  stoppableProperty(
    "a natural decodes to its value in every mix of constructors and normal forms"
  ) { _ =>
    for
      value <- number.forAll
      chosen <- spellings.forAll
    yield Result.diff(
      compilation.constant(mixedNumeral(value, chosen, 0)),
      Some(NarrowConstant.Natural(BigInt(value)))
    )(_ == _)
  }

  stoppableProperty(
    "a list decodes to its elements in every mix of spellings, and only under a filter at its root"
  ) { _ =>
    for
      values <- Gen.list(number, Range.linear(0, 6)).map(_.toVector).forAll
      chosen <- spellings.forAll
    yield
      val written = mixedList(values, chosen)
      Result.all(
        List(
          Result.diff(
            compilation.listDecoded(
              NoFacts.parallel(written, listCriterion(true))
            ),
            Some(
              NarrowList(
                values.map(value => BigInteger.valueOf(value.toLong)),
                0
              )
            )
          )(_ == _),
          Result
            .diff(compilation.listDecoded(written), None)(_ == _)
            .log("with no filter at its root")
        )
      )
  }

  stoppableProperty(
    "constructors bound under a noinline marker read both spellings as the bare ones do"
  ) { _ =>
    for
      values <- Gen.list(number, Range.linear(0, 6)).map(_.toVector).forAll
      chosen <- spellings.forAll
    yield
      val end =
        if spelledAsNormalForm(chosen, values.size) then nil else markedNil
      val written = values.indices.foldRight(end)((place, tail) =>
        val element = mixedNumeral(values(place), chosen, place)
        if spelledAsNormalForm(chosen, place) then consNormalForm(element, tail)
        else NoFacts.application(NoFacts.application(markedCons, element), tail)
      )
      Result.diff(
        markedCompilation.listDecoded(
          NoFacts.parallel(written, listCriterion(true))
        ),
        Some(
          NarrowList(values.map(value => BigInteger.valueOf(value.toLong)), 0)
        )
      )(_ == _)
  }

  /** λy. field y: the even cell's parts in the other order, of another code. */
  private def lookalike(
      field: Configured[NoFacts.type]
  ): Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Slot(1), Code.Slot(0)),
      Vector(Hole.Bound(0)),
      Vector(field)
    )

  stoppableProperty("a term outside the family is refused in both spellings") {
    _ =>
      for positive <- Gen.int(Range.constant(1, 63)).forAll
      yield
        val field = numeral(positive)
        val unreduced =
          NoFacts.application(NoFacts.application(plus, field), field)
        val refused = Vector(
          "even of zero, by the constructor" -> NoFacts.application(even, zero),
          "even of zero, as a normal form" -> evenNormalForm(zero),
          "even of an unreduced call, by the constructor" -> NoFacts
            .application(even, unreduced),
          "even of an unreduced call, as a normal form" -> evenNormalForm(
            unreduced
          ),
          "another code with the same parts" -> lookalike(field)
        )
        val refusedLists = Vector(
          "an unreduced element, by the constructor" -> NoFacts
            .application(NoFacts.application(cons, unreduced), nil),
          "an unreduced element, as a normal form" -> consNormalForm(
            unreduced,
            nil
          ),
          "a tail that is no list, by the constructor" -> NoFacts
            .application(NoFacts.application(cons, field), field),
          "a tail that is no list, as a normal form" -> consNormalForm(
            field,
            numeral(positive + 1)
          ),
          "cons of one field" -> NoFacts.application(cons, field)
        )
        Result.all(
          refused.toList.map((name, term) =>
            Result.diff(compilation.constant(term), None)(_ == _).log(name)
          ) ++
            refusedLists.toList.map((name, term) =>
              Result
                .diff(
                  compilation.listDecoded(
                    NoFacts.parallel(term, listCriterion(true))
                  ),
                  None
                )(_ == _)
                .log(name)
            )
        )
  }
