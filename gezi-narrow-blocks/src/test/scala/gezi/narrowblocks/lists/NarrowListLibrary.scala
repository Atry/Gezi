package gezi.narrowblocks
package lists

import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Pure
import gezi.jit.BooleanFamily
import gezi.jit.NativesProvider
import gezi.jit.Representation
import gezi.standardlibrary.CombinatorProperty
import gezi.standardlibrary.NativeBound
import gezi.standardlibrary.Property
import gezi.standardlibrary.StandardLibraryIndex
import gezi.ir.{Configured, NativeSpecializer}

private given narrowListLibraryNoFacts: NoFacts.type = NoFacts

/** A library of the narrow lists' and booleans' laws, its names bound by hand,
  * as in `NarrowBlockSumLawTest`: the binary naturals' constructors, plus,
  * increment and equality by `native` declarations, `binary_set` by its
  * `native_specialization`, `list_type` by its `native_specialization` naming
  * the framework's list representation and its `data_family` naming nil and
  * cons, `boolean_type` by its `native_specialization` naming the boolean
  * family; and the compilation over it.
  */
object NarrowListLibrary:

  private def thunk[C <: NativeSpecializer & Singleton](code: Code, holes: Int)(
      using C
  ): Configured[C] =
    NoFacts.thunkOrInstance(
      code,
      (0 until holes).map(Hole.Bound(_)).toVector,
      Vector.empty
    )

  private def slot(index: Int): Code = Code.Slot(index)

  private def applied(function: Code, arguments: Code*): Code =
    arguments.foldLeft(function)(Code.Apply(_, _))

  /** λx. x x, bound to zero. */
  val zero: Configured[NoFacts.type] = thunk(applied(slot(0), slot(0)), 1)

  /** λx y. y x, bound to even. */
  val even: Configured[NoFacts.type] = thunk(applied(slot(1), slot(0)), 2)

  /** λx y z. z y x, bound to odd. */
  val odd: Configured[NoFacts.type] =
    thunk(applied(slot(2), slot(1), slot(0)), 3)

  /** λx y. y y x, bound to plus. */
  val plus: Configured[NoFacts.type] =
    thunk(applied(slot(1), slot(1), slot(0)), 2)

  /** λt f. t, the boolean true, and nil, the same term. */
  val truth: Configured[NoFacts.type] = NoFacts.thunkOrInstance(
    slot(0),
    Vector(Hole.Bound(0), Hole.Ignored),
    Vector.empty
  )

  /** λt f. f, the boolean false. */
  val falsity: Configured[NoFacts.type] = NoFacts.thunkOrInstance(
    slot(0),
    Vector(Hole.Ignored, Hole.Bound(0)),
    Vector.empty
  )

  /** λn c. n, nil, the term of true. */
  val nil: Configured[NoFacts.type] = truth

  /** λh t n c. c h t, cons. */
  val cons: Configured[NoFacts.type] =
    thunk(applied(slot(3), slot(0), slot(1)), 4)

  /** λx y. x (y y), bound to binary_set by its native_specialization. */
  val binarySet: Configured[NoFacts.type] =
    thunk(applied(slot(0), applied(slot(1), slot(1))), 2)

  /** λx. x (x x), bound to list_type by its native_specialization. */
  val listType: Configured[NoFacts.type] =
    thunk(applied(slot(0), applied(slot(0), slot(0))), 1)

  /** λx. x x x, bound to increment. */
  val increment: Configured[NoFacts.type] =
    thunk(applied(slot(0), slot(0), slot(0)), 1)

  /** λx y. x y y, bound to equality, whose result is a boolean. */
  val equality: Configured[NoFacts.type] =
    thunk(applied(slot(0), slot(1), slot(1)), 2)

  /** λx. x x (x x), bound to boolean_type by its native_specialization naming
    * the standard set's boolean family.
    */
  val booleanType: Configured[NoFacts.type] =
    thunk(applied(applied(slot(0), slot(0)), applied(slot(0), slot(0))), 1)

  /** The compilation over the library with the list's constructors bound to the
    * terms given, and the further properties.
    */
  private def compilationOf[C <: NativeSpecializer & Singleton](
      boundNil: Configured[C],
      boundCons: Configured[C],
      further: Vector[CombinatorProperty]
  )(using C): NarrowBlockCompilation = NarrowBlockCompilation(
    StandardLibraryIndex(
      NoFacts,
      Vector.empty,
      Vector.empty,
      Vector(
        NativeBound(Pure.required(plus), "wren_binary_plus"),
        NativeBound(Pure.required(increment), "wren_binary_increment"),
        NativeBound(Pure.required(equality), "wren_binary_equality")
      ),
      Vector(
        CombinatorProperty(
          Pure.required(binarySet),
          Property.NativeSpecialization("binary_natural")
        ),
        CombinatorProperty(
          Pure.required(binarySet),
          Property.DataFamily(0, Vector(zero, even, odd).map(Pure.required))
        ),
        CombinatorProperty(
          Pure.required(booleanType),
          Property.NativeSpecialization(BooleanFamily.identity.name)
        ),
        CombinatorProperty(
          Pure.required(listType),
          Property.NativeSpecialization(Representation.listFamily.name)
        ),
        CombinatorProperty(
          Pure.required(listType),
          Property.DataFamily(1, Vector(boundNil, boundCons).map(Pure.required))
        )
      ) ++ further
    ),
    NativesProvider.loaded,
    gezi.weakhead.ReadingConfiguration.withoutFacts
  )

  val compilation: NarrowBlockCompilation =
    compilationOf(nil, cons, Vector.empty)

  /** λx. (λy. y) x, a noinline marker that reads as the identity, as the
    * library's `$constructor` does.
    */
  val marker: Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      applied(slot(0), slot(1)),
      Vector(Hole.Bound(1)),
      Vector(thunk(slot(0), 1))
    )

  /** nil under the marker. */
  val markedNil: Configured[NoFacts.type] = NoFacts.application(marker, nil)

  /** cons under the marker. */
  val markedCons: Configured[NoFacts.type] = NoFacts.application(marker, cons)

  /** The compilation with the list's constructors bound under the marker. */
  val markedCompilation: NarrowBlockCompilation =
    compilationOf(
      markedNil,
      markedCons,
      Vector(CombinatorProperty(Pure.required(marker), Property.Noinline))
    )

  /** The canonical binary numeral of the value, least significant digit
    * outermost.
    */
  def numeral[C <: NativeSpecializer & Singleton](
      value: Int
  )(using C): Configured[C] =
    if value == 0 then zero
    else
      NoFacts.application(
        if (value & 1) == 1 then odd else even,
        numeral(value >> 1)
      )

  /** `even field` as its normal form, λy. y field, written as the front end
    * spells it: the binder at slot 0 and the field at slot 1.
    */
  def evenNormalForm[C <: NativeSpecializer & Singleton](
      field: Configured[C]
  )(using C): Configured[C] =
    NoFacts.thunkOrInstance(
      applied(slot(0), slot(1)),
      Vector(Hole.Bound(0)),
      Vector(field)
    )

  /** `odd field` as its normal form, λy z. z y field, spelled the same way. */
  def oddNormalForm[C <: NativeSpecializer & Singleton](
      field: Configured[C]
  )(using C): Configured[C] =
    NoFacts.thunkOrInstance(
      applied(slot(0), slot(1), slot(2)),
      Vector(Hole.Bound(1), Hole.Bound(0)),
      Vector(field)
    )

  /** `cons element tail` as its normal form, λn c. c element tail, spelled the
    * same way.
    */
  def consNormalForm[C <: NativeSpecializer & Singleton](
      element: Configured[C],
      tail: Configured[C]
  )(using C): Configured[C] =
    NoFacts.thunkOrInstance(
      applied(slot(0), slot(1), slot(2)),
      Vector(Hole.Ignored, Hole.Bound(0)),
      Vector(element, tail)
    )

  /** `binary_set p`. */
  def criterion[C <: NativeSpecializer & Singleton](
      admitsZero: Boolean
  )(using C): Configured[C] =
    NoFacts.application(binarySet, if admitsZero then truth else falsity)

  /** `list_type (binary_set p)`. */
  def listCriterion[C <: NativeSpecializer & Singleton](admitsZero: Boolean)(
      using C
  ): Configured[C] = NoFacts.application(listType, criterion(admitsZero))

  /** The list of the elements, each written as a numeral or as a numeral
    * filtered by `binary_set true`.
    */
  def list[C <: NativeSpecializer & Singleton](
      elements: Vector[(Int, Boolean)]
  )(using C): Configured[C] = tailsFiltered(elements, Map.empty)

  /** The list of the elements, written as `list` writes them, each tail at
    * whose place `filters` holds an entry filtered by `list_type (binary_set
    * p)` of that entry, the tail after the first element at place 1 and nil at
    * the list's length; the list itself at place 0 is not filtered here.
    */
  def tailsFiltered[C <: NativeSpecializer & Singleton](
      elements: Vector[(Int, Boolean)],
      filters: Map[Int, Boolean]
  )(using C): Configured[C] =
    elements.indices.foldRight(nil)((place, rest) =>
      val (value, filtered) = elements(place)
      val written =
        if filtered then NoFacts.parallel(numeral(value), criterion(true))
        else numeral(value)
      val tail = filters
        .get(place + 1)
        .fold(rest)(admitsZero =>
          NoFacts.parallel(rest, listCriterion(admitsZero))
        )
      NoFacts.application(NoFacts.application(cons, written), tail)
    )
