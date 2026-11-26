package gezi.narrowblocks
package lists

import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Instruction
import gezi.jit.BooleanFamily
import gezi.jit.NativesProvider
import gezi.jit.Representation
import gezi.standardlibrary.CombinatorProperty
import gezi.standardlibrary.NativeBound
import gezi.standardlibrary.Property
import gezi.standardlibrary.StandardLibraryIndex

/** A library of the narrow lists' and booleans' laws, its names bound by
  * hand, as in `NarrowBlockSumLawTest`: the binary naturals' constructors,
  * plus, increment and equality by `native` declarations, `binary_set` by
  * its `native_specialization`, `list_type` by its `native_specialization`
  * naming the framework's list representation and its `data_family` naming
  * nil and cons, `boolean_type` by its `native_specialization` naming the
  * boolean family; and the compilation over it.
  */
object NarrowListLibrary:

  private def thunk(code: Code, holes: Int): Instruction =
    Instruction.Thunk(code, (0 until holes).map(Hole.Bound(_)).toVector, Vector.empty)

  private def slot(index: Int): Code = Code.Slot(index)

  private def applied(function: Code, arguments: Code*): Code = arguments.foldLeft(function)(Code.Apply(_, _))

  /** λx. x x, bound to zero. */
  val zero: Instruction = thunk(applied(slot(0), slot(0)), 1)

  /** λx y. y x, bound to even. */
  val even: Instruction = thunk(applied(slot(1), slot(0)), 2)

  /** λx y z. z y x, bound to odd. */
  val odd: Instruction = thunk(applied(slot(2), slot(1), slot(0)), 3)

  /** λx y. y y x, bound to plus. */
  val plus: Instruction = thunk(applied(slot(1), slot(1), slot(0)), 2)

  /** λt f. t, the boolean true, and nil, the same term. */
  val truth: Instruction = Instruction.Thunk(slot(0), Vector(Hole.Bound(0), Hole.Ignored), Vector.empty)

  /** λt f. f, the boolean false. */
  val falsity: Instruction = Instruction.Thunk(slot(0), Vector(Hole.Ignored, Hole.Bound(0)), Vector.empty)

  /** λn c. n, nil, the term of true. */
  val nil: Instruction = truth

  /** λh t n c. c h t, cons. */
  val cons: Instruction = thunk(applied(slot(3), slot(0), slot(1)), 4)

  /** λx y. x (y y), bound to binary_set by its native_specialization. */
  val binarySet: Instruction = thunk(applied(slot(0), applied(slot(1), slot(1))), 2)

  /** λx. x (x x), bound to list_type by its native_specialization. */
  val listType: Instruction = thunk(applied(slot(0), applied(slot(0), slot(0))), 1)

  /** λx. x x x, bound to increment. */
  val increment: Instruction = thunk(applied(slot(0), slot(0), slot(0)), 1)

  /** λx y. x y y, bound to equality, whose result is a boolean. */
  val equality: Instruction = thunk(applied(slot(0), slot(1), slot(1)), 2)

  /** λx. x x (x x), bound to boolean_type by its native_specialization
    * naming the standard set's boolean family.
    */
  val booleanType: Instruction = thunk(applied(applied(slot(0), slot(0)), applied(slot(0), slot(0))), 1)

  val compilation: NarrowBlockCompilation = NarrowBlockCompilation(
    StandardLibraryIndex(
      Vector.empty,
      Vector.empty,
      Vector(
        NativeBound(zero, "binary_zero"),
        NativeBound(even, "binary_even"),
        NativeBound(odd, "binary_odd"),
        NativeBound(plus, "wren_binary_plus"),
        NativeBound(increment, "wren_binary_increment"),
        NativeBound(equality, "wren_binary_equality")
      ),
      Vector(
        CombinatorProperty(binarySet, Property.NativeSpecialization("binary_natural")),
        CombinatorProperty(booleanType, Property.NativeSpecialization(BooleanFamily.identity.name)),
        CombinatorProperty(listType, Property.NativeSpecialization(Representation.listFamily.name)),
        CombinatorProperty(listType, Property.DataFamily(1, Vector(nil, cons)))
      )
    ),
    NativesProvider.loaded
  )

  /** The canonical binary numeral of the value, least significant digit
    * outermost.
    */
  def numeral(value: Int): Instruction =
    if value == 0 then zero
    else Instruction.Apply(if (value & 1) == 1 then odd else even, numeral(value >> 1))

  /** `binary_set p`. */
  def criterion(admitsZero: Boolean): Instruction = Instruction.Apply(binarySet, if admitsZero then truth else falsity)

  /** `list_type (binary_set p)`. */
  def listCriterion(admitsZero: Boolean): Instruction = Instruction.Apply(listType, criterion(admitsZero))

  /** The list of the elements, each written as a numeral or as a numeral
    * filtered by `binary_set true`.
    */
  def list(elements: Vector[(Int, Boolean)]): Instruction = tailsFiltered(elements, Map.empty)

  /** The list of the elements, written as `list` writes them, each tail at
    * whose place `filters` holds an entry filtered by `list_type (binary_set
    * p)` of that entry, the tail after the first element at place 1 and nil
    * at the list's length; the list itself at place 0 is not filtered here.
    */
  def tailsFiltered(elements: Vector[(Int, Boolean)], filters: Map[Int, Boolean]): Instruction =
    elements.indices.foldRight(nil)((place, rest) =>
      val (value, filtered) = elements(place)
      val written = if filtered then Instruction.Parallel(numeral(value), criterion(true)) else numeral(value)
      val tail = filters.get(place + 1).fold(rest)(admitsZero => Instruction.Parallel(rest, listCriterion(admitsZero)))
      Instruction.Apply(Instruction.Apply(cons, written), tail)
    )
