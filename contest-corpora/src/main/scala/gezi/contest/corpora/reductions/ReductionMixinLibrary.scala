package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemField

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The type of a problem's expected values, the constructors of
  * problems/schema/value_type in order: Church Booleans, or Scott integers
  * that a unary numeral reads as. `written` is the type's name in the
  * reduction judge (`Scott.dataType`), which the host gives by the
  * constructor's position; the data do not write it.
  */
enum ValueType(val written: String):
  case BooleanType extends ValueType("boolean")
  case UnaryType extends ValueType("unary")

object ValueType:

  /** The value type a field writes, a constructor of
    * problems/schema/value_type read by its position
    * (`ProblemData.alternative`).
    */
  def read(term: ProblemField): ValueType =
    ProblemData.alternative(term, ValueType.values.size) match
      case (position, Vector()) => ValueType.fromOrdinal(position)
      case (_, fields)          => throw IllegalArgumentException(s"a value type has ${fields.size} fields")

/** Programs over the natural library of the mixin encoding, the port of
  * `problems/reduction_mixin_library`: Boolean and natural
  * operations, the one object that is both 0 and 1, and multiple outers.
  */
object ReductionMixinLibrary:

  private val family = "reduction_mixin_library"

  /** The program of the point (`library_point_surface/2`). */
  def libraryPointSurface(mixins: MixinLibrary, point: String): ProblemTerm =
    val hierarchies = if point == "reduction_mixin_multiple_outers" then Vector("outer", "inner") else Vector.empty
    mixins.withMixinLibrary(Vector("natural"), hierarchies)(names => pointBody(mixins, point, names))

  /** `{zero, {successor, predecessor : 0}}` (`zero_or_one/2`). */
  private def zeroOrOne(mixins: MixinLibrary, names: MixinNames): ProblemTerm =
    members(Vector(mixins.libraryClass(names, "zero"), mixins.successorClass(names, mixins.naturalInstance(names, 0))))

  private def pointBody(mixins: MixinLibrary, point: String, names: MixinNames): ProblemTerm = point match
    case "reduction_mixin_true_not" =>
      mixins.readSlot("boolean", "church", mixins.readSlot("boolean", "not", mixins.libraryClass(names, "true")))
    case "reduction_mixin_true_not_not" =>
      val not = mixins.readSlot("boolean", "not", mixins.libraryClass(names, "true"))
      mixins.readSlot("boolean", "church", mixins.readSlot("boolean", "not", not))
    case "reduction_mixin_true_and_false"      => binaryBoolean(mixins, names, "true", "conjunction", "false")
    case "reduction_mixin_false_and_true"      => binaryBoolean(mixins, names, "false", "conjunction", "true")
    case "reduction_mixin_true_equals_false"   => binaryBoolean(mixins, names, "true", "equality", "false")
    case "reduction_mixin_false_equals_false"  => binaryBoolean(mixins, names, "false", "equality", "false")
    case "reduction_mixin_two_plus_two"        => sumScott(mixins, names, 2, 2)
    case "reduction_mixin_three_plus_two"      => sumScott(mixins, names, 3, 2)
    case "reduction_mixin_one_plus_two_equals_three" =>
      val compared =
        mixins.slotApplied("natural", "equality", mixins.naturalInstance(names, 3), sumInstance(mixins, names, 1, 2))
      mixins.readSlot("boolean", "church", compared)
    case "reduction_mixin_pairwise_sum" =>
      mixins.readSlot("natural", "scott", pairwiseSum(mixins, names))
    case "reduction_mixin_pairwise_sum_self_equal" =>
      λ(sum => mixins.readSlot("boolean", "church", mixins.slotApplied("natural", "equality", sum, sum)))(
        pairwiseSum(mixins, names)
      )
    case "reduction_mixin_multiple_outers" => multipleOuters(mixins)
    case other => throw IllegalArgumentException(s"no library point $other")

  /** `Left.Method(Right)` read at church (`binary_boolean/5`). */
  private def binaryBoolean(mixins: MixinLibrary, names: MixinNames, left: String, method: String, right: String): ProblemTerm =
    val applied =
      mixins.slotApplied("boolean", method, mixins.libraryClass(names, left), mixins.libraryClass(names, right))
    mixins.readSlot("boolean", "church", applied)

  private def sumInstance(mixins: MixinLibrary, names: MixinNames, left: Int, right: Int): ProblemTerm =
    mixins.slotApplied("natural", "plus", mixins.naturalInstance(names, left), mixins.naturalInstance(names, right))

  private def sumScott(mixins: MixinLibrary, names: MixinNames, left: Int, right: Int): ProblemTerm =
    mixins.readSlot("natural", "scott", sumInstance(mixins, names, left, right))

  private def pairwiseSum(mixins: MixinLibrary, names: MixinNames): ProblemTerm =
    mixins.slotApplied("natural", "plus", zeroOrOne(mixins, names), zeroOrOne(mixins, names))

  /** object_one and object_two extend my_outer with the names true and false;
    * the union of their inner classes reads outer.name (`multiple_outers/1`).
    */
  private def multipleOuters(mixins: MixinLibrary): ProblemTerm =
    val innerOne = mixins.readSlot(
      "outer",
      "inner",
      members(Vector(myOuter(mixins), mixins.valueMixin("outer", "name" -> trueTerm)))
    )
    val innerTwo = mixins.readSlot(
      "outer",
      "inner",
      members(Vector(myOuter(mixins), mixins.valueMixin("outer", "name" -> falseTerm)))
    )
    mixins.readSlot("outer", "name", mixins.readSlot("inner", "outer", members(Vector(innerOne, innerTwo))))

  /** The outer whose inner is the class of one inner mixin whose outer is the
    * outer's self (`my_outer/1`).
    */
  private def myOuter(mixins: MixinLibrary): ProblemTerm =
    mixins.selfMixin("outer", "inner")(self => members(Vector(mixins.valueMixin("inner", "outer" -> self))))

  /** The tree of an expected value of the type: a Church Boolean's, or a
    * Scott integer's as a unary numeral.
    */
  private def valueTree(valueType: ValueType, value: ProblemField): ScottTree = valueType match
    case ValueType.BooleanType => Scott.booleanTree(ProblemData.truth(value))
    case ValueType.UnaryType   => Scott.unaryTree(ProblemData.small(value))

  /** The problems (`problem/3`). */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("problem").map {
      case Vector(point, typeField, values) =>
        val (name, valueType) = (ProblemData.text(point), ValueType.read(typeField))
        ReductionProblem(
          name,
          libraryPointSurface(group.mixins, name),
          valueType.written,
          Reduction.expectedOf(ProblemData.list(values).map(valueTree(valueType, _))),
          Reduction.defaultLimits
        )
      case other => throw IllegalArgumentException(s"not a problem: $other")
    }
