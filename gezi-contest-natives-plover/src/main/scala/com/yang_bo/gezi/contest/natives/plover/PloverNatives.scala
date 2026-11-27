package com.yang_bo.gezi.contest.natives.plover

import com.yang_bo.gezi.jit.BinaryNatural
import com.yang_bo.gezi.jit.BinaryNaturalNatives
import com.yang_bo.gezi.jit.Native
import com.yang_bo.gezi.jit.NativeArgument
import com.yang_bo.gezi.jit.NativeBackend
import com.yang_bo.gezi.jit.NativePlace
import com.yang_bo.gezi.jit.NativeValue
import com.yang_bo.gezi.jit.NativesProvider
import com.yang_bo.gezi.jit.StaticBlockMethod
import com.yang_bo.gezi.jit.StaticBlockResult

/** The natives bound by `corpora/compiler/plover_ordered_compositions`,
  * `plover_unordered_combinations`, `plover_edit_distance`,
  * `plover_longest_common_subsequence`, `plover_smallest_team`,
  * `plover_billboard`, `plover_digit_steps`, `plover_modular_power`,
  * `plover_trailing_zeros`, `plover_divisor_sums`, `plover_rectangle_cutting`,
  * `plover_money_sums`, `plover_modular_tower`, `plover_book_shop` and
  * `plover_minimizing_coins`. Each takes and gives backend values. A native
  * does not check its operands (`CONTRIBUTING.md`, "Types live only in the
  * term"): its places are licensed by the filters at the call.
  */
final class PloverNatives extends NativesProvider:

  def natives: NativeBackend = NativeBackend.functions(
    Map(
      OrderedCompositionsMethod.nativeName -> Native(
        Vector(
          NativePlace.NaturalList(BinaryNaturalNatives.positive),
          NativePlace.Fixed(BinaryNaturalNatives.canonical),
          NativePlace.Fixed(BinaryNaturalNatives.positive)
        ),
        NativePlace.Fixed(BinaryNaturalNatives.canonical),
        OrderedCompositionsMethod
      ),
      UnorderedCombinationsMethod.nativeName -> Native(
        Vector(
          NativePlace.NaturalList(BinaryNaturalNatives.positive),
          NativePlace.Fixed(BinaryNaturalNatives.canonical),
          NativePlace.Fixed(BinaryNaturalNatives.positive)
        ),
        NativePlace.Fixed(BinaryNaturalNatives.canonical),
        UnorderedCombinationsMethod
      ),
      EditDistanceMethod.nativeName -> Native(
        Vector(
          NativePlace.NaturalList(BinaryNaturalNatives.canonical),
          NativePlace.NaturalList(BinaryNaturalNatives.canonical)
        ),
        NativePlace.Fixed(BinaryNaturalNatives.canonical),
        EditDistanceMethod
      ),
      LongestCommonSubsequenceMethod.nativeName -> Native(
        Vector(
          NativePlace.NaturalList(BinaryNaturalNatives.canonical),
          NativePlace.NaturalList(BinaryNaturalNatives.canonical)
        ),
        NativePlace.Fixed(BinaryNaturalNatives.canonical),
        LongestCommonSubsequenceMethod
      ),
      SmallestTeamMethod.nativeName -> Native(
        Vector(
          NativePlace.NaturalList(BinaryNaturalNatives.canonical),
          NativePlace.Fixed(BinaryNaturalNatives.canonical),
          NativePlace.Fixed(BinaryNaturalNatives.canonical)
        ),
        NativePlace.Fixed(BinaryNaturalNatives.canonical),
        SmallestTeamMethod
      ),
      BillboardMethod.nativeName -> Native(
        Vector(
          NativePlace.NaturalList(BinaryNaturalNatives.canonical),
          NativePlace.Fixed(BinaryNaturalNatives.canonical)
        ),
        NativePlace.Fixed(BinaryNaturalNatives.canonical),
        BillboardMethod
      ),
      DigitStepsMethod.nativeName -> Native(
        Vector(NativePlace.Fixed(BinaryNaturalNatives.canonical)),
        NativePlace.Fixed(BinaryNaturalNatives.canonical),
        DigitStepsMethod
      ),
      ModularPowerMethod.nativeName -> Native(
        Vector(
          NativePlace.Fixed(BinaryNaturalNatives.canonical),
          NativePlace.Fixed(BinaryNaturalNatives.canonical),
          NativePlace.Fixed(BinaryNaturalNatives.positive)
        ),
        NativePlace.Fixed(BinaryNaturalNatives.canonical),
        ModularPowerMethod
      ),
      TrailingZerosMethod.nativeName -> Native(
        Vector(NativePlace.Fixed(BinaryNaturalNatives.canonical)),
        NativePlace.Fixed(BinaryNaturalNatives.canonical),
        TrailingZerosMethod
      ),
      DivisorSumsMethod.nativeName -> Native(
        Vector(
          NativePlace.Fixed(BinaryNaturalNatives.canonical),
          NativePlace.Fixed(BinaryNaturalNatives.positive)
        ),
        NativePlace.Fixed(BinaryNaturalNatives.canonical),
        DivisorSumsMethod
      ),
      RectangleCuttingMethod.nativeName -> Native(
        Vector(
          NativePlace.Fixed(BinaryNaturalNatives.positive),
          NativePlace.Fixed(BinaryNaturalNatives.positive)
        ),
        NativePlace.Fixed(BinaryNaturalNatives.canonical),
        RectangleCuttingMethod
      ),
      MoneySumsMethod.nativeName -> Native(
        Vector(NativePlace.NaturalList(BinaryNaturalNatives.canonical)),
        NativePlace.Fixed(BinaryNaturalNatives.canonical),
        MoneySumsMethod
      ),
      ModularTowerMethod.nativeName -> Native(
        Vector(
          NativePlace.Fixed(BinaryNaturalNatives.canonical),
          NativePlace.Fixed(BinaryNaturalNatives.canonical),
          NativePlace.Fixed(BinaryNaturalNatives.canonical),
          NativePlace.Fixed(BinaryNaturalNatives.positive)
        ),
        NativePlace.Fixed(BinaryNaturalNatives.canonical),
        ModularTowerMethod
      ),
      BookShopMethod.nativeName -> Native(
        Vector(
          NativePlace.NaturalRecordList(
            Vector(
              BinaryNaturalNatives.canonical,
              BinaryNaturalNatives.canonical
            )
          ),
          NativePlace.Fixed(BinaryNaturalNatives.canonical)
        ),
        NativePlace.Fixed(BinaryNaturalNatives.canonical),
        BookShopMethod
      ),
      MinimizingCoinsMethod.nativeName -> Native(
        Vector(
          NativePlace.NaturalList(BinaryNaturalNatives.positive),
          NativePlace.Fixed(BinaryNaturalNatives.canonical)
        ),
        NativePlace.DeclaredFamilyValue,
        MinimizingCoinsMethod
      ),
      NaturalModuloMethod.nativeName -> Native(
        Vector(
          NativePlace.Fixed(BinaryNaturalNatives.canonical),
          NativePlace.Fixed(BinaryNaturalNatives.canonical)
        ),
        NativePlace.Fixed(BinaryNaturalNatives.canonical),
        NaturalModuloMethod
      ),
      NaturalDifferenceMethod.nativeName -> Native(
        Vector(
          NativePlace.Fixed(BinaryNaturalNatives.canonical),
          NativePlace.Fixed(BinaryNaturalNatives.canonical)
        ),
        NativePlace.Fixed(BinaryNaturalNatives.canonical),
        NaturalDifferenceMethod
      )
    ),
    Vector.empty
  )

/** `EditDistance.distance` as a static method a narrow block calls, its two
  * list places filled by a block alone, as `OrderedCompositionsMethod`'s is.
  */
private object EditDistanceMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "plover_edit_distance"

  val className: String = classOf[EditDistance.type].getName.stripSuffix("$")

  val methodName: String = "distance"

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    Native.outsidePlaces(nativeName, arguments)

/** `LongestCommonSubsequence.length` as a static method a narrow block calls,
  * its two list places filled by a block alone, as
  * `OrderedCompositionsMethod`'s is.
  */
private object LongestCommonSubsequenceMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "plover_longest_common_subsequence"

  val className: String =
    classOf[LongestCommonSubsequence.type].getName.stripSuffix("$")

  val methodName: String = "length"

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    Native.outsidePlaces(nativeName, arguments)

/** `SmallestTeam.size` as a static method a narrow block calls, its list place
  * filled by a block alone, as `OrderedCompositionsMethod`'s is.
  */
private object SmallestTeamMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "plover_smallest_team"

  val className: String = classOf[SmallestTeam.type].getName.stripSuffix("$")

  val methodName: String = "size"

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    Native.outsidePlaces(nativeName, arguments)

/** `Billboard.term` as a static method a narrow block calls at its root, its
  * list place filled by a block alone, as `OrderedCompositionsMethod`'s is. Its
  * result is the term over naturals that the typed version is ≃_O to.
  */
private object BillboardMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "plover_billboard"

  val className: String = classOf[Billboard.type].getName.stripSuffix("$")

  val methodName: String = "term"

  override val result: StaticBlockResult = StaticBlockResult.Lattice

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    Native.outsidePlaces(nativeName, arguments)

/** `BookShop.most` as a static method a narrow block over declared families
  * calls. Its record list place (`NativePlace.NaturalRecordList`) is one the
  * JIT never fills, so the implementation on an argument vector is never run.
  */
private object BookShopMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "plover_book_shop"

  val className: String = classOf[BookShop.type].getName.stripSuffix("$")

  val methodName: String = "most"

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    Native.outsidePlaces(nativeName, arguments)

/** `MinimizingCoins.fewest` as a static method a narrow block over declared
  * families calls at its root. Its list place is one the JIT never fills, so
  * the implementation on an argument vector is never run.
  */
private object MinimizingCoinsMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "plover_minimizing_coins"

  val className: String = classOf[MinimizingCoins.type].getName.stripSuffix("$")

  val methodName: String = "fewest"

  override val result: StaticBlockResult = StaticBlockResult.Constructed

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    Native.outsidePlaces(nativeName, arguments)

/** `ModularTower.power` as a static method a narrow block calls and, its places
  * naturals the JIT can fill, as an implementation on an argument vector.
  */
private object ModularTowerMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "plover_modular_tower"

  val className: String = classOf[ModularTower.type].getName.stripSuffix("$")

  val methodName: String = "power"

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    arguments match
      case Vector(
            NativeArgument.Represented(BinaryNatural(base)),
            NativeArgument.Represented(BinaryNatural(exponentBase)),
            NativeArgument.Represented(BinaryNatural(exponentPower)),
            NativeArgument.Represented(BinaryNatural(modulus))
          ) =>
        BinaryNatural(
          BigInt(
            ModularTower.power(
              base.bigInteger,
              exponentBase.bigInteger,
              exponentPower.bigInteger,
              modulus.bigInteger
            )
          )
        )
      case other => Native.outsidePlaces(nativeName, other)

/** `OrderedCompositions.count` as a static method a narrow block calls. Its
  * list place (`NativePlace.NaturalList`) is one the JIT never fills, so the
  * implementation on an argument vector is never run.
  */
private object OrderedCompositionsMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "plover_ordered_compositions"

  val className: String =
    classOf[OrderedCompositions.type].getName.stripSuffix("$")

  val methodName: String = "count"

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    Native.outsidePlaces(nativeName, arguments)

/** `UnorderedCombinations.count` as a static method a narrow block calls, its
  * list place filled by a block alone, as `OrderedCompositionsMethod`'s is.
  */
private object UnorderedCombinationsMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "plover_unordered_combinations"

  val className: String =
    classOf[UnorderedCombinations.type].getName.stripSuffix("$")

  val methodName: String = "count"

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    Native.outsidePlaces(nativeName, arguments)

/** `DigitSteps.count` as a static method a narrow block calls and, its one
  * place a natural the JIT can fill, as an implementation on an argument
  * vector.
  */
private object DigitStepsMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "plover_digit_steps"

  val className: String = classOf[DigitSteps.type].getName.stripSuffix("$")

  val methodName: String = "count"

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    arguments match
      case Vector(NativeArgument.Represented(BinaryNatural(value))) =>
        BinaryNatural(BigInt(DigitSteps.count(value.bigInteger)))
      case other => Native.outsidePlaces(nativeName, other)

/** `ModularPower.power` as a static method a narrow block calls and, its places
  * naturals the JIT can fill, as an implementation on an argument vector.
  */
private object ModularPowerMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "plover_modular_power"

  val className: String = classOf[ModularPower.type].getName.stripSuffix("$")

  val methodName: String = "power"

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    arguments match
      case Vector(
            NativeArgument.Represented(BinaryNatural(base)),
            NativeArgument.Represented(BinaryNatural(exponent)),
            NativeArgument.Represented(BinaryNatural(modulus))
          ) =>
        BinaryNatural(
          BigInt(
            ModularPower.power(
              base.bigInteger,
              exponent.bigInteger,
              modulus.bigInteger
            )
          )
        )
      case other => Native.outsidePlaces(nativeName, other)

/** `TrailingZeros.count` as a static method a narrow block calls and, its place
  * a natural the JIT can fill, as an implementation on an argument vector.
  */
private object TrailingZerosMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "plover_trailing_zeros"

  val className: String = classOf[TrailingZeros.type].getName.stripSuffix("$")

  val methodName: String = "count"

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    arguments match
      case Vector(NativeArgument.Represented(BinaryNatural(number))) =>
        BinaryNatural(BigInt(TrailingZeros.count(number.bigInteger)))
      case other => Native.outsidePlaces(nativeName, other)

/** `DivisorSums.total` as a static method a narrow block calls and, its places
  * naturals the JIT can fill, as an implementation on an argument vector.
  */
private object DivisorSumsMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "plover_divisor_sums"

  val className: String = classOf[DivisorSums.type].getName.stripSuffix("$")

  val methodName: String = "total"

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    arguments match
      case Vector(
            NativeArgument.Represented(BinaryNatural(limit)),
            NativeArgument.Represented(BinaryNatural(modulus))
          ) =>
        BinaryNatural(
          BigInt(DivisorSums.total(limit.bigInteger, modulus.bigInteger))
        )
      case other => Native.outsidePlaces(nativeName, other)

/** `RectangleCutting.cuts` as a static method a narrow block calls and, its
  * places naturals the JIT can fill, as an implementation on an argument
  * vector.
  */
private object RectangleCuttingMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "plover_rectangle_cutting"

  val className: String =
    classOf[RectangleCutting.type].getName.stripSuffix("$")

  val methodName: String = "cuts"

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    arguments match
      case Vector(
            NativeArgument.Represented(BinaryNatural(first)),
            NativeArgument.Represented(BinaryNatural(second))
          ) =>
        BinaryNatural(
          BigInt(RectangleCutting.cuts(first.bigInteger, second.bigInteger))
        )
      case other => Native.outsidePlaces(nativeName, other)

/** `MoneySums.total` as a static method a narrow block calls. Its list place
  * (`NativePlace.NaturalList`) is one the JIT never fills, so the
  * implementation on an argument vector is never run.
  */
private object MoneySumsMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "plover_money_sums"

  val className: String = classOf[MoneySums.type].getName.stripSuffix("$")

  val methodName: String = "total"

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    Native.outsidePlaces(nativeName, arguments)

/** `NaturalArithmetic.modulo` as a static method a block calls and, its places
  * naturals the JIT can fill, as an implementation on an argument vector.
  */
private object NaturalModuloMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "plover_natural_modulo"

  val className: String =
    classOf[NaturalArithmetic.type].getName.stripSuffix("$")

  val methodName: String = "modulo"

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    arguments match
      case Vector(
            NativeArgument.Represented(BinaryNatural(number)),
            NativeArgument.Represented(BinaryNatural(modulus))
          ) =>
        BinaryNatural(
          BigInt(
            NaturalArithmetic.modulo(number.bigInteger, modulus.bigInteger)
          )
        )
      case other => Native.outsidePlaces(nativeName, other)

/** `NaturalArithmetic.difference` as a static method a block calls and, its
  * places naturals the JIT can fill, as an implementation on an argument
  * vector.
  */
private object NaturalDifferenceMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "plover_natural_difference"

  val className: String =
    classOf[NaturalArithmetic.type].getName.stripSuffix("$")

  val methodName: String = "difference"

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    arguments match
      case Vector(
            NativeArgument.Represented(BinaryNatural(minuend)),
            NativeArgument.Represented(BinaryNatural(subtrahend))
          ) =>
        BinaryNatural(
          BigInt(
            NaturalArithmetic.difference(
              minuend.bigInteger,
              subtrahend.bigInteger
            )
          )
        )
      case other => Native.outsidePlaces(nativeName, other)
