package gezi.contest.natives.plover

import gezi.jit.BinaryNatural
import gezi.jit.BinaryNaturalNatives
import gezi.jit.Native
import gezi.jit.NativeArgument
import gezi.jit.NativeBackend
import gezi.jit.NativePlace
import gezi.jit.NativeValue
import gezi.jit.NativesProvider
import gezi.jit.StaticBlockMethod

/** The natives bound by `corpora/compiler/plover_ordered_compositions`,
  * `plover_unordered_combinations`, `plover_digit_steps` and
  * `plover_modular_power`. Each takes and gives backend values. A native does not check its operands
  * (`CONTRIBUTING.md`, "Types live only in the term"): its places are licensed
  * by the filters at the call.
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
      )
    ),
    Vector.empty
  )

/** `OrderedCompositions.count` as a static method a narrow block calls. Its
  * list place (`NativePlace.NaturalList`) is one the JIT never fills, so the
  * implementation on an argument vector is never run.
  */
private object OrderedCompositionsMethod extends (Vector[NativeArgument] => NativeValue), StaticBlockMethod:

  val nativeName: String = "plover_ordered_compositions"

  val className: String = classOf[OrderedCompositions.type].getName.stripSuffix("$")

  val methodName: String = "count"

  def apply(arguments: Vector[NativeArgument]): NativeValue = Native.outsidePlaces(nativeName, arguments)

/** `UnorderedCombinations.count` as a static method a narrow block calls, its
  * list place filled by a block alone, as `OrderedCompositionsMethod`'s is.
  */
private object UnorderedCombinationsMethod extends (Vector[NativeArgument] => NativeValue), StaticBlockMethod:

  val nativeName: String = "plover_unordered_combinations"

  val className: String = classOf[UnorderedCombinations.type].getName.stripSuffix("$")

  val methodName: String = "count"

  def apply(arguments: Vector[NativeArgument]): NativeValue = Native.outsidePlaces(nativeName, arguments)

/** `DigitSteps.count` as a static method a narrow block calls and, its one
  * place a natural the JIT can fill, as an implementation on an argument vector.
  */
private object DigitStepsMethod extends (Vector[NativeArgument] => NativeValue), StaticBlockMethod:

  val nativeName: String = "plover_digit_steps"

  val className: String = classOf[DigitSteps.type].getName.stripSuffix("$")

  val methodName: String = "count"

  def apply(arguments: Vector[NativeArgument]): NativeValue = arguments match
    case Vector(NativeArgument.Represented(BinaryNatural(value))) => BinaryNatural(BigInt(DigitSteps.count(value.bigInteger)))
    case other                                                    => Native.outsidePlaces(nativeName, other)

/** `ModularPower.power` as a static method a narrow block calls and, its places
  * naturals the JIT can fill, as an implementation on an argument vector.
  */
private object ModularPowerMethod extends (Vector[NativeArgument] => NativeValue), StaticBlockMethod:

  val nativeName: String = "plover_modular_power"

  val className: String = classOf[ModularPower.type].getName.stripSuffix("$")

  val methodName: String = "power"

  def apply(arguments: Vector[NativeArgument]): NativeValue = arguments match
    case Vector(
          NativeArgument.Represented(BinaryNatural(base)),
          NativeArgument.Represented(BinaryNatural(exponent)),
          NativeArgument.Represented(BinaryNatural(modulus))
        ) =>
      BinaryNatural(BigInt(ModularPower.power(base.bigInteger, exponent.bigInteger, modulus.bigInteger)))
    case other => Native.outsidePlaces(nativeName, other)
