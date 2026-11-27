package gezi.narrowblocks.groups

import java.math.BigInteger
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Pure
import gezi.jit.BinaryNatural
import gezi.jit.BinaryNaturalNatives
import gezi.jit.JitValue
import gezi.jit.Native
import gezi.jit.NativeArgument
import gezi.jit.NativeBackend
import gezi.jit.NativePlace
import gezi.jit.NativeValue
import gezi.jit.Representation
import gezi.jit.StaticBlockMethod
import gezi.jit.StaticBlockResult
import gezi.narrowblocks.lists.NarrowListLibrary
import gezi.saturation.StopSignal
import gezi.standardlibrary.CombinatorProperty
import gezi.standardlibrary.NativeBound
import gezi.standardlibrary.Property
import gezi.ir.{Configured, NativeSpecializer}

private given groupListLibraryNoFacts: NoFacts.type = NoFacts

/** The static methods of the natives the list laws bind by hand: the sum of
  * a list's elements, the list 0, 1, …, n − 1, a list's length, the lesser
  * of two naturals, the count of a list's distinct elements, a natural's
  * residue modulo 3, and a natural less one (no answer, null, on zero).
  * Public, since a block calls them by their names.
  */
object GroupListNatives:
  def summed(values: Vector[BigInteger]): BigInteger = values.foldLeft(BigInteger.ZERO)(_.add(_))
  def ranged(count: BigInteger): Vector[BigInteger] = Vector.tabulate(count.intValueExact)(BigInteger.valueOf(_))
  def length(values: Vector[BigInteger]): BigInteger = BigInteger.valueOf(values.size.toLong)
  def minimum(left: BigInteger, right: BigInteger): BigInteger = left.min(right)
  def distinctCount(values: Vector[BigInteger]): BigInteger = BigInteger.valueOf(values.distinct.size.toLong)
  def residue(value: BigInteger): BigInteger = value.mod(BigInteger.valueOf(3))
  def decremented(value: BigInteger): BigInteger = if value.signum == 0 then null else value.subtract(BigInteger.ONE)

/** A list native as a block calls it; the laws never run it on an argument
  * vector.
  */
final class GroupListNativeMethod(val methodName: String, override val result: StaticBlockResult)
    extends (Vector[NativeArgument] => NativeValue),
      StaticBlockMethod:
  val className: String = classOf[GroupListNatives.type].getName.stripSuffix("$")
  def apply(arguments: Vector[NativeArgument]): NativeValue = Native.outsidePlaces(methodName, arguments)

/** The library of the group blocks' list laws: the narrow lists' test
  * library with an array lists' criterion `array_list` (its
  * `native_specialization` and `data_family` naming the library's nil and
  * cons) and the list natives bound by hand (`GroupListNatives`), with the
  * helpers that write a block's code. N is `binary_set true`, P
  * `binary_set false`, A `array_list N` and A⁺ `array_list P`.
  */
object GroupListLibrary:

  import NarrowListLibrary.*

  /** λx. x x x x, a term of no other name of the library, the array lists'
    * criterion.
    */
  val arrayList: Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(Code.Apply(Code.Apply(Code.Apply(Code.Slot(0), Code.Slot(0)), Code.Slot(0)), Code.Slot(0)), Vector(Hole.Bound(0)), Vector.empty)

  /** Terms of no other name, bound to the natives. */
  def bound[C <: NativeSpecializer & Singleton](depth: Int)(using C): Configured[C] =
    (summon[C]: C).thunkOrInstance((0 until depth).foldLeft(Code.Slot(0): Code)((code, _) => Code.Apply(Code.Slot(0), code)), Vector(Hole.Bound(0)), Vector.empty)
  val sumList: Configured[NoFacts.type] = bound(5)
  val sumPositive: Configured[NoFacts.type] = bound(6)
  val range: Configured[NoFacts.type] = bound(7)
  val length: Configured[NoFacts.type] = bound(8)
  val minimum: Configured[NoFacts.type] = bound(9)
  val distinctCount: Configured[NoFacts.type] = bound(10)
  val residue: Configured[NoFacts.type] = bound(11)
  val decrement: Configured[NoFacts.type] = bound(12)

  private val canonical: NativePlace = NativePlace.Fixed(BinaryNaturalNatives.canonical)

  def listNative(name: String, places: Vector[NativePlace], result: NativePlace, convention: StaticBlockResult) =
    name -> Native(places, result, GroupListNativeMethod(name, convention))

  val compilation = GroupCompilation(gezi.jit.BackendFacts(
    NarrowListLibrary.compilation.index.copy(
      nativeBound = NarrowListLibrary.compilation.index.nativeBound ++ Vector(
        NativeBound(Pure.required(sumList), "summed"),
        NativeBound(Pure.required(sumPositive), "summedPositive"),
        NativeBound(Pure.required(range), "ranged"),
        NativeBound(Pure.required(length), "length"),
        NativeBound(Pure.required(minimum), "minimum"),
        NativeBound(Pure.required(distinctCount), "distinctCount"),
        NativeBound(Pure.required(residue), "residue"),
        NativeBound(Pure.required(decrement), "decremented")
      ),
      combinatorProperties = NarrowListLibrary.compilation.index.combinatorProperties ++ Vector(
        // The booleans' constructors, which a storage's criterion `binary_set true` is spelled with.
        CombinatorProperty(Pure.required(booleanType), Property.DataFamily(0, Vector(truth, falsity).map(Pure.required))),
        CombinatorProperty(Pure.required(arrayList), Property.NativeSpecialization(Representation.arrayListFamily.name)),
        CombinatorProperty(Pure.required(arrayList), Property.DataFamily(1, Vector(nil, cons).map(Pure.required)))
      )
    ),
    gezi.jit.NativesProvider.loaded.extended(
      NativeBackend.functions(
        Map(
          listNative(
            "summed",
            Vector(NativePlace.NaturalList(BinaryNaturalNatives.canonical)),
            NativePlace.Fixed(BinaryNaturalNatives.canonical),
            StaticBlockResult.Natural
          ),
          // The same static method at a place of the positive naturals' lists.
          "summedPositive" -> Native(
            Vector(NativePlace.NaturalList(BinaryNaturalNatives.positive)),
            NativePlace.Fixed(BinaryNaturalNatives.canonical),
            GroupListNativeMethod("summed", StaticBlockResult.Natural)
          ),
          listNative(
            "ranged",
            Vector(NativePlace.Fixed(BinaryNaturalNatives.canonical)),
            NativePlace.NaturalList(BinaryNaturalNatives.canonical),
            StaticBlockResult.NaturalList
          ),
          listNative("length", Vector(NativePlace.NaturalList(BinaryNaturalNatives.canonical)), canonical, StaticBlockResult.Natural),
          listNative("minimum", Vector(canonical, canonical), canonical, StaticBlockResult.Natural),
          listNative("distinctCount", Vector(NativePlace.NaturalList(BinaryNaturalNatives.canonical)), canonical, StaticBlockResult.Natural),
          listNative("residue", Vector(canonical), canonical, StaticBlockResult.Natural),
          listNative("decremented", Vector(canonical), canonical, StaticBlockResult.NaturalOrNoAnswer)
        ),
        Vector.empty
      )
    )
  ))

  val facts: gezi.jit.BackendFacts = compilation.facts

  val naturals: Configured[NoFacts.type] = NoFacts.application(binarySet, truth)
  val positives: Configured[NoFacts.type] = NoFacts.application(binarySet, falsity)
  val lists: Configured[NoFacts.type] = NoFacts.application(arrayList, naturals)
  val positiveLists: Configured[NoFacts.type] = NoFacts.application(arrayList, positives)

  /** The encoding of the backend's facts, the configuration in which a storage is a term. */
  val encoding: gezi.jit.StorageEncoding = facts.storageEncoding

  /** The storage of the binary natural of the value, a term of the backend's encoding. */
  def storage(value: Long): Configured[encoding.type] =
    given encoding.type = encoding
    gezi.ir.Closed
      .configured(encoding.operations.storageOf(BinaryNaturalNatives.canonical, BinaryNatural(BigInt(value))))
      .getOrElse(throw IllegalStateException(s"the storage of $value holds a suspension"))

  def applied(function: Code, arguments: Code*): Code = arguments.foldLeft(function)(Code.Apply(_, _))

  def filtered(value: Code, criterion: Code): Code = Code.Parallel(value, criterion)

  /** `λh t. b`, the code b reading h at slot 0, t at 1 and the enclosing
    * code's slots given as the fillings, in order, from slot 2.
    */
  def consCase(body: Code, enclosing: Int*): Code =
    Code.Thunk(body, Vector(Hole.Bound(0), Hole.Bound(1)), enclosing.toVector.map(Code.Slot(_)))

  /** A block of one parameter at slot 0, its code's other slots the
    * fillings in order from slot 1.
    */
  def block[C <: NativeSpecializer & Singleton](code: Code, fillings: Configured[C]*)(using C): Configured[C] = (summon[C]: C).thunkOrInstance(code, Vector(Hole.Bound(0)), fillings.toVector)

  /** A pure term of the library as a term of the backend's encoding. */
  def crossed(term: Configured[NoFacts.type]): Configured[encoding.type] = Configured.fromPure(encoding)(Pure.required(term))

  def compiled(thunk: Configured[encoding.type]): GroupBlock[encoding.type] =
    given encoding.type = encoding
    compilation.compiled(thunk, encoding.operations).getOrElse(throw IllegalStateException(s"the block compiles: $thunk"))

  def run(stop: StopSignal, thunk: Configured[encoding.type], group: Vector[GroupValue]): GroupOutcome =
    given encoding.type = encoding
    GroupRun.run(compiled(thunk), Vector(group), ScalarGroupBackend, 100000000L, stop)

  def listOf(values: Vector[BigInteger]): GroupValue =
    GroupValue.List(GroupListKind(encoding.operations, Representation.ArrayListOf(BinaryNaturalNatives.canonical)).of(values))

