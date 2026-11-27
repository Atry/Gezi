package com.yang_bo.gezi.contest.entry.generic

import java.nio.file.Paths
import com.yang_bo.gezi.contest.entry.ArticleDestination
import com.yang_bo.gezi.contest.entry.Defaults
import com.yang_bo.gezi.contest.entry.EntryData
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.Value
import com.yang_bo.gezi.jit.StorageEncoding
import com.yang_bo.gezi.jit.BackendFacts
import com.yang_bo.gezi.jit.BinaryCanonicity
import com.yang_bo.gezi.jit.BinaryNatural
import com.yang_bo.gezi.jit.BinaryNaturalFamily
import com.yang_bo.gezi.jit.BigIntegerFamily
import com.yang_bo.gezi.jit.BooleanFamily
import com.yang_bo.gezi.jit.DataFamily
import com.yang_bo.gezi.jit.CriterionParameters
import com.yang_bo.gezi.jit.DeclaredFamily
import com.yang_bo.gezi.jit.FamilyIdentity
import com.yang_bo.gezi.jit.FamilyParameter
import com.yang_bo.gezi.jit.JitValue
import com.yang_bo.gezi.jit.JvmBits
import com.yang_bo.gezi.jit.JvmBitsFamily
import com.yang_bo.gezi.jit.JvmIntFamily
import com.yang_bo.gezi.jit.Native
import com.yang_bo.gezi.jit.NativeArgument
import com.yang_bo.gezi.jit.NativeBackend
import com.yang_bo.gezi.jit.NativeName
import com.yang_bo.gezi.jit.NativePlace
import com.yang_bo.gezi.jit.NativeValue
import com.yang_bo.gezi.jit.NativesProvider
import com.yang_bo.gezi.jit.Representation
import com.yang_bo.gezi.jit.StaticBlockMethod
import com.yang_bo.gezi.jit.Word
import com.yang_bo.gezi.jit.WordFamily
import com.yang_bo.gezi.jit.WordWidth
import com.yang_bo.gezi.weakhead.ListRepresentation
import snapshot4s.generated.snapshotConfig
import scala.util.Random

/** The results of every native the JIT can call, of the standard set and of
  * every natives provider on the classpath (plover's, solo's), and of the
  * constructors of the data families an in-tree entry's knowledge declares,
  * each called on generated arguments of its places from a fixed seed, the
  * binary naturals drawn at both parameters, canonical and positive; and the
  * names of the natives a narrow block calls by a static method. A value is
  * printed by its family and its data, a list's item or tail by its position
  * among the library terms the generator draws, a declared family by its
  * position among the entry's families, so the text depends on what a native
  * computes and not on how the backend holds it. The natives only a block calls
  * (a list or a record list among their places, or a declared family's value as
  * their result) are listed by name and not called. Its purpose is to catch a
  * native whose result changes, or that loses its static method and so silently
  * leaves its blocks, when the natives' values move to another representation
  * in the host: recorded before such a move, the snapshot is kept byte for byte
  * by it.
  */
class NativeResultsSnapshotTest
    extends com.yang_bo.gezi.generatedinputs.FailFastSuite
    with snapshot4s.munit.SnapshotAssertions:

  // Reading plover's entry, whose knowledge declares families, takes most of
  // the run (InTreeEntriesTest measures about 20 s for an entry).
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(60, "s")

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  private val backend: NativeBackend = NativesProvider.loaded

  /** The encoding of plover's facts, the configuration the natives are called
    * in.
    */
  private lazy val encoding: StorageEncoding = declared._3.storageEncoding

  private given encodingConfiguration: encoding.type = encoding

  /** A value of the encoding's configuration. */
  private type Term = JitValue[encoding.type]

  /** The library terms an item or a tail is drawn from: the constructors the
    * facts bind for zero, successor, true, nil and cons.
    */
  private lazy val terms: Vector[Term] =
    val facts = declared._3
    Vector(
      facts.constructorDefine(
        NativeName.Constructor(BigIntegerFamily.identity, 0)
      ),
      facts.constructorDefine(
        NativeName.Constructor(BigIntegerFamily.identity, 1)
      ),
      facts.constructorDefine(
        NativeName.Constructor(BooleanFamily.identity, 0)
      ),
      facts.nil,
      facts.cons
    ).map(pure => Value.of(Configured.fromPure(encoding)(pure)))

  private val callsPerNative = 6

  /** The greatest binary natural drawn: the natives of plover over them (the
    * rectangle's table is cubic in its sides) stay small.
    */
  private val greatestBinaryNatural = 40

  private def term(random: Random): Term = terms(random.nextInt(terms.size))

  private def termShown(value: Term): String =
    terms.indexWhere(Value.same(_, value)) match
      case -1 =>
        throw IllegalStateException(
          s"a term the generator did not draw: $value"
        )
      case index => s"term#$index"

  /** The declared families of plover's knowledge, the in-tree entry that
    * declares some, with the backend its facts extend.
    */
  private lazy val declared
      : (NativeBackend, Vector[DeclaredFamily], BackendFacts) =
    val entryDirectory = buildRoot.resolve("gezi-contest-entries-plover")
    val (data, afterEntry) =
      EntryData.read(entryDirectory, Defaults.entryDataState)
    val (library, _) = GenericEntryProvider.initializedWithLibrary(
      data,
      com.yang_bo.gezi.contest.entry.ExecutorModules.registeredFor(entryDirectory),
      com.yang_bo.gezi.contest.entry.ExtractorModules.registeredFor(entryDirectory),
      backend,
      ArticleDestination.Discarded,
      afterEntry,
      Defaults.caches()
    )
    val facts = BackendFacts.of(library, backend)
    val extended = facts.nativeBackend
    (
      extended,
      extended.families
        .collect { case family: DeclaredFamily => family }
        .sortBy(_.identity.shown),
      facts
    )

  private def familyShown(identity: FamilyIdentity): String =
    declared._2.indexWhere(_.identity == identity) match
      case -1    => identity.shown
      case index => s"declared#$index"

  /** A value of the representation, drawn. */
  private def value(
      random: Random,
      representation: Representation[Term]
  ): NativeValue[Term] = representation match
    case Representation.Data(identity, None)
        if identity == BigIntegerFamily.identity =>
      NativeValue.Natural(
        BigInt(random.nextLong(1L << 40)) << random.nextInt(40)
      )
    case Representation.Data(identity, None)
        if identity == BooleanFamily.identity =>
      NativeValue.Truth(random.nextBoolean())
    case Representation.Data(identity, Some(WordWidth(width)))
        if identity == WordFamily.identity =>
      Word(width, BigInt(width.toInt, random))
    case Representation.Data(identity, Some(BinaryCanonicity(canonical)))
        if identity == BinaryNaturalFamily.identity =>
      BinaryNatural(BigInt((if canonical then 0
                            else 1) + random.nextInt(greatestBinaryNatural)))
    case Representation.Data(identity, None)
        if JvmBitsFamily.all.exists(_.identity == identity) =>
      val width = JvmBitsFamily.all
        .find(_.identity == identity)
        .map(_.width)
        .getOrElse(throw IllegalStateException(s"$identity"))
      JvmBitsFamily.masked(width, random.nextLong())
    case Representation.Data(identity, None)
        if identity == JvmIntFamily.identity =>
      JvmBitsFamily.masked(32, random.nextLong())
    case other => throw IllegalArgumentException(s"no generator of $other")

  /** The representations a declared family's criterion parameters are drawn
    * among.
    */
  private val parameterRepresentations: Vector[Representation[Nothing]] =
    Vector(
      Representation.BigInteger,
      Representation.Truth,
      com.yang_bo.gezi.jit.BinaryNaturalNatives.canonical
    )

  /** The parameter of a call of the family's constructor, drawn. */
  private def parameter(
      random: Random,
      family: DataFamily,
      native: NativeName
  ): Option[FamilyParameter[Term]] =
    family match
      case WordFamily =>
        Some(
          WordWidth(
            if family
                .constructors(Some(WordWidth(0)))
                .exists(_.native == native)
            then 0
            else 1 + random.nextInt(70)
          )
        )
      case BinaryNaturalFamily =>
        val canonical = random.nextBoolean() || native == NativeName
          .Constructor(BinaryNaturalFamily.identity, 0)
        Some(BinaryCanonicity(canonical))
      case declaredFamily: DeclaredFamily
          if declaredFamily.criterionArity > 0 =>
        Some(
          CriterionParameters(
            Vector.fill(declaredFamily.criterionArity)(
              parameterRepresentations(
                random.nextInt(parameterRepresentations.size)
              )
            )
          )
        )
      case _ => None

  private def arguments(
      random: Random,
      name: NativeName,
      native: Native,
      natives: NativeBackend
  ): (Option[FamilyParameter[Term]], Vector[NativeArgument[Term]]) =
    val callParameter = name match
      case NativeName.Constructor(identity, _) =>
        natives.family(identity).flatMap(parameter(random, _, name))
      case _ => None
    callParameter -> native.parameters.map {
      case NativePlace.Fixed(representation) =>
        NativeArgument.Represented(value(random, representation))
      case NativePlace.OfParameter(representation) =>
        NativeArgument.Represented(value(random, representation(callParameter)))
      case NativePlace.Item => NativeArgument.Item(term(random))
      case NativePlace.Tail => NativeArgument.Tail(term(random))
      case other            =>
        throw IllegalArgumentException(
          s"no generator of the place $other of $name"
        )
    }

  private def shown(value: NativeValue[Term]): String = value match
    case NativeValue.Natural(natural) => s"natural $natural"
    case NativeValue.Truth(truth)     => s"truth $truth"
    case Word(width, bits)            => s"word $width $bits"
    case BinaryNatural(natural)       => s"binary_natural $natural"
    case JvmBits(width, bits)         => s"jvm_bits $width $bits"
    case NativeValue.Listed(ListRepresentation.Items(0, _))      => "nil"
    case NativeValue.Listed(ListRepresentation.Cell(item, tail)) =>
      s"cell ${termShown(item)} ${termShown(tail)}"
    case NativeValue.Constructed(family, constructor, fields) =>
      s"constructed ${familyShown(family)} $constructor [${fields.map(shown).mkString(", ")}]"
    case other => throw IllegalArgumentException(s"no text of $other")

  /** A parameter, printed as the value that spells it in the criterion was when
    * the snapshot was recorded.
    */
  private def parameterShown(parameter: FamilyParameter[Term]): String =
    parameter match
      case WordWidth(width)              => s"natural $width"
      case BinaryCanonicity(canonical)   => s"truth $canonical"
      case CriterionParameters(criteria) =>
        s"parameters [${criteria.map(_.familyIdentity.shown).mkString(", ")}]"
      case other => throw IllegalArgumentException(s"no text of $other")

  private def argumentShown(argument: NativeArgument[Term]): String =
    argument match
      case NativeArgument.Represented(value) => shown(value)
      case NativeArgument.Item(item)         => s"item ${termShown(item)}"
      case NativeArgument.Tail(tail)         => s"tail ${termShown(tail)}"

  /** Whether only a narrow block calls the native: a list or a record list
    * among its places, or a declared family's value as its result.
    */
  private def blockOnly(native: Native): Boolean =
    native.result == NativePlace.DeclaredFamilyValue || native.parameters
      .exists {
        case NativePlace.NaturalList(_) | NativePlace.NaturalRecordList(_) =>
          true
        case _ => false
      }

  private def nameShown(name: NativeName): String = name match
    case NativeName.Constructor(identity, position) =>
      s"Constructor(${familyShown(identity)},$position)"
    case other => other.toString

  test("theResultsOfEveryNativeTheJitCalls") {
    val (natives, families, _) = declared
    assert(families.nonEmpty, "plover's knowledge declares no family")
    assert(
      natives.natives.keySet.exists(_.toString.contains("plover")),
      "plover's natives are not on the classpath"
    )
    val random = Random(20261124)
    val sorted = natives.natives.toVector.sortBy((name, _) => nameShown(name))
    val called = sorted
      .filterNot((_, native) => blockOnly(native))
      .flatMap((name, native) =>
        // A native of two places of one representation is called once on two
        // equal operands, its first call, so that an equality's true result
        // and a difference's zero are drawn too.
        Vector
          .tabulate(callsPerNative)(index =>
            val (callParameter, drawn) =
              arguments(random, name, native, natives)
            native.parameters match
              case Vector(NativePlace.Fixed(first), NativePlace.Fixed(second))
                  if index == 0 && first == second =>
                drawn match
                  case Vector(operand, _) =>
                    (callParameter, Vector(operand, operand))
                  case other =>
                    throw IllegalStateException(
                      s"a native of two places has two operands, not ${other.size}"
                    )
              case _ => (callParameter, drawn)
          )
          .map((callParameter, drawn) =>
            s"${nameShown(name)}\t${callParameter.map(parameterShown).getOrElse("-")}\t${drawn.map(argumentShown).mkString(", ")}\t=> ${shown(native.implementation(drawn))}"
          )
      )
    val onlyBlocks = sorted
      .filter((_, native) => blockOnly(native))
      .map((name, _) => s"block only\t${nameShown(name)}")
    val staticMethods = sorted.flatMap((name, native) =>
      native.implementation match
        case _: StaticBlockMethod => Some(s"static method\t${nameShown(name)}")
        case _                    => None
    )
    assertFileSnapshot(
      (called ++ onlyBlocks ++ staticMethods).mkString("\n") + "\n",
      "native-results/every-native.txt"
    )
  }
