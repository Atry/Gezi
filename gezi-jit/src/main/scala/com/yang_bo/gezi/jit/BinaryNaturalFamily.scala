package com.yang_bo.gezi.jit

/** A natural of the family `binary_natural`, held as one integer.
  *
  * The value is checked by its sign, not by `require(value >= 0, ...)`: that
  * form allocated the message's closure and compared with a cached `BigInt(0)`
  * at every construction, and every binary native's result is one. Measured on
  * calls_1000000_hot (`contest-entries-wren`'s block, 2026-11-03, CPUs 2-3,
  * nice 19, the judge's practice run, the point read again in one JVM): 0.51 to
  * 0.63 s with `require`, 0.39 to 0.49 s with the sign.
  */
final case class BinaryNatural(value: BigInt) extends NativeValue[Nothing]:
  if value.signum < 0 then
    throw IllegalArgumentException(s"a binary natural of the value $value")

/** The family `binary_natural` of the standard library's binary naturals: the
  * numerals of the module binary, `binary_zero`, `binary_even h` for 2h and
  * `binary_odd h` for 2h + 1, each a term of three cases. The family's
  * parameter is a boolean, read from the decoding criterion `binary_set P`:
  * true for the canonical naturals, false for the canonical positive ones.
  * Every numeral takes the three cases at both parameters, so the three
  * constructors are given at both, and zero is EXCLUDED at false: a canonical
  * positive natural is never zero, so `binary_even binary_zero`, whose field is
  * read at false, reads no value. That its filter is below no closed βη normal
  * form in ⊑_O is a paper argument (zero's case and the even and odd cases are
  * separable), not yet a complete proof; the decoding law checks the member
  * side only. The field of `binary_even` is read at false, the field of
  * `binary_odd` at true. It reads no type: it says how the backend holds a
  * value the term already asserts to be a canonical binary natural.
  *
  * THE SHAPE CHECK reads the three constructors at true, since they are the
  * same defines with the same fields at both parameters; only the exclusion
  * differs.
  */
/** The parameter of the family `binary_natural`: whether the set is the
  * canonical naturals' (true) or the positive ones' (false), written
  * `binary_set P` in the criterion.
  */
final case class BinaryCanonicity(canonical: Boolean)
    extends FamilyParameter[Nothing]

object BinaryNaturalFamily extends DataFamily:

  val identity: FamilyIdentity.Codec = FamilyIdentity.Codec("binary_natural")

  val parameterFamily: Option[FamilyIdentity] = Some(BooleanFamily.identity)

  /** The native names the codec encodes the three constructors with: the
    * family's identity and each constructor's position in the `data_family` of
    * `binary_set` (`binary_prolog_backend`), `binary_zero` at 0, `binary_even`
    * at 1 and `binary_odd` at 2, never a string of their own
    * ([[FamilyIdentity]]).
    */
  val zeroNative: NativeName = NativeName.Constructor(identity, 0)
  val evenNative: NativeName = NativeName.Constructor(identity, 1)
  val oddNative: NativeName = NativeName.Constructor(identity, 2)

  private val canonical: Option[FamilyParameter[Nothing]] = Some(
    BinaryCanonicity(true)
  )
  private val positive: Option[FamilyParameter[Nothing]] = Some(
    BinaryCanonicity(false)
  )

  private val all: Vector[DataConstructor] = Vector(
    DataConstructor(zeroNative, Vector.empty),
    DataConstructor(evenNative, Vector(DataField(identity, _ => positive))),
    DataConstructor(oddNative, Vector(DataField(identity, _ => canonical)))
  )

  def constructors[Term](
      parameter: Option[FamilyParameter[Term]]
  ): Vector[DataConstructor] =
    canonicity(parameter)
    all

  override def excluded[Term](
      parameter: Option[FamilyParameter[Term]],
      constructor: Int
  ): Boolean =
    !canonicity(parameter) && constructor == 0

  def built[Term](
      parameter: Option[FamilyParameter[Term]],
      layer: DataLayer[Term]
  ): NativeValue[Term] =
    (canonicity(parameter), layer) match
      case (true, DataLayer(0, Vector())) => BinaryNatural(0)
      case (_, DataLayer(1, Vector(BinaryNatural(half)))) if half > 0 =>
        BinaryNatural(half * 2)
      case (_, DataLayer(2, Vector(BinaryNatural(half)))) =>
        BinaryNatural(half * 2 + 1)
      case (atParameter, other) =>
        throw IllegalArgumentException(
          s"no layer of a binary natural at $atParameter: $other"
        )

  def taken[Term](
      parameter: Option[FamilyParameter[Term]],
      value: NativeValue[Term]
  ): DataLayer[Term] =
    (canonicity(parameter), value) match
      case (true, BinaryNatural(found)) if found == 0 =>
        DataLayer(0, Vector.empty)
      case (_, BinaryNatural(found)) if found > 0 && !found.testBit(0) =>
        DataLayer(1, Vector.empty :+ BinaryNatural(found >> 1))
      case (_, BinaryNatural(found)) if found.testBit(0) =>
        DataLayer(2, Vector.empty :+ BinaryNatural(found >> 1))
      case (atParameter, other) =>
        throw IllegalArgumentException(
          s"no binary natural at $atParameter: $other"
        )

  /** Every layer is one at true, the canonical naturals, which hold the
    * positive ones as well: zero, `binary_even h` for h > 0, and
    * `binary_odd h`. `binary_even binary_zero` is no layer.
    */
  override def builtParameter[Term](
      native: NativeName,
      fields: Vector[NativeValue[Term]]
  ): Option[Option[FamilyParameter[Term]]] =
    (native, fields) match
      case (`zeroNative`, Vector()) => Some(canonical)
      case (`evenNative`, Vector(BinaryNatural(half))) if half > 0 =>
        Some(canonical)
      case (`oddNative`, Vector(BinaryNatural(_))) => Some(canonical)
      case _                                       => None

  /** The constructors at true, which are those at false as well. */
  override val shapeParameters: Vector[Option[FamilyParameter[Nothing]]] =
    Vector(canonical)

  override def parameterOf[Term](
      value: NativeValue[Term]
  ): FamilyParameter[Term] = value match
    case NativeValue.Truth(canonical) => BinaryCanonicity(canonical)
    case other                        =>
      throw IllegalArgumentException(
        s"no parameter of a binary natural: $other"
      )

  override def parameterValue[Term](
      parameter: FamilyParameter[Term]
  ): NativeValue[Term] = parameter match
    case BinaryCanonicity(canonical) => NativeValue.Truth(canonical)
    case other                       =>
      throw IllegalArgumentException(
        s"no parameter of a binary natural: $other"
      )

  /** Whether the parameter is the canonical naturals' (true) or the positive
    * ones' (false). Throws `IllegalArgumentException` for any other parameter:
    * the JIT gives the family only parameters it decoded in `boolean`.
    */
  private def canonicity(parameter: Option[FamilyParameter[Any]]): Boolean =
    parameter match
      case Some(BinaryCanonicity(value)) => value
      case other                         =>
        throw IllegalArgumentException(
          s"no parameter of a binary natural: $other"
        )
