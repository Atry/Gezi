package com.yang_bo.gezi.weakhead

import com.yang_bo.gezi.ir.{Configured, NativeSpecializer, Value}

/** A constructor of the naturals the codec decodes into and encodes from. */
enum NaturalConstructor:
  case Zero
  case Successor

/** A case a natural is applied to in a decoding: the decoding, the field depth
  * and the constructor; a neutral value no closed program can name.
  *
  * A neutral value, a free variable (`CONTRIBUTING.md`, "Types live only in the
  * term"), kept as an exception argued here: it stands for a binder of the
  * value read (a Scott value's handler, a constructor's or a define's
  * parameter), opened to read the value's head, as the normal-form reader's
  * `BoundVariable` opens a lambda, whose Scaladoc has the argument. A closed
  * term in its place would not do: a term that is no such value could ignore it
  * and build the reading itself.
  */
final case class NaturalCase(
    decoding: Decoding,
    level: Int,
    constructor: NaturalConstructor
) extends NeutralVariable

/** The fresh field the check of the constructors applies successor to.
  *
  * A neutral value, a free variable (`CONTRIBUTING.md`, "Types live only in the
  * term"), kept as an exception argued here: it stands for a binder of the
  * value read (a Scott value's handler, a constructor's or a define's
  * parameter), opened to read the value's head, as the normal-form reader's
  * `BoundVariable` opens a lambda, whose Scaladoc has the argument. A closed
  * term in its place would not do: a term that is no such value could ignore it
  * and build the reading itself.
  */
final case class NaturalField(decoding: Decoding) extends NeutralVariable

/** What a head of a value applied to a decoding's cases reads. */
enum NaturalReading[C <: NativeSpecializer & Singleton]:

  /** The first case with no argument. */
  case Zero()

  /** The second case over one argument, the field. */
  case Successor(field: Value[C])

  /** Any other head (the Prolog codec's `none`). */
  case NoCase()

/** The codec of the representation big_integer: the library's naturals as
  * integers. The port of `gezi/prolog/gezi/big_integer_codec.pl`, a
  * hand-written codec, for the representation the Prolog backend's fact
  * `native_specialization(big_integer)` names: the integer n stands for the
  * term successor^n zero, zero and successor the terms at the positions 0 and 1
  * of the `data_family` of the type the knowledge module of the backend
  * specializes to big_integer (`position`). The runtime reads no description of
  * a type: this codec assumes one shape of value, and the JIT drives the
  * decoding and the encoding by evaluation. It decides no type: it reads the
  * heads a value applied to its own cases answers.
  *
  * THE ASSUMED SHAPE. A natural is a Scott value of two cases: applied to two
  * arguments, zero's value answers the first and successor p's value answers
  * the second applied to p, as `\z. \s. z` and `\p. \z. \s. s p` do. DECODING a
  * value applies it to the two cases of `decodingCases` and reads each head
  * with `caseReading`: the first case alone reads Zero, the second over one
  * argument reads Successor of it, the field then decoded one level deeper with
  * cases of its own level, so that a field that answers an outer level's case
  * reads NoCase; any other head reads NoCase, and decoding there gives no
  * answer.
  *
  * WHY A DECODED INTEGER STANDS FOR THE FILTERED VALUE, and why the declaration
  * native_specialization(big_integer) is trusted as a native is and vouched for
  * by the comparison test of the JIT's natives: the Prolog module comment,
  * unchanged (x ⊑ N(n) by the decoding, T ⊑ N(n) by the declaration, x ∥ T ⊑
  * N(n) by the parallel's row of `NormalForms`).
  */
object BigIntegerCodec:

  /** The two cases a value of the decoding is applied to at the field depth.
    */
  def decodingCases[C <: NativeSpecializer & Singleton](
      decoding: Decoding,
      level: Int
  )(using C): (Value[C], Value[C]) =
    (
      NeutralValue(
        NaturalCase(decoding, level, NaturalConstructor.Zero),
        Vector.empty
      ),
      NeutralValue(
        NaturalCase(decoding, level, NaturalConstructor.Successor),
        Vector.empty
      )
    )

  /** What a head of a value applied to the decoding's cases at the level reads.
    */
  def caseReading[C <: NativeSpecializer & Singleton](
      head: Head[C],
      decoding: Decoding,
      level: Int
  )(using
      C
  ): NaturalReading[C] = head match
    case Head.Neutral(
          NaturalCase(`decoding`, `level`, NaturalConstructor.Zero),
          arguments
        ) if arguments.isEmpty =>
      NaturalReading.Zero()
    case Head.Neutral(
          NaturalCase(`decoding`, `level`, NaturalConstructor.Successor),
          Vector(field)
        ) =>
      NaturalReading.Successor(field)
    case _ => NaturalReading.NoCase()

  /** The position of the constructor among the cases, by the assumed shape, and
    * so in the `data_family` of a type the codec holds: zero 0, successor 1. A
    * constructor is its position, never a name.
    */
  def position(constructor: NaturalConstructor): Int = constructor match
    case NaturalConstructor.Zero      => 0
    case NaturalConstructor.Successor => 1

  /** The term successor^natural zero applied to the count of arguments answers
    * its branch-th argument applied to the naturals of the fields, by the
    * assumed shape: 0 answers the first of two arguments with no field, n + 1
    * the second applied to n. The count, the branch and the fields.
    */
  def eliminatedBranch(natural: BigInt): (Int, Int, Vector[BigInt]) =
    require(natural >= 0, s"a natural is not negative: $natural")
    if natural == 0 then (2, 1, Vector.empty) else (2, 2, Vector(natural - 1))

  /** Whether the defines zero and successor have the assumed shape, read under
    * weak_head: every head of zero applied to the cases reads Zero, and every
    * head of successor applied to a fresh field and then to the cases reads
    * Successor of that field, each with at least one head; `Shape.LimitReached`
    * when a reading runs past its budget. Each reading within
    * `Codecs.shapeStepLimit` steps.
    */
  def constructorsShape[C <: NativeSpecializer & Singleton](
      zero: Configured[C],
      successor: Configured[C]
  )(using
      C,
      com.yang_bo.gezi.ir.StorageAccess
  ): Shape[NaturalReading[C]] =
    val (zeroCase, successorCase) = decodingCases[C](Decoding.Shape, 0)
    val field = NeutralValue[C](NaturalField(Decoding.Shape), Vector.empty)
    val zeroReadings = Codecs.readingsWithin(
      Value.Apply(Value.Apply(Value.of(zero), zeroCase), successorCase),
      NaturalReading.NoCase[C]()
    )(caseReading(_, Decoding.Shape, 0))
    val successorReadings = Codecs.readingsWithin(
      Value.Apply(
        Value.Apply(Value.Apply(Value.of(successor), field), zeroCase),
        successorCase
      ),
      NaturalReading.NoCase[C]()
    )(caseReading(_, Decoding.Shape, 0))
    Codecs.shapeOf(
      zeroReadings,
      successorReadings,
      NaturalReading.Zero[C](),
      NaturalReading.Successor(field)
    )
