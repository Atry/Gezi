package gezi.weakhead

import gezi.ir.Instruction

/** A case a boolean is applied to in a decoding: the decoding and the truth
  * value of the case, the first case `true`; a neutral value no closed
  * program can name.
  *
  * A neutral value, a free variable (`CONTRIBUTING.md`, "Types live only in the term"), kept as an exception argued here:
  * it stands for a
  * binder of the value read (a Scott value's handler, a constructor's or a
  * define's parameter), opened to read the value's head, as the normal-form
  * reader's `BoundVariable` opens a lambda, whose Scaladoc has the argument.
  * A closed term in its place would not do: a term that is no such value
  * could ignore it and build the reading itself.
  */
final case class BooleanCase(decoding: Decoding, truth: Boolean) extends NeutralVariable

/** What a head of a value applied to a decoding's cases reads. */
enum BooleanReading:

  /** The first case or the second, with no argument: the truth value. */
  case Truth(value: Boolean)

  /** Any other head (the Prolog codec's `none`). */
  case NoCase

/** The codec of the representation boolean: the library's booleans as the
  * host's truth values. The port of
  * `gezi/prolog/gezi/boolean_codec.pl`, a hand-written codec, for
  * the representation the Prolog backend's fact
  * `native_specialization(boolean)` names: true stands for the term at the
  * position 0 of the `data_family` of the type the knowledge module of the
  * backend specializes to boolean, false for the term at the position 1
  * (`position`; the Prolog codec's atoms `true` and `false`). It assumes one shape of value and decides no type.
  *
  * THE ASSUMED SHAPE. A boolean is a value of two cases with no field:
  * applied to two arguments, true's value answers the first and false's
  * value the second, as `\t. \f. t` and `\t. \f. f` do. DECODING applies a
  * value to the cases of `decodingCases` and reads each head with
  * `caseReading`. WHY A DECODED BOOLEAN STANDS FOR THE FILTERED VALUE and A
  * TRUSTED DECLARATION: the Prolog module comment, unchanged.
  */
object BooleanCodec:

  /** The two cases a value of the decoding is applied to. */
  def decodingCases(decoding: Decoding): (Value, Value) =
    (
      Value.Neutral(BooleanCase(decoding, true), Vector.empty),
      Value.Neutral(BooleanCase(decoding, false), Vector.empty)
    )

  /** What a head of a value applied to the decoding's cases reads. */
  def caseReading(head: Head, decoding: Decoding): BooleanReading = head match
    case Head.Neutral(BooleanCase(`decoding`, truth), arguments) if arguments.isEmpty =>
      BooleanReading.Truth(truth)
    case _ => BooleanReading.NoCase

  /** The position of the truth value's constructor among the cases, by the
    * assumed shape, and so in the `data_family` of a type the codec holds:
    * true 0, false 1. A constructor is its position, never a name.
    */
  def position(truth: Boolean): Int = if truth then 0 else 1

  /** The define the truth value stands for, applied to the count of
    * arguments, answers its branch-th argument applied to the fields, by the
    * assumed shape: true the first of two, false the second, with no field.
    * The count, the branch and the fields.
    */
  def eliminatedBranch(truth: Boolean): (Int, Int, Vector[Nothing]) =
    if truth then (2, 1, Vector.empty) else (2, 2, Vector.empty)

  /** Whether the defines true and false have the assumed shape, read under
    * weak_head: every head of true applied to the cases reads true, every
    * head of false applied to them reads false, each with at least one head;
    * `Shape.LimitReached` when a reading runs past its budget. Each reading
    * within `Codecs.shapeStepLimit` steps.
    */
  def constructorsShape(trueDefine: Instruction, falseDefine: Instruction): Shape[BooleanReading] =
    val (trueCase, falseCase) = decodingCases(Decoding.Shape)
    def readings(define: Instruction) =
      Codecs.readingsWithin(
        Value.Apply(Value.Apply(define, trueCase), falseCase),
        BooleanReading.NoCase
      )(caseReading(_, Decoding.Shape))
    val trueReadings = readings(trueDefine)
    val falseReadings = readings(falseDefine)
    Codecs.shapeOf(trueReadings, falseReadings, BooleanReading.Truth(true), BooleanReading.Truth(false))
