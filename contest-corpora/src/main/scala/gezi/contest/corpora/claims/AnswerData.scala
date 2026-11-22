package gezi.contest.corpora.claims

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamily
import gezi.contest.corpora.common.ProblemField


/** A number of the answer tables as Prolog's arithmetic gives it: an
  * integer, or a float. `written` is its text as `writeq/1` writes it.
  */
enum PrologNumber:
  case IntegerNumber(value: BigInt)
  case FloatNumber(value: Double)

  def written: String = this match
    case IntegerNumber(value) => value.toString
    case FloatNumber(value)   => value.toString

  /** The value as a double, for comparisons. */
  def toDouble: Double = this match
    case IntegerNumber(value) => value.toDouble
    case FloatNumber(value)   => value

/** Prolog's arithmetic on the answer tables' numbers. */
object PrologNumber:

  /** `Dividend / Divisor` as SWI-Prolog evaluates `/` with its default
    * flags: an integer when the integers divide exactly, a float otherwise.
    */
  def divided(dividend: BigInt, divisor: BigInt): PrologNumber =
    if dividend % divisor == 0 then IntegerNumber(dividend / divisor)
    else FloatNumber(dividend.toDouble / divisor.toDouble)

  /** `max(Left, Right)` and `min(Left, Right)`: the larger, or the smaller,
    * of the two as it stands.
    */
  def maximum(left: PrologNumber, right: PrologNumber): PrologNumber =
    if left.toDouble >= right.toDouble then left else right

  def minimum(left: PrologNumber, right: PrologNumber): PrologNumber =
    if left.toDouble <= right.toDouble then left else right


/** `limits(Seconds, StackMegabytes, TableMegabytes)`. */
final case class Limits(seconds: PrologNumber, stackMegabytes: Int, tableMegabytes: Int):
  def written: String = s"limits(${seconds.written},$stackMegabytes,$tableMegabytes)"

object Limits:

  /** Limits of whole seconds. */
  def of(seconds: Int, stackMegabytes: Int, tableMegabytes: Int): Limits =
    Limits(PrologNumber.IntegerNumber(seconds), stackMegabytes, tableMegabytes)

  /** The limits a data file writes, the plain tuple `λtuple. tuple S M T`
    * of the seconds, the stack megabytes and the table megabytes, each the
    * library's Scott integer (`ProblemData.integer`), read as the one
    * alternative of one handler (`ProblemData.alternative`).
    */
  def read(field: ProblemField): Limits = ProblemData.alternative(field, 1) match
    case (0, Vector(seconds, stack, table)) =>
      Limits(PrologNumber.IntegerNumber(ProblemData.integer(seconds)), ProblemData.small(stack), ProblemData.small(table))
    case (position, fields) =>
      throw IllegalArgumentException(s"limits are a tuple of three fields, not alternative $position of ${fields.size}")

/** The value of an intended answer: `boolean(B)`, `natural(N)`,
  * `certificate(Name)` or `none`, the constructors of
  * problems/schema/intended_value in order. `written` is the value as the
  * claims print it and as `ContestAnswers.decodingsVerdict` compares the
  * decodings with it; the data do not write it.
  */
enum IntendedValue:
  case BooleanValue(value: Boolean)
  case NaturalValue(value: Int)
  case CertificateValue(name: String)
  case NoValue

  def written: String = this match
    case BooleanValue(value)    => s"boolean($value)"
    case NaturalValue(value)    => s"natural($value)"
    case CertificateValue(name) => s"certificate($name)"
    case NoValue                => "none"

object IntendedValue:

  /** The value a field writes, a constructor of
    * problems/schema/intended_value read by its position
    * (`ProblemData.alternative`), in the order of the enum's cases: boolean
    * of a Church Boolean (`ProblemData.boolean`), natural of its count,
    * certificate of its name, none. Throws for any other term.
    */
  def read(term: ProblemField): IntendedValue =
    ProblemData.alternative(term, ProblemData.caseCount[IntendedValue]) match
      case (0, Vector(value)) => BooleanValue(ProblemData.boolean(value))
      case (1, Vector(count)) => NaturalValue(ProblemData.small(count))
      case (2, Vector(name))  => CertificateValue(ProblemData.text(name))
      case (3, Vector())      => NoValue
      case (position, fields) =>
        throw IllegalArgumentException(s"an intended value at position $position has ${fields.size} fields")

/** An intended answer: `head` or `failed`, and its value. */
final case class Intended(outcome: IntendedOutcome, value: IntendedValue)

/** The outcome of an intended answer, the constructors of
  * problems/schema/outcome in order: the program has a weak head, or it
  * has none. `written` is the outcome as the claims print it; the data do
  * not write it.
  */
enum IntendedOutcome(val written: String):
  case Head extends IntendedOutcome("head")
  case Failed extends IntendedOutcome("failed")

object IntendedOutcome:

  /** The outcome a field writes, a constructor of problems/schema/outcome
    * read by its position (`ProblemData.alternative`).
    */
  def read(term: ProblemField): IntendedOutcome =
    ProblemData.alternative(term, IntendedOutcome.values.size) match
      case (position, Vector()) => IntendedOutcome.fromOrdinal(position)
      case (_, fields)          => throw IllegalArgumentException(s"an intended outcome has ${fields.size} fields")

/** A claim's template (`problems/hard_claims`): `boolean(B)`,
  * `natural(Count)` or `member(Index, Certificate)`, the constructors of
  * problems/schema/template in order. `written` is the template as the
  * claims print it; the data do not write it.
  */
enum Template:
  case BooleanTemplate(value: Boolean)
  case NaturalTemplate(count: Int)
  case MemberTemplate(index: Int, certificate: String)

  def written: String = this match
    case BooleanTemplate(value)              => s"boolean($value)"
    case NaturalTemplate(count)              => s"natural($count)"
    case MemberTemplate(index, certificate) => s"member($index,$certificate)"

object Template:

  /** The template a field writes, a constructor of problems/schema/template
    * read by its position (`ProblemData.alternative`), in the order of the
    * enum's cases: boolean of a Church Boolean (`ProblemData.boolean`),
    * natural of its count, member of its index and certificate. Throws for
    * any other term.
    */
  def read(term: ProblemField): Template =
    ProblemData.alternative(term, ProblemData.caseCount[Template]) match
      case (0, Vector(value))              => BooleanTemplate(ProblemData.boolean(value))
      case (1, Vector(count))              => NaturalTemplate(ProblemData.small(count))
      case (2, Vector(index, certificate)) => MemberTemplate(ProblemData.small(index), ProblemData.text(certificate))
      case (position, fields) =>
        throw IllegalArgumentException(s"a template at position $position has ${fields.size} fields")

  /** The template of an intended value of a finite head. Throws for a value
    * that is no template.
    */
  def of(value: IntendedValue): Template = value match
    case IntendedValue.BooleanValue(boolean) => BooleanTemplate(boolean)
    case IntendedValue.NaturalValue(count)   => NaturalTemplate(count)
    case other => throw IllegalArgumentException(s"no template of ${other.written}")

/** A claim's proof: `proved(Argument)` or `conjecture(Class)`. */
final case class Proof(proved: Boolean, argument: String):
  def written: String = if proved then s"proved($argument)" else s"conjecture($argument)"

object Proof:

  /** The number of constructors of problems/schema/proof: proved, then
    * conjecture.
    */
  private val constructorCount: Int = 2

  /** The proof a field writes, a constructor of problems/schema/proof read
    * by its position (`ProblemData.alternative`): proved of its argument,
    * then conjecture of its class. Throws for any other term.
    */
  def read(term: ProblemField): Proof = ProblemData.alternative(term, constructorCount) match
    case (0, Vector(argument)) => Proof(true, ProblemData.text(argument))
    case (1, Vector(argument)) => Proof(false, ProblemData.text(argument))
    case (position, fields) =>
      throw IllegalArgumentException(s"a proof at position $position has ${fields.size} fields")

/** `cycle_claim(Class, Kind, Template, Proof)`. */
final case class CycleClaim(cycleClass: String, kind: String, template: Template, proof: Proof)

object CycleClaim:

  /** The `cycle_claim/4` rows of the family, in order: its own (the table
    * `cycle_claim`), or with `qualified` those it adds to
    * `contest_hard_claims` (the table `contest_hard_claims__cycle_claim`).
    */
  def facts(file: ProblemFamily, qualified: Boolean): Vector[CycleClaim] =
    file.rows(if qualified then "contest_hard_claims__cycle_claim" else "cycle_claim").map(arguments =>
      CycleClaim(
        ProblemData.text(arguments(0)),
        ProblemData.text(arguments(1)),
        Template.read(arguments(2)),
        Proof.read(arguments(3))
      )
    )

/** What one file of the hard corpus contributes to the multifile tables of
  * `contest_hard_answers` and `contest_hard_claims`, and its points. Each
  * hidden family's file added these clauses with bodies in Prolog; here they
  * are values computed from the family's facts.
  */
trait HardFamily:

  /** The points the file defines in `contest_hard`, by name. */
  def points: Map[String, () => gezi.frontend.Term]

  /** `contest_hard_answers:hard_intended/3`, point and answer. */
  def intended: Vector[(String, Intended)]

  /** `contest_hard_claims:unread_finite_head/2`, point and argument. */
  def unreadFiniteHeads: Vector[(String, String)]

  /** `contest_hard_claims:cycle/3`, point, class and construction. */
  def cycles: Vector[(String, String, String)]

  /** `contest_hard_claims:cycle_claim/4`. */
  def cycleClaims: Vector[CycleClaim]

  /** `contest_hard_claims:scored_finite_head/3`, point and templates: the
    * hook the merge and mixin families and the empty-set reachability pose
    * their scored claims by; none for the claims group's families.
    */
  def scoredFiniteHeads: Vector[(String, Vector[Template])] = Vector.empty

  /** `contest_hard_claims:no_yield_trap/3`, point and templates; none for
    * the claims group's families.
    */
  def noYieldTraps: Vector[(String, Vector[Template])] = Vector.empty
