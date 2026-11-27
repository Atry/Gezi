package com.yang_bo.gezi.contest.corpora.merges

import com.yang_bo.gezi.contest.corpora.claims

/** One fact a family poses about one of its points, the ports of the multifile
  * hooks the Prolog files defined clauses of:
  * `contest_hard_answers:hard_intended/3`, `point_purpose/2` and
  * `hard_raised_limits/2`, and `contest_hard_claims:scored_finite_head/3` and
  * `no_yield_trap/3`. A value, a template and limits are the claims group's
  * (`claims.IntendedValue`, `claims.Template`, `claims.Limits`), as the judges
  * read them; an argument or a reason is the text the claim cites.
  */
enum ClaimFact:

  /** The point the fact is about. */
  def point: String

  /** `hard_intended(Point, Outcome, Value)`. */
  case HardIntended(
      point: String,
      outcome: claims.IntendedOutcome,
      value: claims.IntendedValue
  )

  /** `point_purpose(Point, Purpose)`. */
  case PointPurpose(point: String, purpose: String)

  /** `hard_raised_limits(Point, Limits)`. */
  case HardRaisedLimits(point: String, limits: claims.Limits)

  /** `scored_finite_head(Point, Templates, Argument)`. */
  case ScoredFiniteHead(
      point: String,
      templates: Vector[claims.Template],
      argument: String
  )

  /** `no_yield_trap(Point, Templates, Reason)`. */
  case NoYieldTrap(
      point: String,
      templates: Vector[claims.Template],
      reason: String
  )

  /** The line the reference of the file's claims holds for this fact:
    * `Kind(Point)`, then each other argument, a term as Prolog's `~q` wrote it
    * and a text as it is, separated by tabs.
    */
  def line: String = this match
    case HardIntended(point, outcome, value) =>
      s"hard_intended($point)\t${outcome.written}\t${value.written}"
    case PointPurpose(point, purpose)    => s"point_purpose($point)\t$purpose"
    case HardRaisedLimits(point, limits) =>
      s"hard_raised_limits($point)\t${limits.written}"
    case ScoredFiniteHead(point, templates, argument) =>
      s"scored_finite_head($point)\t${templates.map(_.written).mkString("[", ",", "]")}\t$argument"
    case NoYieldTrap(point, templates, reason) =>
      s"no_yield_trap($point)\t${templates.map(_.written).mkString("[", ",", "]")}\t$reason"

/** The templates and limits the claims of this package name. */
object ClaimFact:

  /** `boolean(Truth)`. */
  def boolean(truth: Boolean): claims.Template =
    claims.Template.BooleanTemplate(truth)

  /** The template's text as `~w` writes it inside an argument. */
  def text(template: claims.Template): String = template.written

  /** The limits of the merge and mixin families, 10 s, 256 MB of stack and 256
    * MB of table space: `limits(10, 256, 256)`.
    */
  val familyLimits: claims.Limits = claims.Limits.of(10, 256, 256)

  /** The intended value a finite head's template names. Throws for a template
    * that names no value (a member of a certificate).
    */
  def intendedValue(template: claims.Template): claims.IntendedValue =
    template match
      case claims.Template.BooleanTemplate(value) =>
        claims.IntendedValue.BooleanValue(value)
      case claims.Template.NaturalTemplate(count) =>
        claims.IntendedValue.NaturalValue(count)
      case other =>
        throw IllegalArgumentException(s"no intended value of ${other.written}")

  /** The three facts every scored point of the merge and mixin families poses
    * besides its claim: its intended head, the purpose `inheritance` and the
    * family's limits, in the order the Prolog files enumerate them.
    */
  def headPoint(point: String, template: claims.Template): Vector[ClaimFact] =
    Vector(
      HardIntended(point, claims.IntendedOutcome.Head, intendedValue(template)),
      PointPurpose(point, "inheritance"),
      HardRaisedLimits(point, familyLimits)
    )
