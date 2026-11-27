package gezi.contest.corpora.claims

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamily

import gezi.frontend.Term
import gezi.frontend.Term.λ

/** A claim of the hard corpus: `hard_claim(Point, Kind, Template, Proof)`. */
final case class HardClaim(point: String, kind: String, template: Template, proof: Proof)

/** The claims of the hard corpus under rule 30, the code of
  * `problems/hard_claims`: which claims a point poses
  * (finite heads, their traps, and the cycles' classes), and each claim's
  * test program over the point's term. Its facts (`unread_finite_head/2`,
  * `cycle/3`, `cycle_claim/4`, `conjecture_proved/3`, `wrong_value/2`,
  * `round_ten_least_solution_reading/2` and the templates' bodies
  * `template_body/4`) are read from the tables of the family
  * `gezi/problems/hard_claims`; the families add their own clauses
  * (`HardFamily`).
  *
  * The merge and mixin families and the empty-set reachability pose their
  * claims by the hooks `scored_finite_head/3` and `no_yield_trap/3`
  * (`HardFamily.scoredFiniteHeads`, `noYieldTraps`); the families of all the
  * groups are gathered by `common.HardCorpus`. No corpus file defines a
  * clause of the third hook, `no_yield_conjecture/3`, so it is not ported.
  */
final class HardClaims(
    corpora: Corpora,
    answers: HardAnswers,
    families: Vector[HardFamily],
    points: Map[String, () => ProblemTerm]
):

  private def file: ProblemFamily = corpora.contestHardClaims

  /** `unread_finite_head(Point, Argument)`, every clause's argument. */
  def unreadFiniteHeads(point: String): Vector[String] =
    file.rows("unread_finite_head").collect {
      case Vector(key, text) if ProblemData.text(key) == point => ProblemData.text(text)
    } ++ families.flatMap(_.unreadFiniteHeads).collect { case (`point`, text) => text }

  /** `round_ten_least_solution_reading(Point, Setting)`: the first reading
    * of round 10 that read the point's intended head under a least-solution
    * setting. The readings are those of the archived round-10 log of the
    * hard corpus, carried as data in the family.
    */
  lazy val roundTenReadings: Map[String, String] =
    file.rows("round_ten_least_solution_reading").map {
      case Vector(point, setting) => ProblemData.text(point) -> ProblemData.text(setting)
      case row => throw IllegalArgumentException(s"a round_ten_least_solution_reading row of ${row.length} fields")
    }.toMap

  /** `finite_head(Point, Certificate)`: `read(Setting)` or
    * `argument(Text)`, as text.
    */
  def finiteHeads(point: String): Vector[String] =
    val read =
      if answers.hardIntended(point).exists(_.outcome == IntendedOutcome.Head) && unreadFiniteHeads(point).isEmpty then
        roundTenReadings.get(point).map(setting => s"read($setting)").toVector
      else Vector.empty
    read ++ unreadFiniteHeads(point).map(text => s"argument($text)")

  /** `wrong_value(Template, Wrong)`: the facts for the booleans, and the
    * numerals one above and one below.
    */
  def wrongValues(template: Template): Vector[Template] = template match
    case Template.NaturalTemplate(count) =>
      Template.NaturalTemplate(count + 1) +: (if count > 0 then Vector(Template.NaturalTemplate(count - 1)) else Vector.empty)
    case _ =>
      file.rows("wrong_value").collect {
        case Vector(right, wrong) if Template.read(right) == template => Template.read(wrong)
      }

  /** `cycle(Point, Class, Construction)`, class and construction. */
  def cycles(point: String): Vector[(String, String)] =
    file.rows("cycle").collect {
      case Vector(key, cycleClass, construction) if ProblemData.text(key) == point =>
        ProblemData.text(cycleClass) -> ProblemData.text(construction)
    } ++ families.flatMap(_.cycles).collect { case (`point`, cycleClass, construction) => cycleClass -> construction }

  /** `cycle_claim/4`: the file's facts, then the families'. */
  def cycleClaims: Vector[CycleClaim] = CycleClaim.facts(file, false) ++ families.flatMap(_.cycleClaims)

  /** The points of the rules of `conjecture_proved/3`, by argument, each
    * with the templates it proves.
    */
  private def provedByRules: Vector[(Vector[String], Vector[Template], String)] =
    val both = Vector(Template.BooleanTemplate(true), Template.BooleanTemplate(false))
    Vector(
      (Vector("respelled_and_false_self", "respelled_and_false_identity", "respelled_if_false_self"),
        Vector(Template.BooleanTemplate(false)), "respelled_collapse"),
      (Vector("path_rebuilt_by_identity", "path_rebuilt_by_plus_minus_small", "path_rebuilt_by_plus_minus_tiny",
        "path_eta_expanded", "safety_escape_behind_traps"), both, "safety_collapse"),
      (Vector("type_dead_index_subtype", "type_recomputed_index_subtype", "type_periods_subtype_small",
        "type_periods_subtype_large"), both, "subtype_collapse"),
      (Vector("arithmetic_double_at_least_itself", "arithmetic_plus_three_differs", "arithmetic_plus_two_commutes"),
        both, "arithmetic_search"),
      (Vector("continuation_true_eta"), both, "continuation_eta_omega"),
      (Vector("continuation_nested_true", "continuation_nested_false"), both, "continuation_projection_collapse")
    )

  /** `conjecture_proved(Point, Template, Argument)`, the first argument. */
  def conjectureProved(point: String, template: Template): Option[String] =
    file.rows("conjecture_proved").collectFirst {
      case Vector(key, proved, argument) if ProblemData.text(key) == point && Template.read(proved) == template =>
        ProblemData.text(argument)
    }.orElse(provedByRules.collectFirst {
      case (provedPoints, templates, argument) if provedPoints.contains(point) && templates.contains(template) =>
        argument
    })

  /** `claim_proof(Point, Template, ClassProof)`. */
  private def claimProof(point: String, template: Template, classProof: Proof): Proof =
    if classProof.proved then classProof
    else conjectureProved(point, template).fold(classProof)(argument => Proof(true, argument))

  /** `hard_claim(Point, Kind, Template, Proof)`: the claims of the point. */
  def hardClaims(point: String): Vector[HardClaim] =
    val heads = finiteHeads(point)
    // A point with no finite head may intend a certificate, which is no
    // template; only a finite head's intended value is made a template.
    val intendedTemplates =
      if heads.isEmpty then Vector.empty
      else answers.hardIntended(point).filter(_.outcome == IntendedOutcome.Head).map(intended => Template.of(intended.value))
    val scored =
      for
        _ <- heads
        template <- intendedTemplates
      yield HardClaim(point, "scored", template, Proof(true, "finite_head"))
    val traps =
      for
        _ <- heads
        template <- intendedTemplates
        wrong <- wrongValues(template)
      yield HardClaim(point, "trap", wrong, Proof(true, "finite_head"))
    val scoredByHook =
      for
        (hookPoint, templates) <- families.flatMap(_.scoredFiniteHeads)
        if hookPoint == point
        template <- templates
      yield HardClaim(point, "scored", template, Proof(true, "finite_head"))
    val trapsByHook =
      for
        (hookPoint, templates) <- families.flatMap(_.noYieldTraps)
        if hookPoint == point
        template <- templates
      yield HardClaim(point, "trap", template, Proof(true, "no_yield"))
    val cycleClaimsOfPoint =
      for
        (cycleClass, _) <- cycles(point)
        claim <- cycleClaims.filter(_.cycleClass == cycleClass)
      yield HardClaim(point, claim.kind, claim.template, claimProof(point, claim.template, claim.proof))
    scored ++ traps ++ scoredByHook ++ trapsByHook ++ cycleClaimsOfPoint

  /** `claim_test(Point, Template, Test)`: `\a. Body`, the template's body
    * over the point's term. A natural's body is the rule `numeral_test/5`;
    * the other templates' bodies are the rows of `template_body/4`, each an
    * open program over the term, the argument and its free variables.
    * Throws for a point with no generator.
    */
  def claimTest(point: String, template: Template): OpenTest =
    val term = points.getOrElse(point, throw IllegalArgumentException(s"no generator for the point $point"))()
    template match
      case Template.NaturalTemplate(count) =>
        OpenTest(1, free => λ(argument => numeralTest(count, term, argument, free(0))))
      case _ =>
        val arguments = file.rows("template_body").filter(row => Template.read(row(0)) == template) match
          case Vector(single) => single
          case found => throw IllegalArgumentException(s"${found.length} bodies of ${template.written}")
        val (freeCount, body) = ProblemData.openProgram(arguments(3))
        OpenTest(freeCount, free => λ(argument => body(Vector(term, argument) ++ free.take(freeCount))))

  /** `numeral_test(Count, Term, Argument, Free)`. */
  def numeralTest(count: Int, term: ProblemTerm, argument: ProblemTerm, free: ProblemTerm): ProblemTerm =
    if count == 0 then term(argument)(free)
    else term(free)(λ(predecessor => numeralTest(count - 1, predecessor, argument, free)))

  /** `claim_program(Point, Template, Program, Expected)`. */
  def claimProgram(point: String, template: Template): (ProblemTerm, ProblemTerm) =
    ContestClaims.testProgram(claimTest(point, template))
