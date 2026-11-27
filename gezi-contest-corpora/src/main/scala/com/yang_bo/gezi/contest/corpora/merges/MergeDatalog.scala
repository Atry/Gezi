package com.yang_bo.gezi.contest.corpora.merges

import com.yang_bo.gezi.contest.corpora.common.ProblemData
import com.yang_bo.gezi.contest.corpora.common.ProblemFamilies

import com.yang_bo.gezi.contest.corpora.merges.ClaimFact.ScoredFiniteHead
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.*
import scala.annotation.tailrec

/** A Datalog relation of the merge family over the constants 0 to count - 1:
  * its facts From to To, the rule (`path`, the transitive closure, or `reach`,
  * the closure of the symmetric relation) and the queried tuple (`relation/7`).
  */
final case class MergeDatalogRelation(
    count: Int,
    facts: Vector[(Int, Int)],
    rule: MergeDatalog.DatalogRule,
    from: Int,
    to: Int
)

/** The port of the deleted Prolog file (`git show
  * 91b3f11e1^:lambda_jit/corpora/contest_merge_datalog.pl`; its data are
  * `problems/merge_datalog`): a recursive Datalog rule in lambda plus choice,
  * the constants unary numerals let bound once (`MergeGraph.numeralLets`), the
  * relation a nested numeral case of Church Booleans, existence the choice over
  * every constant. The Booleans, the bodies of `and`, `sym` and the closure,
  * and the table of points are read from the family's directory,
  * `gezi/problems/merge_datalog`.
  */
final class MergeDatalog(problems: ProblemFamilies):
  import MergeDatalog.{DatalogRule, DatalogShape}

  private val file = problems("merge_datalog")

  /** `\x. \y. ...`, the case on x of a case on y of the flag of the tuple
    * (`relation_body/5`).
    */
  private def relationBody(
      facts: Vector[(Int, Int)],
      count: Int,
      trueValue: ProblemTerm,
      falseValue: ProblemTerm
  ): ProblemTerm =
    λ(x =>
      λ(y =>
        MergeGraph.numeralCase(
          (0 until count).toVector.map(from =>
            MergeGraph.numeralCase(
              (0 until count).toVector.map(to =>
                if facts.contains((from, to)) then trueValue else falseValue
              ),
              y
            )
          ),
          x
        )
      )
    )

  /** The program of the rule, the facts and the queried tuple, under the lets
    * of the Booleans, the constants, the relation, existence and `and`
    * (`rule_term/6`).
    */
  def ruleTerm(
      rule: DatalogRule,
      count: Int,
      facts: Vector[(Int, Int)],
      from: Int,
      to: Int
  ): ProblemTerm =
    λ(trueValue =>
      λ(falseValue =>
        MergeGraph.numeralLets(
          count,
          constants =>
            λ(edge =>
              λ(exists =>
                λ(and =>
                  ruleBody(
                    rule,
                    edge,
                    exists,
                    and,
                    constants(from),
                    constants(to)
                  )
                )(
                  file.program("and_body", falseValue)
                )
              )(λ(function => choice(constants.map(function(_))*)))
            )(relationBody(facts, count, trueValue, falseValue))
        )
      )(file.program("false_term"))
    )(file.program("true_term"))

  private def ruleBody(
      rule: DatalogRule,
      edge: ProblemTerm,
      exists: ProblemTerm,
      and: ProblemTerm,
      from: ProblemTerm,
      to: ProblemTerm
  ): ProblemTerm =
    rule match
      case DatalogRule.Path =>
        λ(path => path(from)(to))(
          file.program("closure_body", edge, exists, and)(
            file.program("closure_body", edge, exists, and)
          )
        )
      case DatalogRule.Reach =>
        λ(symmetric =>
          λ(reach => reach(from)(to))(
            file.program("closure_body", symmetric, exists, and)(
              file.program("closure_body", symmetric, exists, and)
            )
          )
        )(file.program("sym_body", edge))

  /** The relation of a shape and a size: two rings joined by one edge, read by
    * `path`, or a line, read by `reach` (`relation/7`).
    */
  def relation(shape: DatalogShape, size: Int): MergeDatalogRelation =
    shape match
      case DatalogShape.TwoRings =>
        val count = 2 * size
        MergeDatalogRelation(
          count,
          MergeGraph.ringEdges(0, size - 1) ++ Vector(
            (size - 1, size)
          ) ++ MergeGraph.ringEdges(size, count - 1),
          DatalogRule.Path,
          0,
          count - 1
        )
      case DatalogShape.Line =>
        MergeDatalogRelation(
          size,
          (0 until size - 1).toVector.map(node => (node, node + 1)),
          DatalogRule.Reach,
          0,
          size - 1
        )

  /** Whether the tuple holds in the least fixed point of the rule over the
    * facts, by semi-naive evaluation (`reference_holds/4`).
    */
  def referenceHolds(
      rule: DatalogRule,
      facts: Vector[(Int, Int)],
      from: Int,
      to: Int
  ): Boolean =
    val step = rule match
      case DatalogRule.Path  => facts
      case DatalogRule.Reach => facts ++ facts.map(_.swap)
    @tailrec
    def fixpoint(
        known: Set[(Int, Int)],
        delta: Set[(Int, Int)]
    ): Set[(Int, Int)] =
      if delta.isEmpty then known
      else
        val joined = for
          (x, y) <- step.toSet
          (middle, z) <- delta
          if middle == y
        yield (x, z)
        val fresh = joined -- known
        fixpoint(known ++ fresh, fresh)
    fixpoint(step.toSet, step.toSet).contains((from, to))

  /** The points, each with its shape and size (`datalog_point/3`), the shape a
    * constructor of problems/merge_datalog/shape read by its position
    * (`ProblemData.alternative`).
    */
  val points: Vector[(String, DatalogShape, Int)] =
    file
      .rows("datalog_point")
      .map(arguments =>
        (
          ProblemData.text(arguments(0)),
          ProblemData.alternative(arguments(1), DatalogShape.values.size) match
            case (position, Vector()) => DatalogShape.fromOrdinal(position)
            case (_, fields)          =>
              throw IllegalArgumentException(
                s"a shape of contest_merge_datalog has ${fields.size} fields"
              ),
          ProblemData.small(arguments(2))
        )
      )

  /** The point's program. */
  def program(name: String): ProblemTerm =
    points
      .find(_._1 == name)
      .map((_, shape, size) =>
        val shown = relation(shape, size)
        ruleTerm(shown.rule, shown.count, shown.facts, shown.from, shown.to)
      )
      .getOrElse(
        throw IllegalArgumentException(
          s"$name is no point of contest_merge_datalog"
        )
      )

  /** The claim facts of the file's points. */
  def claims: Vector[ClaimFact] =
    points.flatMap((name, shape, size) =>
      val shown = relation(shape, size)
      assert(
        referenceHolds(shown.rule, shown.facts, shown.from, shown.to),
        s"the tuple of $name holds"
      )
      ClaimFact.headPoint(name, ClaimFact.boolean(true)) :+ ScoredFiniteHead(
        name,
        Vector(ClaimFact.boolean(true)),
        s"${shown.rule.written}(${shown.from}, ${shown.to}) holds in the least fixpoint of the rule over the ${shape.written} of size $size (semi-naive evaluation); choosing at each existence the constant on a shortest derivation yields the Church true in finitely many head reductions"
      )
    )

object MergeDatalog:

  /** The shape of a point, the constructors of problems/merge_datalog/shape in
    * order: two rings joined by one edge, then a line. `written` is the shape's
    * name in the claims' prose, not a key of the data.
    */
  enum DatalogShape(val written: String):
    case TwoRings extends DatalogShape("two_rings")
    case Line extends DatalogShape("line")

  /** The rule a shape is read by: `path`, the transitive closure, or `reach`,
    * the closure of the symmetric relation. `written` is the rule's name in the
    * claims' prose.
    */
  enum DatalogRule(val written: String):
    case Path extends DatalogRule("path")
    case Reach extends DatalogRule("reach")
