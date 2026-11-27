package gezi.contest.corpora.merges

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamilies
import gezi.contest.corpora.common.ProblemField

import gezi.contest.corpora.merges.ClaimFact.HardIntended
import gezi.contest.corpora.merges.ClaimFact.HardRaisedLimits
import gezi.contest.corpora.merges.ClaimFact.NoYieldTrap
import gezi.contest.corpora.merges.ClaimFact.PointPurpose
import gezi.contest.corpora.reductions
import gezi.frontend.Term

/** The port of the deleted Prolog file (`git show
  * 91b3f11e1^:lambda_jit/corpora/contest_mixin_traps.pl`; its data are
  * `problems/mixin_traps`): the no-yield traps of the mixin family,
  * reachability that misses (the target an isolated node), the diamond's two
  * hops from a back to a, and counterexample searches of true theorems, the
  * searches of `problems/reduction_mixin_theorems` (the reduction group's port,
  * `reductions.ReductionMixinTheorems`, over the group's mixin library). The
  * tables of the misses and the theorems are read from the family's directory,
  * `gezi/problems/mixin_traps`.
  */
final class MixinTraps(
    problems: ProblemFamilies,
    searches: MixinClaims,
    theorems: reductions.ReductionGroup
):

  private val file = problems("mixin_traps")

  /** The misses, each with its graph and source (`miss_point/3`). */
  val missPoints: Vector[(String, MixinGraphName, String)] =
    file
      .rows("miss_point")
      .map(arguments =>
        (
          ProblemData.text(arguments(0)),
          MixinTraps.graphName(arguments(1)),
          ProblemData.text(arguments(2))
        )
      )

  /** The theorem traps, each with its proposition (`theorem_trap/2`). */
  val theoremTraps: Vector[(String, ProblemField)] =
    file
      .rows("theorem_trap")
      .map(arguments => (ProblemData.text(arguments(0)), arguments(1)))

  /** The trap points, in the order of `trap_point/1`. */
  val trapPoints: Vector[String] =
    (missPoints.map(_._1) :+ "mixin_diamond_two_hop_self") ++ theoremTraps.map(
      _._1
    )

  /** The point's program. */
  def program(name: String): ProblemTerm =
    if name == "mixin_diamond_two_hop_self" then
      searches.graphSurface(
        MixinGraphName.Diamond,
        MixinQuery("two_hop", "a", "a")
      )
    else
      missPoints
        .find(_._1 == name)
        .map((_, graph, source) =>
          searches.graphSurface(
            MixinGraphName.Isolated(graph),
            MixinQuery("reachable", source, "z")
          )
        )
        .orElse(
          theoremTraps
            .find(_._1 == name)
            .map((_, proposition) =>
              reductions.ReductionMixinTheorems.propositionSurface(
                theorems.mixins,
                reductions.ReductionMixinTheorems.propositionOf(proposition)
              )
            )
        )
        .getOrElse(
          throw IllegalArgumentException(
            s"$name is no point of contest_mixin_traps"
          )
        )

  /** The claim facts of the file's points. */
  def claims: Vector[ClaimFact] =
    val both = Vector(ClaimFact.boolean(true), ClaimFact.boolean(false))
    val reasons = missPoints.map((name, _, _) =>
      name -> MixinTraps.missReason
    ) ++
      Vector("mixin_diamond_two_hop_self" -> MixinTraps.diamondReason) ++
      theoremTraps.map((name, proposition) =>
        name -> s"the counterexample check ${MixinTraps.written(proposition)} is false at every n, so each round's check computes the Church false and the search spends its step budget of ${reductions.ReductionMixinTheorems.searchBudget} and reaches top; with top replaced by 0 the program terminates, and by the selection theorem (the proofs file's section 20.6) every selection meets 0 and none is a pure term, so neither Boolean is a consistent normal form (Definition 14)"
      )
    reasons.flatMap((name, reason) =>
      Vector(
        HardIntended(
          name,
          gezi.contest.corpora.claims.IntendedOutcome.Failed,
          gezi.contest.corpora.claims.IntendedValue.NoValue
        ),
        PointPurpose(name, "inheritance"),
        HardRaisedLimits(name, ClaimFact.familyLimits),
        NoYieldTrap(name, both, reason)
      )
    )

/** The graphs and the fixed reasons of the traps. */
object MixinTraps:

  /** The proposition a field of `theorem_trap/2` writes, read by the positions
    * of its constructors (`ReductionMixinTheorems.propositionOf`), as the text
    * Prolog's `~w` wrote the term it was ported from, each constructor named by
    * its position (`reductions.Proposition.written`).
    */
  def written(proposition: ProblemField): String =
    reductions.ReductionMixinTheorems.propositionOf(proposition).written

  /** The number of constructors of problems/mixin_traps/graph. */
  private val graphConstructorCount: Int = 8

  /** The graph a datum names, a constructor of problems/mixin_traps/graph read
    * by its position (`ProblemData.alternative`), in the file's order: a ring
    * of its size, the graph with the target isolated of its inner graph, then
    * the direct-first graph, the diamond, the two rings, the ring with chords,
    * the lasso and the double-successor ring.
    */
  def graphName(term: ProblemField): MixinGraphName =
    ProblemData.alternative(term, graphConstructorCount) match
      case (0, Vector(size))  => MixinGraphName.Ring(ProblemData.small(size))
      case (1, Vector(inner)) => MixinGraphName.Isolated(graphName(inner))
      case (2, Vector())      => MixinGraphName.DirectFirst
      case (3, Vector())      => MixinGraphName.Diamond
      case (4, Vector())      => MixinGraphName.TwoRings
      case (5, Vector())      => MixinGraphName.ChordRing
      case (6, Vector())      => MixinGraphName.Lasso
      case (7, Vector())      => MixinGraphName.DoubleSuccessorRing
      case (position, fields) =>
        throw IllegalArgumentException(
          s"the graph of contest_mixin_traps at position $position has ${fields.size} fields"
        )

  /** The reason of the diamond's trap. */
  val diamondReason: String =
    "a does not reach itself in two hops: at every read a sequence reaching a pure term chooses a wrapper defining the slot read, since another slot's wrapper puts the empty set at the head; a.two_hop is self.next.next, a's next is the union of b's and c's classes and theirs is d's class, whose wrappers define is_d, reachable, next and two_hop, none of them is_a, so all of the finitely many sequences end in the empty set at the head and the test yields nothing (contest_mixin_traps.pl, DIAMOND)"

  /** The reason of the misses' traps. */
  val missReason: String =
    "the source does not reach z, which no edge enters: reachable spends a step budget of the node count, so with top replaced by 0 the program terminates, and by the selection theorem (the proofs file's section 20.6) a selection either chooses the class of a node the source reaches, whose wrappers define another slot than is_z and put 0 at the head of the final read, or spends the budget and meets 0; none is a pure term, so neither Boolean is a consistent normal form (Definition 14)"
