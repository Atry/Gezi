package com.yang_bo.gezi.contest.corpora.common

import com.yang_bo.gezi.contest.corpora.claims
import com.yang_bo.gezi.contest.corpora.merges
import com.yang_bo.gezi.contest.corpora.merges.ClaimFact
import com.yang_bo.gezi.contest.corpora.merges.ClaimFactFamily
import com.yang_bo.gezi.contest.corpora.reductions
import com.yang_bo.gezi.contest.corpora.reductions.EmptySetReachability
import com.yang_bo.gezi.contest.corpora.reductions.ReachabilityGraph
import com.yang_bo.gezi.hotspot.Cache
import com.yang_bo.gezi.weakhead.Expansions
import java.nio.file.Path

/** The hard corpus over every group's files, under `root` (the directory
  * `gezi`): the claims group's tables of `contest_hard_answers` and
  * `contest_hard_claims` (`claims.Claims`), with the clauses the merge group's
  * families and the reduction group's empty-set reachability add to them by the
  * multifile hooks. In Prolog `hard_claim/4` gathers every loaded file's
  * clauses; here this aggregation does, each group's facts built by that
  * group's port. Its reads keep their complete tables in the cache service its
  * owner carries (`ProblemFamilies`).
  */
final class HardCorpus(
    root: Path,
    expansions: Expansions[com.yang_bo.gezi.ir.NoFacts.type],
    cache: Cache
):

  val problems: ProblemFamilies = ProblemFamilies(root, expansions, cache)

  val dynamic: merges.MergeDynamic = merges.MergeDynamic(problems)
  val binary: merges.MergeBinary = merges.MergeBinary(problems, dynamic)
  val fibonacci: merges.MergeFibonacci =
    merges.MergeFibonacci(problems, dynamic)
  val power: merges.MergePower = merges.MergePower(problems, dynamic)
  val twins: merges.MergeTwins =
    merges.MergeTwins(problems, dynamic, fibonacci, binary)
  val meanings: merges.MergeMeanings = merges.MergeMeanings(problems)
  val graph: merges.MergeGraph = merges.MergeGraph(problems)
  val datalog: merges.MergeDatalog = merges.MergeDatalog(problems)
  val mixinLibrary: merges.MixinLibrary = merges.MixinLibrary(problems)
  val mixinClaims: merges.MixinClaims =
    merges.MixinClaims(problems, mixinLibrary)
  val mixinDatalog: merges.MixinDatalog =
    merges.MixinDatalog(problems, mixinLibrary)
  val reductionGroup: reductions.ReductionGroup =
    reductions.ReductionGroup(root, problems)
  val mixinTraps: merges.MixinTraps =
    merges.MixinTraps(problems, mixinClaims, reductionGroup)

  /** The clauses `problems/empty_set_reachability` adds: every public point
    * intends the Church true; a cyclic one has the purpose `speed` and the
    * limits `limits(10, 256, 256)`; a point whose target is reachable poses one
    * scored claim.
    */
  def emptySetReachabilityFacts: Vector[ClaimFact] =
    EmptySetReachability
      .points(reductionGroup)
      .flatMap((point, reachability) =>
        val cyclic = reachability match
          case ReachabilityGraph.Cyclic(_, _) => true
          case _                              => false
        // The graph as the claim's reason prints it, the cyclic graph's shape and the tree's order by their written names.
        val written = reachability match
          case ReachabilityGraph.Cyclic(shape, size) =>
            s"Cyclic(${shape.written},$size)"
          case ReachabilityGraph.Tree(order, branches, targetBits) =>
            s"Tree(${order.written},$branches,$targetBits)"
        Vector(
          ClaimFact.HardIntended(
            point,
            com.yang_bo.gezi.contest.corpora.claims.IntendedOutcome.Head,
            ClaimFact.intendedValue(ClaimFact.boolean(true))
          )
        ) ++
          (if cyclic then
             Vector(
               ClaimFact.PointPurpose(point, "speed"),
               ClaimFact.HardRaisedLimits(point, ClaimFact.familyLimits)
             )
           else Vector.empty) ++
          (if EmptySetReachability.graphReachable(reachability) then
             Vector(
               ClaimFact.ScoredFiniteHead(
                 point,
                 Vector(ClaimFact.boolean(true)),
                 s"the target is reachable in $written"
               )
             )
           else Vector.empty)
      )

  private def emptySetReachabilityProgram(point: String) =
    EmptySetReachability
      .points(reductionGroup)
      .collectFirst { case (`point`, reachability) =>
        EmptySetReachability.graphTerm(reductionGroup.attractors, reachability)
      }
      .getOrElse(
        throw IllegalArgumentException(
          s"$point is no point of contest_empty_set_reachability"
        )
      )

  /** The other groups' files, as the clauses they add. */
  val otherGroups: Vector[claims.HardFamily] = Vector(
    ClaimFactFamily(binary.claims, binary.program),
    ClaimFactFamily(fibonacci.claims, fibonacci.program),
    ClaimFactFamily(power.claims, power.program),
    ClaimFactFamily(twins.claims, twins.program),
    ClaimFactFamily(meanings.claims, meanings.program),
    ClaimFactFamily(dynamic.claims, dynamic.program),
    ClaimFactFamily(graph.claims, graph.program),
    ClaimFactFamily(datalog.claims, datalog.program),
    ClaimFactFamily(mixinClaims.claims, mixinClaims.program),
    ClaimFactFamily(mixinDatalog.claims, mixinDatalog.pointTerm),
    ClaimFactFamily(mixinTraps.claims, mixinTraps.program),
    ClaimFactFamily(emptySetReachabilityFacts, emptySetReachabilityProgram)
  )

  /** The claims group's tables over every group's files. */
  val claimsGroup: claims.Claims = claims.Claims(root, problems, otherGroups)

  /** `hard_claim(Point, Kind, Template, Proof)` of any point of any group. */
  def hardClaims(point: String): Vector[claims.HardClaim] =
    claimsGroup.claims.hardClaims(point)
