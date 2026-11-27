package com.yang_bo.gezi.contest.corpora.reductions

import com.yang_bo.gezi.contest.corpora.common.ProblemFamilies

import com.yang_bo.gezi.contest.corpora.claims
import com.yang_bo.gezi.contest.corpora.merges
import com.yang_bo.gezi.hotspot.Cache
import com.yang_bo.gezi.weakhead.Expansions
import java.nio.file.Path

/** What the generators of the reduction group read, from Gezi's directory: the
  * problem data, the Scott types, the attractors (the claims group's port), the
  * binary arithmetic and the Fibonacci and product families (the merge group's
  * ports) and the mixin library over the hierarchies of the group's families.
  * Each is read once, when first used, every read of the tree from the URI
  * expansions `problems` carries (`ProblemFamilies.sharedExpansions`), so that
  * a group lists each directory and parses each file it shares with its other
  * reads once.
  */
final case class ReductionGroup(root: Path, problems: ProblemFamilies):

  /** The Scott types of the problems. */
  lazy val scott: Scott = Scott()

  /** The files the claims group reads, its prelude and contest included. */
  lazy val claimsCorpora: claims.Corpora = claims.Corpora(root, problems)

  /** The attractors of the contest's API and the prelude's fixpoint. */
  lazy val attractors: Attractors = claims.Attractors(claimsCorpora)

  /** The library terms of native_types, native_arithmetic, fixed_width and
    * binary that the programs built from the library hold.
    */
  lazy val standardLibrary: StandardLibraryTerms =
    StandardLibraryTerms(root, problems.sharedExpansions)

  /** The binary arithmetic of `problems/merge_dynamic`. */
  lazy val arithmetic: merges.MergeDynamic = claimsCorpora.mergeDynamic

  /** The Fibonacci family, `problems/merge_fibonacci`. */
  lazy val fibonacci: merges.MergeFibonacci =
    merges.MergeFibonacci(problems, arithmetic)

  /** The product family, `problems/merge_binary`. */
  lazy val products: merges.MergeBinary =
    merges.MergeBinary(problems, arithmetic)

  /** The library of the mixin_builtin families, MIXINv2's Builtin read from
    * `problems/mixin_builtin`.
    */
  lazy val mixinBuiltin: MixinBuiltinLibrary = MixinBuiltinLibrary(root)

  /** The functions of the CSES port, `problems/cses`, each read by projection
    * from the URI expansions `problems` carries.
    */
  lazy val cses: CsesProblems = CsesProblems(root, problems.sharedExpansions)

  /** The mixin library over the hierarchies of the group's mixin families. */
  lazy val mixins: MixinLibrary = MixinLibrary.read(
    problems,
    Vector(
      "reduction_mixins",
      "reduction_mixin_fibonacci",
      "reduction_mixin_grid",
      "reduction_mixin_library",
      "reduction_mixin_theorems"
    )
  )

object ReductionGroup:

  /** The group under the root whose reads start from the expansions, the URI
    * expansions its owner carries (`Expansions`): the judge's run or a test
    * suite builds the group once, from `Expansions.none`; its reads keep their
    * complete tables in the cache service the owner carries
    * (`ProblemFamilies`).
    */
  def apply(
      root: Path,
      expansions: Expansions[com.yang_bo.gezi.ir.NoFacts.type],
      cache: Cache
  ): ReductionGroup =
    ReductionGroup(root, ProblemFamilies(root, expansions, cache))
