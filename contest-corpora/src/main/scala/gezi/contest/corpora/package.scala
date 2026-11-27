package gezi.contest

/** The problem corpora: the generators of the programs of `gezi/corpora`,
  * written in the higher-order abstract syntax, whose data stay in the
  * lambdalattice tables and programs of `gezi/problems`, read under weak head
  * by `common.ProblemFamily`, and the judges that read the programs on the
  * evaluator. The generators are split by group: `claims`, `merges` and
  * `reductions`, with `common` for what the groups share and `oldcorpora` for
  * the reference implementations the old corpora's tests keep. The front end's
  * `gezi.frontend.ExchangeText` writes a generated program as the judge's
  * points file and pipe carry it; the tests' snapshots record a program as the
  * lambdalattice text of its tree.
  *
  * The module `contest-corpora` depends on `standardlibrary` and `weakhead`;
  * its tests also depend on `jit`, and only the judge depends on it. The
  * generators port the deleted Prolog corpora.
  */
package object corpora:

  /** A program of the corpora in the higher-order abstract syntax: a term whose
    * constants are closed terms of no facts, the library's terms and the
    * problems' data, read under no facts.
    */
  type ProblemTerm =
    gezi.frontend.TermOf[gezi.ir.Configured[gezi.ir.NoFacts.type]]

  /** A closed de Bruijn term of the corpora whose constants are closed terms of
    * no facts.
    */
  type ProblemDeBruijnTerm =
    gezi.frontend.DeBruijnTermOf[gezi.ir.Configured[gezi.ir.NoFacts.type]]
