package com.yang_bo.gezi.ir

/** A rule the saturation applies by itself, without a lemma: the β rule. A
  * round lists the rules it enables, as it lists its knowledge modules, and a
  * rule it does not list is not applied: the β rule and δ are opt-in. The set
  * is the saturation's only: the weak-head readings, the JIT and the normal
  * forms are reference readings and apply every rule. It lives in the IR's
  * module so that a round described outside the saturation's modules can name
  * its rules.
  *
  * The β rule here is the e-graph's β step, a pending application of a thunk
  * worked by the saturation (`com.yang_bo.gezi.saturation.Saturation.agendaWorked`). The
  * reverse beta of lemma matching (`com.yang_bo.gezi.saturation.HigherOrderMatching`,
  * `com.yang_bo.gezi.saturation.ReverseBeta`, and the union of a redex with its subterm
  * justified by `com.yang_bo.gezi.egraph.Justification.BetaConversion`) is not this rule:
  * every lemma carries an n-ary native reverse β, and a round without `Beta`
  * keeps it.
  */
enum BuiltInRule:

  /** The β step, `(λx. M) N = M[x := N]`. */
  case Beta

  /** The expansion direction of "the storage's view": a native storage the
    * e-graph keeps as a leaf is united with the nodes of its view `v ∥ T`,
    * which it is by definition, so that a lemma can match inside the value
    * (`com.yang_bo.gezi.egraph.EGraph.storageViewAdded`), one leaf at a time in the
    * saturation's loop, each expansion that changes the graph counted as an
    * instance against the round's budget, the stop read before each. A round
    * that does not enable it matches a storage leaf through its pattern view
    * only, `?x ∥ ?T` with ?x the leaf's own class. A round cannot enable it and
    * also stop matching at the classes of storages of constant size
    * (`SaturationOptions.constantStorageStop` of the strategies, refused
    * together), whose purpose is the opposite.
    */
  case StorageView

object BuiltInRule:

  /** The rules the rounds written before the rules were opt-in apply: the β
    * rule, the only rule then built in.
    */
  val beforeOptIn: Set[BuiltInRule] = Set(Beta)
