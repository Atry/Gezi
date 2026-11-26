package gezi.ir

/** A rule the saturation applies by itself, without a lemma: the β rule. A
  * round lists the rules it enables, as it lists its knowledge modules, and a
  * rule it does not list is not applied: the β rule and δ are opt-in.
  * The set is the saturation's only: the weak-head readings, the JIT and the
  * normal forms are reference readings and apply every rule. It lives in the
  * IR's module so that a round described outside the saturation's modules can
  * name its rules.
  *
  * The β rule here is the e-graph's β step, a pending application of a thunk
  * worked by the saturation (`gezi.saturation.Saturation.agendaWorked`).
  * The reverse beta of lemma matching (`gezi.saturation.HigherOrderMatching`,
  * `gezi.saturation.ReverseBeta`, and the union of a redex with its
  * subterm justified by `gezi.egraph.Justification.BetaConversion`) is
  * not this rule: every lemma carries an n-ary native reverse β, and a round
  * without `Beta` keeps it.
  */
enum BuiltInRule:

  /** The β step, `(λx. M) N = M[x := N]`. */
  case Beta

object BuiltInRule:

  /** Every built-in rule, which the rounds written before the rules were
    * opt-in apply, all of them having been built in.
    */
  val all: Set[BuiltInRule] = values.toSet
