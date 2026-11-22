package gezi.strategies

/** What a dispatch strategy decides at a fallback point whose check does not
  * hold, the operand outside the typed version's domain: take the untyped
  * path, or reject the operand.
  */
enum DispatchDecision:

  /** The untyped path runs. */
  case Untyped

  /** The reading throws `gezi.jit.TypedVersionDomain`. */
  case Rejected

/** A dispatch strategy: its name, by which a strategy of the compilation
  * names it, and its decision at a fallback point whose check does not hold
  * (`lambda_jit_jit:dispatch_outside_decided/2`).
  */
final case class DispatchStrategy(name: String, outsideDecided: DispatchDecision)

/** The dispatch strategy of the baseline, ported from the deleted Prolog
  * implementation. Falling back is a switch at compile time, not at run
  * time: at run time the domain is checked, and the typed version runs where
  * the input is in its domain, the untyped one otherwise (`CONTRIBUTING.md`,
  * "HM exactly, saturation in rounds, the domain checked at run time"). At a
  * fallback point whose
  * check does not hold, `fallback` takes the untyped path.
  *
  * The baseline offers no strategy that rejects such an operand: a typed
  * version the type check writes need not cover every value its application
  * meets, so a strategy that rejects loses answers when knowledge is added,
  * which monotonicity in knowledge forbids (`CONTRIBUTING.md`, "Soundness,
  * monotonicity, modularity, budgets"). The decision `Rejected` is there for an entry's strategy. The
  * module `jit` reads the decision (`DispatchMode`).
  */
object DispatchStrategies:

  val fallback: DispatchStrategy = DispatchStrategy("fallback", DispatchDecision.Untyped)
