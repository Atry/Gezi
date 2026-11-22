import LambdaJit.FourEquations

/-!
# The closed terms K, K* and Ω, and finite sets of equations

The terms of the calculus (module `Terms`) that the derivability ⊢_{λ-lattice-η} (module
`LatticeEtaDerivability`), its consistency (module `LatticeEtaConsistency`) and the contextual
preorder (module `ContextualPreorder`) name: K = λx.λy. x and K* = λx.λy. y, whose equation a
consistent theory does not derive, and Ω = (λx. x x) (λx. x x), a closed term with no head. A set
of equations is a predicate `Term → Term → Prop`, true of `left right` when the equation
`left = right` is in the set; `listed` reads a finite list of equations as one.
-/

namespace LambdaJit.Semantics

open Term

/-- λx.λy. x, the paper's K. -/
def first : Term := abstraction (abstraction (boundVariable 1))

/-- λx.λy. y, the paper's K*. -/
def second : Term := abstraction (abstraction (boundVariable 0))

/-- The finite set of the equations `left = right` for the pairs `(left, right)` in the list. -/
def listed (equations : List (Term × Term)) : Term → Term → Prop :=
  fun left right => (left, right) ∈ equations

/-- λx. x x. -/
def selfApplication : Term := abstraction (application (boundVariable 0) (boundVariable 0))

/-- Ω = (λx. x x) (λx. x x). -/
def Omega : Term := application selfApplication selfApplication

namespace Term

/-- Ω is closed: each of its variable occurrences is index 0 under one abstraction, which a
free index would have to be one past. -/
theorem closedOmega : Closed Omega := by
  intro index occurs
  have selfApplicationClosed : ¬ OccursFree index selfApplication := by
    intro inside
    simp only [selfApplication, OccursFree] at inside
    rcases inside with zeroEqual | zeroEqual <;> exact Nat.succ_ne_zero index zeroEqual.symm
  simp only [Omega, OccursFree] at occurs
  rcases occurs with inside | inside <;> exact selfApplicationClosed inside

/-- Ω is closed, so substitution leaves it unchanged. -/
theorem instantiateOmega (argument : Term) : instantiate Omega argument = Omega :=
  substituteUnchanged Omega 0 argument (fun index _ => closedOmega index)

end Term

end LambdaJit.Semantics
