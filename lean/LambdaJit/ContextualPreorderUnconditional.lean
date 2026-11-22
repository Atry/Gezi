import LambdaJit.ContextualPreorderOmegaBottom
import LambdaJit.DInfinityModel

/-!
# The theorems of the `ContextualPreorder` modules with no model argument

The theorems of modules `ContextualPreorderAdequacy` and `ContextualPreorderOmegaBottom` that take
a `DdLP96Model`, instantiated at `wadsworthModel` of module `DInfinityModel`, Wadsworth's D∞ with
the two-point D₀. The statements that do not mention the model hold with no hypothesis:
Ω ∥ M ≃_O M, Ω + M ≃_O Ω, Ω M ≃_O Ω and Ω ⊑_O M. The statements about the reading are stated in
`wadsworthModel`.
-/

namespace LambdaJit.ContextualPreorder

open LambdaJit.Semantics
open LambdaJit.Semantics.Term
open LambdaJit.DInfinity (wadsworthModel)

/-- The record's theorem 4.1 in Wadsworth's D∞: M ∈ SOL if and only if [[M]]ρ_⊤ ≠ ⊥. -/
theorem solvableIffInterpretNotBottom {term : Term} :
    Solvable term ↔ wadsworthModel.interpret term wadsworthModel.topEnvironment ≠ wadsworthModel.bottom :=
  wadsworthModel.solvableIffInterpretNotBottom

/-- Ω ∥ M ≃_O M, the record's candidate lemma Ω ∥ M = M (section 7.3). -/
theorem omegaParallelContextualEquivalence (term : Term) :
    ContextualEquivalence (.parallel Omega term) term :=
  DdLP96Model.omegaParallelContextualEquivalence wadsworthModel term

/-- Ω ⊑_O M for every term M: Ω is a least element of ⊑_O. -/
theorem omegaContextualPreorder (term : Term) : ContextualPreorder Omega term :=
  DdLP96Model.omegaContextualPreorder wadsworthModel term

/-- Ω + M ≃_O Ω. -/
theorem omegaChoiceContextualEquivalence (term : Term) :
    ContextualEquivalence (.choice Omega term) Omega :=
  DdLP96Model.omegaChoiceContextualEquivalence wadsworthModel term

/-- Ω M ≃_O Ω. -/
theorem omegaApplicationContextualEquivalence (term : Term) :
    ContextualEquivalence (.application Omega term) Omega :=
  DdLP96Model.omegaApplicationContextualEquivalence wadsworthModel term

end LambdaJit.ContextualPreorder
