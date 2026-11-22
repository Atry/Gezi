import LambdaJit.ContextualPreorderApproximation

/-!
# Ω below every term

"Ω 在下" of the proofs file, section 11, with
⊑_O as the primary definition, given a model satisfying the fields of `DdLP96Model`: Ω reads ⊥, so
Ω ∥ M ≃_O M (`DdLP96Model.omegaParallelContextualEquivalence`), Ω is a least element of ⊑_O
(`DdLP96Model.omegaContextualPreorder`), and Ω + M ≃_O Ω and Ω M ≃_O Ω
(`DdLP96Model.omegaChoiceContextualEquivalence`, `DdLP96Model.omegaApplicationContextualEquivalence`),
each by corollary 4.2. The module also proves that K and K* read differently
(`DdLP96Model.interpretFirstNotSecond`) and that λx. (x + Ω) = λx. Ω holds in DdLP96's reading
(`DdLP96Model.interpretOmegaBelow`).

Module `ContextualPreorderUnconditional` states them in the instance `wadsworthModel`, with no
model argument.
-/

namespace LambdaJit.ContextualPreorder

open LambdaJit.Semantics
open LambdaJit.Semantics.Term

namespace DdLP96Model

variable (model : DdLP96Model)

/-- K and K* read differently: applied to ⊤ and ⊥, K gives ⊤ and K* gives ⊥. -/
theorem interpretFirstNotSecond (environment : Nat → model.Value) :
    model.interpret first environment ≠ model.interpret second environment := by
  intro equal
  have applied : model.apply (model.apply (model.interpret first environment) model.top)
      model.bottom =
      model.apply (model.apply (model.interpret second environment) model.top) model.bottom := by
    rw [equal]
  simp only [first, second] at applied
  rw [model.interpretAbstraction, model.interpretAbstraction, model.interpretAbstraction,
    model.interpretAbstraction, model.interpretVariable, model.interpretVariable] at applied
  exact model.topNotBottom applied

/-- λx. (x + Ω) = λx. Ω holds in DdLP96's reading: x ⊓ ⊥ = ⊥, given a model satisfying the fields
of `DdLP96Model`. -/
theorem interpretOmegaBelow (environment : Nat → model.Value) :
    model.interpret (.abstraction (.choice (.boundVariable 0) Omega)) environment =
      model.interpret (.abstraction Omega) environment :=
  model.equalOfApply fun value => by
    rw [model.interpretAbstraction, model.interpretAbstraction, model.interpretChoice,
      model.interpretOmega]
    exact model.bottomOfBelowBottom (model.meetBelowRight _ _)

/-- Ω ∥ M ≃_O M, given a model satisfying the fields of `DdLP96Model`: Ω reads ⊥ and ⊥ ⊔ m = m
(corollary 4.2). The record's candidate lemma Ω ∥ M = M (section 7.3). -/
theorem omegaParallelContextualEquivalence (model : DdLP96Model) (term : Term) :
    ContextualEquivalence (.parallel Omega term) term :=
  model.contextualEquivalenceOfInterpretEqual fun environment => by
    rw [model.interpretParallel, model.interpretOmega]
    exact model.orderAntisymmetric (model.joinLeast (model.bottomLeast _) (model.orderReflexive _))
      (model.joinAboveRight _ _)

/-- Ω ⊑_O M for every term M, given a model satisfying the fields of `DdLP96Model`: Ω reads ⊥,
the least value. -/
theorem omegaContextualPreorder (model : DdLP96Model) (term : Term) :
    ContextualPreorder Omega term :=
  model.contextualPreorderOfInterpretBelow fun environment => by
    rw [model.interpretOmega]
    exact model.bottomLeast _

/-- Ω + M ≃_O Ω, given a model satisfying the fields of `DdLP96Model`: Ω reads ⊥ and
⊥ ⊓ m = ⊥. -/
theorem omegaChoiceContextualEquivalence (model : DdLP96Model) (term : Term) :
    ContextualEquivalence (.choice Omega term) Omega :=
  model.contextualEquivalenceOfInterpretEqual fun environment => by
    rw [model.interpretChoice, model.interpretOmega]
    exact model.bottomOfBelowBottom (model.meetBelowLeft _ _)

/-- Ω M ≃_O Ω, given a model satisfying the fields of `DdLP96Model`: Ω reads ⊥ and ⊥ applied to
any argument is ⊥. -/
theorem omegaApplicationContextualEquivalence (model : DdLP96Model) (term : Term) :
    ContextualEquivalence (.application Omega term) Omega :=
  model.contextualEquivalenceOfInterpretEqual fun environment => by
    rw [model.interpretApplication, model.interpretOmega]
    exact model.applyBottom _

end DdLP96Model

end LambdaJit.ContextualPreorder
