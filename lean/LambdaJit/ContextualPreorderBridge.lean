import LambdaJit.ContextualPreorderAdequacy

/-!
# The reading of a term depends only on its free variables

Given a model satisfying the fields of `DdLP96Model`, environments that agree on the free indices of
a term give it the same value (`DdLP96Model.interpretAgree`), so a closed term reads the same in
every environment (`DdLP96Model.interpretClosed`). The bridge between NF◇_{λ-lattice-η} and
DdLP96's contextual preorder ⊑_O that reads closed terms through it is module `LatticeEtaBridge`.
-/

namespace LambdaJit.ContextualPreorder

open LambdaJit.Semantics
open LambdaJit.Semantics.Term

namespace DdLP96Model

variable (model : DdLP96Model)

/-- The reading depends only on the values of the free variables: environments that agree on the
free indices of a term give it the same value (λ by (P6)). -/
theorem interpretAgree : ∀ (term : Term) {environment other : Nat → model.Value},
    (∀ index, OccursFree index term → environment index = other index) →
      model.interpret term environment = model.interpret term other
  | .boundVariable index, _, _, agree => by
      rw [model.interpretVariable, model.interpretVariable]
      exact agree index rfl
  | .abstraction body, environment, other, agree => model.equalOfApply fun value => by
      rw [model.interpretAbstraction, model.interpretAbstraction]
      apply interpretAgree body
      intro index occurs
      cases index with
      | zero => rfl
      | succ index => exact agree index occurs
  | .application function argument, _, _, agree => by
      rw [model.interpretApplication, model.interpretApplication,
        interpretAgree function fun index occurs => agree index (.inl occurs),
        interpretAgree argument fun index occurs => agree index (.inr occurs)]
  | .choice left right, _, _, agree => by
      rw [model.interpretChoice, model.interpretChoice,
        interpretAgree left fun index occurs => agree index (.inl occurs),
        interpretAgree right fun index occurs => agree index (.inr occurs)]
  | .parallel left right, _, _, agree => by
      rw [model.interpretParallel, model.interpretParallel,
        interpretAgree left fun index occurs => agree index (.inl occurs),
        interpretAgree right fun index occurs => agree index (.inr occurs)]

/-- A closed term reads the same in every environment; [[T]] is its value in ρ_⊤. -/
theorem interpretClosed {term : Term} (closed : Closed term) (environment : Nat → model.Value) :
    model.interpret term environment = model.interpret term model.topEnvironment :=
  model.interpretAgree term fun index occurs => absurd occurs (closed index)

end DdLP96Model

end LambdaJit.ContextualPreorder
