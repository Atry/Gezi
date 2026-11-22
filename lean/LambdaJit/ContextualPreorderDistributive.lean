import LambdaJit.ContextualPreorderUnconditional

/-!
# The parallel distributes over the choice up to ≃_O

M ∥ (N + P) ≃_O (M ∥ N) + (M ∥ P) for all terms M, N, P, with no hypothesis
(`parallelChoiceDistributiveContextualEquivalence`). The law is not among the ten equations of the
formal definition (the proofs file, section 3); it holds by
Definition 14.

The proof reads both sides in a model. DdLP96's reading takes the choice to the meet and the
parallel to the join, so the two sides read m ⊔ (n ⊓ p) and (m ⊔ n) ⊓ (m ⊔ p). The join
distributes over the meet in every lattice where the meet distributes over the join, the model's
field (E1) (`DdLP96Model.joinMeetDistributive`), so the two readings are equal in every
environment, and corollary 4.2 (`DdLP96Model.contextualEquivalenceOfInterpretEqual`) gives ≃_O.
The direction M ∥ (N + P) ⊑_O (M ∥ N) + (M ∥ P) holds in every lattice; only the converse uses
(E1).
-/

namespace LambdaJit.ContextualPreorder

open LambdaJit.Semantics
open LambdaJit.DInfinity (wadsworthModel)

namespace DdLP96Model

/-- m ⊔ (n ⊓ p) = (m ⊔ n) ⊓ (m ⊔ p): the join distributes over the meet, from (E1). -/
theorem joinMeetDistributive (model : DdLP96Model) (first second third : model.Value) :
    model.join first (model.meet second third) =
      model.meet (model.join first second) (model.join first third) := by
  apply model.orderAntisymmetric
  · exact model.meetGreatest
      (model.joinLeast (model.joinAboveLeft _ _)
        (model.orderTransitive (model.meetBelowLeft _ _) (model.joinAboveRight _ _)))
      (model.joinLeast (model.joinAboveLeft _ _)
        (model.orderTransitive (model.meetBelowRight _ _) (model.joinAboveRight _ _)))
  · -- (m ⊔ n) ⊓ (m ⊔ p) ⊑ ((m ⊔ n) ⊓ m) ⊔ ((m ⊔ n) ⊓ p), by (E1).
    refine model.orderTransitive (model.distributive _ _ _) (model.joinLeast ?_ ?_)
    · exact model.orderTransitive (model.meetBelowRight _ _) (model.joinAboveLeft _ _)
    · -- (m ⊔ n) ⊓ p ⊑ p ⊓ (m ⊔ n) ⊑ (p ⊓ m) ⊔ (p ⊓ n) ⊑ m ⊔ (n ⊓ p), the middle step by (E1).
      refine model.orderTransitive
        (model.meetGreatest (model.meetBelowRight _ _) (model.meetBelowLeft _ _))
        (model.orderTransitive (model.distributive _ _ _) (model.joinLeast ?_ ?_))
      · exact model.orderTransitive (model.meetBelowRight _ _) (model.joinAboveLeft _ _)
      · exact model.orderTransitive
          (model.meetGreatest (model.meetBelowRight _ _) (model.meetBelowLeft _ _))
          (model.joinAboveRight _ _)

/-- Given a model, M ∥ (N + P) ≃_O (M ∥ N) + (M ∥ P), by corollary 4.2. -/
theorem parallelChoiceDistributiveContextualEquivalence (model : DdLP96Model)
    (first second third : Term) :
    ContextualEquivalence (.parallel first (.choice second third))
      (.choice (.parallel first second) (.parallel first third)) :=
  model.contextualEquivalenceOfInterpretEqual fun environment => by
    rw [model.interpretParallel, model.interpretChoice, model.interpretChoice,
      model.interpretParallel, model.interpretParallel]
    exact model.joinMeetDistributive _ _ _

end DdLP96Model

/-- M ∥ (N + P) ≃_O (M ∥ N) + (M ∥ P), for all terms M, N, P, with no hypothesis. -/
theorem parallelChoiceDistributiveContextualEquivalence (first second third : Term) :
    ContextualEquivalence (.parallel first (.choice second third))
      (.choice (.parallel first second) (.parallel first third)) :=
  DdLP96Model.parallelChoiceDistributiveContextualEquivalence wadsworthModel first second third

end LambdaJit.ContextualPreorder
