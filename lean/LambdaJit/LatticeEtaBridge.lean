import LambdaJit.LatticeEtaSeparation
import LambdaJit.ContextualPreorderTop

/-!
# NF◇_{λ-lattice-η} is { N ∈ NF_βη | T ⊑_O N }

The bridge between the consistency form of NF◇ in ⊢_{λ-lattice-η} (module `LatticeEtaDerivability`,
the proofs file's ⊢_B of section 21) and DdLP96's
Definition 14 (module `ContextualPreorder`): for a closed T and a closed βη normal form N,

    {N + T = T} ⊬_{λ-lattice-η} K = K*  if and only if  T ⊑_O N

(`consistentNormalFormLatticeEtaIffContextualPreorder`), the proofs file's section 21.

- From right to left, the record's theorem 7.1 for ⊢_{λ-lattice-η}
  (`consistentEquationLatticeEtaOfContextualPreorder`): T ⊑_O N gives N + T ≃_O T
  (`contextualEquivalenceChoiceOfContextualPreorder`: + reads as the meet, and T ≃_O T + T ⊑_O N + T),
  so every equation derivable from N + T = T in ⊢_{λ-lattice-η} is a contextual equivalence
  (`contextualEquivalenceOfDerivableLatticeEtaHypotheses` of module `ContextualPreorderTop`), and
  K ≄_O K* (`notContextuallyEquivalentFirstSecond`).
- From left to right, the completeness of DdLP96's reading for NF◇_{λ-lattice-η}
  (`DdLP96Model.completenessLatticeEta` of module `LatticeEtaSeparation`, theorem A and theorem S with
  Ξ in the place of 0) in Wadsworth's D∞ gives [[T]] ⊑ [[N]], and the record's corollary 4.2 gives
  T ⊑_O N; both terms are closed, so their readings do not depend on the environment.

`consistentNormalFormLatticeEtaIffContextualNormalForm` states it as an equality of sets, and
`contextualPreorderIffInterpretBelowLatticeEta` is the record's proposition 7.3 read through it.
-/

namespace LambdaJit.ContextualPreorder

open LambdaJit.Semantics
open LambdaJit.Semantics.Term
open LambdaJit.DInfinity (wadsworthModel)

/-- T ⊑_O N gives N + T ≃_O T. N + T ⊑_O T because + reads as the meet (corollary 4.2), and
T ⊑_O T + T ⊑_O N + T by T + T = T (derivable with no unit law, `DerivableLatticeEta.choiceIdempotent`,
and theorem 6.1) and T ⊑_O N in the context □ + T. -/
theorem contextualEquivalenceChoiceOfContextualPreorder {term candidate : Term}
    (preorder : ContextualPreorder term candidate) :
    ContextualEquivalence (.choice candidate term) term :=
  ⟨wadsworthModel.contextualPreorderOfInterpretBelow fun environment => by
      rw [wadsworthModel.interpretChoice]
      exact wadsworthModel.meetBelowRight _ _,
    ContextualPreorder.transitive
      (contextualEquivalenceOfDerivableLatticeEta (DerivableLatticeEta.choiceIdempotent term)).2
      (preorder.fill (.choiceLeft .hole term))⟩

/-- The record's theorem 7.1 for ⊢_{λ-lattice-η}: for all terms T and N, T ⊑_O N gives
◇_{λ-lattice-η}(N + T = T). Its one hypothesis N + T = T is a contextual equivalence
(`contextualEquivalenceChoiceOfContextualPreorder`), so a derivation of K = K* from it would give
K ≃_O K* (`contextualEquivalenceOfDerivableLatticeEtaHypotheses`), which is false
(`notContextuallyEquivalentFirstSecond`). -/
theorem consistentEquationLatticeEtaOfContextualPreorder {term candidate : Term}
    (preorder : ContextualPreorder term candidate) :
    ConsistentEquationLatticeEta (.choice candidate term) term := fun derivation =>
  notContextuallyEquivalentFirstSecond
    (contextualEquivalenceOfDerivableLatticeEtaHypotheses
      (fun left right isHypothesis => by
        simp only [listed, List.mem_singleton, Prod.mk.injEq] at isHypothesis
        rw [isHypothesis.1, isHypothesis.2]
        exact contextualEquivalenceChoiceOfContextualPreorder preorder)
      derivation)

/-- The record's theorem 7.1 on normal forms for ⊢_{λ-lattice-η}:
{ N ∈ NF_βη | T ⊑_O N } ⊆ NF◇_{λ-lattice-η}(T), for every term T. -/
theorem consistentNormalFormLatticeEtaOfContextualNormalForm {term candidate : Term}
    (contextual : ContextualNormalForm term candidate) : ConsistentNormalFormLatticeEta term candidate :=
  ⟨contextual.1, consistentEquationLatticeEtaOfContextualPreorder contextual.2⟩

/-- The completeness read through corollary 4.2: for a closed T, N ∈ NF◇_{λ-lattice-η}(T) gives
T ⊑_O N. `DdLP96Model.completenessLatticeEta` in Wadsworth's D∞ gives [[T]]ρ_⊤ ⊑ [[N]]ρ_⊤, and
both terms are closed, so the same holds in every environment. -/
theorem contextualPreorderOfConsistentNormalFormLatticeEta {term candidate : Term}
    (closed : Closed term) (consistent : ConsistentNormalFormLatticeEta term candidate) :
    ContextualPreorder term candidate :=
  wadsworthModel.contextualPreorderOfInterpretBelow fun environment => by
    rw [wadsworthModel.interpretClosed closed environment,
      wadsworthModel.interpretClosed consistent.1.1 environment]
    exact wadsworthModel.completenessLatticeEta closed consistent

/-- The bridge for ⊢_{λ-lattice-η}: for a closed T and a closed βη normal form N,
N ∈ NF◇_{λ-lattice-η}(T) if and only if T ⊑_O N. From left to right by
`contextualPreorderOfConsistentNormalFormLatticeEta`, from right to left by the record's theorem 7.1
for ⊢_{λ-lattice-η}. -/
theorem consistentNormalFormLatticeEtaIffContextualPreorder {term candidate : Term}
    (closed : Closed term) (normal : NormalForm candidate) :
    ConsistentNormalFormLatticeEta term candidate ↔ ContextualPreorder term candidate :=
  ⟨contextualPreorderOfConsistentNormalFormLatticeEta closed,
    fun preorder => ⟨normal, consistentEquationLatticeEtaOfContextualPreorder preorder⟩⟩

/-- The bridge for ⊢_{λ-lattice-η} as an equality of sets: for a closed T,
NF◇_{λ-lattice-η}(T) is { N ∈ NF_βη | T ⊑_O N } (`ContextualNormalForm`). -/
theorem consistentNormalFormLatticeEtaIffContextualNormalForm {term candidate : Term}
    (closed : Closed term) :
    ConsistentNormalFormLatticeEta term candidate ↔ ContextualNormalForm term candidate :=
  ⟨fun consistent => ⟨consistent.1,
      contextualPreorderOfConsistentNormalFormLatticeEta closed consistent⟩,
    consistentNormalFormLatticeEtaOfContextualNormalForm⟩

/-- The record's proposition 7.3 for ⊢_{λ-lattice-η}, in Wadsworth's D∞: for a closed T and a
closed βη normal form N, T ⊑_O N if and only if [[T]] ⊑ [[N]]. From left to right through the
bridge and `DdLP96Model.completenessLatticeEta`; from right to left by corollary 4.2. -/
theorem contextualPreorderIffInterpretBelowLatticeEta {term candidate : Term}
    (closed : Closed term) (normal : NormalForm candidate) :
    ContextualPreorder term candidate ↔
      wadsworthModel.below (wadsworthModel.interpret term wadsworthModel.topEnvironment)
        (wadsworthModel.interpret candidate wadsworthModel.topEnvironment) :=
  ⟨fun preorder => wadsworthModel.completenessLatticeEta closed
      ⟨normal, consistentEquationLatticeEtaOfContextualPreorder preorder⟩,
    fun below => wadsworthModel.contextualPreorderOfInterpretBelow fun environment => by
      rw [wadsworthModel.interpretClosed closed environment,
        wadsworthModel.interpretClosed normal.1 environment]
      exact below⟩

end LambdaJit.ContextualPreorder
