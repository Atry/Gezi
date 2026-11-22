import LambdaJit.LatticeEtaDerivability
import LambdaJit.SyntacticConsistency
import LambdaJit.ContextualPreorderAdequacy
import LambdaJit.DInfinityModel

/-!
# ⊢_{λ-lattice-η} is consistent, and what it derives is a contextual equivalence

Two theorems about the derivability without the unit law of module `LatticeEtaDerivability`, the
proofs file's ⊢_B of section 21. No proof in this
module uses the unit law:

- With no hypothesis, ⊢_{λ-lattice-η} is consistent (`consistentLatticeEtaWithoutHypotheses`): the
  the syntactic consistency proof (module
  `SyntacticConsistency`), run on ⊢_{λ-lattice-η} itself. Two terms it equates have the same readings
  in every context (`SyntacticConsistency.derivableLatticeEtaSameReadings`), so it relates two pure
  terms only when λβη converts them, and λβη does not convert K and K*. No model is used.
- Every equation it derives with no hypothesis is a contextual equivalence ≃_O
  (`contextualEquivalenceOfDerivableLatticeEta`, the record's theorem 6.1 of
  the contextual preorder record): DdLP96's reading is a model of
  ⊢_{λ-lattice-η} (`DdLP96Model.interpretDerivableLatticeEta`), and the record's corollary 4.2, in
  Wadsworth's D∞ (`DInfinity.wadsworthModel`).
-/

namespace LambdaJit.SyntacticConsistency

open LambdaJit.Semantics
open LambdaJit.BetaEtaConfluence

/-- The theorem of the syntactic consistency proof, section 4, for
⊢_{λ-lattice-η}: two terms equal by ⊢_{λ-lattice-η} with no hypotheses have the same readings in
every context, case by case: the β rule is a step of →o (lemma 4); the η rule and the axioms (3),
(5) and (10) hold in both directions of ≼ (lemma 13), and so does the axiom (1), by the clauses 选左
and 选右. -/
theorem derivableLatticeEtaSameReadings {left right : Term}
    (derivation : DerivableLatticeEta (fun _ _ => False) left right) : SameReadings left right := by
  induction derivation with
  | hypothesis impossible => exact impossible.elim
  | symmetric _ inner => exact fun context reading => (inner context reading).symm
  | transitive _ _ leftInner rightInner =>
      exact fun context reading => (leftInner context reading).trans (rightInner context reading)
  | congruenceArgument function _ inner => exact inner.fill (.applicationArgument function .hole)
  | congruenceAbstraction _ inner => exact inner.fill (.abstraction .hole)
  | beta body argument =>
      exact sameReadingsOfSimultaneousReduces
        (.beta (SimultaneousReduces.reflexive body) (SimultaneousReduces.reflexive argument))
  | eta function =>
      exact sameReadingsOfBelow (.etaLower (Below.reflexive function))
        (.etaUpper (Below.reflexive function))
  | choiceCommutative left right =>
      exact sameReadingsOfBelow
        (.choice (.reflexive _) (.choiceUpperRight (.reflexive _) (Below.reflexive left))
          (.reflexive _) (.choiceUpperLeft (.reflexive _) (Below.reflexive right)))
        (.choice (.reflexive _) (.choiceUpperRight (.reflexive _) (Below.reflexive right))
          (.reflexive _) (.choiceUpperLeft (.reflexive _) (Below.reflexive left)))
  | parallelCommutative left right =>
      exact sameReadingsOfBelow
        (.parallelUpper (.reflexive _) (.parallelRight (.reflexive _) (Below.reflexive right))
          (.reflexive _) (.parallelLeft (.reflexive _) (Below.reflexive left)))
        (.parallelUpper (.reflexive _) (.parallelRight (.reflexive _) (Below.reflexive left))
          (.reflexive _) (.parallelLeft (.reflexive _) (Below.reflexive right)))
  | parallelAbsorption kept other =>
      exact sameReadingsOfBelow (.parallelLeft (.reflexive _) (Below.reflexive kept))
        (.parallelUpper (.reflexive _) (Below.reflexive kept) (.reflexive _)
          (.choiceUpperLeft (.reflexive _) (Below.reflexive kept)))
  | argumentMonotone function argument addition =>
      exact sameReadingsOfBelow
        (.choice (.reflexive _)
          (.application (Below.reflexive function)
            (.choiceUpperLeft (.reflexive _) (Below.reflexive argument)))
          (.reflexive _) (Below.reflexive _))
        (.choiceUpperRight (.reflexive _) (Below.reflexive _))

/-- The record's corollary 2 for ⊢_{λ-lattice-η}: with no hypotheses, it relates two pure terms
only when they are βη-convertible. -/
theorem derivableLatticeEtaPureConvertible {left right : Term} (leftPure : Term.Pure left)
    (rightPure : Term.Pure right) (derivation : DerivableLatticeEta (fun _ _ => False) left right) :
    Convertible left right :=
  .symmetric ((readingOfPure rightPure).mp
    ((derivableLatticeEtaSameReadings derivation .hole left).mp
      ((readingOfPure leftPure).mpr (.reflexive left))))

end LambdaJit.SyntacticConsistency

namespace LambdaJit.Semantics

/-- ⊢_{λ-lattice-η} with no hypothesis is consistent: ∅ ⊬_{λ-lattice-η} K = K*. The syntactic proof of
the syntactic consistency proof run on ⊢_{λ-lattice-η} itself
(`SyntacticConsistency.derivableLatticeEtaPureConvertible`): a derivation of K = K* would make λβη
convert the two terms, which the confluence of β and η rules out
(`BetaEtaConfluence.firstNotConvertibleSecond`). No D∞. -/
theorem consistentLatticeEtaWithoutHypotheses : ConsistentLatticeEta (fun _ _ => False) :=
  fun derivation => BetaEtaConfluence.firstNotConvertibleSecond
    (SyntacticConsistency.derivableLatticeEtaPureConvertible (by simp [first, Term.Pure])
      (by simp [second, Term.Pure]) derivation)

end LambdaJit.Semantics

namespace LambdaJit.ContextualPreorder

open LambdaJit.Semantics

namespace DdLP96Model

variable (model : DdLP96Model)

/-- The proofs file's section 4 for ⊢_{λ-lattice-η}, given a model satisfying the fields of
`DdLP96Model`: DdLP96's reading is a model of ⊢_{λ-lattice-η}. Under hypotheses whose two sides read
alike in every environment, two terms equal by ⊢_{λ-lattice-η} read alike in every environment. Case
by case: the β rule by the substitution lemma, the η rule by (P6) and weakening, (1) by the commutativity of ⊓, (3) by the
commutativity of ⊔, (5) by m ⊔ (m ⊓ n) = m, (10) by the monotonicity of application in its argument,
and the congruences by the compositionality of the reading. The reading of 0 as ⊤ is not used. -/
theorem interpretDerivableLatticeEta {hypotheses : Term → Term → Prop}
    (hypothesesHold : ∀ left right, hypotheses left right →
      ∀ environment, model.interpret left environment = model.interpret right environment)
    {left right : Term} (derivation : DerivableLatticeEta hypotheses left right) :
    ∀ environment, model.interpret left environment = model.interpret right environment := by
  induction derivation with
  | hypothesis isHypothesis => exact hypothesesHold _ _ isHypothesis
  | symmetric _ inner => exact fun environment => (inner environment).symm
  | transitive _ _ leftEqual rightEqual =>
      exact fun environment => (leftEqual environment).trans (rightEqual environment)
  | congruenceArgument function _ inner =>
      intro environment
      rw [model.interpretApplication, model.interpretApplication, inner]
  | congruenceAbstraction _ inner => exact model.interpretAbstractionCongruence inner
  | beta body argument =>
      intro environment
      rw [model.interpretApplication, model.interpretAbstraction, model.interpretInstantiate]
  | eta function => exact model.interpretEta function
  | choiceCommutative left right =>
      intro environment
      rw [model.interpretChoice, model.interpretChoice, model.meetCommutative]
  | parallelCommutative left right =>
      intro environment
      rw [model.interpretParallel, model.interpretParallel, model.joinCommutative]
  | parallelAbsorption kept other =>
      intro environment
      rw [model.interpretParallel, model.interpretChoice, model.joinAbsorption]
  | argumentMonotone function argument addition =>
      intro environment
      simp only [model.interpretChoice, model.interpretApplication]
      rw [model.meetCommutative]
      exact model.meetOfBelow
        (model.applyMonotoneArgument _ (model.meetBelowLeft _ _))

/-- The record's theorem 6.1 for ⊢_{λ-lattice-η}, given a model satisfying the fields of
`DdLP96Model`: ∅ ⊢_{λ-lattice-η} M = M′ gives M ≃_O M′, by `interpretDerivableLatticeEta` and the
record's corollary 4.2. -/
theorem contextualEquivalenceOfDerivableLatticeEta (model : DdLP96Model) {left right : Term}
    (derivation : DerivableLatticeEta (fun _ _ => False) left right) :
    ContextualEquivalence left right :=
  model.contextualEquivalenceOfInterpretEqual
    (model.interpretDerivableLatticeEta (fun _ _ impossible => impossible.elim) derivation)

end DdLP96Model

/-- The record's theorem 6.1 for ⊢_{λ-lattice-η}: ∅ ⊢_{λ-lattice-η} M = M′ gives M ≃_O M′, in
Wadsworth's D∞ (`DdLP96Model.contextualEquivalenceOfDerivableLatticeEta`), with no hypothesis. The
proof does not use the unit law. -/
theorem contextualEquivalenceOfDerivableLatticeEta {left right : Term}
    (derivation : DerivableLatticeEta (fun _ _ => False) left right) :
    ContextualEquivalence left right :=
  DInfinity.wadsworthModel.contextualEquivalenceOfDerivableLatticeEta derivation

end LambdaJit.ContextualPreorder
