import LambdaJit.LatticeEtaSeparation

/-!
# The axioms of the theorems on ⊢_{λ-lattice-η}

`#print axioms` for the main theorems of modules `LatticeEtaDerivability`, `LatticeEtaConsistency`,
`LatticeEtaXi`, `LatticeEtaApproximation` and `LatticeEtaSeparation` (the proofs file's section 21,
the proofs file). Read on 2026-11-07, and for the two theorems of
`LatticeEtaConsistency` again on 2026-11-10 with the same result (module `LatticeEtaBridgeAxioms`):
the theorems of the derivability,
of Ξ and of the separation depend on propext and Quot.sound; those that go through Wadsworth's D∞
(the contextual equivalence, theorem A and the completeness) also on Classical.choice. No `sorry`,
no axiom of this repository. The equivalences of NF◇_{λ-lattice-η} with ⊑_O are printed by module
`LatticeEtaBridgeAxioms`.
-/

#print axioms LambdaJit.Semantics.DerivableLatticeEta.choiceAssociative
#print axioms LambdaJit.Semantics.DerivableLatticeEta.parallelAssociative
#print axioms LambdaJit.Semantics.DerivableLatticeEta.choiceAbsorption
#print axioms LambdaJit.Semantics.DerivableLatticeEta.choiceFunctionDistributive
#print axioms LambdaJit.Semantics.DerivableLatticeEta.parallelFunctionDistributive
#print axioms LambdaJit.Semantics.consistentLatticeEtaWithoutHypotheses
#print axioms LambdaJit.ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta
#print axioms LambdaJit.LatticeEta.embedTranslate
#print axioms LambdaJit.LatticeEta.xiRefinesClosed
#print axioms LambdaJit.LatticeEta.refinesClosedTermsApplyAll
#print axioms LambdaJit.LatticeEta.inconsistentOfChoiceRefines
#print axioms LambdaJit.ContextualPreorder.DdLP96Model.approximationLatticeEta
#print axioms LambdaJit.ContextualPreorder.separationLatticeEta
#print axioms LambdaJit.ContextualPreorder.DdLP96Model.completenessLatticeEta
