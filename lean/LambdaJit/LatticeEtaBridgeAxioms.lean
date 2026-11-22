import LambdaJit.LatticeEtaBridge

/-!
# The axioms of the consistency, theorem 6.1 and the bridge for ⊢_{λ-lattice-η}

`#print axioms` for the main theorems of modules `LatticeEtaConsistency` and `LatticeEtaBridge`, and
for the theorems of module `ContextualPreorderAdequacy` that use `top` as their closed argument,
printed on every build of this module. Recorded 2026-11-10:

    'LambdaJit.SyntacticConsistency.derivableLatticeEtaSameReadings' depends on axioms: [propext, Quot.sound]
    'LambdaJit.SyntacticConsistency.derivableLatticeEtaPureConvertible' depends on axioms: [propext, Quot.sound]
    'LambdaJit.Semantics.consistentLatticeEtaWithoutHypotheses' depends on axioms: [propext, Quot.sound]
    'LambdaJit.ContextualPreorder.DdLP96Model.interpretDerivableLatticeEta' depends on axioms: [propext, Quot.sound]
    'LambdaJit.ContextualPreorder.DdLP96Model.contextualEquivalenceOfDerivableLatticeEta' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.contextualEquivalenceChoiceOfContextualPreorder' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.consistentEquationLatticeEtaOfContextualPreorder' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.consistentNormalFormLatticeEtaOfContextualNormalForm' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.contextualPreorderOfConsistentNormalFormLatticeEta' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.consistentNormalFormLatticeEtaIffContextualPreorder' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.consistentNormalFormLatticeEtaIffContextualNormalForm' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.contextualPreorderIffInterpretBelowLatticeEta' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.solvableApplicationsTop' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.DdLP96Model.computableOfSolvableApplications' depends on axioms: [propext]
    'LambdaJit.ContextualPreorder.DdLP96Model.solvableOfComputable' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.DdLP96Model.computableSucc' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.DdLP96Model.solvableOfInterpretNotBottom' depends on axioms: [propext, Classical.choice, Quot.sound]

Only Lean's built-in axioms are listed: there is no named axiom, and no placeholder of an
unfinished proof. The syntactic consistency of ⊢_{λ-lattice-η} uses no model and no classical
choice. The theorems in the namespace `DdLP96Model` take a model as an explicit argument; the others
are stated in Wadsworth's D∞ with no hypothesis beyond their premises.
-/

#print axioms LambdaJit.SyntacticConsistency.derivableLatticeEtaSameReadings
#print axioms LambdaJit.SyntacticConsistency.derivableLatticeEtaPureConvertible
#print axioms LambdaJit.Semantics.consistentLatticeEtaWithoutHypotheses
#print axioms LambdaJit.ContextualPreorder.DdLP96Model.interpretDerivableLatticeEta
#print axioms LambdaJit.ContextualPreorder.DdLP96Model.contextualEquivalenceOfDerivableLatticeEta
#print axioms LambdaJit.ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta
#print axioms LambdaJit.ContextualPreorder.contextualEquivalenceChoiceOfContextualPreorder
#print axioms LambdaJit.ContextualPreorder.consistentEquationLatticeEtaOfContextualPreorder
#print axioms LambdaJit.ContextualPreorder.consistentNormalFormLatticeEtaOfContextualNormalForm
#print axioms LambdaJit.ContextualPreorder.contextualPreorderOfConsistentNormalFormLatticeEta
#print axioms LambdaJit.ContextualPreorder.consistentNormalFormLatticeEtaIffContextualPreorder
#print axioms LambdaJit.ContextualPreorder.consistentNormalFormLatticeEtaIffContextualNormalForm
#print axioms LambdaJit.ContextualPreorder.contextualPreorderIffInterpretBelowLatticeEta
#print axioms LambdaJit.ContextualPreorder.solvableApplicationsTop
#print axioms LambdaJit.ContextualPreorder.DdLP96Model.computableOfSolvableApplications
#print axioms LambdaJit.ContextualPreorder.DdLP96Model.solvableOfComputable
#print axioms LambdaJit.ContextualPreorder.DdLP96Model.computableSucc
#print axioms LambdaJit.ContextualPreorder.DdLP96Model.solvableOfInterpretNotBottom
