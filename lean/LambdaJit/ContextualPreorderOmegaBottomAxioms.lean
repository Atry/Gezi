import LambdaJit.ContextualPreorderOmegaBottom

/-!
# The axioms of the Ω-below theorems

`#print axioms` for the theorems of module `ContextualPreorderOmegaBottom`, printed on every
build of this module. Recorded 2026-11-07, the three Ω theorems after
`omegaParallelContextualEquivalence` on 2026-11-11:

    'LambdaJit.ContextualPreorder.DdLP96Model.omegaParallelContextualEquivalence' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.DdLP96Model.omegaContextualPreorder' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.DdLP96Model.omegaChoiceContextualEquivalence' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.DdLP96Model.omegaApplicationContextualEquivalence' depends on axioms: [propext, Classical.choice, Quot.sound]

Only Lean's built-in axioms are listed: there is no named axiom, and no placeholder of an
unfinished proof. Every theorem listed takes a `DdLP96Model` as an explicit argument, which the
instance `wadsworthModel` discharges (module `ContextualPreorderUnconditionalAxioms`).
-/

#print axioms LambdaJit.ContextualPreorder.DdLP96Model.omegaParallelContextualEquivalence
#print axioms LambdaJit.ContextualPreorder.DdLP96Model.omegaContextualPreorder
#print axioms LambdaJit.ContextualPreorder.DdLP96Model.omegaChoiceContextualEquivalence
#print axioms LambdaJit.ContextualPreorder.DdLP96Model.omegaApplicationContextualEquivalence
