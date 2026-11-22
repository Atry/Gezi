import LambdaJit.ContextualPreorderUnconditional

/-!
# The axioms of the instance `wadsworthModel` and of the theorems with no model argument

`#print axioms` for the instance of module `DInfinityModel` and the theorems of module
`ContextualPreorderUnconditional`, printed on every build of this module. Recorded 2026-11-07,
the three Ω theorems after `omegaParallelContextualEquivalence` on 2026-11-11:

    'LambdaJit.DInfinity.wadsworthModel' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.solvableIffInterpretNotBottom' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.omegaParallelContextualEquivalence' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.omegaContextualPreorder' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.omegaChoiceContextualEquivalence' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.omegaApplicationContextualEquivalence' depends on axioms: [propext, Classical.choice, Quot.sound]

Only Lean's built-in axioms are listed: there is no named axiom, and no placeholder of an
unfinished proof. No theorem listed takes a hypothesis beyond its statement's premises.
-/

#print axioms LambdaJit.DInfinity.wadsworthModel
#print axioms LambdaJit.ContextualPreorder.solvableIffInterpretNotBottom
#print axioms LambdaJit.ContextualPreorder.omegaParallelContextualEquivalence
#print axioms LambdaJit.ContextualPreorder.omegaContextualPreorder
#print axioms LambdaJit.ContextualPreorder.omegaChoiceContextualEquivalence
#print axioms LambdaJit.ContextualPreorder.omegaApplicationContextualEquivalence
