import LambdaJit.ContextualPreorder

/-!
# The axioms of the syntactic part of the contextual preorder

`#print axioms` for the main theorems of module `ContextualPreorder`, printed on every build of
this module. Recorded 2026-11-07:

    'LambdaJit.ContextualPreorder.headStepIffMem' depends on axioms: [propext, Quot.sound]
    'LambdaJit.ContextualPreorder.solvableIffAccessible' depends on axioms: [propext, Quot.sound]
    'LambdaJit.ContextualPreorder.headStepNoneIffHeadNormalForm' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.solvableChoice' depends on axioms: [propext, Quot.sound]
    'LambdaJit.ContextualPreorder.solvableParallel' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.solvableOfUniqueSuccessor' does not depend on any axioms
    'LambdaJit.ContextualPreorder.solvableBetaSpine' depends on axioms: [propext]
    'LambdaJit.ContextualPreorder.solvableChoiceSpine' depends on axioms: [propext, Quot.sound]
    'LambdaJit.ContextualPreorder.solvableParallelSpine' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.solvableOfSolvableApplication' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.ContextualPreorder.fill' depends on axioms: [propext]

Only Lean's built-in axioms are listed: there is no named axiom, and no placeholder of an
unfinished proof. Classical.choice enters through excluded middle in the parallel cases: a bound
of M ∥ N bounds M or N, and a →hsa normal form M ∥ N has a side with no step.
-/

#print axioms LambdaJit.ContextualPreorder.headStepIffMem
#print axioms LambdaJit.ContextualPreorder.solvableIffAccessible
#print axioms LambdaJit.ContextualPreorder.headStepNoneIffHeadNormalForm
#print axioms LambdaJit.ContextualPreorder.solvableChoice
#print axioms LambdaJit.ContextualPreorder.solvableParallel
#print axioms LambdaJit.ContextualPreorder.solvableOfUniqueSuccessor
#print axioms LambdaJit.ContextualPreorder.solvableBetaSpine
#print axioms LambdaJit.ContextualPreorder.solvableChoiceSpine
#print axioms LambdaJit.ContextualPreorder.solvableParallelSpine
#print axioms LambdaJit.ContextualPreorder.solvableOfSolvableApplication
#print axioms LambdaJit.ContextualPreorder.ContextualPreorder.fill
