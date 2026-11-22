import LambdaJit.ContextualPreorderAdequacy

/-!
# The axioms of the adequacy theorems, given a model

`#print axioms` for the main theorems of modules `DdLP96Model` and `ContextualPreorderAdequacy`,
printed on every build of this module. Recorded 2026-11-07:

    'LambdaJit.ContextualPreorder.DdLP96Model.interpretHeadStep' depends on axioms: [propext, Quot.sound]
    'LambdaJit.ContextualPreorder.DdLP96Model.interpretNotBottomOfSolvable' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.DdLP96Model.basicLemma' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.DdLP96Model.solvableIffInterpretNotBottom' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.DdLP96Model.contextualPreorderOfInterpretBelow' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.notContextuallyEquivalentFirstSecond' depends on axioms: [propext, Classical.choice, Quot.sound]

Only Lean's built-in axioms are listed: there is no named axiom, and no placeholder of an
unfinished proof. Every theorem listed but `notContextuallyEquivalentFirstSecond` takes a
`DdLP96Model` as an explicit argument, which the instance `wadsworthModel` discharges (module
`ContextualPreorderUnconditionalAxioms`).
-/

#print axioms LambdaJit.ContextualPreorder.DdLP96Model.interpretHeadStep
#print axioms LambdaJit.ContextualPreorder.DdLP96Model.interpretNotBottomOfSolvable
#print axioms LambdaJit.ContextualPreorder.DdLP96Model.basicLemma
#print axioms LambdaJit.ContextualPreorder.DdLP96Model.solvableIffInterpretNotBottom
#print axioms LambdaJit.ContextualPreorder.DdLP96Model.contextualPreorderOfInterpretBelow
#print axioms LambdaJit.ContextualPreorder.notContextuallyEquivalentFirstSecond
