import LambdaJit.ContextualPreorderTop

/-!
# The axioms of the criterion for the tops of ⊑_O, and of the facts about `top`

`#print axioms` for the theorems of module `ContextualPreorderTop`, printed on every build of this
module. Recorded 2026-11-10:

    'LambdaJit.ContextualPreorder.contextualTopIff' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.contextualTopIffClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.contextualTop' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.contextualTopXi' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.contextualEquivalenceTopChoiceOfContextualTop' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.contextualEquivalenceChoiceTopOfContextualTop' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.contextualEquivalenceTopParallelOfContextualTop' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.contextualEquivalenceParallelTopOfContextualTop' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.contextualEquivalenceTopChoice' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.contextualEquivalenceChoiceTop' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.contextualEquivalenceTopParallel' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.contextualEquivalenceParallelTop' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.derivableTopApplication' depends on axioms: [propext, Quot.sound]
    'LambdaJit.ContextualPreorder.contextualEquivalenceTopApplication' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.ContextualPreorder.contextualEquivalenceOfDerivableLatticeEtaHypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]

Only Lean's built-in axioms are listed: there is no named axiom, and no placeholder of an
unfinished proof. No theorem listed takes a hypothesis beyond its statement's premises.
-/

#print axioms LambdaJit.ContextualPreorder.contextualTopIff
#print axioms LambdaJit.ContextualPreorder.contextualTopIffClosed
#print axioms LambdaJit.ContextualPreorder.contextualTop
#print axioms LambdaJit.ContextualPreorder.contextualTopXi
#print axioms LambdaJit.ContextualPreorder.contextualEquivalenceTopChoiceOfContextualTop
#print axioms LambdaJit.ContextualPreorder.contextualEquivalenceChoiceTopOfContextualTop
#print axioms LambdaJit.ContextualPreorder.contextualEquivalenceTopParallelOfContextualTop
#print axioms LambdaJit.ContextualPreorder.contextualEquivalenceParallelTopOfContextualTop
#print axioms LambdaJit.ContextualPreorder.contextualEquivalenceTopChoice
#print axioms LambdaJit.ContextualPreorder.contextualEquivalenceChoiceTop
#print axioms LambdaJit.ContextualPreorder.contextualEquivalenceTopParallel
#print axioms LambdaJit.ContextualPreorder.contextualEquivalenceParallelTop
#print axioms LambdaJit.ContextualPreorder.derivableTopApplication
#print axioms LambdaJit.ContextualPreorder.contextualEquivalenceTopApplication
#print axioms LambdaJit.ContextualPreorder.contextualEquivalenceOfDerivableLatticeEtaHypotheses
