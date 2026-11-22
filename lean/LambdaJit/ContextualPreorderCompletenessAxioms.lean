import LambdaJit.ContextualPreorderCompleteness

/-!
# The axioms of lemma C and of the head-node reading

`#print axioms` for the theorems of modules `ContextualPreorderSeparationProof` and
`ContextualPreorderCompleteness` that the completeness for ⊢_{λ-lattice-η} (module
`LatticeEtaSeparation`) uses, printed on every build of this module. Recorded 2026-11-07:

    'LambdaJit.ContextualPreorder.betaNormalOfNormalForm' depends on axioms: [propext]
    'LambdaJit.ContextualPreorder.DdLP96Model.interpretBelowOfNotConflicts' depends on axioms: [propext, Classical.choice, Quot.sound]

Only Lean's built-in axioms are listed: there is no named axiom, and no placeholder of an
unfinished proof. `betaNormalOfNormalForm` takes no hypothesis; `interpretBelowOfNotConflicts`
(lemma C) takes a `DdLP96Model` as an explicit argument, which the instance `wadsworthModel`
discharges.
-/

#print axioms LambdaJit.ContextualPreorder.betaNormalOfNormalForm
#print axioms LambdaJit.ContextualPreorder.DdLP96Model.interpretBelowOfNotConflicts
