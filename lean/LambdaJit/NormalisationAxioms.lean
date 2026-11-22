import LambdaJit.Normalisation

/-!
# The axioms of the normaliser's soundness

`#print axioms` for the soundness theorems of module `Normalisation`, for the theorem that the
eta contraction finds every left side of the η rule, and for the theorem that a result of
the normaliser has no redex, printed on every build of this module. Recorded 2026-10-04, the
normal form by weak head reduction 2026-11-21:

    'LambdaJit.Semantics.stepSound' depends on axioms: [propext, Quot.sound]
    'LambdaJit.Semantics.normaliseSound' depends on axioms: [propext, Quot.sound]
    'LambdaJit.Semantics.derivableOfNormaliseEqual' depends on axioms: [propext, Quot.sound]
    'LambdaJit.Semantics.Term.etaContractumShift' depends on axioms: [propext, Quot.sound]
    'LambdaJit.Semantics.normaliseNoRedex' depends on axioms: [propext]
    'LambdaJit.Semantics.weakHeadSound' depends on axioms: [propext, Quot.sound]
    'LambdaJit.Semantics.normalFormSound' depends on axioms: [propext, Quot.sound]
    'LambdaJit.Semantics.derivableOfNormalFormWithinEqual' depends on axioms: [propext, Quot.sound]

Only Lean's built-in axioms are listed: there is no named axiom, and no placeholder of an
unfinished proof. The three soundness theorems hold for every set of hypotheses, which they take
as an implicit argument.
-/

#print axioms LambdaJit.Semantics.stepSound
#print axioms LambdaJit.Semantics.normaliseSound
#print axioms LambdaJit.Semantics.derivableOfNormaliseEqual
#print axioms LambdaJit.Semantics.Term.etaContractumShift
#print axioms LambdaJit.Semantics.normaliseNoRedex
#print axioms LambdaJit.Semantics.weakHeadSound
#print axioms LambdaJit.Semantics.normalFormSound
#print axioms LambdaJit.Semantics.derivableOfNormalFormWithinEqual
