import LambdaJit.PreludeLemmas

/-!
# The axioms of module `PreludeLemmas`

`#print axioms` for the soundness of head steps and for the fifteen equation lemmas of the prelude
in λ-lattice-η on defunctionalized terms, printed on every build of this module. Recorded
2026-10-07:

    'LambdaJit.PreludeLemmas.headStepEqual' depends on axioms: [propext, Quot.sound]
    'LambdaJit.PreludeLemmas.headStepsEqual' depends on axioms: [propext, Quot.sound]
    'LambdaJit.PreludeLemmas.equalOfHeadSteps' depends on axioms: [propext, Quot.sound]
    'LambdaJit.PreludeLemmas.naturalEqualZeroZero' depends on axioms: [propext, Quot.sound]
    'LambdaJit.PreludeLemmas.naturalEqualZeroSuccessor' depends on axioms: [propext, Quot.sound]
    'LambdaJit.PreludeLemmas.naturalEqualSuccessorZero' depends on axioms: [propext, Quot.sound]
    'LambdaJit.PreludeLemmas.naturalEqualSuccessorSuccessor' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.PreludeLemmas.naturalAtLeastZero' depends on axioms: [propext, Quot.sound]
    'LambdaJit.PreludeLemmas.naturalAtLeastZeroSuccessor' depends on axioms: [propext, Quot.sound]
    'LambdaJit.PreludeLemmas.naturalAtLeastSuccessorSuccessor' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.PreludeLemmas.naturalDifferenceZero' depends on axioms: [propext, Quot.sound]
    'LambdaJit.PreludeLemmas.naturalDifferenceZeroSuccessor' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.PreludeLemmas.naturalDifferenceSuccessorSuccessor' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.PreludeLemmas.naturalDoubleZero' depends on axioms: [propext, Quot.sound]
    'LambdaJit.PreludeLemmas.naturalDoubleSuccessor' depends on axioms: [propext, Quot.sound]
    'LambdaJit.PreludeLemmas.applyToApplied' depends on axioms: [propext, Quot.sound]
    'LambdaJit.PreludeLemmas.identityApplied' depends on axioms: [propext, Quot.sound]
    'LambdaJit.PreludeLemmas.composeApplied' depends on axioms: [propext, Quot.sound]

Only Lean's built-in axioms are listed.
-/

#print axioms LambdaJit.PreludeLemmas.headStepEqual
#print axioms LambdaJit.PreludeLemmas.headStepsEqual
#print axioms LambdaJit.PreludeLemmas.equalOfHeadSteps
#print axioms LambdaJit.PreludeLemmas.naturalEqualZeroZero
#print axioms LambdaJit.PreludeLemmas.naturalEqualZeroSuccessor
#print axioms LambdaJit.PreludeLemmas.naturalEqualSuccessorZero
#print axioms LambdaJit.PreludeLemmas.naturalEqualSuccessorSuccessor
#print axioms LambdaJit.PreludeLemmas.naturalAtLeastZero
#print axioms LambdaJit.PreludeLemmas.naturalAtLeastZeroSuccessor
#print axioms LambdaJit.PreludeLemmas.naturalAtLeastSuccessorSuccessor
#print axioms LambdaJit.PreludeLemmas.naturalDifferenceZero
#print axioms LambdaJit.PreludeLemmas.naturalDifferenceZeroSuccessor
#print axioms LambdaJit.PreludeLemmas.naturalDifferenceSuccessorSuccessor
#print axioms LambdaJit.PreludeLemmas.naturalDoubleZero
#print axioms LambdaJit.PreludeLemmas.naturalDoubleSuccessor
#print axioms LambdaJit.PreludeLemmas.applyToApplied
#print axioms LambdaJit.PreludeLemmas.identityApplied
#print axioms LambdaJit.PreludeLemmas.composeApplied
