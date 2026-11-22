import LambdaJit.BinaryNaturalsNonMember

/-!
# The axioms of the theorems on the filters of non-member binary numerals

`#print axioms` for the two theorems of module `BinaryNaturalsNonMember`, printed on every build of
this module. Recorded 2026-11-16:

    'LambdaJit.BinaryNaturalsNonMember.nonMemberIncompatible' depends on axioms: [propext, Quot.sound]
    'LambdaJit.BinaryNaturalsNonMember.nonMemberNotContextualPreorder' depends on axioms:
      [propext, Classical.choice, Quot.sound]

Only Lean's built-in axioms are listed: there is no named axiom, and no placeholder of an
unfinished proof.
-/

#print axioms LambdaJit.BinaryNaturalsNonMember.nonMemberIncompatible
#print axioms LambdaJit.BinaryNaturalsNonMember.nonMemberNotContextualPreorder
