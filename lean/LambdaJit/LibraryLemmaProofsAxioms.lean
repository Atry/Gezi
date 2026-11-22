import LambdaJit.LibraryLemmaProofs

/-!
# The axioms of the hand-written proofs of library lemmas

`#print axioms` for the twelve theorems of module `LibraryLemmaProofs`, printed on every build of
this module. Recorded 2026-10-07: each depends on `propext`, `Classical.choice` and `Quot.sound`
and on no other axiom.

Only Lean's built-in axioms are listed: the kernel evaluates the searches (`decide +kernel`), so
there is no `Lean.ofReduceBool`, and there is no named axiom.
-/

#print axioms LambdaJit.LibraryLemmaProofs.«successor_filtered»
#print axioms LambdaJit.LibraryLemmaProofs.«successor_filtered_chained»
#print axioms LambdaJit.LibraryLemmaProofs.«natural_double_as_fold»
#print axioms LambdaJit.LibraryLemmaProofs.«nat_fold_filtered_contract»
#print axioms LambdaJit.LibraryLemmaProofs.«nat_fold_filtered_contract_chained»
#print axioms LambdaJit.LibraryLemmaProofs.«nat_fold_filtered_branch»
#print axioms LambdaJit.LibraryLemmaProofs.«nat_fold_filtered_branch_in_context»
#print axioms LambdaJit.LibraryLemmaProofs.«zero_filtered»
#print axioms LambdaJit.LibraryLemmaProofs.«true_filtered»
#print axioms LambdaJit.LibraryLemmaProofs.«false_filtered»
#print axioms LambdaJit.LibraryLemmaProofs.«filter_nat_idempotent»
#print axioms LambdaJit.LibraryLemmaProofs.«unary_as_fold»
