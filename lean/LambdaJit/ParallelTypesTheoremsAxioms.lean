import LambdaJit.ParallelTypesTheorems

/-!
# The axioms of the theorems on the lemmas of `parallel_types.pl` and `filtered_recursion_naturals.pl`

`#print axioms` for the seven theorems of module `ParallelTypesTheorems` on the lemmas of
`parallel_types.pl` and `filtered_recursion_naturals.pl`, printed on every build of this module.
Recorded 2026-10-07:

    'LambdaJit.ParallelTypesTheorems.successorFiltered' depends on axioms: [propext, Quot.sound]
    'LambdaJit.ParallelTypesTheorems.successorFilteredChained' depends on axioms: [propext, Quot.sound]
    'LambdaJit.ParallelTypesTheorems.naturalFoldFilteredContract' depends on axioms: [propext, Quot.sound]
    'LambdaJit.ParallelTypesTheorems.naturalFoldFilteredContractChained' depends on axioms: [propext, Quot.sound]
    'LambdaJit.ParallelTypesTheorems.naturalFoldFilteredBranch' depends on axioms: [propext, Quot.sound]
    'LambdaJit.ParallelTypesTheorems.naturalFoldFilteredBranchInContext' depends on axioms: [propext, Quot.sound]
    'LambdaJit.ParallelTypesTheorems.naturalDoubleAsFold' depends on axioms: [propext, Quot.sound]

Only Lean's built-in axioms are listed: there is no named axiom, and no placeholder of an
unfinished proof.
-/

#print axioms LambdaJit.ParallelTypesTheorems.successorFiltered
#print axioms LambdaJit.ParallelTypesTheorems.successorFilteredChained
#print axioms LambdaJit.ParallelTypesTheorems.naturalFoldFilteredContract
#print axioms LambdaJit.ParallelTypesTheorems.naturalFoldFilteredContractChained
#print axioms LambdaJit.ParallelTypesTheorems.naturalFoldFilteredBranch
#print axioms LambdaJit.ParallelTypesTheorems.naturalFoldFilteredBranchInContext
#print axioms LambdaJit.ParallelTypesTheorems.naturalDoubleAsFold
