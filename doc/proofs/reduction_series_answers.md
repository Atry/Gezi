# The answers of a reduction series family under Definition 14

The families of the reduction series (`problems/shortest_superstring`, `problems/smallest_team`,
`problems/path_lengths`, `problems/collect_keys` and the `problems/hidden_37_*` families) and
`problems/empty_set_reachability` state their programs'
answers by pseudo-code and an argument written in the calculus that still has the empty choice `{}`, from before
Definition 14 became the primary definition (CONTRIBUTING.md, ["Terms"](../../CONTRIBUTING.md#terms)). This note
carries those arguments over to ⊑_O; each family's header points here.

The program writes `top` (`corpora/library/top`) where the pseudo-code and the argument write `{}`. `top` ≃_O `{}`
(proved in Lean before the empty choice left the Lean term type), and ≃_O is a congruence, so the program and the one
with `{}` in `top`'s place are contextually equivalent and have the same answers.

An answer of the program T is a closed βη normal form N with T ⊑_O N (Definition 14).

- (⊇) Choosing one member at each choice and reducing to a normal form N gives T + N ≃_O T, since the λ-lattice laws
  hold up to ≃_O (Lean `ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta`) and so does `top` + M ≃_O M
  (`ContextualPreorder.contextualEquivalenceTopChoice`); the choice reads as the meet of ⊑_O
  (`lean/LambdaJit/LatticeEtaBridge.lean`), so T ≃_O T + N ⊑_O N.
- (⊆) The answers of T are the closed βη normal forms N with ◇(N + T = T), the consistent normal forms of T (Lean
  `consistentNormalFormLatticeEtaIffContextualPreorder`, `lean/LambdaJit/LatticeEtaBridge.lean`). The program, with
  `top` read as `{}` and its choices as constructors, reduces to a normal form (every recursive call consumes finite
  Scott data or a budget), so the selection theorem, a paper proof not in this repository, makes its answers the union
  of the answers of its selections, which are the members the (⊆) half of each family's argument computes.

The families' arguments use the lemmas of [certificate_meta_lemmas.md](certificate_meta_lemmas.md). Their Prolog
files and predicates (`corpora/contest_*.pl` and the name/arity references) are those of the deleted Prolog port; each
generator is now the family's Scala object in `contest-corpora`.
