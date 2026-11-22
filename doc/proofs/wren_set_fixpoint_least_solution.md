# The least solution of a knot over value sets (the keyed calls' meta lemma)

Written 2026-10-01: the keyed calls, the
least-fixed-point iteration of `value_set_evaluation`'s re-entrant knots, is the
native implementation of the attractor "a knot over a set-valued template", and
its monotonicity is a meta lemma checked once instead of per point. Hand proof,
not machine-checked.

The judgment is the one restated in
[certificate_meta_lemmas.md](certificate_meta_lemmas.md): terms Λ⁺ with sets, the
meaning ⟦T⟧ ⊆ Λ (the yields of T), and S(T), the closed beta eta normal forms N
consistent with some yield T′ of T (Th({T′ = N}) does not equate the two
Booleans). Write NF⟦T⟧ for the beta eta normal forms of the yields of T that
have one. NF⟦T⟧ ⊆ S(T), since a yield is consistent with its own normal form;
S(T) can be larger, since a yield with no normal form can be consistent with
normal forms (S(Ω) is all of them). Th(E) is defined there too, as the least set of equations
over Λ⁺ that contains E, B (beta), H (eta) and R (reflexivity) and is closed
under symmetry, transitivity and the congruences ν, μ, ξ and σ. Th(∅) is that
theory with no further equations, lambda beta eta on Λ⁺, with sets treated as
constructors.
The facts about the evaluator are those argued in the module comment of
`prolog/gezi/value_set_evaluation.pl` (the evaluation's SOUNDNESS,
COMPLETENESS and FOLDING BY VALUE; memoised ties; the keyed calls,
`keyed_call/4`).

## The setting

A *knot* is a closed term K that is a fixed point of a template, `Y G` or `W W`
(`set_tie/4`), applied through its leading abstractions to arguments. Fix one
knot K of arity m. A *key* is an m-tuple k of canonical data (numerals,
Booleans, lists of these): single_key/2 reads each argument's thunk as one
canonical datum. Write ⟨K k⟩ for the term K applied to the canonical terms of
k, and V(k) ⊆ Λ for the set of the weak heads that the evaluation reaches for
⟨K k⟩, up to beta eta equality.

A keyed call applies when the computation of ⟨K k⟩ meets ⟨K k′⟩ for a key k′ whose
call is in progress. Its restriction (enforced by
`data_key/1` and the `datum_value` test of `leader_values/6`): every key met in
progress is data, and every value of an approximation is a canonical datum.
Otherwise the evaluation gives up and answers nothing.

## The operator

Let C be the set of keys of one strongly connected group of calls, the calls
that met one another in progress, with their leader at the lowest depth
(`lowered/1`, `left/4`). C is finite whenever the iteration ends, since each
iteration computes finitely many calls. An *assignment* A maps each k ∈ C to a
finite set A(k) of canonical data. Assignments are ordered pointwise by
inclusion, and the empty assignment ∅ is the least.

For an assignment A, let F(A) be the assignment that maps k to the set of
values that the evaluation computes for ⟨K k⟩, where every call ⟨K k′⟩ with
k′ ∈ C met *inside* that computation is answered A(k′) instead of being
computed, after folding by value (`values_folded/2`).

The iteration of `leader_values/6` computes A₀ = ∅ and A_{i+1} = F(A_i) on the
leader's key, and with it the values of the calls inside, which are not
remembered until the leader is stable (`keyed_call/4`). It stops at the first i
with A_{i+1} = A_i, compared by `==` on sorted canonical data. Write A* for
that assignment.

## Lemma 1 (monotonicity): A ⊆ B implies F(A) ⊆ F(B)

Each construct of the evaluator acts on the members of its sets one at a time
(the evaluator's module comment):
- a merge unites its members' values;
- an application applies each value of the function to the argument's thunk;
- a variable's uses each range over the whole set its thunk holds.

No construct observes a set's size or emptiness. The places that could look at
a set as a whole are these.
- `single_key/2` reads an argument as *one* datum, and fails on a set of two or
  more. A failed key makes the call run unremembered, which computes the same
  values, so only the cost differs (memoised ties).
- `values_folded/2` replaces data by their canonical terms. Each value is beta
  eta equal to its datum, so the fold preserves the set's meaning.
- `thunk_data/3` reads a thunk's set as a set of data, member by member.

So enlarging the answer given to an inner call can only enlarge each set that
depends on it, member by member, and F is monotone. ∎

## Lemma 2 (soundness): every value in A* is a value of a yield of ⟨K k⟩

By induction on i: every datum in A_i(k) is the normal form of some yield of
⟨K k⟩.
- i = 0: ∅, vacuous.
- Step: a datum d ∈ A_{i+1}(k) = F(A_i)(k) is computed by the evaluation of
  ⟨K k⟩, with finitely many inner calls ⟨K k′⟩ answered by members d′ of
  A_i(k′). By induction each d′ is the normal form of a yield Y′ of ⟨K k′⟩.
- The evaluation's soundness says the evaluation's value is the weak head of a yield of
  the term with each such inner call replaced by d′. Replacing each d′ back by
  its yield Y′ (Th(∅)-equal to d′) gives a yield of ⟨K k⟩ itself, with the same
  normal form d. This uses the closure of ⟦·⟧ under set occurrences in
  any context, and Th(∅) equality. ∎

## Lemma 3 (completeness): every datum that is the normal form of a yield of ⟨K k⟩ is in A*(k)

- A yield Y of ⟨K k⟩ with normal form d is reached by a finite reduction. It
  therefore unfolds K finitely often: its re-entries into calls of C form a
  finite tree.
- By induction on the height h of that tree, d ∈ F^{h+1}(∅)(k).
  - Height 0: Y's evaluation meets no call of C, so it does not depend on the
    assignment, and d ∈ F(∅)(k) by the evaluation's completeness.
  - Height h + 1: every inner call's yield has height at most h. That yield
    has a normal form, and the normal form is a canonical datum, because of
    the keyed calls' restriction: every value of an approximation is a canonical datum
    (the `datum_value` test of `leader_values/6`), and otherwise the
    evaluator gives up instead of answering. By induction its normal form is
    in F^{h+1}(∅). F answers those inner calls with supersets of what Y uses
    (Lemma 1), so d ∈ F^{h+2}(∅)(k).
- The chain ∅ ⊆ F(∅) ⊆ F²(∅) ⊆ … is increasing (Lemma 1), and A* is its first
  repeat. An increasing chain that repeats once is constant from then on.
- So A* = F^n(∅) for every n past the stop, and d ∈ A*(k). ∎

## Theorem (the knot's value set)

When the iteration stops, A*(k) is exactly the set of normal forms of the
yields of ⟨K k⟩, and A* is the least fixed point of F.
- The first claim is Lemmas 2 and 3.
- A* = F(A*) by the stopping test.
- For any fixed point B, ∅ ⊆ B gives F^n(∅) ⊆ F^n(B) = B by Lemma 1, so A* ⊆ B.

The theorem is what a native relies on when it answers a knot's call with
the value set of `keyed_call/4`, and it gives two things.
- Soundness: A*(k) ⊆ NF⟦⟨K k⟩⟧ ⊆ S(⟨K k⟩), so every value answered is in S.
- Completeness for NF⟦⟨K k⟩⟧, and not for S(⟨K k⟩).
  - Rule 36's set clause lets one choice act on a set occurrence inside the
    generator, shared by every unfolding: a limit yield.
  - Where the iteration meets a re-entry, such a yield can be pure, have no
    head normal form, and be consistent with normal forms outside NF⟦⟨K k⟩⟧.
  - The witness is the infinite tree of
    `corpora/contest_empty_set_reachability.pl`, `without(Bit)`. Its yield
    Y (λs.λn. s (cons b n)) nil is easy by the collapse lemma
    (`solo_collapse_lemma.md`), so both Booleans are in S of its test.
  - So the answer is A*(k) = NF⟦⟨K k⟩⟧, which can be a proper part of
    S(⟨K k⟩). A native that answers it claims membership, never the whole of S.

## Worklist iteration over a growing set of keys (the knot attractor)

The core of the keyed calls gives the knot attractor's native one service: `unfolding(Generator, Arguments,
Table, values(Values, Missing))`.
- It evaluates one unfolding of the generator on the arguments.
- Each inner call whose arguments are all canonical data is answered from
  Table: the set Table holds for its key, or the empty set when Table lacks
  the key, in which case the call is listed in Missing.
- An inner call that cannot be keyed is unfolded in place.
- A key is the generator with the canonical literal Ids of the arguments.

So Values is F(A_T)(k), for the assignment A_T that is Table on its keys and
the empty set elsewhere. The native iterates over a growing set R of keys:
- start with R = {k₀} and Table empty;
- recompute every key of R from the current Table, store the results, and add
  every Missing key to R;
- stop after a full round over R that changes no entry and adds no key.

Write A* for the final Table. This is a chaotic iteration of F, not the
synchronous chain of the sections above, so the theorem is restated for it.

**Theorem 2.** When the worklist iteration stops, A*(k) is exactly the set of
normal forms of the yields of ⟨K k⟩, for every k ∈ R.

*Soundness.* By induction on the number of updates of Table: every datum ever
stored for k is the normal form of a yield of ⟨K k⟩. An update computes F(A_T)(k)
with inner calls answered by stored data (normal forms of yields, by
induction) or by the empty set. Lemma 2's argument applies unchanged: each
answered datum can be replaced back by its yield, and the empty set
contributes nothing.

*Completeness.* Let Y be a yield of ⟨K k⟩ with normal form d, k ∈ R. By
induction on the height h of Y's finite tree of keyed re-entries, d ∈ A*(k).
- The final round recomputes k under A*. By the evaluation's completeness that
  computation follows Y's choices along Y's path.
- At the first inner keyed call on that path, of key k′, the call is made
  under A*, so k′ is in Table or in Missing. Either way k′ ∈ R, by the stopping
  test.
- The sub-yield of Y for that call has height below h + 1. Its normal form d′
  is a canonical datum, by the keyed calls' restriction as in Lemma 3. By induction
  d′ ∈ A*(k′).
- So the computation answers that call with a set that contains d′, and
  continues along Y's path. The same argument applies at each later inner
  call, and calls unfolded in place are part of the path.
- The computation therefore reaches d, so d ∈ F(A*)(k). The stopping test
  gives F(A*)(k) = A*(k), and so d ∈ A*(k).
- Height 0 is the case with no inner keyed call on the path. ∎

Theorem 2 needs no fairness beyond the stopping test: the final round
recomputes every key of R under the final Table, and that is what both halves
use. Keying by canonical literal Ids makes two spellings of one datum one key,
as the memoised ties' keys do, so R is a set of keys up to beta eta equality of the
arguments.

## What the theorem does not say

- It does not say A*(k) is S(⟨K k⟩): it is NF⟦⟨K k⟩⟧, see the paragraph after the
  Theorem.
- It does not say either iteration stops. When ⟨K k⟩ has infinitely many normal
  forms (the unbounded counter of `tests/value_set_evaluation.plt`), the chain
  never repeats. The evaluation ends at its budget and answers nothing, never a
  part of the set.
- It assumes the restriction above. With a closure among the keys or values,
  `==` on values would compare spellings, not meanings, and a stable chain
  would prove nothing. That is why the evaluator gives up there
  (`value_set_evaluation_not_data`).
- It assumes no deferred choice was made inside a call of C. A call that
  made a choice is not remembered, and gives up when it also met a call in
  progress (`leader_values/6`), so no assignment ever depends on a choice.
