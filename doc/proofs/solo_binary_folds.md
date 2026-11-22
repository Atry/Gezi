# The lemmas of `binary_folds` are sound with respect to S

The Prolog library these proofs were written beside has been deleted; the
proofs still stand.

Written 2026-10-01; the premise section 2026-10-02. A hand proof, not machine-checked. A
lemma is DSL data with a pointer to a proof that it is sound with respect
to S, on paper or in an external program; the framework does not check it.
This file is that proof for the four lemmas of
`corpora/standard_library/binary_folds.pl`.

## What is proved

Every lemma here is an equation `Left = Right` over metavariables, under the
premise that one metavariable X is a finite member of a type. For each
lemma and each instance σ of its metavariables by terms of Λ⁺ that meets the
premise, we show

    (Left σ = Right σ) ∈ Th(∅).                                        (E)

That suffices for the equation reading of a lemma ("S is the same in every
context"). Th(∅) is closed under ν, μ, ξ and σ, so (E) gives
(C[Left σ] = C[Right σ]) ∈ Th(∅) for every one-hole context C; the rule th
of the definition of ⟦·⟧ makes the meaning invariant under Th(∅) equality,
so ⟦C[Left σ]⟧ = ⟦C[Right σ]⟧, and S(C[Left σ]) = S(C[Right σ]) because S
reads a term only through its meaning. The proofs below are therefore chains of equations of Th(∅); each
link is a beta step in one direction or the other, a define constant read as
its term, or an equation already proved, used under a context.

## The premise

A FINITE TREE of `binary_tree` is a term built from `binary_zero`,
`binary_even` and `binary_odd` alone: `binary_zero`, `binary_even t` or
`binary_odd t` for a finite tree t. A FINITE MEMBER of `binary_tree` is a
term X with (X = t) ∈ Th(∅) for some finite tree t. A finite member of
`binary` is one equal to a finite tree with no subterm `binary_even
binary_zero` (`binary`'s even handler excludes even zero). Because every
link below is an equation of a congruence, X may be replaced by its tree t
everywhere, and each proof is an induction on t.

The lemmas are declared with the membership premise `T @ X = X` (T is
`binary_tree`, or `binary` for idempotence_binary). Each proof below shows
(E) at X := t for every finite tree t of T (for `binary`, one without
`binary_even binary_zero`), every other metavariable any term of Λ⁺. So each
lemma is sound by S, in every context, at the instances whose X is a finite
member.

THE PREMISE ALONE DOES NOT GIVE A FINITE MEMBER. The single premise
`T @ X = X` does not make X a finite tree: X = `fixpoint @ binary_tree`
meets it by beta, in Th(∅), and is no finite tree. The lifting conjecture of
[ruler_premise_lifting_counterexample.md](ruler_premise_lifting_counterexample.md) is about `T @ X = X` together with
the type's structural equality, a premise these lemmas do not carry. So
neither these proofs nor that conjecture cover such an instance.

The way forward is a stronger premise in the object language: the
structural equality premise, under which the instances are those of the
lifting conjecture.

The premise cannot be dropped. For an opaque atom p, `binary_tree p` beta
reduces to `p binary_zero B_e B_o`, a normal form other than p, so
`binary_tree p = p` is not an equation of λβη (Böhm), and the involution
fails at p in the same way. A set is not a finite member: sets enter no
equation of Th(∅) other than by σ, so `{t1, t2}` is equal to no tree; at
X = `{binary_zero, binary_odd binary_zero}` the two occurrences of X in a
lemma would choose their members independently.

## The rows

`fixpoint` is `prelude`'s fixpoint combinator, so for every term G,
(fixpoint G = G (fixpoint G)) ∈ Th(∅) by two beta steps (both sides reduce to
G applied to the self-application). The constructors are
`binary_zero = \z.\e.\o. z`, `binary_even = \h.\z.\e.\o. e h`,
`binary_odd = \h.\z.\e.\o. o h`.

FOLD. `fold_binary = fixpoint F`, F = `\self.\z.\e.\o.\n. n z (\h. e (self z
e o h)) (\h. o (self z e o h))`. For all terms Z, E, O, h, unfolding the
fixpoint once and taking the constructor apart (beta steps only, the
arguments only substituted):

    fold_binary Z E O binary_zero    = Z                                  (F1)
    fold_binary Z E O (binary_even h) = E (fold_binary Z E O h)          (F2)
    fold_binary Z E O (binary_odd h)  = O (fold_binary Z E O h)          (F3)

COMPLEMENT. `complement_binary` is an equational define: its three rows

    complement_binary binary_zero      = binary_zero                      (C1)
    complement_binary (binary_even h)  = binary_odd (complement_binary h) (C2)
    complement_binary (binary_odd h)   = binary_even (complement_binary h) (C3)

are, for every term h, equations of Th(∅) between the compiled entry and the
row's right side: the compiler generates the entry as a knot of the rows,
and the rows do not overlap, so each row alone is a true equation; the chain of beta steps for one row is the one of
Lemma 1 of `doc/proofs/solo_fold_reflection.md` (branch solo-fold-laws), h
only substituted.

ASSERTION. `binary_tree = fixpoint T`, T = `\self.\n. n binary_zero (\h.
binary_even (self h)) (\h. binary_odd (self h))`, is the plain rebuild, so in
the same way

    binary_tree binary_zero     = binary_zero
    binary_tree (binary_even h) = binary_even (binary_tree h)
    binary_tree (binary_odd h)  = binary_odd (binary_tree h)

and by induction on a finite tree t, (binary_tree t = t) ∈ Th(∅) (R). For
`binary` (problem module `binary`), Theorem 4 of
`doc/proofs/solo_fold_reflection.md` gives (binary t = t) ∈ Th(∅) for every
finite tree t without `binary_even binary_zero`; its proof uses only beta
steps, so it is a chain of equations of Th(∅) (R').

## complement_contract

    complement_binary X  is a finite member of binary_tree,  for X a finite member.

By induction on X's tree t, (complement_binary t = c(t)) ∈ Th(∅), where c
is the tree swapping `binary_even` and `binary_odd`: (C1) at zero; at
`binary_even h`, (C2) and the induction hypothesis under `binary_odd` give
`binary_odd c(h)`; at `binary_odd h` the same with (C3). This is the
membership the contract states; as an equation it reads
`binary_tree (complement_binary X) = complement_binary X`, which follows from
the tree c(t) and (R).

## involution_binary

    complement_binary (complement_binary X) = X,   X a finite member of binary_tree.

By induction on t. At `binary_zero`, (C1) twice. At `binary_even h`:

    complement_binary (complement_binary (binary_even h))
      = complement_binary (binary_odd (complement_binary h))      (C2) under the context
      = binary_even (complement_binary (complement_binary h))     (C3), h := complement_binary h
      = binary_even h                                              induction hypothesis

and symmetrically at `binary_odd h` with (C3) then (C2). (C2) and (C3) hold
for every h, so the instance `complement_binary h` needs no premise.

## fusion_binary

    fold_binary Z E O (complement_binary X) = fold_binary Z O E X,
    Z, E, O any terms, X a finite member of binary_tree.

By induction on t. At `binary_zero`, both sides are Z by (C1) and (F1). At
`binary_even h`:

    fold_binary Z E O (complement_binary (binary_even h))
      = fold_binary Z E O (binary_odd (complement_binary h))      (C2)
      = O (fold_binary Z E O (complement_binary h))               (F3)
      = O (fold_binary Z O E h)                                    induction hypothesis
      = fold_binary Z O E (binary_even h)                          (F2), branches O, E

and symmetrically at `binary_odd h`. Z, E and O are only substituted, and
the rule B of Th substitutes any term of Λ⁺, so (E) holds for any terms
there, sets included.

## idempotence_binary

    binary (binary X) = binary X,   X a finite member of binary.

By (R'), binary t = t, so the inner `binary X` equals t and the outer
`binary (binary X)` equals binary t = t; both sides equal t.

## Length of the chains

Each case uses a constant number of row equations, each a bounded chain of
beta steps (at most 2m + k + 3 per constructor, `solo_fold_reflection.md`,
"Length of the chains"), so for a tree of n constructors every proof is a
chain of O(n) beta steps: the lemma states, at each instance, a finite
conversion.
