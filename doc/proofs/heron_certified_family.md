# The family theorem that `certified_first` applies

This document states the one theorem the claims layer `certified_first(Inner)`
applies, and proves it. It is the family argument of
`gezi/doc/proofs/kestrel_false_only_family.md` (its
Lemmas 1 to 8), stated for a general context C and for either boolean value V.
Every lemma below is that document's; the only change is that the replacement of the
knot U, written `F` there, is the value V here, and the one fact the argument
uses about V, `C[F] ->> F` there, is `C[V] ->> V` here. Where a lemma needs a
word changed, the change is shown.

## Statement

Notation as in that document: terms modulo alpha; `I = \f. f`,
`T = \t. \f. t`, `F = \t. \f. f`; `K(P) = \z. P` for a closed P, z fresh;
`Y = \g. (\p. g (p p)) (\q. g (q q))`, the prelude's fixpoint.

**The family.** For a closed term U, the FAMILY of U is the smallest set that
contains U, I and T and is closed under application and under K. Its U-FREE
part is the same construction without U. F = K(I) and every `K(...)` built
from I and T are U-free members.

**Theorem.** Let `G = \x. C[x]` be closed, `D = \p. C[p p]`, `U = D D` and
`M = Y G`. Suppose

- (F1) C[x] is built by application from the variable x and closed U-free
  members (so `C[P]` is a member for every member P);
- (F2) D is in beta normal form and contains no eta redex;
- (F3) V is T or F, and `C[V]` beta-normalises to V.

Then lambda beta eta + `M = V` is consistent.

**Corollary (the claims).** Under (F1) to (F3), with y a variable:

- if V = F, lambda beta eta + (`\a. M y a` = `\x. x`) is consistent;
- if V = T, lambda beta eta + (`\a. M a y` = `\x. x`) is consistent.

*Proof of the corollary.* The theory lambda beta eta + `M = V` proves
`\a. M y a = \a. F y a = \a. a` in the first case and
`\a. M a y = \a. T a y = \a. a` in the second; the claim's theory is contained
in it, which is consistent by the theorem. ∎

## Proof of the theorem

The facts that document checks by hand for its five points are here the
hypotheses or follow from them:

- its (C1) is (F1);
- its (C2), `C[F] ->> F`, is replaced by (F3), `C[V] ->> V`;
- its (C3), D normal and eta-redex-free, is (F2);
- its (C4), `M ->> U`, holds for every G: `Y G -> (\p. G (p p)) (\q.
  G (q q))`, and inside each abstraction `G (p p) -> C[p p]`, which gives
  `D D` up to alpha;
- its (C5), U's only redex is U and `U -> C[U]`, follows from (F2):
  D is normal, so the only redex of `D D` is itself, and contracting it gives
  `C[D D]`.

With these, its Lemmas go through as follows.

- **Lemma 1** (members are read one way; nodes): unchanged. It uses that D is
  not a member (p is free in its body) and that I, T are not of the form
  `K(P)`. Part (a)'s occurrences inside a node U are closed parts of C, which
  are U-free members by (F1).
- **Lemma 2** (closed under beta): unchanged. A redex in a member is U (whose
  contractum `C[U]` is a member by (F1)) or an application node whose
  operator is I, T or `K(Q)`, contracted to R, `K(R)` or Q.
- **Lemma 3** (the U-free family normalises): unchanged; it does not mention U
  or V.
- For a member P, `P°` is P with every occurrence of U replaced by **V** (in
  that document, by F), a U-free member since V is one; `tau(P)` is the beta
  normal form of `P°` (Lemma 3).
- **Lemma 4** (tau is invariant): (a) if the redex is a node U, `P'°` is `P°`
  with one node V replaced by `C[V]`, and `C[V] ->> V` by (F3), so
  `P'° ->> P°`; the other cases are unchanged. (b) and (c) are unchanged.
  (d) `tau(U) = V`, since `U° = V` and V is normal.
- **The reduction rho**: `M ->rho N` replaces one occurrence of a member P by
  `tau(P)`; every step is an equation of lambda beta plus `U = V`; and
  `U ->rho V` by Lemma 4(d).
- **Lemma 5** (rho is Church-Rosser): unchanged.
- **Lemma 6** (beta and rho commute): unchanged. Its last case, P the
  operator of the redex, uses that the abstraction members are I, T and
  `K(Q)`, with `tau(I) = I`, `tau(T) = T` (U-free and normal) and
  `tau(K(Q)) = K(tau(Q))`; none of this depends on V.
- **Lemma 7** (eta and rho commute): unchanged; members have no eta redex by
  (F2) for U and by the shapes of I, T and `K(P)`.
- **Lemma 8** (commutation): unchanged.

The theorem's final step is that document's with `F` read as V: beta, eta and rho
are Church-Rosser and commute, so their union is Church-Rosser; its
convertibility contains lambda beta eta + `U = V`; two distinct variables are
irreducible in it (a variable has no beta, eta or rho redex, since members
are closed), so they are not equated, and the theory is consistent. Since
`M ->> U`, it proves `M = V`. ∎

## What `certified_first` checks, and why that is the theorem's hypotheses

For a claim `is_identity(Term)`, Term the test's single open surface term,
the layer succeeds only when all of the following are checked mechanically
on Term converted to de Bruijn form; any failure of a check sends the claim
to Inner. The V = F case is `prolog/gezi/certified_first.pl`, since
deleted; the V = T case is not in that code.

1. Term is `\a. (M y) a` (then V = F) or `\a. (M a) y` (then V = T), with y
   Term's one free variable, and M closed.
2. M is `Y G` with Y the prelude's fixpoint exactly (up to alpha) and G an
   abstraction `\x. C[x]`.
3. (F1): C, read as a term in x, is built by application from x and closed
   subterms each recognised as a U-free member: I, T, `\z. P` with P closed
   and a recognised member, or an application of recognised members.
4. (F2): `C[p p]` has no beta redex and `\p. C[p p]` has no eta redex (checked
   on the term).
5. (F3): `C[V]` is beta-normalised by leftmost-outermost reduction within a
   step bound (the U-free family is strongly normalising, Lemma 3; past the
   bound the layer declines) and its normal form is V up to alpha.

Each check is exactly one hypothesis of the theorem (1 fixes V and the
template of the corollary; 2 fixes M = Y G; 3, 4, 5 are F1, F2, F3), so a
success of the layer is an instance of the corollary.
