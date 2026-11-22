# Three addenda to the family proof

A and B extend what the claims layer
`knot_consistent(Steps, Inner)` (`prolog/gezi/knot_consistency.pl`) may
replace; C carries the theorems to the judging theory lambda beta eta with
merges. Until an addendum is reviewed, the layer does not rely on it.
Notation and lemma numbers are those of `kestrel_false_only_family.md`,
"the proof" below.

## A. Any U-free family normal form in place of F

**Claim A.** Let U = D D, with D = \p. C[p p] satisfying (C1), (C3) and (C5)
of the proof. Let V be a U-free family member in beta normal form with
`C[V] ->> V`. Then lambda beta eta plus `U = V` is consistent.

The proof uses F in three places only. We check each with V in F's place.

1. The definition of `P°`: every occurrence of U replaced by F. Replace it
   by V. `P°` is still a U-free member, because V is one. Lemma 3 (the
   U-free family normalizes) does not mention F, so `tau(P)`, the normal
   form of `P°`, still exists and is unique.
2. Lemma 4(a), the case of a node U contracted to `C[U]`. `P'°` is `P°`
   with one node V replaced by `C[V]`. The hypothesis `C[V] ->> V` gives
   `P'° ->> P°`, as `C[F] ->> F` did.
3. Lemma 4(d), `tau(U) = V`. `U° = V`, and V is in normal form.

Lemmas 1, 2 and 5 to 8 do not mention F. Lemma 7 needs every member to be
free of eta redexes, and V is a member. The theorem's last step is now
`U ->rho V` by 4(d). So beta eta rho is Church-Rosser and contains
`U = V`, and it equates no two variables. ∎

The layer would try V among `I`, `true` and `false`, all members in normal
form, and apply one only after checking `C[V] ->> V`. On H29's and H30's
knots, `C[true]` never reduces to `true`: those points' boolean(true) traps
are the reason (their proofs, `corpora/contest_hard_claims.pl`, class
false_only). So the addendum proves nothing new on them. It matters for
knots whose context gives back `true` or `I`.

## B. A redex that reproduces itself is easy

**Claim B.** Let M be a closed beta redex whose only one-step beta reduct
is M itself (up to alpha), and which contains no other redex. For example,
Omega = (\x. x x)(\x. x x). Then for every closed term N, lambda beta plus
`M = N` is consistent.

This is Jacopini's argument for Omega (Barendregt 1984, §15.3). We write it
out in the form of the proof, since the layer applies it mechanically.

**Which terms these are.** The hypothesis holds exactly for the alpha
variants of Omega. Let `M = (\x. B) A`, closed, with B and A beta normal
and `B[x := A]` alpha equal to M.

- B is not an abstraction, since then `B[x := A]` would be one, and M is
  an application.
- So `B = P Q`, and `B[x := A] = P[x := A] Q[x := A]`, with
  `P[x := A] = \x. B` and `Q[x := A] = A`.
- P is beta normal and is the operator of the normal term B, so P is not
  an abstraction. `P[x := A]` is an abstraction, so P is a variable, and
  since M is closed, `P = x`. Then `A = \x. B`.
- Q is normal and `Q[x := A] = A`. If x did not occur in Q, Q would be
  `A = \x. x Q`, a term that contains itself as a proper subterm, which is
  impossible. So x occurs in Q, say n >= 1 times. Counting nodes,
  `|Q[x := A]| = |Q| + n (|A| - 1) = |A|`. That forces n = 1 and
  `|Q| = 1`, so `Q = x`.

Hence `B = x x`, `A = \x. x x`, and M is Omega. The module checks the
hypothesis literally (`self_reproducing/1`): M is closed, both parts are
beta normal, and contracting M gives M back. By the argument above, this
accepts Omega's alpha variants and nothing else. Claim B is therefore
Jacopini's theorem that Omega is easy, written out in the proof's form so
that the layer applies a checked argument.

*Occurrences.* Two occurrences of M in a term are equal or disjoint. If
they overlapped, one would lie strictly inside the other, and M would be a
proper subterm of M, which has fewer nodes than M. M is closed, so
substitution neither changes an occurrence nor makes a new one out of a
variable. New occurrences appear only inside a copy of N, or as a copy of
an existing occurrence.

*The reduction rho.* `X ->rho Y` when Y is X with one occurrence of M
replaced by N. The parallel step `X =>rho Y` replaces any set of
occurrences at once. The occurrences in X are pairwise disjoint, so any
set of them can be replaced together.

**Lemma B1 (rho is Church-Rosser).** If `X =>rho X1` replaces the set S1
and `X =>rho X2` replaces the set S2, let X3 be X with every occurrence
in S1 ∪ S2 replaced. The occurrences of S2 not in S1 are still occurrences
of M in X1, at the same places, and likewise for S1 in X2. So
`X1 =>rho X3` and `X2 =>rho X3`. The parallel step has the diamond
property, so `->>rho`, its transitive closure, is Church-Rosser.

**Lemma B2 (beta and rho commute).** If `X ->beta X1` and `X ->rho X2`,
there is X3 with `X1 ->>rho X3` (several single rho steps, or one parallel
step) and `X2 ->beta= X3`. This is exactly the condition of Lemma 8 of
the proof, with R1 = beta and R2 = rho, so `->>beta` and `->>rho`
commute.

*Proof.* Let O be the occurrence of M replaced, and R the redex contracted.

- R inside O. M's only redex is M itself, and its contractum is M, so
  `X1 = X`. Take `X3 = X2`: one rho step from X1, none from X2.
- R and O disjoint. The occurrence O survives in X1 and the redex R
  survives in X2. One step each way.
- O inside R's argument S. X1 holds n >= 0 copies of M, one for each
  occurrence of the bound variable in the body. Take X3 as X1 with all n
  copies replaced, one parallel rho step. `X2 ->beta X3` contracts the
  same redex, whose argument now holds N.
- O inside R's body. M is closed, so the contractum holds M at the
  corresponding place. One step each way.
- O as R's operator is impossible: R's operator is an abstraction, and M
  is an application. ∎

**Proof of Claim B.** Beta is Church-Rosser, and so is rho (Lemma B1).
They commute (Lemma B2 and Lemma 8), so beta rho is Church-Rosser (Hindley
and Rosen). Its convertibility contains beta and `M = N`. A variable has
no beta redex and no occurrence of M (M is closed), so two distinct
variables are not convertible. ∎

**How the layer would use it.** When the head of the spine is such an M,
applied to arguments `A1 ... Ak`, the layer picks a closed N that makes the
run go on to the witness. For example, the projection `\x1. ... \xk. xi`,
when the argument Ai reduces to the witness. It replaces M by N and
continues. The success is sound because every step of the run is an
equation of lambda beta plus `M = N`, which Claim B makes consistent, and
xi closes the test as in the proof.

One claim uses one theorem instance: either the knot of Claim A (or the
proof) or the M of Claim B, never both. A knot U with `U -> C[U]` and
`C[U]` different from U does not satisfy Claim B's hypothesis. So a term
whose reduction grows is never treated as easy.

## C. The family theorems over lambda beta eta with merges

Under this judgment a claim is judged by the normal form solution set: the
theory is Th(E) over Λ⁺, the terms with merges, under lambda beta eta, and
the claim of a test is that the curried identity N is in S(P) for the
program P the test is curried into (`contest_hard_claims:claim_program/4`).
The proof and addendum A are stated over pure terms. This addendum carries
them to Λ⁺ and states what a success of the layer then proves
(2026-09-29).

**Claim C.** Let U and V be as in the proof or in addendum A. Then Th(E)
over Λ⁺, E = {U = V}, is consistent.

A merge {M1, …, Mn} is a constructor: no rule of β, η or ρ has a merge at
the root of its redex, and every rule is closed under merge contexts. The
proof's lemmas are checked with that in mind.

1. Lemmas 1 to 4 speak only of family members, which are closed pure terms
   (U, I, T, application and K). They are unchanged.
2. Lemma 5 (ρ is Church-Rosser). Two occurrences of members in a term of
   Λ⁺ are disjoint, the same, or nested, as in any term. In the nested case
   both lie inside the outer member, which is pure. The proof is unchanged.
3. Lemma 6 (β and ρ commute). The redex R = (λx. B) S is a term of Λ⁺: B
   and S may hold merges. The positions of the member P relative to R are
   the proof's cases: R inside P (then R is pure), disjoint, P inside S
   (substitution copies S, merges included, and P is closed, so each copy
   holds P unchanged), P inside B, and P the operator. A merge adds no
   position, since it is never part of the redex's own shape.
4. Lemma 7 (η and ρ commute). The η redex λz. Q z may have a merge as Q.
   P holds no η redex, and P is not Q z (P is closed), so the cases are the
   proof's: disjoint, or P inside Q, unchanged by the step.
5. Lemma 8 is about abstract relations.
6. β ∪ η is Church-Rosser on Λ⁺, with merges as constructors: it is weakly
   orthogonal (van Oostrom and van Raamsdonk, LFCS 1994), the fact
   `omega_easy_beta_eta.md` uses (item 7 of the label-free design).

So β ∪ η ∪ ρ is Church-Rosser on Λ⁺ (Hindley and Rosen, as in the proof's
theorem). Its convertibility is closed under every context of Λ⁺, merge
contexts included, and contains β, η and U = V (U →ρ V), so it contains
Th(E): Th(E) is the least set closed under the rules of the formal
definition, and the convertibility is closed under each of them. A variable
has no β, η or ρ redex (members are closed), so two distinct variables x
and y are not convertible, and x = y ∉ Th(E). If
λx. λy. x = λx. λy. y were in Th(E), then by ν and β so would be x = y.
Hence Th(E) is consistent in the sense of the formal definition. ∎

**Omega.** For E = {Ω = M}, M closed, Th(E) over Λ⁺ is consistent by
`omega_easy_beta_eta.md`, which is stated for λβη with merges. It
supersedes addendum B, which is stated for λβ, for the layer's use under
this judgment. The layer's M are the projections λx1. … λxk. xi, closed.

**What a success proves.** The layer translates the test by its own
de Bruijn translation, which reads variables, `^` and `@` only; a test
with a merge (a list) or an embedded inheritance-calculus program fails
the translation, and the claim goes to Inner. So a test the layer proves
is merge-free, and so is its program P = λy1. … λyk. Test. Every step of
the run is a β step or an instance of E, so Th(E) proves
Body[Argument := a] = a, with the free variables y1, …, yk as variables
(the constants stand for them, and no step inspects a constant). By ξ,
Th(E) proves Test = λa. a, and by ξ k more times P = λy1. … λyk. λa. a,
that is P = N. P is merge-free and P = P, so P ∈ Yield(P) (the first clause
of Yield). Th({P = N}) ⊆ Th(E), which is consistent (Claim C, or Omega's
theorem), so N ∈ S(P): the claim holds under this judgment.
