# The five false-only cycles of H29 and H30: `boolean(false)` is consistent

The claim proved is the scored `boolean(false)` of

    probe_cycle_and_false   x = x false false
    probe_cycle_if_false    x = x false x
    probe_cycle_and_or      x = (x true x) false false
    value_map_two_cycle     x = x (\p. \q. true) false
    value_map_three_cycle   x = x (\p. \q. \r. \s. true) false

(`corpora/contest_hard_clauses.pl`, H29 and H30): for the point's term M, the
test `\a. M y a` (`corpora/contest_hard_claims.pl`, template `boolean(false)`)
can consistently be the identity, that is, lambda beta eta plus
`(\a. M y a) = \x. x` is consistent.

The proof is one argument for all five points: a Church-Rosser reduction that
contains the equation `U = false`, U the knot the point's term reduces to. It
is written out in full, lemma by lemma, so that each step can be checked.

## Notation

Terms are lambda terms modulo alpha conversion. The encodings are the
prelude's (`corpora/prelude_clauses.pl`):

    I = \f. f          T = \t. \f. t  (true)          F = \t. \f. f  (false)
    Y = \g. (\p. g (p p)) (\q. g (q q))                (fixpoint)

For a closed term P, `K(P)` is `\z. P` with z a fresh variable (z is not free
in P, since P is closed). So `F = K(I)`, and the arguments of the value map
points are `\p. \q. T = K(K(T))` and `\p. \q. \r. \s. T = K(K(K(K(T))))`.

Each point's term is `M = Y G` with `G = \x. C[x]`, C[x] the right-hand side
above, so:

    and_false   C[x] = x F F
    if_false    C[x] = x F x
    and_or      C[x] = (x T x) F F
    two         C[x] = x K(K(T)) F
    three       C[x] = x K(K(K(K(T)))) F

Let `D = \p. C[p p]` and `U = D D`.

Facts about C, checked by hand for each point:

- (C1) C[x] is built from the variable x and the closed terms I, T, K(...) by
  application and K alone.
- (C2) `C[F]` beta-reduces to F. and_false and if_false: `F F F -> (\f. f) F
  -> F`. and_or: `F T F -> F` as before, then `F F F -> F`. two and three:
  `F A F -> (\f. f) F -> F` for any A.
- (C3) D is in beta normal form (the head of `C[p p]` is the variable p, and
  every other part is one of the closed normal terms of (C1)), and D is not an
  eta redex: the body `C[p p]` is an application whose last argument is F
  (and_false, and_or, two, three) or `p p` (if_false), never the variable p
  alone. No part of D is an eta redex either (the closed parts are I, T and
  `K(P)` with P closed, and the body of `K(P)` is closed, so it is not of the
  form `Q z`).
- (C4) `M ->> U` by beta: `Y G -> (\p. G (p p)) (\q. G (q q))`, and inside
  each abstraction `G (p p) -> C[p p]`, which gives `D D` up to alpha.
- (C5) The only beta redex of U is U itself (D is normal), and `U -> C[U]`.

## The family

The FAMILY is the smallest set of terms that contains U, I and T and is closed
under application (P, Q in the family gives `P Q`) and under K (P in the
family gives `K(P)`). Every member is closed. The U-free family is the same
construction without U. By (C1), `C[P]` is in the family for every P in the
family; in particular `C[U]` is.

**Lemma 1 (members are read one way; nodes).** Every member is exactly one of:
U, I, T, `P Q` with P and Q members, `K(P)` with P a member; and in the last
two cases P and Q are determined. Call the members met while taking a member
apart this way its NODES (U, I and T are not taken apart). Then:

- (a) an occurrence of a member inside a member P is a node of P, or lies
  inside a node U, where it is a closed part of C or a subterm of one: one of
  I, T, `K(...)` built from them, all U-free and in normal form;
- (b) replacing a node of P by any member gives a member.

*Proof.* U is an application whose parts are D and D, and D is not a member:
it is not I, not T, not an application, and not `K(P)`, since p is free in its
body. I and T are not of the form `K(P)`: their bodies `f` and `\f. t` have
the bound variable free. So the cases are exclusive and the parts determined.
(a) By induction on P: an occurrence is P itself or lies inside a part. The
proper subterms of I and T are open. The proper subterms of U are D and the
subterms of D; those that are closed are the closed parts of C (C1) and their
subterms. (b) By induction on P. ∎

The occurrences of the second kind in (a) are U-free normal members, so tau
below leaves each unchanged, and a rho step (below) at one of them changes
nothing. Where a proof below speaks of the occurrence a rho step acts on, a
step of this kind is the trivial case `M2 = M`.

**Lemma 2 (closed under beta).** If P is a member and `P -> P'` by beta, P' is
a member, obtained from P by replacing one node by a member.

*Proof.* A beta redex is an application whose operator is an abstraction. The
applications in a member are its application nodes and the applications inside
the atom U (U itself, and those inside D, which is normal by (C3)). So the
redex is U, contracted to `C[U]`, a member (C5, C1); or an application node
`A R` with A an abstraction node, A one of I, T, `K(Q)`: `I R -> R`,
`T R -> \f. R = K(R)` (R is closed, so f is not free in it), `K(Q) R -> Q`. In
each case the contractum is a member and replaces the node, so Lemma 1(b)
applies. ∎

**Lemma 3 (the U-free family normalizes).** Every U-free member is strongly
beta normalizing, and its normal form is a U-free member.

*Proof.* Size: `|I| = |T| = 1`, `|P Q| = |P| + |Q| + 1`, `|K(P)| = |P| + 1`.
By Lemma 2 (with no U) every beta step replaces a node `I R` by R, `T R` by
`K(R)`, or `K(Q) R` by Q, and each of these is smaller; size is compositional
over nodes, so every step decreases the size. The normal form is a member by
Lemma 2. ∎

For a member P let `P°` be P with every occurrence of U replaced by F (by Lemma
1(a) these are nodes, and they do not overlap), a U-free member, and let
`tau(P)` be the beta normal form of `P°` (Lemma 3; unique by Church-Rosser).

**Lemma 4 (tau is invariant).** For every member P:

- (a) if `P -> P'` by beta, then `tau(P') = tau(P)`;
- (b) if P' is P with a node Q replaced by `tau(Q)`, then `tau(P') = tau(P)`;
- (c) `tau(P)` is a U-free member in normal form, and `tau(tau(P)) = tau(P)`;
- (d) `tau(U) = F`.

*Proof.* (a) If the redex is a node U, `P'°` is `P°` with one node F replaced
by `C[F]` (C contains no U), and `C[F] ->> F` (C2), so `P'° ->> P°`: the same
normal form. Otherwise the redex is a node `I R`, `T R` or `K(Q) R`; the
corresponding node of `P°` is `I R°`, `T R°`, `K(Q°) R°`, and contracting it
gives `P'°`, so `P° -> P'°`. (b) `P'°` is `P°` with the node `Q°` replaced by
its normal form `tau(Q)`, so `P° ->> P'°`. (c) Lemma 3, and a U-free normal
term is its own `°` and its own normal form. (d) `U° = F`, which is normal. ∎

## The reduction rho

`M ->rho N` when N is M with one occurrence of a family member P replaced by
`tau(P)`. Every rho step is an equation of lambda beta plus `U = F`: P equals
`P°` by `U = F` at each node U, and `P°` equals `tau(P)` by beta. And
`U ->rho F` by Lemma 4(d).

**Lemma 5 (rho is Church-Rosser).** If `M ->rho M1` and `M ->rho M2`, there is
M3 with `M1 ->rho= M3` and `M2 ->rho= M3` (`->=` is at most one step); hence
rho is Church-Rosser.

*Proof.* Let the steps act at occurrences of P1 and P2. Disjoint occurrences:
take M3 with both replacements. The same occurrence: `M1 = M2`. Nested, P2
inside P1: if the step at P2 is trivial, `M2 = M` and M3 = M1; otherwise, by
Lemma 1(a), P2 is a node of P1, so in M2 the occurrence holds `P1'` = P1 with P2
replaced by `tau(P2)`, a member (Lemma 1(b)) with `tau(P1') = tau(P1)` (Lemma
4(b)). So `M2 ->rho M1` by replacing `P1'`, and M3 = M1. A relation with this
one-step diamond (up to reflexivity) is Church-Rosser. ∎

**Lemma 6 (beta and rho commute).** If `M ->beta M1` and `M ->rho M2`, there
is M3 with `M1 ->>rho M3` and `M2 ->beta= M3`.

*Proof.* Let the rho step replace an occurrence of the member P, and the beta
step contract the redex `R = (\x. B) S`.

1. R lies inside P (R = P included). By Lemma 2 and Lemma 4(a) the occurrence
   in M1 holds a member `P'` with `tau(P') = tau(P)`, so `M1 ->rho M2`:
   M3 = M2.
2. R and P are disjoint: M3 has both changes; one step each way.
3. P lies strictly inside R.
   - Inside S: M1 holds n >= 0 copies of P (P is closed, so the substitution
     neither changes it nor captures anything). `M1 ->>rho M3` by n steps, M3
     with every copy replaced, and `M2 -> M3` by the same beta step on the
     redex whose argument now holds `tau(P)`.
   - Inside B: P is closed, so `B[x := S]` holds P at the corresponding place;
     one step each way.
   - P is the operator `\x. B`: P is an abstraction member, I, T or `K(Q)`. For
     I and T, `tau(P) = P` and `M2 = M`: M3 = M1. For `K(Q)`,
     `tau(K(Q)) = K(tau(Q))` (the normal form of `\z. Q°` is `\z.` the normal
     form of `Q°`), so `M2` holds `K(tau(Q)) S -> tau(Q)`, and M1 holds Q
     (z is not free in Q): `M1 ->rho M3` by replacing Q, and `M2 ->beta M3`.

These are all the positions of P relative to R. ∎

**Lemma 7 (eta and rho commute).** If `M ->eta M1` and `M ->rho M2`, there is
M3 with `M1 ->rho= M3` and `M2 ->eta M3`.

*Proof.* No member contains an eta redex: I, T are not eta redexes (their
bodies are not applications), U contains none (C3), `K(P)` is not one (its
body is closed, so not `Q z` with z bound), and applications and K of terms
without eta redexes add none. So the eta redex `\z. Q z` (z not free in Q) is
disjoint from P or contains it; it cannot be P, and P cannot be `Q z` (P is
closed). If P lies inside Q, M1 holds P unchanged: one step each way. ∎

**Lemma 8 (commutation, Hindley and Rosen).** If relations R1 and R2 satisfy:
`M ->R1 N1` and `M ->R2 N2` imply `N1 ->>R2 N3` and `N2 ->R1= N3` for some N3,
then `->>R1` and `->>R2` commute.

*Proof.* First, by induction on the length of `M ->>R2 N2`, a single R1 step
against a sequence of R2 steps: the first tile gives `N1 ->>R2 X` and
`M' ->R1= X` for the first R2 step `M ->R2 M'`; if `M' = X`, then
`N1 ->>R2 M' ->>R2 N2`; otherwise continue from `M' ->R1 X` against the rest.
Then by induction on the number of R1 steps. (Barendregt 1984, section 3.3.) ∎

**Theorem.** Lambda beta eta plus `M = F` is consistent, for M the term of any
of the five points. Hence lambda beta eta plus `(\a. M y a) = \x. x` is
consistent.

*Proof.* Beta and eta are Church-Rosser, and their reductions commute
(Barendregt 1984, section 3.3). Rho is Church-Rosser (Lemma 5). By Lemmas 6, 7
and 8, `->>rho` commutes with `->>beta` and with `->>eta`, hence with
`->>(beta eta)`, whose sequences are made of beta and eta steps (tile one
relation at a time). By Hindley and Rosen, the union beta eta rho is
Church-Rosser.

Its convertibility is a congruence that contains beta, eta and `U = F`
(`U ->rho F`), so it contains every equation of lambda beta eta plus `U = F`.
If that theory proved `x = y` for distinct variables x and y, then x and y
would have a common reduct; but a variable has no beta redex, no eta redex,
and no rho redex (members are closed), so it reduces only to itself, and
`x = y` is impossible. So lambda beta eta plus `U = F` is consistent. Since
`M ->> U` (C4), it proves `M = F`, and then
`\a. M y a = \a. F y a = \a. a`. The theory lambda beta eta plus
`(\a. M y a) = \x. x` is contained in it, hence consistent. ∎

## What the proof does not use

It uses no model and no property of the reading any setting makes; only the
syntax of the five points, (C1) to (C5). The same argument proves any claim
`M = V` for a knot `U = D D`, `D = \p. C[p p]` normal and eta-redex-free,
whose context C is built by application and K from closed normal terms that
generate, with U, a family closed under beta (Lemma 2) whose U-free part
normalizes (Lemma 3), whenever `C[V] ->> V`.
