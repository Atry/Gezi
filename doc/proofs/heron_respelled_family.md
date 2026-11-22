# Respelled knots: `boolean(false)` of the respelled cycles is consistent

The claim proved is the scored `boolean(false)` of the three points of
`corpora/contest_respelled_cycles.pl`:

    respelled_and_false_self       C[x] = x F F      A[i] = i i
    respelled_and_false_identity   C[x] = x F F      A[i] = (\z. z) i
    respelled_if_false_self        C[x1, x2] = x1 F x2   A[i] = i i

each M = W W I with W = \p. \i. C[p p A[i], ..., p p A[i]] (every hole filled by
`p p A[i]`): for the test `\a. M y a` (template `boolean(false)`), lambda beta eta plus
`(\a. M y a) = \x. x` is consistent.

The argument is that of `doc/proofs/kestrel_false_only_family.md`, THE FAMILY PROOF: a
Church-Rosser reduction rho that contains the equation "knot = F", commuting with
beta and eta. The one change is the knot. In the family proof's points the knot is one term,
`U = D D`, whose only redex is itself (its (C5)). Here M's weak head reduction never
repeats a term: every lap passes a new spelling of I. So the single knot is widened to a
KNOT FAMILY that is closed under every reduction inside it, and rho replaces any knot by F.
Every lemma below is the family proof's lemma of the same
number, restated for the knot family.

## Notation

Terms are lambda terms modulo alpha conversion.

    I = \f. f      T = \t. \f. t      F = \t. \f. f

For a closed term P, `K(P)` is `\z. P`, z fresh. A context `C[x1, ..., xk]` (k >= 1) has
holes x1, ..., xk, each occurring once; `C[E1, ..., Ek]` fills hole j with Ej.

## The theorem

Let C, A and Q0 satisfy:

- (R1) `C[x1, ..., xk]` is built by application from its holes and from closed terms
  each built from I, T and K(...) by application and K; C is not a bare hole; and
  `C[x1, ..., xk]`, read with the holes as variables, is in beta normal form.
- (R2) `A[i]` is an application tree over the leaves i and I (a term built from i and I
  by application alone) with at least one leaf i.
- (R3) Q0 is an I-TREE: a term built from I by application alone.
- (R4) `C[F, ..., F] ->>beta F`.

Let `W = \p. \i. C[p p A[i], ..., p p A[i]]` and `M = W W Q0`. Then lambda beta eta plus
`M = F` is consistent.

**Corollary.** Under (R1) to (R4), for a variable y, lambda beta eta plus
`(\a. M y a) = \x. x` is consistent.

*Proof of the corollary.* The theory lambda beta eta plus `M = F` proves
`\a. M y a = \a. F y a = \a. a`; the claim's theory is contained in it, which is
consistent by the theorem. ∎

The three points are instances with Q0 = I: (R1) `x F F` and `x1 F x2` are normal and
not bare holes, their closed parts are F = K(I); (R2) `i i` and `(\z. z) i = I i` are
trees over {i, I} with a leaf i; (R4) `F F F -> (\f. f) F -> F` in both.

## The sets

**Arguments.** The I-TREES are the terms built from I by application. The OPEN TREES are
the application trees over {i, I} with at least one leaf i.

**Fact A.** (a) Every I-tree is closed and normalizes to I; an I-tree's beta reducts are
I-trees (its only redexes are `I R -> R`, R an I-tree). (b) An open tree's beta reducts
are open trees: its only redexes are `I R -> R`, which removes a leaf I and keeps every
leaf i. (c) If B is an open tree and Q an I-tree, `B[i := Q]` is an I-tree; if B' is an
open tree over i' and B an open tree over i, `B'[i' := B]` is an open tree over i.
(d) Replacing a closed subtree of an open tree (an I-tree) by I gives an open tree.

**W-variants.** A W-VARIANT is `\p. \i. C[p p B1, ..., p p Bk]` with B1, ..., Bk open
trees. W is one (every Bj is A[i]).

**Heads and C-terms.** HEADS and OPEN C-TERMS are the least sets such that

- `W1 W2` is a head for W-variants W1, W2;
- `\i. E` is a head for an open C-term E of the form `C[E1, ..., Ek]`;
- `H B` is an open C-term for a head H and an open tree B (an OPEN KNOT);
- `C[E1, ..., Ek]` is an open C-term for open C-terms E1, ..., Ek.

A KNOT is `H Q` with H a head and Q an I-tree. A CLOSED C-TERM is built from knots by
C: a knot is one, and `C[E1, ..., Ek]` is one for closed C-terms Ej.

**Fact B.** (a) Heads, knots and closed C-terms are closed. (b) The body of a head
`\i. E` has a free i (every open tree has a leaf i). (c) No head, W-variant, knot or
C-term is an abstraction of the form I, T or K(P), and a knot and a C-term are not
abstractions at all: a knot is an application, and `C[...]` is an application because C
is built by application and is not a bare hole (R1).

**Fact C (knots are closed under beta).** (a) A reduct of a head is a head. (b) A reduct
of a knot H Q is a knot, or, when the redex is the knot itself, a closed C-term.
(c) A reduct of an open (closed) C-term is an open (closed) C-term.

*Proof.* By induction on the term, the redex being at the root or inside.

- `W1 W2`: at the root, `(\p. \i. C[p p B1, ...]) W2 -> \i. C[W2 W2 B1, ...]`, a head whose
  body is C over the open knots `(W2 W2) Bj`. Inside a W-variant
  `\p. \i. C[p p B1, ..., p p Bk]` every redex is inside some Bj: C's closed parts are
  normal and C creates no redex, being normal as a context (R1); a hole's content
  `(p p) Bj` has the operator `p p`, no abstraction, and `p p` is no redex, p being a
  variable. A step inside Bj gives an application tree over {i, I} that still has a leaf
  i (Fact A(b): the step contracts `I R` to R, removing a leaf I and no leaf i). So the
  reduct is a W-variant, and `W1 W2`'s reduct is again `W1' W2` or `W1 W2'`, a head.
- `\i. C[E1, ..., Ek]`: C creates no redex: it is normal as a context (R1), so no closed
  part of C is applied to anything that would make a redex, and a hole's content Ej is
  applied only where C applies a hole, and Ej is no abstraction (Fact B(c)). So the redex
  is inside an Ej, and (c) applies: the body stays `C[E1', ..., Ek']`, and every open tree
  in it stays an open tree with a leaf i (Fact A(b), (c)).
- An open knot `H B`: inside H, (a); inside B, Fact A(b); at the root only when H is
  `\i'. E'`, and then `E'[i' := B]` replaces each open tree B' of E' by `B'[i' := B]`, an
  open tree over i (Fact A(c)), heads being closed: an open C-term.
- A knot `H Q`: inside H or Q as for an open knot (Fact A(a)); at the root only when H is
  `\i. E`, and then `E[i := Q]` is a closed C-term (Fact A(c)).
- `C[E1, ..., Ek]`: as for a head's body. ∎

## The family

The FAMILY is the least set of terms that contains every knot, I and T, and is closed
under application and under K. Every member is closed. The KNOT-FREE family is the same
construction without knots. Every closed C-term is a member (its closed parts are
knot-free members, (R1)).

**Lemma 1 (members are read one way; nodes).** Every member is exactly one of: a knot, I,
T, `P Q` with P and Q members, `K(P)` with P a member; the parts are determined. Its
NODES are the members met while taking it apart (knots, I and T are not taken apart).

- (a) An occurrence of a member inside a member P is a node of P, or lies inside a knot
  of P, where it is an I-tree (inside the knot's argument, or a closed subtree of an open
  tree of its head) or a closed part of C (inside its head) or a subterm of one.
- (b) Replacing a node of P by any member gives a member.
- (c) Replacing, inside a knot, an occurrence of a member R by `tau(R)` (defined below)
  gives a knot.

*Proof.* A knot is an application whose operator is a head; a head is not a member (it
is not I, T or K(...) by Fact B(c), and not an application of members: `W1 W2`'s parts
are W-variants, which are not members, their bodies having p free). So the cases are
exclusive. (a) By induction on P. Inside a knot the closed subterms are: the argument's
subtrees (I-trees), the closed subtrees of the open trees (I-trees), the closed parts of
C and their subterms, and heads and W-variants, which are not members. (b) By induction
on P. (c) tau of an I-tree is I (Fact A(a)); tau of a closed part of C is itself (knot
free and normal). Replacing an I-tree argument by I gives an I-tree, replacing a closed
subtree of an open tree by I gives an open tree (Fact A(d)); so the heads stay heads and
the knot stays a knot. ∎

**Lemma 2 (closed under beta).** If P is a member and `P -> P'` by beta, P' is a member.

*Proof.* A redex of P is one of:

- inside a knot of P, the knot itself included: P' has a knot or a closed C-term there
  (Fact C(b)), a member (Lemma 1(b));
- inside a closed C-term but not inside its knots: impossible, C creating no redex (R1)
  and a knot being no abstraction;
- a node `I R`, `T R` or `K(Q) R` of P, contracted to R, `K(R)` or Q (the family proof's Lemma 2).

A KNOT IS NEVER THE OPERATOR OF A REDEX: a knot `H Q` is an application, and an
application is no abstraction, so `(H Q) R` is not a redex. And a knot's own root is a
redex exactly when its head is an abstraction `\i. E`, the redex being the knot `H Q`
itself: when the head is `W1 W2`, the root `(W1 W2) Q` has the operator `W1 W2`, an
application, and is no redex (its redex `W1 W2` lies inside the head). ∎

**Lemma 3 (the knot-free family normalizes).** The family proof's Lemma 3, unchanged.

For a member P let `P°` be P with every knot replaced by F (the knots of P are nodes and
do not overlap: no knot contains a knot, since heads and I-trees contain none), a
knot-free member, and let `tau(P)` be the beta normal form of `P°`.

**Lemma 4 (tau is invariant).** For every member P:

- (a) if `P -> P'` by beta, then `tau(P') = tau(P)`;
- (b) if P' is P with a node Q replaced by `tau(Q)`, then `tau(P') = tau(P)`;
- (c) `tau(P)` is a knot-free member in normal form, and `tau(tau(P)) = tau(P)`;
- (d) `tau(H Q) = F` for every knot H Q.

*Proof.* (a) If the redex is inside a knot and not the knot itself, P' has a knot at the
same place (Fact C(b)) and `P'° = P°`. If the redex is a knot, `P'°` is `P°` with one
node F replaced by `G°`, G the closed C-term the knot reduces to; `G° ->> F` by
induction on G: a knot gives F, and `C[G1°, ..., Gk°] ->> C[F, ..., F] ->> F` by (R4).
So `P'° ->> P°`, and both have the same normal form. Otherwise the redex is a node
`I R`, `T R` or `K(Q) R`, and `P° -> P'°` as in the family proof's Lemma 4(a). (b), (c) as in
the family proof's. (d) `(H Q)° = F`, which is normal. ∎

## The reduction rho

`N ->rho N'` when N' is N with one occurrence of a member P replaced by `tau(P)`. Every
rho step is an equation of lambda beta plus "every knot = F". Since M is the knot
`(W W) Q0` (W is a W-variant, (R2); Q0 an I-tree, (R3)), `M ->rho F` by Lemma 4(d).

**Lemma 5 (rho is Church-Rosser).** The family proof's Lemma 5. In the nested case, P2 inside P1,
P2 is a node of P1 or lies inside a knot of P1 (Lemma 1(a)); in the second case the
occurrence in M2 holds P1' = P1 with a member inside a knot replaced by its tau, a member
(Lemma 1(c)) with `P1'° = P1°`, so `tau(P1') = tau(P1)`, and `M2 ->rho M1`. ∎

**Lemma 6 (beta and rho commute).** The family proof's Lemma 6, case by case:

1. R lies inside P (R = P included): Lemma 2 and Lemma 4(a).
2. R and P disjoint: one step each way.
3. P lies strictly inside R = `(\x. B) S`:
   - inside S: the copies of P in M1 are replaced one by one (P closed);
   - inside B: P is closed, so `B[x := S]` holds P at the corresponding place. When R is
     a knot `(\i. E) Q`, P lies inside the argument Q or is a closed subterm of the head
     (Lemma 1(a)), and the same holds;
   - P is the operator `\x. B`: P is an abstraction member, I, T or `K(Q)`; a head is
     never P, not being a member. The family proof's argument. ∎

**Lemma 7 (eta and rho commute).** No member contains an eta redex. The abstractions
that occur in members are exactly these, and none is an eta redex `\z. N z` with z not
free in N:

- I, T and `K(P)` (the family proof): their bodies are f, `\f. t` and a closed P, none of the form
  `N z` with z bound here;
- a W-variant `\p. \i. ...`: its body is an abstraction, not an application `N p`;
- a W-variant's inner abstraction `\i. C[p p B1, ..., p p Bk]`, and a head
  `\i. C[E1, ..., Ek]`: the body is `C[...]`, an application because C is not a bare
  hole (R1), whose last argument is a closed part of C (closed, so not i) or a hole's
  content (`p p Bj`, an open knot or an open C-term: an application, not the variable
  i). This is the case the condition "C is not a bare hole" of (R1) is there for: with a
  bare hole, a head's body would be one open knot `H B`, and B can reduce to i
  (`(\z. z) i -> i`), giving the eta redex `\i. H i`;
- the abstractions inside C's closed parts: built from I, T and K, as above;
- open trees and I-trees contain no abstraction but I.

Reduction inside a knot gives a knot (Fact C) and so no new kind of abstraction. The family proof's
argument then applies: the eta redex of an eta step is disjoint from P or contains it,
and when P lies inside it, M1 holds P unchanged. ∎

**Lemma 8 (commutation, Hindley and Rosen).** The family proof's Lemma 8. ∎

## Proof of the theorem

Beta, eta and rho are Church-Rosser and commute (Lemmas 5 to 8), so their union is
Church-Rosser. Its convertibility contains beta, eta and `M = F` (`M ->rho F`). A
variable has no beta, eta or rho redex (members are closed), so two distinct variables
are not convertible, and lambda beta eta plus `M = F` is consistent. ∎

## What the proof does not use

No model and no reading of any setting. Of the point it uses only (R1) to (R4). It does
not need any term of M's reduction to repeat, which is what makes these points
different from the family proof's: the family is closed under every reduction inside a knot.
