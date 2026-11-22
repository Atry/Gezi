# The respelled cycles: `boolean(false)` is consistent

The claim proved is the scored `boolean(false)` of the three
points of `corpora/contest_respelled_cycles.pl`:

    respelled_and_false_self       C[h] = h F F    A[i] = i i
    respelled_and_false_identity   C[h] = h F F    A[i] = (\z. z) i
    respelled_if_false_self        C[h] = h F h    A[i] = i i

Each point's term is `M = W W I` with `W = \p. \i. C[p p (A[i])]`. The
claim: lambda beta plus `(\a. M y a) = \x. x` is consistent (the test of
template `boolean(false)`, `corpora/contest_hard_claims.pl`).

The proof uses no other proof as a lemma; it follows the method of
`kestrel_false_only_family.md`, a Church-Rosser reduction that contains the
equation, with a different family.

## The idea

That proof sets a knot `U = D D` equal to false and shows that the
knot's reducts form a family closed under beta. Here the knot passes an
argument that changes every lap, and the reducts of M include abstractions
over the argument, `\i. C[W W (A[i])]`, whose bodies are open and reduce
further. So the family below takes the argument positions as ARBITRARY
terms: it contains `w1 w2 Z` for every Z. The theory sets every member equal
to false. The argument A plays no part in the proof, which therefore holds
for any spelling of the argument, not only for the two above.

## Notation

Terms are lambda terms modulo alpha conversion; the theory is lambda beta (no
eta). `I = \f. f`, `F = \t. \f. f` (false). Every term below may be open
unless it is said to be closed.

**The knot functions.** For the contexts `C[h] = h F F` (and_false) and
`C[h] = h F h` (if_false), the set 𝒲 is:

- and_false: every term `\p. \i. (p p Y) F F`,
- if_false: every term `\p. \i. (p p Y1) F (p p Y2)`,

for ANY terms Y, Y1, Y2 (in which p and i may occur). The point's W is in 𝒲:
Y = A[i], and for if_false Y1 = Y2 = A[i]. We write `C[p p Y]` for either
body, with the understanding that for if_false the two holes may hold
different arguments.

**The family 𝒦** is the smallest set of terms such that:

- (k1) F ∈ 𝒦;
- (k2) `w1 w2 Z` ∈ 𝒦 for w1, w2 ∈ 𝒲 and ANY term Z;
- (k3) `(\i. K) Z` ∈ 𝒦 for K ∈ 𝒦 and ANY term Z;
- (k4) and_false: `K F F` ∈ 𝒦 for K ∈ 𝒦; if_false: `K F K'` ∈ 𝒦 for
  K, K' ∈ 𝒦;
- (k5) `I K` ∈ 𝒦 for K ∈ 𝒦.

M = W W I is in 𝒦 by (k2).

**The reduction rho.** `X ->rho X'` when X' is X with one occurrence of a
member K ∈ 𝒦 (open or closed) replaced by F. Every rho step is an equation
of lambda beta plus the set of equations `K = F`, K ∈ 𝒦.

## Shapes

**Lemma 1 (shapes).**

- (a) The only abstraction in 𝒦 is F. Every other member is an application.
- (b) No member of 𝒲 is in 𝒦, and neither is I, nor a variable.
- (c) No pair `w1 w2` (w1, w2 ∈ 𝒲) is in 𝒦.
- (d) For K ∈ 𝒦, the term `K F` is not in 𝒦.

*Proof.* (a) Read off (k1) to (k5). (b) A member of 𝒲 and I are
abstractions different from F: the body of the body of F is the variable f,
that of a w is an application, and the body of I is a variable, not an
abstraction. A variable is neither F nor an application.

(c) Suppose `w1 w2` ∈ 𝒦. Not (k1). (k2) would make w1 an application. (k3)
would make w1 = `\i. K` with K ∈ 𝒦; K is then `\i'. C[...]`, an
abstraction, so K = F by (a), and `C[...]`, an application, would be `\f. f`.
(k4) would make w2 = F or w1 an application. (k5) would make w1 = I. None
holds.

(d) Suppose `K F` ∈ 𝒦 with K ∈ 𝒦, and K is the smallest such. Not (k1).
(k2): K = `w1 w2`, excluded by (c). (k3): K = `\i. K0` is an abstraction, so
K = F by (a), and then K0 = `\f. f` = I, not in 𝒦 by (b). (k4): `K F` =
`(K0 F) F` or `(K0 F) K0'` with K0' = F, so K = `K0 F` with K0 ∈ 𝒦, and
`K0 F` ∈ 𝒦 with K0 smaller than K, against the choice of K. (k5): K = I,
excluded by (b). ∎

**Lemma 2 (substitution).** If K ∈ 𝒦 then `K[x := S]` ∈ 𝒦 for every
variable x and every term S. Likewise for 𝒲.

*Proof.* By induction on K. F is closed. The arguments Z, Y, Y1, Y2 are
arbitrary, so substituting inside them stays in the set; the fixed parts (F,
I, the shape of a w and of the clauses) are closed or bind only p and i,
which alpha conversion keeps apart from x and from the free variables of S. ∎

**Lemma 3 (closed under beta).** If K ∈ 𝒦 and `K ->beta K'`, then K' ∈ 𝒦.
If w ∈ 𝒲 and `w ->beta w'`, then w' ∈ 𝒲.

*Proof.* For w: the body `C[p p Y]` has no redex outside Y, Y1, Y2 (the
applications `p p Y`, `(p p Y) F` and the whole body have a variable at
their head, and F is normal), so a step changes one argument and w' ∈ 𝒲.

For K ∈ 𝒦, by induction on K; let R be the redex contracted.

- (k1) F is normal.
- (k2) `w1 w2 Z`. The applications in it are the whole term, whose operator
  `w1 w2` is an application and so not a redex, the pair `w1 w2`, and those
  inside w1, w2 and Z. R inside w1, w2 or Z: the step stays in (k2), by the
  case of 𝒲 and since Z is arbitrary. R the pair: `w1 = \p. \i. C[p p Y]`,
  so `w1 w2 -> \i. C[w2 w2 Y']` with `Y' = Y[p := w2]` (and likewise Y1', Y2').
  The body is `(w2 w2 Y') F F`, an instance of (k4) over the (k2) member
  `w2 w2 Y'`; for if_false, `(w2 w2 Y1') F (w2 w2 Y2')`, (k4) over two (k2)
  members. So K' = `(\i. C[w2 w2 Y']) Z` is in 𝒦 by (k3).
- (k3) `(\i. K0) Z`. R the whole term: K' = `K0[i := Z]` ∈ 𝒦 by Lemma 2.
  R inside K0: induction, and (k3). R inside Z: (k3).
- (k4) `K0 F F` (resp. `K0 F K1`). The whole term has the application
  `K0 F` as its operator, not a redex. The node `K0 F` is a redex only when
  K0 is an abstraction, that is K0 = F (Lemma 1(a)): `F F -> \f. f = I`, and
  K' = `I F` (resp. `I K1`), in 𝒦 by (k5). R inside K0 or K1: induction and
  (k4). F is normal.
- (k5) `I K0`. R the whole term: K' = K0. R inside K0: induction. ∎

**Lemma 4 (replacing inside a member).** If K ∈ 𝒦 and K2 ∈ 𝒦 occurs in K,
then K with that occurrence replaced by F is in 𝒦.

*Proof.* By induction on the size of K; take a derivation of K ∈ 𝒦 and look
at where the occurrence lies. If it is K itself, the result is F (k1).

- Inside an argument Z, Y, Y1 or Y2: these are arbitrary terms, so the clause
  still applies.
- Inside a w, outside its arguments: the subterms of `\p. \i. C[p p Y]` other
  than the arguments are w itself and `\i. C[p p Y]` (abstractions other than
  F, Lemma 1(a)), `C[p p Y]`, `(p p Y) F`, `p p Y`, `p p` and p, whose heads are
  the variable p (not in 𝒦: no clause yields an application headed by a
  variable, by induction on the clauses), and the occurrences of F, which are
  replaced by F with no change.
- The pair `w1 w2` of (k2): not in 𝒦, Lemma 1(c).
- The abstraction `\i. K0` of (k3): an abstraction other than F, since
  K0 ≠ I (Lemma 1(b)). Inside K0: induction, then (k3).
- The node `K0 F` of (k4): not in 𝒦, Lemma 1(d). Inside K0 or K1: induction,
  then (k4). An occurrence of F: no change.
- The I of (k5): not in 𝒦. Inside K0: induction, then (k5).

The subterms of F other than F itself are `\f. f` and f, not in 𝒦. ∎

## Church-Rosser

**Lemma 5 (rho is Church-Rosser).** If `X ->rho X1` and `X ->rho X2`, there
is X3 with `X1 ->rho= X3` and `X2 ->rho= X3` (at most one step each).

*Proof.* Let the steps replace the occurrences K1 and K2. Disjoint: replace
both. The same occurrence: X1 = X2. Nested, K2 inside K1: in X2 the
occurrence of K1 holds K1 with K2 replaced by F, a member by Lemma 4; replace
it by F, which gives X1. So X3 = X1. A relation with this diamond is
Church-Rosser (Barendregt 1984, §3.2). ∎

**Lemma 6 (beta and rho commute).** If `X ->beta X1` and `X ->rho X2`, there
is X3 with `X1 ->>rho X3` and `X2 ->beta= X3`.

*Proof.* Let the rho step replace an occurrence of K ∈ 𝒦 and the beta step
contract `R = (\x. B) S`.

1. R inside K (R = K included): the occurrence in X1 holds K' ∈ 𝒦 (Lemma 3);
   replacing it gives X2. X3 = X2.
2. R and K disjoint: one step each way.
3. K strictly inside R.
   - K inside S: X1 holds n >= 0 copies of S, each with K unchanged at the
     same place. X3 replaces all n copies (n rho steps), and `X2 ->beta X3`
     contracts the same redex, whose argument holds F.
   - K inside B: X1 holds `K[x := S]` at the corresponding place, a member by
     Lemma 2; replace it. Since F is closed, the result is `B'[x := S]` with
     B' = B with K replaced by F, which is also what `X2 ->beta` gives. One
     step each way.
   - K = `\x. B`: K is an abstraction in 𝒦, so K = F (Lemma 1(a)) and X2 = X.
     X3 = X1.

These are all the positions. ∎

**Lemma 7 (Hindley and Rosen).** If relations R1 and R2 satisfy: `X ->R1 X1`
and `X ->R2 X2` imply `X1 ->>R2 X3` and `X2 ->R1= X3` for some X3, then
`->>R1` and `->>R2` commute; and if R1 and R2 are Church-Rosser and commute,
their union is Church-Rosser (Barendregt 1984, Lemma 3.3.6 and Proposition
3.3.5; the tiling is written out as Lemma 8 of `kestrel_false_only_family.md`).

**Theorem.** For each of the three points, lambda beta plus
`(\a. M y a) = \x. x` is consistent.

*Proof.* Beta is Church-Rosser, rho is (Lemma 5), and they commute (Lemmas 6
and 7), so beta ∪ rho is Church-Rosser. Its convertibility is a congruence
that contains beta and every equation `K = F`, K ∈ 𝒦; so it contains the
theory lambda beta plus these equations. It does not equate
`T = \x. \y. x` with F: both are beta normal; T is an abstraction other
than F, so it is not in 𝒦 (Lemma 1(a)), nor are its subterms `\y. x` and x;
and the only member occurring in F is F itself, whose replacement changes
nothing. So T and F reduce only to themselves and have no common reduct.
So lambda beta plus { K = F : K ∈ 𝒦 } is consistent.

It proves M = F, since M = W W I ∈ 𝒦 by (k2). Hence, for every term Q
substituted for the free variable y, it proves
`\a. M Q a = \a. F Q a = \a. a`, and by (ξ) the closed form
`\y. \a. M y a = \y. \a. a`. The theory lambda beta plus
`(\a. M y a) = \x. x` is contained in it, so it is consistent. ∎

## Remarks

- The argument A[i] never enters the proof: the arguments of (k2) are
  arbitrary. The theorem holds for `W W X` with any argument X and any
  respelling A, and with the two holes of if_false fed different arguments.
- The trap `boolean(true)` of the same points stays refuted: the theory above
  equates M with F, and M = T would give T = F with `C[T] ->> F`.
- Clauses (k1), (k4) with K = F, and (k5) are there only to make the family
  closed under beta and under Lemma 4: `F F F -> I F -> F` and
  `F F K -> I K -> K`, so a member whose knot was already replaced by F keeps
  reducing inside the family.
