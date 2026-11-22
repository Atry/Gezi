# Omega is easy in lambda beta eta with sets

Written 2026-09-29.
The argument is a hand proof and has not been machine-checked.

The judgment asks consistency over lambda beta eta with sets.
The class `easy` of `corpora/contest_easy_terms.pl` rested on Jacopini's
theorem, which is stated for lambda beta. This document extends it.

**Theorem.** Let Ω = (λx. x x)(λx. x x) and let N be any closed term, possibly
containing sets. Then λβη with sets, plus the equation Ω = N, is
consistent.

## Proof

Let ρ be the rewrite rule `Ω → N`, applied at any position. The equational
theory λβη + (Ω = N) with sets is the convertibility of the union of β, η
and ρ, each closed under contexts; sets are constructors with only
congruence. So it suffices to show that β ∪ η ∪ ρ is confluent: then
`λx. λy. x` and `λx. λy. y`, which contain no β redex, no η redex and no Ω,
are distinct normal forms of the union and are not convertible.

**Occurrences of Ω are disjoint.** The proper subterms of Ω are `λx. x x`,
`x x` and `x`, none of them Ω. So no occurrence of Ω contains another.

**Parallel ρ.** Let X ⇉ρ Y mean that Y is X with some collection of
occurrences of Ω each replaced by N. Because the occurrences are disjoint,
⇉ρ has the diamond property: from X, replacing the occurrences in a
collection S, or those in a collection S', gives two terms with a common
result, reached by replacing the rest of S ∪ S' on each side. Also
ρ ⊆ ⇉ρ ⊆ ρ*, so ρ is confluent.

**Ω contains no redex but itself.** `λx. x x` and `x x` contain no β redex.
There is also no η redex, since in `λx. x x` the body is `x x` and x is free
in its function part x. The only β redex inside Ω is Ω itself, and
Ω →β Ω.

**Lemma 1 (⇉ρ commutes with one β step).** If X →β X1 and X ⇉ρ X2, there is
X3 with X1 ⇉ρ X3 and X2 →β X3 or X2 = X3.

*Proof.* Let R = (λy. P) Q be the contracted redex. By the last paragraph, R is
not strictly inside a replaced occurrence of Ω.
- If R is itself a replaced occurrence of Ω, then X1 = X, because Ω reduces
  to itself. Take X3 = X2: X1 ⇉ρ X2, and X2 = X3.
- Otherwise every replaced occurrence is disjoint from R or lies inside P or
  Q. Contracting R copies the occurrences in Q once per free occurrence of y
  in P, keeps those in P and outside R, and erases those in Q when y is not
  free in P. Their residuals are disjoint occurrences of Ω in X1. Let X3 be
  X1 with every residual replaced by N, so that X1 ⇉ρ X3. In X2 the same R is
  still a redex, since replacing occurrences inside P or Q, or outside R,
  does not change the abstraction or the application. Contracting it gives
  X3. ∎

**Lemma 2 (⇉ρ commutes with one η step).** If X →η X1 and X ⇉ρ X2, there is
X3 with X1 ⇉ρ X3 and X2 →η X3.

*Proof.* Let E = λz. M z, with z not free in M, be the contracted redex. By
the paragraph on Ω, E is not inside an occurrence of Ω, and an occurrence of
Ω is not E, since Ω is an application. So every replaced occurrence is
disjoint from E or lies inside M. Contracting E keeps M as it is, so the
residuals are the same occurrences. Let X3 be X1 with them replaced by N. In
X2, M has become M′, M with some occurrences replaced by N. Since N is
closed, z is still not free in M′, so λz. M′ z is still an η redex, and
contracting it gives X3. ∎

**Conclusion.**
- Commutation lifts from one step to many. By Lemmas 1 and 2, the reflexive
  transitive closure of ⇉ρ commutes with that of β and with that of η, and
  so with that of β ∪ η; this is Hindley's tiling argument.
- β ∪ η with sets is confluent. It is weakly orthogonal, with sets as
  constructors, by item 7 of the label-free design and van Oostrom and
  van Raamsdonk, LFCS 1994.
- ρ is confluent (parallel ρ).
- By the Hindley–Rosen lemma, β ∪ η ∪ ρ is confluent, and the theorem
  follows. ∎

## Use in the corpus

- The scored claims of class `easy` hold when the judgment is over λβη:
  `easy_second_first`, `easy_nested` and `easy_applied`, five claims in all.
- Each claim's test becomes \a. a when every Ω is replaced by one closed N.
  The point names that N: \u. \v. u, \u. \v. v, or \u. u.
- So the test equals \a. a in λβη + (Ω = N), and that theory is consistent
  by the theorem.

The traps of class `constant_body` are refuted by Böhm's theorem. That
argument uses β alone, so it stands in λβη.
