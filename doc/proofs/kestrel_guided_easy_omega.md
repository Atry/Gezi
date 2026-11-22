# Guided membership through Omega's easiness (the guided read's second step)

Written 2026-09-29, before any code: the soundness argument of the second
step is reviewed first. It uses one theorem as a lemma,
`omega_easy_beta_eta.md` (Omega is easy in lambda beta eta with merges). The
argument is a hand proof and has not been machine-checked.

## What is claimed

The guided read's first step (`prolog/gezi/guided_normal_form.pl`) answers
N ∈ S(P) when a yield of P reduces to N: it reads P's Böhm tree against N.
Some members of S(P) come from yields with no normal form: S(Ω) is all of NF.
The second step lets the guided read, when it meets Omega at the head of the
term it is reading, answer through the equation Ω = M for one closed M
chosen from N, and go on. The theorem below states exactly which reads this
licenses.

## Definitions

Λ⁺, NF, Th(E), Sel, Yield and S are those of the contest's formal
definition of the normal form solution sets at that time. Further:

- ω = λx. x x and Ω = ω ω, up to alpha. These are the only terms the second
  step treats as easy (condition a).
- X ⇝ Y means that Y is reached from X by a finite sequence of steps, each
  either an equation of Th(∅) or a pair of Sel. By the two clauses of Yield,
  if X ⇝ Y and Y is merge-free, then Y ∈ Yield(X): Y ∈ Yield(Y) by clause 1
  with Y = Y, and each Sel pair, preceded by Th(∅) equations, is clause 2.
  The relation ⇝ is closed under contexts, since Th(∅) is closed under ν, μ
  and ξ and Sel is closed under the four contexts in its definition.
- A term is FREE OF EMPTY MERGES when {} does not occur in it.

## The read

The read is a judgment "t reads as Q", t a term of Λ⁺ and Q a βη normal
form, both possibly open over variables introduced by the read. It carries
one piece of state, the EQUATION: none at first, and once fixed
Ω = λx1. … λxk. Q0, with Q0 closed. The rules are those of the first step,
plus two for Omega:

1. (abstraction) t ⇝ λx. t1, Q = λx. Q1, and t1 reads as Q1.
2. (eta of the read term) Q = λx. Q1, t ⇝ h with h not an abstraction, x
   fresh, and h x reads as Q1.
3. (eta of the form) t ⇝ λx. t1, Q is not an abstraction, and t1 reads as
   Q x, x not free in Q.
4. (spine) t ⇝ y A1 … Aj with y a variable, Q = y B1 … Bj, and each Ai
   reads as Bi.
5. (Omega, fixing the equation) t ⇝ Ω A1 … Aj, no equation is fixed, and Q
   is closed. The equation becomes Ω = λx1. … λxj. Q.
6. (Omega, using the equation) t ⇝ Ω A1 … Aj, the equation
   Ω = λx1. … λxk. Q0 is fixed, j ≤ k, and Q is the normal form
   λx(j+1). … λxk. Q0.

A read of P against N succeeds when "P reads as N" is derived, P a program
free of empty merges. Rules 5 and 6 read none of the arguments Ai.

## Theorem

If P is free of empty merges and the read of P against N succeeds, then
N ∈ S(P).

## Proof

**Lemma 1 (completion).** A term X free of empty merges has a merge-free Y
with X ⇝ Y by Sel steps alone.

*Proof.* Select any member at an outermost occurrence of a merge. The
occurrence and every occurrence inside its other members disappear, and no
occurrence is created, so the number of occurrences decreases. A member of
a merge free of empty merges is free of empty merges, and a merge with a
member exists since the merge is not {}. Repeat until none is left. ∎

**Lemma 2 (the witness).** If t reads as Q, with the equation E fixed at
the end of the read (none, or Ω = M), then there is a term t̂ with t ⇝ t̂,
t̂ merge-free, and t̂ = Q ∈ Th(E'), where E' is ∅ when no equation was fixed
and {Ω = M} otherwise, whenever t is free of empty merges.

*Proof.* By induction on the derivation.
- Rule 1: t ⇝ λx. t1 ⇝ λx. t̂1 by the context λx, and λx. t̂1 = λx. Q1 by ξ.
- Rule 2: t ⇝ h = λx. h x by η (x fresh, so not free in h), and
  λx. h x ⇝ λx. ĥ where h x ⇝ ĥ = Q1; so t ⇝ λx. ĥ = λx. Q1 = Q.
- Rule 3: t ⇝ λx. t1 ⇝ λx. t̂1, and λx. t̂1 = λx. Q x = Q by ξ and η, x not
  free in Q.
- Rule 4: t ⇝ y A1 … Aj ⇝ y Â1 … Âj by the argument contexts, one argument
  after another, and y Â1 … Âj = y B1 … Bj by μ, ν.
- Rules 5 and 6: t ⇝ Ω A1 … Aj. Each Ai is free of empty merges (every term
  the read meets is built by substitution from subterms of P, and P has
  none), so Lemma 1 gives merge-free Âi with Ai ⇝ Âi, and t ⇝ Ω Â1 … Âj
  by the argument contexts. With M = λx1. … λxk. Q0 fixed (k = j and Q0 = Q
  under rule 5), Th({Ω = M}) proves Ω Â1 … Âj = M Â1 … Âj, and j ≤ k beta
  steps give λx(j+1). … λxk. Q0, since Q0 is closed and so no Âi is
  substituted into it; that is Q, by the rule's condition.

The theory only grows along the read: an equation of Th(∅), used before the
equation was fixed, is in Th({Ω = M}). ∎

**Conclusion.** Let P̂ be the witness of Lemma 2 for P and N. P ⇝ P̂ and P̂
is merge-free, so P̂ ∈ Yield(P). P̂ = N is in Th(E'), so
Th({P̂ = N}) ⊆ Th(E'). If no equation was fixed, Th(E') = Th(∅), which is
consistent (the first step's case). Otherwise E' = {Ω = M} with M closed,
and Th({Ω = M}) is consistent by the theorem of `omega_easy_beta_eta.md`
(M may contain merges there; here it is a normal form and has none). In
both cases λx. λy. x = λx. λy. y is not in Th({P̂ = N}), so N ∈ S(P). ∎

## Why each condition is there

- **One equation for the whole read** (condition b). Rule 5
  fixes the equation once, and rule 6 accepts a later Omega only where the
  same equation gives the form asked there. Without it, P = λz. z Ω Ω read
  against λz. z (λa. a) (λa. λb. a) would take Ω = λa. a at the first
  occurrence and Ω = λa. λb. a at the second, and together they prove
  λa. a = λa. λb. a, which is inconsistent (Böhm's theorem). With it, the
  second occurrence is compared with λa. a, the fixed value, and the read
  fails.
- **A closed form at the fixing position** (condition c). The
  Omega met under the read's abstractions is compared with a subterm Q of N
  that may use their variables. P = λy. Ω read against λy. y would need
  Ω = y, an open equation: with ξ it gives λy. Ω = λy. y, then by ν for every
  term Z, Ω = Z, so λx. λy. x = Ω = λx. λy. y. Rule 5 requires Q closed, so
  that M = λx1. … λxj. Q is closed and the theorem of `omega_easy_beta_eta.md`
  applies as stated.
- **No more arguments than the equation's abstractions** (rule 6, j ≤ k).
  When j > k, M A1 … Aj reduces to Q0 A(k+1) … Aj, and reading it would
  reduce inside the arguments after the equation was used. A reduction of
  Q0 applied to an argument can copy the argument, and the read can then
  select different members of a merge in different copies. Those selections
  are made in a term that only Th({Ω = M}) reaches from P, while a yield
  must be reached by Th(∅) and Sel alone (the definition of Yield). With
  j ≤ k every argument is discarded by M, the arguments are completed by
  Lemma 1 before the equation is used, and the rest of the comparison is
  between closed normal forms.
- **No empty merge in the program.** A yield is merge-free. An argument of
  an Omega that holds {} has no merge-free completion, and Ω applied to it
  reduces only to terms that still hold it, so the equation would not reach
  a yield. P = Ω {} has S(P) = ∅ (no yield at all), and a read that
  discarded the argument through Ω = λx. Q would claim every closed Q.
  Requiring P to be free of empty merges is checked once, syntactically, and
  every term the read meets is then free of them.

## What the implementation must do

- Detect Omega only as ω applied to an argument whose weak head is ω, both
  up to alpha, that is `lambda(apply(variable(0), variable(0)))` in de Bruijn
  form. The step from the argument to ω is part of t ⇝ Ω A1 … Aj.
- Keep the equation for the whole read of one claim, and undo it on
  backtracking into an earlier choice, so that each finished read uses one
  equation.
- Check the program for {} before the read, and use rules 5 and 6 only when
  there is none.
- Compare under rule 6 by the de Bruijn equality of closed normal forms,
  λ(j + 1) … λk. Q0 against Q. The left side is a βη normal form: Q0 is one,
  and an abstraction over the closed Q0 is no η redex, since Q0 cannot end
  in the abstracted variable. Two βη normal forms are βη equal exactly when
  they are equal as de Bruijn terms (confluence), so the equality is the
  condition of rule 6.

## Not covered

The knot families (`kestrel_false_only_family.md` and its addenda)
are proved over lambda beta eta without merges; using them here would need
a lemma that their consistency extends to Λ⁺, which this document does not
give. Terms other than Omega's alpha variants are not treated as easy
(condition a: an unsolvable term is not always easy).
