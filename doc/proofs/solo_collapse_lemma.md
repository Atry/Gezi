# The collapse lemma

The lemma below is section 1 of a proof of the false-only conjectures (value_map_two_cycle,
value_map_three_cycle and the three probe cycles). It was written on the
branch `solo-false-only-proof`, commit 11af801d61244a0a070cdb53a91c261947517247,
file `gezi/doc/proofs/false-only-consistency.md`, and was never merged
to main. This file carries it to main unchanged. The checker that applied
it to closed grammars can be read back with
`git show cab4bc415:lambda_jit/prolog/lambda_jit/collapse_proof.pl`. The lemma is stated over lambda
beta eta, the judging theory for pure programs (for a pure
program, S(P) is the set of beta eta normal forms consistent with P).

## The lemma

Let 𝒦 be a set of closed terms and v a closed term with:

- (K0) v ∈ 𝒦;
- (K1) 𝒦 is closed under one-step beta reduction: t ∈ 𝒦 and t →β t' give
  t' ∈ 𝒦;
- (K2) 𝒦 is closed under replacing an occurrence of a subterm that belongs
  to 𝒦 by v: t ∈ 𝒦, s an occurrence in t with s ∈ 𝒦, give t[s := v] ∈ 𝒦;
- (K3) no term of 𝒦 contains an eta redex (a subterm `\x. P x` with x not
  free in P);
- (K4) there is a closed beta-eta normal form N ≠ v such that no subterm of
  N is in 𝒦, v is beta-eta normal, and no proper subterm of v is in 𝒦;
- (K5) v is the only abstraction in 𝒦.

**Lemma.** Under (K0)-(K5), lambda beta eta + {s = v : s ∈ 𝒦} is
consistent.

*Proof.* Let →ρ be the compatible closure of {s → v : s ∈ 𝒦} (all s are
closed, so an occurrence of s is a subterm with no free variable), and
→R = →β ∪ →ρ.

(i) *→R is confluent.* Define parallel reduction ⇒ by

1. x ⇒ x;
2. P ⇒ P' gives λx.P ⇒ λx.P';
3. P ⇒ P' and Q ⇒ Q' give P Q ⇒ P' Q';
4. P ⇒ P' and Q ⇒ Q' give (λx.P) Q ⇒ P'[x := Q'];
5. s ∈ 𝒦 gives s ⇒ v.

As in Barendregt 3.2: ⇒ is reflexive, →R ⊆ ⇒ ⊆ →R* (a step by rule 5 is a
ρ step; the others are beta developments), and the substitution lemma holds:
P ⇒ P' and Q ⇒ Q' give P[x := Q] ⇒ P'[x := Q'] (in the case of rule 5, P is
closed, so P[x := Q] = P ⇒ v = v[x := Q']).

*Closure:* t ∈ 𝒦 and t ⇒ t' give t' ∈ 𝒦, since t →R* t' and each →β step
(K1) and each →ρ step (K2) keeps a term in 𝒦.

Define t* by: t* = v when t ∈ 𝒦; otherwise x* = x, (λx.P)* = λx.P*,
((λx.P) Q)* = P*[x := Q*], (P Q)* = P* Q* when P is not an abstraction.
Then t ⇒ t' gives t' ⇒ t*, by induction on t ⇒ t'. If t ∈ 𝒦, then t' ∈ 𝒦
by closure, and t' ⇒ v = t* by rule 5. If t ∉ 𝒦, rule 5 does not apply at
the root, and the cases are Barendregt's, using the substitution lemma. One
sub-case is new: t = (λx.P) Q with t' = R Q' by rule 3, where λx.P ⇒ R by
rule 5. Then λx.P ∈ 𝒦, so λx.P = v by (K5), and R = v = λx.P. v is normal
and has no proper subterm in 𝒦 (K4), so P* = P, and rule 4 gives
t' = (λx.P) Q' ⇒ P[x := Q*] = t*, using Q' ⇒ Q* from the induction. So ⇒
has the diamond property, and →R, whose reflexive transitive closure is
⇒*, is confluent.

(ii) *→R and →η commute.* β and η commute (Barendregt, section 3.3). For ρ and η,
let t →ρ u by replacing an occurrence of s ∈ 𝒦 and t →η w by contracting
`\x. P x`. By (K3) the eta redex is not inside s and is not s. Since s is
closed and x is free in P x, s is not P x. So either the two are disjoint, or
s lies inside P. In both cases u →η w' and w →ρ w' for the same w', where w'
is t with both steps done. This one-step square tiles, so →ρ* and →η*
commute. Since β* and η* commute too, tiling β and ρ steps against η*
shows that →R* and →η* commute. By the Hindley-Rosen lemma (Barendregt,
section 3.3), →R ∪ →η is confluent, since both are confluent (η is
confluent: Barendregt, section 3.3).

(iii) *Consistency.* The convertibility of →R ∪ →η contains beta, eta and
every s = v, and is a congruence, so it contains the theory. N has no redex
and no subterm in 𝒦, so its only reduct is N. v is normal and no proper
subterm of v is in 𝒦, so its only reduct is v (rule 5 on v gives v). By
confluence, N and v are not convertible, and the theory does not equate the
two distinct normal forms N and v. ∎

