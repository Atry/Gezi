# The set laws hold in every context (2026-10-01)

The Prolog library these proofs were written beside has been deleted; the
proofs still stand.

Written 2026-10-01. A hand proof, not machine-checked.

The judgment is the contest's formal definition of that time: terms Λ⁺, the theory Th(E), the meaning ⟦T⟧ (the
least relation D closed under the conditions pure, th and set) and the set
S(T) of normal forms consistent with T. Th(∅) has no set law (sets enter no
other equation: no distributive, unit or idempotent law), so a merge tree such as `{{}, {{}, {}}}`
is not equal to `{}` in Th(∅): both are beta eta normal and distinct. A
native that answers "exactly these" or "empty" needs the laws below to
turn such a tree into its answer. This file proves that they hold at the
level of ⟦·⟧ in every one-hole context, so they are sound as equation
lemmas (a lemma is sound when S(C[Left σ]) = S(C[Right σ]) for every σ
and C), whichever form
they are given.

## What is proved

For terms M1, …, Mn, N1, …, Nk, A of Λ⁺ and every one-hole context C:

| law | left | right |
|---|---|---|
| singleton | C[{M}] | C[M] |
| flattening | C[{M1, …, Mi, {N1, …, Nk}, Mi+1, …, Mn}] | C[{M1, …, Mi, N1, …, Nk, Mi+1, …, Mn}] |
| duplicate removal | C[{M1, …, Mn, A, A}] | C[{M1, …, Mn, A}] |
| swap | C[{M1, …, Mi, Mi+1, …, Mn}] | C[{M1, …, Mi+1, Mi, …, Mn}] |

For each law, ⟦left⟧ = ⟦right⟧, and hence S(left) = S(right). Flattening with
k = 0 removes an empty member. Duplicate removal is stated for two adjacent
copies; with swap it removes a copy anywhere.

All four laws are corollaries of one theorem (section 4): **a set is the
least upper bound of its members** in the contextual preorder of meanings.
The same theorem, for the contextual preorder of S, justifies the
`members` narrowing node (section 5).

Section 5 also covers the binary representation of sets,
`[A | B]` for {A, B} and `[]` for {}. Corollary 7 shows that a
source set read as its right-nested form keeps its meaning in every context.
Corollary 8 proves the four fixed-shape equation lemmas on that
representation (unit, commutativity, associativity and idempotence), and
Corollary 9 the two choice narrowings `[A | B] ⇝ A` and `[A | B] ⇝ B`.

The proof has to deal with contexts that copy the hole. In (λx. x x) □ the
set is copied, and the two copies choose their members independently
(the formal definition: (λx. x x) {A, B} equals {A, B} {A, B}, whose
meaning is {A A, A B, B A, B B}). The proof marks the set occurrence and carries the
mark through every copy; each copy is then resolved on its own.

## 1. Notation and cited facts

We use the vocabulary of `gezi/doc/proofs/certificate_meta_lemmas.md`
(2026-09-29):
- a *yield* of T is an element of ⟦T⟧;
- a term is *pure* when it contains no set;
- a *member replacement* U ▷ U′ replaces one set occurrence of U by one of
  its members: U = C[{M1, …, Mn}] and U′ = C[Mi].

We write →β, →η for one β or η step anywhere in a term, sets included,
and →c for one β step, one η step or one member replacement. From that
document we use:

- **Lemma 2b.2.** If T →c A, then ⟦A⟧ ⊆ ⟦T⟧. Terms equal in Th(∅) have
  equal meanings.
- **Lemma 2b.3.** For every w ∈ ⟦T⟧ there is a pure P with T →c* P and
  (P = w) ∈ Th(∅).

Reduction never creates a set, and η removes none, so a term that reduces to
a pure term by η steps is itself pure.

## 2. η steps can be postponed

**Lemma 1.** If T →c* P, then T →(β ∪ ▷)* P′ →η* P for some P′.

The proof is the standard postponement argument with parallel η reduction
(cf. Barendregt 1984, section 15.1), with a member replacement treated like a
β step. *Parallel η reduction* ⇒ is the least relation with
- x ⇒ x;
- λx. M ⇒ λx. M′, M N ⇒ M′ N′ and {M1, …, Mn} ⇒ {M′1, …, M′n}, when the
  parts are related by ⇒;
- λx. M x ⇒ M′, when M ⇒ M′ and x ∉ FV(M).

Then →η ⊆ ⇒ ⊆ →η*, ⇒ is reflexive, M ⇒ M′ implies FV(M′) ⊆ FV(M), and
M ⇒ M′ with N ⇒ N′ implies M[x := N] ⇒ M′[x := N′] (induction on M ⇒ M′).
Write →X for one β step or one member replacement.

**Lemma 1a.** If M ⇒ N →X L, then M →X+ L′ ⇒ L for some L′.

*Proof.* By induction on the size of M; case on the last rule of M ⇒ N.

- *The η rule:* M = λx. M0 x with M0 ⇒ N and x ∉ FV(M0). M0 is smaller
  than M, and M0 ⇒ N →X L, so the induction hypothesis gives
  M0 →X+ L0 ⇒ L. Then M →X+ λx. L0 x ⇒ L by the η rule, since
  x ∉ FV(L0) ⊆ FV(M0).
- *A congruence rule, the X step below the root of N:* apply the induction
  hypothesis to the part of M that contains the step; the other parts keep
  their relation ⇒.
- *A congruence rule, the X step a member replacement at the root:*
  M = {M1, …, Mn} with Mj ⇒ Nj and L = Ni. Then M ▷ Mi ⇒ Ni.
- *A congruence rule, the X step β at the root:* N = (λy. B′) A′,
  L = B′[y := A′], and M = F A with F ⇒ λy. B′ and A ⇒ A′. Case on the last
  rule of F ⇒ λy. B′:
  - F = λy. B with B ⇒ B′: M →β B[y := A] ⇒ B′[y := A′] = L.
  - F = λz. F0 z with F0 ⇒ λy. B′ and z ∉ FV(F0): M →β F0 A, and
    F0 A ⇒ N →β L with F0 A smaller than M. The induction hypothesis gives
    F0 A →X+ L′ ⇒ L, so M →X+ L′ ⇒ L. ∎

*Proof of Lemma 1.* By induction on k, Lemma 1a gives
⇒ᵏ · →X⁺ ⊆ →X⁺ · ⇒ᵏ: for k = 1, apply Lemma 1a to the X steps one at a
time; for k > 1, ⇒ᵏ · →X⁺ = ⇒ᵏ⁻¹ · (⇒ · →X⁺) ⊆ ⇒ᵏ⁻¹ · →X⁺ · ⇒ ⊆ →X⁺ · ⇒ᵏ.
Split T →c* P into blocks of η steps and blocks of X steps. Moving the
η blocks to the right one at a time, and joining each one to the next η
block, ends with T →X* P′ ⇒* P, and ⇒* = →η*. ∎

**Lemma 2 (yields by β and member replacement).** For every w ∈ ⟦T⟧ there
is a pure Q with T →(β ∪ ▷)* Q and (Q = w) ∈ Th(∅). Conversely, every pure Q
with T →(β ∪ ▷)* Q is a yield of T.

*Proof.* Lemma 2b.3 and Lemma 1 give T →(β ∪ ▷)* Q →η* P with P pure, so
Q is pure, and (Q = P), (P = w) ∈ Th(∅). The converse is Lemma 2b.2 and the
pure condition. ∎

## 3. The contextual preorders

For terms A and B of Λ⁺ (open terms allowed), write

    A ≤ B    when ⟦C[A]⟧ ⊆ ⟦C[B]⟧ for every one-hole context C,
    A ≤S B   when S(C[A]) ⊆ S(C[B]) for every one-hole context C.

A context may bind free variables of A and B. ≤S is the relation that a
narrowing lemma B ⇝ A states. Let ⊑ stand for either relation.

**Lemma 3.** ⊑ has these properties:
1. it is reflexive and transitive;
2. it is a precongruence: A ⊑ B implies C[A] ⊑ C[B] for every C;
3. (A = B) ∈ Th(∅) implies A ⊑ B and B ⊑ A;
4. Mi ⊑ {M1, …, Mn} for every i;
5. A ⊑ B implies A[x := N] ⊑ B[x := N] for every N;
6. A ≤ B implies A ≤S B.

*Proof.*
1 and 2 are immediate, contexts being closed under composition.
3: Th(∅) is a congruence, so C[A] = C[B] in Th(∅), and equal terms have
equal meanings (Lemma 2b.2), hence equal S.
4: C[{M1, …, Mn}] ▷ C[Mi], and Lemma 2b.2.
5: (λx. A) N = A[x := N] is an equation of B, so for every C,
C[A[x := N]] = C[(λx. A) N] in Th(∅). The context C[(λx. □) N] then gives
the inclusion, by 3.
6: S(T) = ⋃ { K(T′) | T′ ∈ ⟦T⟧ } with K(T′) the normal forms N for which
Th({T′ = N}) is consistent, so S is monotone in ⟦·⟧. ∎

## 4. A set is the least upper bound of its members

**Theorem 4.** Let ⊑ be ≤ or ≤S. If Mi ⊑ P for every i, then
{M1, …, Mn} ⊑ P. (For n = 0: {} ⊑ P for every P.)

With Lemma 3.4, {M1, …, Mn} is the least ⊑-upper bound of its members.

*Marked terms.* A marked term is a term of Λ⁺ that may also contain *boxes*
⟨S | P⟩, S a set {M1, …, Mn} (n ≥ 0) of marked terms and P a marked term,
the *bound*. FV(⟨S | P⟩) = FV(S) ∪ FV(P), and substitution acts on both
parts, avoiding capture. Two maps send marked terms to Λ⁺; both act
homomorphically on every other constructor:

    |⟨S | P⟩| = |S|        (forget the bound: the term being reduced)
    φ(⟨S | P⟩) = φ(P)      (put the bound in place of the set)

Both commute with substitution: |M[x := N]| = |M|[x := |N|] and
φ(M[x := N]) = φ(M)[x := φ(N)]. A position of a marked term is *active*
when it is not inside a bound.

*Steps of marked terms* are taken at active positions only:
- β: (λx. A) B → A[x := B];
- a member replacement at a set that is not a box;
- a box replacement: ⟨{M1, …, Mn} | P⟩ → Mi.

**Lemma 4a (lifting).** If |T| →β U or |T| ▷ U, then T → T′ for a step of
marked terms with |T′| = U.

*Proof.* The active positions of T and the positions of |T| correspond. A
box is mapped to a set, which is neither an abstraction nor an application,
so a β redex (λx. A) B of |T| is the image of an active subterm
(λx. A′) B′ of T, and |A′[x := B′]| = A[x := B]. A set occurrence of |T| is
the image of a set or of a box; replace the corresponding member. ∎

*The invariant.* Inv(T) holds when every box ⟨{M1, …, Mn} | P⟩ at an active
position of T has φ(Mi) ⊑ φ(P) for every i.

**Lemma 4b.** If Inv(T) and T → T′, then Inv(T′) and φ(T′) ⊑ φ(T).

*Proof.* Call a box *outermost* when it is at an active position and not
inside a member of another box. Every position inside a member of a box is
erased by φ.

The step changes φ as follows.
- β outside every box: φ(T) →β φ(T′), since φ commutes with substitution;
  Lemma 3.3.
- Member replacement of a set outside every box: φ(T) ▷ φ(T′); Lemma 3.4 and
  3.2.
- Box replacement of an outermost box: φ(T) = E[φ(P)] and
  φ(T′) = E[φ(Mi)] for the context E that φ makes of the rest; Inv(T) and
  Lemma 3.2.
- Any step inside a member of a box: φ(T′) = φ(T).

Inv(T′) holds for each box at an active position of T′:
- A box of T that the step does not touch is unchanged.
- A box inside the redex of a β step, in the argument, is copied or erased
  unchanged. Every copy satisfies the condition on its own.
- A box inside the body of a β step becomes ⟨S[x := B] | P[x := B]⟩, and
  φ(Mi[x := B]) = φ(Mi)[x := φ(B)] ⊑ φ(P)[x := φ(B)] = φ(P[x := B]) by
  Lemma 3.5.
- A box with the step inside its member Mj: Mj becomes Mj′, and
  φ(Mj′) ⊑ φ(Mj) by the cases for φ above, applied to Mj (Lemma 3.3 for β,
  Lemma 3.4 for a member replacement, Inv(T) for a box replacement, equality
  when the step is inside a deeper box). With φ(Mj) ⊑ φ(P), Lemma 3.1 gives
  φ(Mj′) ⊑ φ(P).
- A box inside the member chosen by a member replacement or a box
  replacement keeps its members and its bound. ∎

*Proof of Theorem 4.* Let C be a one-hole context of Λ⁺ and
T0 = C[⟨{M1, …, Mn} | P⟩]. Then |T0| = C[{M1, …, Mn}], φ(T0) = C[P], and
Inv(T0) holds by hypothesis.

Case ⊑ = ≤. Let w ∈ ⟦C[{M1, …, Mn}]⟧. Lemma 2 gives
C[{M1, …, Mn}] →(β ∪ ▷)* Q with Q pure and (Q = w) ∈ Th(∅). Lift the
sequence step by step with Lemma 4a: T0 → T1 → … → Tm with |Tm| = Q. Q has
no set, so Tm has no box at an active position, and φ(Tm) = |Tm| = Q. By
Lemma 4b, Q = φ(Tm) ≤ φ(Tm−1) ≤ … ≤ φ(T0) = C[P], so ⟦Q⟧ ⊆ ⟦C[P]⟧. w is a
yield of Q (pure and th), hence w ∈ ⟦C[P]⟧.

Case ⊑ = ≤S. Let N ∈ S(C[{M1, …, Mn}]), witnessed by a yield w with
Th({w = N}) consistent. Take Q, the Ti and the chain as above, now in ≤S:
S(Q) ⊆ S(C[P]). Q = w in Th(∅), so Th({Q = N}) = Th({w = N}) is consistent,
and Q ∈ ⟦Q⟧; so N ∈ S(Q) ⊆ S(C[P]).

Both cases hold for every C, which is the claim. ∎

Where the copying went: the box is copied with its bound by the β case of
Lemma 4b, and each copy is replaced later by its own member under its own
instance of the invariant. Nothing requires two copies to make the same
choice.

## 5. Corollaries

**Corollary 5 (the four laws).** For every one-hole context C, each law of
the table in "What is proved" has ⟦C[left]⟧ = ⟦C[right]⟧, and so
S(C[left]) = S(C[right]).

*Proof.* By Lemma 3.2 it suffices to show left ≤ right and right ≤ left,
with C empty. Each direction is Theorem 4: every member of the side on the
left of ≤ is ≤ the side on the right.
- Singleton: M ≤ M (Lemma 3.1) gives {M} ≤ M; M ≤ {M} is Lemma 3.4.
- Flattening: each Mi ≤ right by Lemma 3.4, and {N1, …, Nk} ≤ right by
  Theorem 4, each Nj ≤ right by Lemma 3.4; so left ≤ right. Conversely each
  Nj ≤ {N1, …, Nk} ≤ left by Lemma 3.4 twice and Lemma 3.1, and each
  Mi ≤ left; so right ≤ left.
- Duplicate removal and swap: both sides have the same members, so every
  member of one side is ≤ the other side by Lemma 3.4. ∎

The laws therefore meet the soundness condition of an equation lemma: S(C[Left σ]) = S(C[Right σ]) for every instance σ and
every context C, Left and Right being the two sides of a row of the table.

**Corollary 6 (the `members` narrowing node).** If T ⇝ vi is a sound
narrowing for every i (vi ≤S T), then so is T ⇝ {v1, …, vk}:
{v1, …, vk} ≤S T. This is Theorem 4 for ≤S. A node T ⇝ {} (k = 0) is sound
for every T, and claims nothing.

Corollary 6 gives only the narrowing reading. "S(T) is exactly
S({v1, …, vk})" needs the converse T ≤S {v1, …, vk}, which no member
derivation supplies (a narrowing is never evidence that a set is exact
or empty).

### The binary representation

The binary representation writes a set with two constructors, as the DSL surface
spells a list: `[A | B]`, the set {A, B} of two members, and `[]`, the
empty set {} (2026-10-01).
A source set {M1, …, Mn} is then the right-nested term

    R(M1, …, Mn) = {M1, R(M2, …, Mn)},    R() = {},

and its number of members is the nesting depth of a term, never a Prolog
structure. The three corollaries below are the facts a rewriting in this
representation relies on. Write A ≡ B for A ≤ B and B ≤ A; by the definition of ≤
and Lemma 3.6, A ≡ B gives ⟦C[A]⟧ = ⟦C[B]⟧ and S(C[A]) = S(C[B]) for every
C.

**Corollary 7 (the reading).** {M1, …, Mn} ≡ R(M1, …, Mn) for all terms
M1, …, Mn (n ≥ 0). Hence a term of Λ⁺ and the term obtained from it by
rewriting each of its sets, at any depth, into its right-nested form have
the same meaning in every context.

*Proof.* Induction on n. For n = 0 both sides are {}. For n ≥ 1, the
induction hypothesis gives {M2, …, Mn} ≡ R(M2, …, Mn), and Lemma 3.2 with
the context {M1, □} gives {M1, {M2, …, Mn}} ≡ R(M1, …, Mn). Flattening
(Corollary 5, with i = 1 and the inner set of n − 1 members) gives
{M1, {M2, …, Mn}} ≡ {M1, …, Mn}. Lemma 3.1 composes the two. For a whole
term, rewrite its sets one at a time, innermost first. Each rewrite
replaces a subterm S by R(S) inside the context made of the rest of the
term, which is ≡ by Lemma 3.2, and Lemma 3.1 composes the rewrites. ∎

**Corollary 8 (the binary laws).** For all terms A, B, C:

| law | left | right |
|---|---|---|
| unit | [A \| []] | A |
| commutativity | [A \| B] | [B \| A] |
| associativity | [A \| [B \| C]] | [[A \| B] \| C] |
| idempotence | [A \| A] | A |

each left ≡ its right, so each row is a sound equation lemma.

*Proof.* Each is a chain of laws of Corollary 5, composed by Lemma 3.1.
- Unit: {A, {}} ≡ {A} by flattening with k = 0, and {A} ≡ A by singleton.
- Commutativity: {A, B} ≡ {B, A} by swap.
- Associativity: {A, {B, C}} ≡ {A, B, C} by flattening at i = 1, and
  {{A, B}, C} ≡ {A, B, C} by flattening at i = 0.
- Idempotence: {A, A} ≡ {A} by duplicate removal with n = 0, and
  {A} ≡ A by singleton. ∎

**Corollary 9 (the two choices).** For all terms A and B, A ≤S [A | B] and
B ≤S [A | B]. So `[A | B] ⇝ A` and `[A | B] ⇝ B` are sound narrowing
lemmas: S(C[A]) ⊆ S(C[[A | B]]) and S(C[B]) ⊆ S(C[[A | B]]) for
every C.

*Proof.* Lemma 3.4, with the two members of {A, B}, and Lemma 3.6. ∎

Picking the i-th member of R(M1, …, Mn) takes i − 1 steps of the second
choice and one step of the first, each sound by Corollary 9 in its own
context. Corollary 7 says they pick from the source set {M1, …, Mn} itself.

## 6. What is not proved here

- Laws that relate a set to the constructors around it, for instance
  `{A, B} N = {A N, B N}`: they are not needed by the natives, and the
  ones that hold are not covered by this file.

## References

- H. P. Barendregt, The Lambda Calculus: Its Syntax and Semantics, revised
  edition, North-Holland, 1984, section 15.1 (η postponement).
- `gezi/doc/proofs/certificate_meta_lemmas.md` (2026-09-29),
  Lemmas 2a and 2b, and Theorem 9 (more operands never remove a solution),
  of which Lemma 3.4 with Theorem 4 is a contextual form.
