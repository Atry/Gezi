# The prefix of a program's own list is the prefix of its assertion

The Prolog library these proofs were written beside has been deleted; the
proofs still stand.

Written 2026-10-02, for lemmas on infinite members of a recursive type. It
is a hand proof, not machine-checked.

The subject is the lemma `fixpoint_list_prefix` of `corpora/standard_library/scott_lists.pl`:

    lemma(fixpoint_list_prefix, [K, A, H, Seed],
          [unary @ K = K,
           A @ Seed = Seed,
           R^Z^(H @ R @ Z) = R^Z^(cons @ (H @ identity @ Z @ nil @ true)
                                      @ (R @ (H @ identity @ Z @ nil @ false))),
           Z^(list_layer @ A @ (H @ identity @ Z)) = Z^(H @ identity @ (A @ Z))],
          list_take @ K @ (list @ A @ (fixpoint @ H @ Seed)),
          list_take @ K @ (fixpoint @ H @ Seed)).

The theorem says that each instance the lemma rewrites, its premises established, has sides that
are equivalent in every context, so the rewrite is sound by S.

## 0. The setting

The setting is that of `doc/proofs/osprey_library_lemmas.md`, section 0: Λ⁺ is the set of λ terms
with sets, Th(∅) is λβη on Λ⁺ with sets treated as constructors, S is the set of consistent normal
forms, and a define's name and its term are one term (δ is no step). prelude's `fixpoint` is
Curry's Y, and Y G = G (Y G) ∈ Th(∅).

The proof is stated with the contextual equivalence ≡ of `doc/proofs/solo_set_laws.md`
(sections 3 and 7): A ≤ B when ⟦C[A]⟧ ⊆ ⟦C[B]⟧ for every one-hole context C, which may bind free
variables of A and B, and A ≡ B when A ≤ B and B ≤ A. Lemma 3 there, read at ≤, makes ≡ an
equivalence (3.1) and a congruence (3.2) that contains Th(∅) (3.3), and with 3.6, A ≡ B gives
S(C[A]) = S(C[B]) for every C. The proof below uses only these, written "Lemma 3.n", so it holds
as well with Th(∅) in place of ≡: an instance whose premises are equations of Th(∅) has sides that are
equal in Th(∅), βη convertible. That is the condition every sound equation lemma meets.

The defines the proof reads, from `prelude.pl` and `scott_lists.pl`:

    true  = λt f. t                      false = λt f. f
    nil   = λn c. n                      cons  = λh t n c. c h t
    zero  = λz s. z                      successor = λp z s. s p
    identity = λx. x
    list  = λA. Y (λself l. l nil (λh t. cons (A h) (self t)))
    list_layer = λA l. l nil (λh next. cons (A h) (A next))
    list_take  = Y (λself k l. k nil (λp. l nil (λh t. cons h (self p t))))

Write k̄ for the numeral successorᵏ zero, ℓ for `list A`, and T for `list_take`. By β and Y's
equation:

- (T0) T zero X ≡ nil;
- (T1) T (successor p) X ≡ X nil (λh t. cons h (T p t));
- (L) ℓ X ≡ X nil (λh t. cons (A h) (ℓ t));
- (C) cons a b nil c ≡ c a b, so cons a b nil true ≡ a and cons a b nil false ≡ b.

## 1. The layers of the program

Fix terms A, H and Seed of Λ⁺ for which premises 2, 3 and 4 hold in ≡. For a term s, write
L(s) = H identity s for the layer at s, and h(s) = L(s) nil true and n(s) = L(s) nil false for its
two projections.

**Lemma 1 (the guard).** For every term s:

1. L(s) ≡ cons h(s) n(s);
2. Y H s ≡ cons h(s) (Y H n(s)).

*Proof.* Premise 3 says λr z. H r z ≡ λr z. cons h′ (r n′), with h′ = H identity z nil true and
n′ = H identity z nil false. Apply both sides to two terms and use β and Lemma 3.2.

1. At r := identity and z := s: L(s) = H identity s ≡ cons h(s) (identity n(s)) ≡ cons h(s) n(s).
2. At r := Y H and z := s: H (Y H) s ≡ cons h(s) (Y H n(s)). And Y H s ≡ H (Y H) s by Y's
   equation. ∎

**Lemma 2 (the layer asserted).** For every term s, h(A s) ≡ A h(s) and n(A s) ≡ A n(s).

*Proof.* Premise 4 at z := s, by β and Lemma 3.2: list_layer A L(s) ≡ L(A s). On the left, by
Lemma 1.1 and (C):

    list_layer A L(s) ≡ L(s) nil (λh next. cons (A h) (A next))
                      ≡ cons h(s) n(s) nil (λh next. cons (A h) (A next))
                      ≡ cons (A h(s)) (A n(s)).

So L(A s) ≡ cons (A h(s)) (A n(s)), and by (C), h(A s) = L(A s) nil true ≡ A h(s), and
n(A s) ≡ A n(s). ∎

**Lemma 3 (fixed seeds).** If A s ≡ s, then A h(s) ≡ h(s) and A n(s) ≡ n(s).

*Proof.* A s ≡ s gives L(A s) ≡ L(s) by Lemma 3.2, so h(A s) ≡ h(s) and n(A s) ≡ n(s). Lemma 2
gives the rest. ∎

So from a seed the assertion fixes, every element is fixed by A and every next seed is again a
fixed seed. Premise 2 says Seed is one.

## 2. The theorem

**Theorem 4.** For every natural number k and every term s with A s ≡ s:

    T k̄ (ℓ (Y H s)) ≡ T k̄ (Y H s).

*Proof.* Induction on k, for all s at once.

- k = 0. Both sides are ≡ nil by (T0).
- k + 1. By Lemma 1.2, (L), (C) and Lemma 3:

      ℓ (Y H s) ≡ cons h(s) (Y H n(s)) nil (λh t. cons (A h) (ℓ t))
                ≡ cons (A h(s)) (ℓ (Y H n(s)))
                ≡ cons h(s) (ℓ (Y H n(s))).

  Then by (T1) and (C), on the two sides:

      T (k+1)‾ (ℓ (Y H s)) ≡ cons h(s) (T k̄ (ℓ (Y H n(s))))
      T (k+1)‾ (Y H s)     ≡ cons h(s) (T k̄ (Y H n(s))).

  A n(s) ≡ n(s) by Lemma 3, so the induction hypothesis at n(s) makes the two tails ≡, and Lemma
  3.2 makes the two sides ≡. ∎

**Corollary 5 (the lemma is sound by S).** Let σ be an instance of `fixpoint_list_prefix` with
σ(K) ≡ k̄ for a finite numeral k̄, whose premises 2, 3 and 4 are met by a derivation each of whose
steps gives ≡. Then S(C[Left σ]) = S(C[Right σ]) for every context C.

*Proof.* σ(K) ≡ k̄ by hypothesis. Premises 2, 3 and 4 do not hold K, so they hold at σ
in ≡. Theorem 4 at s := σ(Seed) gives T k̄ (ℓ (Y H s)) ≡ T k̄ (Y H s), with A and H read as σ's.
Replacing k̄ by σ(K) on both sides, by Lemma 3.2, gives Left σ ≡ Right σ, and Lemma 3.6 gives the
claim. ∎

A step of β, η or δ gives ≡ by Lemma 3.3, and so does a step of any lemma already proved sound in
this sense. A derivation that uses `fixpoint_list_prefix` itself in a premise is covered as well,
by induction on the size of the derivation: each such use has smaller premise derivations.

## 3. What the premises exclude, and what the theorem does not cover

The premises are where the program's own combinator is checked.

- A K that is no finite numeral is outside Corollary 5's hypothesis.
- A seed the assertion does not fix fails premise 2 (`successor zero` at boolean).
- An element the assertion does not fix fails premise 4 (`successor zero` as the element of a
  boolean list).
- A self that stands under no cons fails premise 3: the unguarded `λself s. self s`, and `Y K`,
  whose layer absorbs every argument and so meets premise 4, yet is no cons of its projections.

Not covered, each listed in a FIXME of the lemma's comment:

- Premise 1 met by the equation `unary @ K = K` alone. reference's W2 = `\a. \b. b P1 I (V V)`,
  P1 = `\c. \d. \e. \f. c`, I = `\x. x`, V = `\w. \u. \a. \b. b P1 I (w w)`, is no numeral, and `unary W2`
  reduces to W2 verbatim, so it meets the equation; Theorem 4's induction on k then does not
  apply. Corollary 5 covers such an instance once a premise written in the object language
  excludes W2.

- A step that cases on its seed, such as `not` in the list true, false, true, …: premise 4 is
  then no equation at an opaque z.
- Seeds of a type other than the element type, lists with no seed or with more than one, and
  lists that may end.
