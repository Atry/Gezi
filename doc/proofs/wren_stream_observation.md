# The n-th element of a mapped stream

The Prolog library these proofs were written beside has been deleted; the
proofs still stand.

Written 2026-10-02, for lemmas on infinite members of a recursive type, at
the points of `corpora/contest_infinite_members.pl`. It is a hand proof, not machine-checked.

The subject is the lemmas of `corpora/standard_library/scott_streams.pl`; the first two are

    lemma(stream_nth_map, [N, F, X],
          [unary @ N = N,
           stream_rebuild @ (successor @ N) @ X = X],
          stream_nth @ N @ (map @ F @ X),
          F @ (stream_nth @ N @ X)).

    lemma(stream_rebuild_map, [M, F, X],
          [unary @ M = M,
           stream_rebuild @ M @ X = X],
          stream_rebuild @ M @ (map @ F @ X),
          map @ F @ X).

and section 3 adds stream_rebuild_cons and stream_rebuild_zero, which meet the premise
`stream_rebuild m x = x` one layer at a time. The theorems say that each instance a lemma
rewrites, its premises established, has sides that are equivalent in every context, so the
rewrite is sound by S.

## 0. The setting

The setting is that of `doc/proofs/wren_fixpoint_list_prefix.md`, section 0: Λ⁺, Th(∅), S, δ
as no step, prelude's `fixpoint` as Curry's Y with Y G = G (Y G) ∈ Th(∅), and the contextual
equivalence ≡ of `doc/proofs/solo_set_laws.md` (sections 3 and 7), with Lemma 3.1 (≡ is an
equivalence), 3.2 (a congruence), 3.3 (it contains Th(∅)) and 3.6 (A ≡ B gives
S(C[A]) = S(C[B]) for every C). Write ≡S for the S-form of the equivalence: A ≡S B when A ≤S B
and B ≤S A in section 3 of that document, that is, S(C[A]) = S(C[B]) for every C. It states Lemmas 3.1,
3.2 and 3.3 for both preorders, and the proofs of the lemmas and theorems below use only these, so
each holds with ≡S in place of ≡ as well; that reading is the one a premise derived with library
lemmas needs, since a lemma proved sound by S gives ≡S, not ≡. The proofs hold as well with Th(∅)
in place of ≡: an instance whose premises are equations of Th(∅) has sides that are βη
convertible, which is the condition every sound equation lemma meets.

The defines the proof reads, from `prelude.pl` and `scott_streams.pl`:

    true = λt f. t        false = λt f. f        nil = λn c. n        cons = λh t n c. c h t
    zero = λz s. z        successor = λp z s. s p
    map            = Y (λself f xs. xs nil (λh t. cons (f h) (self f t)))
    stream_nth     = Y (λself i s. s zero (λh t. i h (λp. self p t)))
    stream_rebuild = Y (λself m x. m x (λp. cons (x nil true) (self p (x nil false))))

Write k̄ for the numeral successorᵏ zero. By β and Y's equation:

- (C) cons a b nil true ≡ a and cons a b nil false ≡ b;
- (M) map f (cons h t) ≡ cons (f h) (map f t);
- (N0) stream_nth zero (cons h t) ≡ h;
- (N1) stream_nth (successor p) (cons h t) ≡ stream_nth p t;
- (R0) stream_rebuild zero x ≡ x;
- (R1) stream_rebuild (successor p) x ≡ cons (x nil true) (stream_rebuild p (x nil false)).

For (N0) and (N1): `cons h t zero (λh t. i h (λp. stream_nth p t))` reduces to
`i h (λp. stream_nth p t)`, which is h at i = zero and `stream_nth p t` at i = successor p.

A **chain of m layers** is a term `cons h0 (cons h1 (… (cons h(m−1) R)))`, for any terms h0 to
h(m−1) and R; a chain of 0 layers is any R.

## 1. Layers

**Lemma 1 (the rebuild sees its layers).** For every natural number m and every term X with
stream_rebuild m̄ X ≡ X, X is ≡ a chain of m layers.

*Proof.* Induction on m. At m = 0 there is nothing to show. At m + 1, write X1 = X nil false. By
the hypothesis and (R1),

    X ≡ stream_rebuild (m+1)‾ X ≡ cons (X nil true) (stream_rebuild m̄ X1).

Apply both ends to nil and false (Lemma 3.2) and use (C): X1 ≡ stream_rebuild m̄ X1. By the
induction hypothesis, X1 is ≡ a chain of m layers, and so

    X ≡ cons (X nil true) (stream_rebuild m̄ X1) ≡ cons (X nil true) X1,

a chain of m + 1 layers. ∎

**Lemma 2 (a chain is rebuilt).** For every chain Z of m layers, stream_rebuild m̄ Z ≡ Z.

*Proof.* Induction on m. At 0, (R0). At m + 1, Z = cons h T with T a chain of m layers, and by
(R1), (C) and the induction hypothesis,
stream_rebuild (m+1)‾ Z ≡ cons h (stream_rebuild m̄ T) ≡ cons h T = Z. ∎

**Lemma 3 (map keeps the layers).** If X ≡ cons h0 (… (cons h(m−1) R)), then
map f X ≡ cons (f h0) (… (cons (f h(m−1)) (map f R))), a chain of m layers.

*Proof.* (M), m times, and Lemma 3.2. ∎

## 2. The theorems

**Theorem 4 (stream_nth_map).** For every natural number n and all terms F and X with
stream_rebuild (n+1)‾ X ≡ X:

    stream_nth n̄ (map F X) ≡ F (stream_nth n̄ X).

*Proof.* By Lemma 1, X ≡ cons h0 (… (cons hn R)). By Lemma 3,
map F X ≡ cons (F h0) (… (cons (F hn) (map F R))). Then (N1) n times and (N0) give
stream_nth n̄ (map F X) ≡ F hn and stream_nth n̄ X ≡ hn, and Lemma 3.2 gives F (stream_nth n̄ X)
≡ F hn. ∎

**Theorem 5 (stream_rebuild_map).** For every natural number m and all terms F and X with
stream_rebuild m̄ X ≡ X:

    stream_rebuild m̄ (map F X) ≡ map F X.

*Proof.* By Lemma 1 and Lemma 3, map F X is ≡ a chain Z of m layers. By Lemma 2,
stream_rebuild m̄ Z ≡ Z, and Lemma 3.2 carries it to map F X on both sides. ∎

With F the identity, Theorem 4 and one β step give stream_nth n̄ (map identity X) ≡ stream_nth
n̄ X: the observation of the points of `contest_infinite_members.pl`, a layer of `map id` taken
off.

**Corollary 6 (the lemmas are sound by S).** Let σ be an instance of either lemma with σ(N) ≡ n̄
(or σ(M) ≡ m̄) for a finite numeral, an equation of Th(∅) and so of ≡S, whose second premise,
`stream_rebuild … = X`, is met by a derivation each of whose steps gives ≡S. Then
S(C[Left σ]) = S(C[Right σ]) for every context C.

*Proof.* Replacing σ(N) by n̄ in the second
premise, by Lemma 3.2, gives stream_rebuild (n+1)‾ σ(X) ≡S σ(X) (or stream_rebuild m̄ σ(X) ≡S
σ(X)). Theorem 4 (or 5), read with ≡S, gives the sides at n̄ ≡S-equivalent, and Lemma 3.2 carries
n̄ back to σ(N) on both sides: Left σ ≡S Right σ, which is the claim. ∎

A step of β, η or δ gives ≡S by Lemma 3.3, and a step of a lemma proved sound by S, Corollary 6
or 9 included, gives ≡S by its soundness. A derivation of stream_nth_map's second premise by a rewrite with stream_rebuild_map, whose
own second premise is derived in the same way one layer down, is covered by induction on the size
of the derivation: each use has smaller premise derivations. That is how the premise of a tower
of maps over a knot is met: one rewrite by stream_rebuild_map a layer, and β at the knot, where
stream_rebuild m̄ (Y G) and Y G are β convertible for a G that unfolds into conses at least m
deep.

## 3. The rebuild, one layer at a time

The two lemmas below meet the premise `stream_rebuild m x = x` at a cons chain, the knot's weak
head included, one rewrite a layer:

    lemma(stream_rebuild_cons, [M, H, T],
          [stream_rebuild @ M @ T = T],
          stream_rebuild @ (successor @ M) @ (cons @ H @ T),
          cons @ H @ T).

    lemma(stream_rebuild_zero, [X], [],
          stream_rebuild @ zero @ X,
          X).

**Lemma 7 (a cons rebuilt).** Let ≈ be ≡ or ≡S. For all terms M, H and T with
stream_rebuild M T ≈ T:

    stream_rebuild (successor M) (cons H T) ≈ cons H T.

*Proof.* (R1) holds at every term p, not only at numerals: it is β and Y's equation. At p := M
and x := cons H T, with (C):

    stream_rebuild (successor M) (cons H T) ≈ cons (cons H T nil true) (stream_rebuild M (cons H T nil false))
                                            ≈ cons H (stream_rebuild M T),

each step an equation of Th(∅) (Lemma 3.3), and the hypothesis under the context `cons H []`
(Lemma 3.2) gives cons H T. ∎

**Lemma 8 (no layer).** stream_rebuild zero X ≡ X, and so ≡S, for every term X: (R0), an equation
of Th(∅). ∎

**Corollary 9 (sound by S).** Let σ be an instance of stream_rebuild_cons whose premise holds in
≡S, or any instance of stream_rebuild_zero. Then S(C[Left σ]) = S(C[Right σ]) for every context C.

*Proof.* Lemma 7 with ≈ := ≡S, or Lemma 8, at σ: Left σ ≡S Right σ, which is the claim. ∎

Neither lemma has a membership premise, so neither depends on a finiteness argument: M ranges
over every term. A premise derived by a derivation each of whose steps is β, η, δ or a lemma
proved sound by S holds in ≡S, so every instance such a derivation reaches is covered, a
non-numeral M such as W2 (below) included. Under Th(∅) in place of ≡ the same proof gives βη convertible
sides, the condition every sound equation lemma meets.

## 4. What the premises exclude, and what is not covered

In each case below, the second premise is no equation, so the lemma does not apply.

- A cons cell with a third field (the shape of `infinite_stream_map_identity_non_stream_nth`):
  the cons its projections rebuild has two.
- A term that passes `map id X = X` and is no stream (the shape
  of `infinite_stream_map_identity_premised_non_stream`).
- `Y K`, which absorbs every argument, and nil.
- A list of fewer layers than the index needs.

Not covered: the first premise met by the equation `unary @ N = N` alone. reference's
W2 = `\a. \b. b P1 I (V V)`, P1 = `\c. \d. \e. \f. c`, I = `\x. x`,
V = `\w. \u. \a. \b. b P1 I (w w)`, is no numeral, and `unary W2` reduces to W2 verbatim. At
N = W2 and X = Y (λy. stream_rebuild (successor W2) y), both premises are met by β, yet in
stream_nth W2 (map (λx. true) X) applied to false and true, the left side's weak head is W2
itself and the right side's is false, which Böhm separates. Corollary 6 covers such an instance
once a premise written in the object language excludes W2.
