# A counterexample to the lifting step of the premise argument (2026-10-02)

A hand argument, not machine-checked.
The vocabulary is that of `gezi/doc/proofs/solo_set_laws.md`: Λ⁺, Th(∅),
the meaning ⟦T⟧, S(T), the member replacement ▷, the contextual preorders ≤
and ≤S (section 3 there), and A ≡ B for A ≤ B and B ≤ A.

## The statement refuted

The replay of a lemma premise in the lemma engine establishes the premise by
steps that are each sound in ≡ (the contextual equivalence of `solo_set_laws.md`), or only in its
S-form ≡S (A ≤S B and B ≤S A) when a step cites a lemma proved sound by S, and
not in Th(∅). The counterexample below refutes step 3 for both ≡ and ≡S.
To show that an instance established that way is a finite canonical member of
the premise's type, the question was reduced (2026-10-01) to three steps:

1. In the empty context, any two pure reducts of X are related by the
   type's structural equality.
2. A Böhm tree argument: from `T X = X` and the structural equality, X is βη
   equal to a canonical member.
3. **Lifting** from the empty context to every context, stated as the lemma:
   *if every pure reduct of a closed term X is βη equal to one βη normal form
   P, then X ≡ P.*

Step 3 is false, and adding it to the semantics as an axiom gives an absurd
result.

## The counterexample

Let

    X = {I, J},    J = λf. f {},    I = λx. x.

**Every pure reduct of X is I.** X has two member replacements, to I and to J.
J is a βη normal form with a set in it. Its only set is {}, which has no
member to replace. That set is the argument of the bound variable f, so no β
step erases it. So J has no pure reduct, and the pure reducts of X are I and
the terms it reduces to, all equal to I. By Lemma 2b.3 of
`certificate_meta_lemmas.md`, ⟦X⟧ = [I], the terms equal to I in Th(∅).

**X ≰ I and X ≰S I.** Take the context C = □ (λz. K), with K = λa. λb. a. Then

    C[X] = {I, J} (λz. K)  ▷  J (λz. K)  →β  (λz. K) {}  →β  K,

so K ∈ ⟦C[X]⟧, and K ∈ S(C[X]). On the other side, C[I] = I (λz. K) is pure
with normal form λz. K, so ⟦C[I]⟧ = [λz. K] and S(C[I]) = {λz. K}. The two
are distinct βη normal forms, so K ∉ ⟦C[I]⟧ and K ∉ S(C[I]).

The member J contributes nothing in the empty context, because its empty set
is never erased there. A context that applies X to a function ignoring its
argument erases that set, and then J contributes.

## Taking step 3 as an axiom is absurd

Suppose step 3 is added to the semantics as an axiom, so that X ≡ I. Then
⟦C[X]⟧ = ⟦C[I]⟧ for every C, and the derivation above, with any closed pure M
in place of K, gives

    M ∈ ⟦I (λz. M)⟧ = ⟦λz. M⟧.

So every constant function λz. M would also mean M. With M = I this reads
I ∈ ⟦λz. I⟧ = ⟦false⟧ for the Scott boolean false = λa. λb. b. Then
S(false) ⊇ {false, I}: a pure program that is already a normal form would have
a second answer.

## What is still open

The counterexample refutes step 3 as an isolated lemma. It does not refute
the goal the three steps were for: if the engine establishes both `T @ X = X`
and the structural equality premise in ≡, then X ≡ t for a canonical member t.
The second premise sees the junk member. For the Scott booleans with
`equal x y = x (y true false) (y false true)`, take X = {true, J′} with a
junk member J′ that is itself a fixed point of `boolean`, for instance
J′ = Y (λq. λa. λb. a q {}), for which `J′ true false` is β equal to J′
and J′ has no pure reduct. Then `equal true J′` is β equal to J′, so
`equal X X ≡ true` would force J′ ≤ true (J′ ≤ `equal true J′` ≤ `equal X X`
by Lemma 3 of `solo_set_laws.md`), which fails in the context
□ (λz. λw. K) D for any closed D: J′ gives (λz. λw. K) J′ {} →β* K, and
true gives λz. λw. K. So this X does not meet the second premise.
That remark is made on one type, and is not a proof. A lifting
lemma that is true has to use both premises in ≡, not the pure reducts in the
empty context alone.
