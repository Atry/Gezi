# The lemmas of the arithmetic and circuit library modules, by S

The Prolog library these proofs were written beside has been deleted; the
proofs still stand.

Written 2026-10-01. A lemma is proved on paper or in an external program
such as Lean; a lemma's proof is metadata, the PlDoc comment before
its declaration. Hand proofs, not machine-checked. They cover every lemma
of `corpora/standard_library/binary_arithmetic.pl`, `unary_comparison.pl`,
`twin_arithmetic.pl` and `boolean_quantified_circuits.pl` that is not a
row; the rows are proved by derivations of β, η and δ steps (section 1).

Every lemma here is proved the same way: each of its instances that meets
its premises is an equation of Th(∅). No lemma needs a consistency argument,
an infinite Böhm tree, or H*.

## 0. The setting

The judgment is the one restated in `certificate_meta_lemmas.md`:
terms Λ⁺ (λ terms with sets), the theory Th(E), the meaning ⟦T⟧ ⊆ Λ (the
yields of T), and

    S(T) = { N ∈ NF | ∃ T′ ∈ ⟦T⟧. Th({T′ = N}) is consistent }.

Th(∅) is λβη on Λ⁺ with sets treated as constructors.

A lemma `lemma(Name, Metavariables, Premises, Left, Right)` is sound
by S when, for every substitution σ of closed terms of Λ⁺ for its
metavariables that meets its premises, and every one-hole context C,
S(C[Left σ]) = S(C[Right σ]).

**Lemma 0 (equations of Th(∅) are sound by S in every context).** If
L = R ∈ Th(∅), then S(C[L]) = S(C[R]) for every one-hole context C of Λ⁺,
sets included.

*Proof.* Th(∅) is closed under the congruences, so C[L] = C[R] ∈ Th(∅).
Terms equal in Th(∅) have equal meanings (`certificate_meta_lemmas.md`,
Lemma 2b, part 2), and S(T) depends on T only through ⟦T⟧. ∎

Th(∅) is closed under substitution, so an equation of Th(∅) between open
terms gives one for every instance.

**Names.** A define's name stands for its term: the compiled program holds
the term, and the name is its content address. An occurrence of a name and
its term are one term of Λ⁺, so unfolding a name (δ) is no step at all.

**The fixpoint.** prelude's `fixpoint` is Curry's combinator
Y = λf. (λx. f (x x)) (λy. f (y y)). For every G, Y G →β (λx. G (x x))
(λy. G (y y)) →β G ((λy. G (y y)) (λy. G (y y))), and G (Y G) →β the same
term, so Y G = G (Y G) ∈ Th(∅).

**Canonical values.** A *tree* of binary_folds' `binary_tree` is a term
built from `binary_zero`, `binary_even h` and `binary_odd h`, h a tree. A
*canonical binary numeral* is a tree with no `binary_even` over
`binary_zero`. A *unary numeral* is built from prelude's `zero` and
`successor n`. The value of a tree is val(binary_zero) = 0,
val(binary_even h) = 2 val(h), val(binary_odd h) = 2 val(h) + 1, and the
value of a unary numeral is its count of successors. For every natural n
there is exactly one canonical binary numeral of value n, written ⌜n⌝: a
nonzero canonical numeral's lowest constructor gives the parity of its
value and its field is ⌜⌊n/2⌋⌝, nonzero under an even. A canonical
numeral is nonzero exactly when its value is.

**Premises.** A membership premise is the equation `T @ X = X`, T one of binary,
binary_tree, unary and boolean. The proofs below assume that a met premise
gives σ(X) ≡ t for a *finite* canonical value t of T, ≡ the contextual
equivalence of `solo_set_laws.md`, section 3, and use nothing else of it.
Each proof shows that the instance with t in place of X is an equation of
Th(∅), for every term in place of the other metavariables.

FIXME (2026-10-02): the equation `T @ X = X` alone does not give a finite https://github.com/Atry/private-overlay/issues/2015
canonical value: `fixpoint @ T` and `W W`,
W = λs.λa.λb. b (s s) (s s), for boolean meet `T @ X = X` by β. An
instance with such an X is not covered by the proofs below, which assume
the finite canonical value. A premise that excludes the witnesses, written
in the object language, is needed; none of these lemmas has one yet.

## 1. The rows

Every row lemma, binary_arithmetic's 22 (increment 3, plus 7, times 3,
equality 9) and twin_arithmetic's 34 (twin plus 7, twin equality 9,
binary_double 3, twin times 3, binary_fibonacci 3, twin_binary_fibonacci 3,
grid_paths 3, twin_grid_paths 3), is proved by a derivation of β, η and δ
steps between its two sides, each metavariable read as a constant that no
declaration names (the derivations were found and replayed by
`tests/osprey_library_rows.plt`, since deleted). No step looks inside
such a constant, so each row is an equation of Th(∅) with its metavariables
free, and by Lemma 0 it is sound by S at every instance, with no premise.
The prelude's rows of natural_at_least, natural_difference and
natural_equal, the canonical translation of their equations, are
proved the same way by the compiler's tests. Sections 3 to 5 cite the rows
by name.

## 2. Assertions on canonical values

**Lemma 2.** For every canonical binary numeral t, binary t = t ∈ Th(∅);
for every tree t, binary_tree t = t; for every unary numeral t, unary t = t.

*Proof.* Induction on t, by the assertions' own rows (each is `fixpoint @
G`, read as in Theorem 1). binary_tree and unary rebuild each constructor
over the assertion of its field. binary on `binary_even h`, h canonical and
nonzero, reduces to (binary h) [] (λg. even (even g)) (λk. even (odd k));
by the induction hypothesis binary h = h, which is `even g` or `odd k`, so
the term is even (even g) or even (odd k), that is even h. ∎

## 3. unary_comparison

The three lemmas have membership premises at unary on every metavariable.
By section 0 it is enough to show that the instance with unary numerals t
and u in place of M and N is an equation of Th(∅).

**at_least_reflexive**, natural_at_least M M = true. The instance is
natural_at_least t t = true. Induction on t: zero by
row 1 with M := zero; successor t′ by row 3, natural_at_least t′ t′, then
the induction hypothesis. So the instance is in Th(∅). ∎

The premise is needed: M occurs twice. On M = {zero, successor zero}, a
set, the left side has the yields true and false, the right side true
alone (the witness in `unary_comparison.pl`).

**difference_self**, natural_difference M M = zero. As above with
natural_difference's rows 1 and 3: zero by row 1 with M := zero gives zero.
∎

**equal_commutes**, natural_equal M N = natural_equal N M. Induction on t,
for every u: (zero, zero) is one term; (zero, successor u′) gives false by
row 2 and (successor u′, zero) gives false by row 3; (successor t′,
successor u′) gives natural_equal t′ u′ and natural_equal u′ t′ by row 4,
equal by the induction hypothesis at t′. ∎

## 4. binary_arithmetic

Every contract has membership premises at binary on its metavariables. By
section 0 it is enough to take canonical numerals a and b in place of A and
B. Each statement below is about the call on canonical numerals, and gives
the contract `binary @ (f @ a @ b) = f @ a @ b` (`boolean @ ...` for
equality): the call equals a canonical value v of the result type, and by
congruence and Lemma 2 so does the left side, the assertion of v.

**Lemma 4.1 (increment).** merge_binary_increment ⌜n⌝ = ⌜n + 1⌝ ∈ Th(∅),
and ⌜n + 1⌝ is nonzero. Induction on ⌜n⌝ by the increment rows: zero gives
odd zero = ⌜1⌝; even h gives odd h = ⌜2 val(h) + 1⌝; odd g gives even
(increment g) = even ⌜val(g) + 1⌝ by the induction hypothesis, canonical
since its field is nonzero, of value 2 val(g) + 2. ∎

This proves merge_binary_increment_contract.

**Lemma 4.2 (plus).** merge_binary_plus ⌜m⌝ ⌜n⌝ = ⌜m + n⌝ ∈ Th(∅).
Induction on ⌜m⌝ for every n, by the plus rows on the levels of the two
operands (h, k the fields):

- zero, any: the row gives ⌜n⌝.
- even h, zero and odd h, zero: the row gives the operand itself.
- even h, even k: even (plus h k) = even ⌜val(h) + val(k)⌝, canonical
  since val(h) > 0, of value 2 val(h) + 2 val(k).
- even h, odd k and odd h, even k: odd (plus h k) = odd ⌜val(h) + val(k)⌝,
  of value 2 (val(h) + val(k)) + 1.
- odd h, odd k: even (increment (plus h k)) = even ⌜val(h) + val(k) + 1⌝
  by the induction hypothesis and Lemma 4.1, canonical since the field is
  nonzero, of value 2 val(h) + 1 + 2 val(k) + 1. ∎

This is merge_binary_plus_contract. The value also shows the sum nonzero
when an operand is, which the even rows need of their fields.

**Lemma 4.3 (doubling).** For the inline doubling d = λy. y binary_zero
(λ_. even y) (λ_. even y), d ⌜n⌝ = ⌜2n⌝: zero gives zero; a nonzero ⌜n⌝ is
even h or odd k, and d gives even ⌜n⌝, canonical since its field is
nonzero. ∎

**Lemma 4.4 (times).** merge_binary_times ⌜m⌝ ⌜n⌝ = ⌜m n⌝. Induction on
⌜m⌝ by the times rows: zero gives zero; even h gives d (times h ⌜n⌝) =
d ⌜val(h) n⌝ = ⌜2 val(h) n⌝; odd h gives plus ⌜n⌝ (d ⌜val(h) n⌝) =
⌜n + 2 val(h) n⌝ by Lemmas 4.2 and 4.3. This is merge_binary_times_contract.
∎

**Lemma 4.5 (equality).** merge_binary_equality ⌜m⌝ ⌜n⌝ is true when
m = n and false otherwise, in Th(∅). Induction on ⌜m⌝ for every n, by the
equality rows: zero, zero gives true; a zero against a nonzero gives false,
and the values differ; even against odd gives false, and the parities
differ; two evens or two odds give the equality of the halves, true exactly
when the halves' values are equal (induction hypothesis), which is when
m = n. This is merge_binary_equality_contract. ∎

## 5. twin_arithmetic

The twin functions' membership lemmas are over binary_tree, every tree:
binary's even excludes zero below it, and the even rows of the twins put
binary_even over a recursive call, which a type cannot say is nonzero. The
natives' premises are at binary, the canonical numerals, so the answer
statements below are about canonical numerals, and the membership ones
about trees. By section 0 it is enough to take finite canonical values a,
b, n, r and c of the premises' types in place of A, B, N, R and C. Each
lemma's conclusion `T @ Call = Call` follows
from the call's value as in section 4, binary_tree t = t holding of every
tree (Lemma 2).

**Lemma 5.1 (merge_binary_increment_tree_member).** For every tree t,
merge_binary_increment t is a tree of value val(t) + 1, in Th(∅): Lemma 4.1's
induction, which never uses canonicity except for canonicity of the result.
∎

**Lemma 5.2 (binary_double_tree_member).** binary_double t is a tree of
value 2 val(t), by its three rows; on canonical t it is ⌜2 val(t)⌝ (Lemma
4.3). ∎

**Lemma 5.3 (twin_binary_plus_tree_member).** For trees a and b,
twin_binary_plus a b is a tree of value val(a) + val(b); on canonical a
and b it is ⌜val(a) + val(b)⌝. Induction on b, for every a: by the twin plus rows, b zero gives a; a zero gives
b; on two nonzero levels the row gives even or odd over twin plus of the
halves (induction hypothesis at k), except on two odds, where it gives
even (twin_binary_plus (increment h) k), the induction hypothesis at k
with Lemma 5.1 for the first operand. The values add as in Lemma 4.2. On
canonical operands every even the rows build is over a nonzero tree (the
halves of a canonical even are nonzero, and so is increment h), so the
result is canonical. ∎

**Lemma 5.4 (twin_binary_times_tree_member).** For trees a and b,
twin_binary_times a b is a tree of value val(a) val(b), and ⌜val(a)
val(b)⌝ on canonical operands. Induction on b by the twin times rows: zero
gives zero; even k gives binary_double (times a k), Lemma 5.2; odd k gives
twin_binary_plus a (binary_double (times a k)), Lemmas 5.2 and 5.3. ∎

**Lemma 5.5 (twin_binary_equality_member).** For trees a and b,
twin_binary_equality a b is true or false; on canonical operands it is
true exactly when val(a) = val(b). Induction on b, for every a, by the nine
rows, as Lemma 4.5. On trees that are not canonical the value can be wrong
(twin_binary_equality (even zero) zero is false), which is why the native's
premises are at binary. ∎

**Lemma 5.6 (merge_binary_plus_tree_member).** For trees a and b,
merge_binary_plus a b is a tree of value val(a) + val(b): Lemma 4.2's
induction with Lemma 5.1. ∎

**Lemma 5.7 (binary_fibonacci_tree_member and
twin_binary_fibonacci_tree_member).** For a unary numeral n,
binary_fibonacci n = ⌜F(n)⌝ and twin_binary_fibonacci n = ⌜F(n)⌝, F the
Fibonacci numbers (F(0) = 0, F(1) = 1, F(q + 2) = F(q + 1) + F(q)).
Strong induction on the count of n: rows zero and one; successor
(successor q) gives merge_binary_plus (fib (successor q)) (fib q), by the
induction hypothesis twice and Lemma 4.2 ⌜F(q + 1) + F(q)⌝; the twin gives
twin_binary_plus (fib q) (fib (successor q)), Lemma 5.3. ∎

**Lemma 5.8 (grid_paths_tree_member and twin_grid_paths_tree_member).**
For unary numerals r and c of counts i and j, grid_paths r c and
twin_grid_paths r c equal ⌜(i + j choose i)⌝. Induction on i + j: a zero
side gives odd zero = ⌜1⌝; otherwise the row gives the plus of the two
cells (i - 1, j) and (i, j - 1), by the induction hypothesis and Lemma 4.2
(Lemma 5.3 for the twin, whose operands are in the other order),
⌜(i - 1 + j choose i - 1) + (i + j - 1 choose i)⌝, which is Pascal's rule.
∎

Lemmas 5.7 and 5.8 are what an integer computation of the Fibonacci
numbers and the binomial coefficient by closed formulas must agree with.

## 6. boolean_quantified_circuits

**and_idempotent**, and X X = X, under the premise boolean X = X. By
section 0 it is enough to take b, true or false, in place of X. `and` is λl.λr. l r false (the module
tautology). and true true →β true true false →β true, and and false false
→β false false false →β false. So the instance is in Th(∅). ∎

The premise is needed: on X = λx. x, the left side is X X false, which β
reduces to false.
