# The reflection and involution laws of Scott folds

The Prolog library these proofs were written beside has been deleted; the
proofs still stand.

Written 2026-10-01. A hand proof, not machine-checked. It is
the meta-theorem behind the fold laws: a
function that takes a Scott value apart and rebuilds it, constructor by
constructor, is the identity on finite canonical values; one that swaps
constructors by an involution is its own inverse there. The same induction
is the one `prolog/gezi/identity_premise.pl` runs per
closure; here it is proved once for every fold of the shape below.

## Definitions

A Scott type T has constructors C_1, ..., C_k, the constructor C_i with
m_i fields, each field of type T (a RECURSIVE field) or of another type (a
PLAIN field). In the types of `lambda_jit_scott_decoding:scott_constructors/2`
every field is recursive (boolean: true, false with no field; unary: zero,
successor with one; binary: zero, even and odd with none, one and one); a
list's cons has a plain head and a recursive tail. The constructor is the
closed term

    C_i = \f_1. ... \f_m. \c_1. ... \c_k. c_i f_1 ... f_m        (m = m_i).

A CANONICAL VALUE of T is a closed term C_i v_1 ... v_m in which every
v_j at a recursive field is a canonical value of T and every v_j at a plain
field is any closed term: a finite tree of constructor applications along
the recursive fields.

Let σ be a permutation of 1 .. k such that C_σ(i) has the same fields as
C_i, recursive and plain at the same positions: the
identity (the rebuild) or a swap of constructors with the same number of
fields (the complement of the binary numerals swaps even and odd). The FOLD
GENERATOR of σ is

    G = \self. \x. x B_1 ... B_k,
    B_i = \f_1. ... \f_m. C_σ(i) (R f_1) ... (R f_m),

where, at a recursive field, R f is `self f` for the fixpoint kind and
`self self f` for the self-application kind, and at a plain field R f is f. Its KNOT F is `Y G` for the fixpoint kind, Y the
prelude's fixpoint combinator, and `G G` for the self-application kind.
These are the two recursion kinds of the attractor library
(`corpora/contest_attractors.pl`, RECURSION). The two knots of one fold are
beta convertible: write G_fix and G_self for the generators of one σ in
the fixpoint and the self-application kind; then \p. G_fix (p p) →β G_self
(contract G_fix's redex under \p), so
Y G_fix →β (\p. G_fix (p p)) (\p. G_fix (p p)) →β* G_self G_self. The laws are still stated for each kind, because a derivation
starts from the spelling the program holds.

## The unfolded knot

Let F° be the term the recursive calls of F name:

- fixpoint kind: Y G = (\h. (\p. h (p p)) (\p. h (p p))) G →β F°, with
  F° = (\p. G (p p)) (\p. G (p p)), and F° →β G F°;
- self-application kind: F° = F = G G, and F° →β (\x. x B_1 ... B_k)[self := G],
  in which R f = G G f = F° f.

In both kinds, therefore, for any term v,

    F° v →β+ v B'_1 ... B'_k,  B'_i = \f_1. ... \f_m. C_σ(i) (R' f_1) ... (R' f_m),   (U)

with R' f = F° f at a recursive field and R' f = f at a plain one,

and F v →β* F° v.

## Lemma 1 (one layer)

For any terms w_1, ..., w_m, with m = m_i,

    F° (C_i w_1 ... w_m) →β* C_σ(i) (R' w_1) ... (R' w_m).

Proof. By (U), F° (C_i w̄) →β+ (C_i w̄) B'_1 ... B'_k. C_i w̄ applied to k
arguments reduces by m + k beta steps to B'_i w_1 ... w_m, and B'_i
applied to w̄ reduces by m beta steps to C_σ(i) (R' w_1) ... (R' w_m). The
w_j are only substituted, never evaluated, so the lemma holds for any
terms, canonical or not. ∎

## Theorem 1 (reflection)

Let σ be the identity. For every canonical value v of T, F° v →β* v, and so
F v →β* v.

Proof. By induction on the tree v = C_i v_1 ... v_m. By Lemma 1,
F° v →β* C_i (R' v_1) ... (R' v_m). At a plain field R' v_j is v_j. At a
recursive field v_j is a smaller canonical value, so F° v_j →β* v_j by the
induction hypothesis. Beta reduction is a congruence, so
C_i (R' v_1) ... (R' v_m) →β* C_i v_1 ... v_m, which is v.
For a constructor with no field the first step already ends at C_i. ∎

## Theorem 2 (involution)

Let σ be an involution, σ(σ(i)) = i, and F its knot. For every canonical
value v of T, F° (F° v) →β* v, and so F (F v) →β* v.

Proof. By induction on v = C_i v_1 ... v_m. By Lemma 1 inside the
argument, F° (F° v) →β* F° (C_σ(i) (F° v_1) ... (F° v_m)). By Lemma 1
again, with w_j = F° v_j, which Lemma 1 allows since it asks nothing of its
fields, this reduces to C_σ(σ(i)) (F° (F° v_1)) ... (F° (F° v_m)), which is
C_i (F° (F° v_1)) ... (F° (F° v_m)). By the induction hypothesis on each
v_j and congruence it reduces to C_i v_1 ... v_m = v. ∎

## Theorem 3 (swap fusion)

Generalise the branches. For terms b_1, ..., b_k, the fold with branches b
has the generator G_b = \self. \x. x B_1 ... B_k with
B_l = \f_1. ... \f_m. b_l (R f_1) ... (R f_m), its knot F_b and its
unfolded knot F°_b as above; the rebuild of the definitions is the case
b_l = C_σ(l). The proof of Lemma 1 gives, for any terms w_1, ..., w_m,

    F°_b (C_l w_1 ... w_m) →β* b_l (F°_b w_1) ... (F°_b w_m).        (Lemma 1')

Let K be the knot of the swap σ (an involution, the complement of the
binary numerals), and write b∘σ for the branches (b_σ(1), ..., b_σ(k)).
For every canonical value v of T,

    F°_b (K° v)  and  F°_(b∘σ) v

are beta equal: both reduce to one term.

Proof. By induction on v = C_i v_1 ... v_m. By Lemma 1 inside the
argument and then Lemma 1',

    F°_b (K° v) →β* F°_b (C_σ(i) (K° v_1) ... (K° v_m))
                →β* b_σ(i) (F°_b (K° v_1)) ... (F°_b (K° v_m)),

and by Lemma 1', F°_(b∘σ) v →β* b_σ(i) (F°_(b∘σ) v_1) ... (F°_(b∘σ) v_m).
By the induction hypothesis each F°_b (K° v_j) and F°_(b∘σ) v_j reduce to
one term, so by congruence the two right-hand sides do. ∎

The equation is a chain of beta steps forward from each side to the common
term, so a chain of equations with no eta step and no merge, as a kernel
node asks. Theorem 2 follows from Theorems 3 and 1: with b the rebuild's
branches, F_b is the rebuild R and F_(b∘σ) is K itself, so
K (K v) = F_(b∘σ) (K v) is, by Theorem 3 applied to the branches b∘σ
(whose swap is b), F_b v = R v, and R v = v by Theorem 1. A library may
therefore state the involution as derived from the fusion and the
reflection.

## Plain fields in Theorems 2 and 3

Theorems 2 and 3 are written for a type whose fields are all recursive. With
plain fields, read every F° w_j, K° v_j and F°_b w_j at a plain position as
w_j or v_j itself (the branch passes a plain field on untouched, R f = f),
and drop the induction hypothesis there: a plain field is substituted and
never folded, on both sides alike, so the two sides meet at the same term
position by position. Theorem 3 then needs σ to keep plain and recursive
positions in place, which the definition of σ asks.

## Theorem 4 (assertions with a canonical condition)

The assertions of the standard library's DSL may
use a second kind of handler, which takes a recursive field apart once more
to exclude a case:

    H_i = \f. (S f) B_1 ... B_k,    each B_l either [] or \g_1 ... \g_n. C_i (C_l g_1 ... g_n),

S being `self` (or `self self`) and n the number of fields of C_l. Such an
assertion A is the generator G of the Definitions with these handlers in
place of the rebuild's; its knot and unfolded knot A° are as in "The
unfolded knot". The CANONICAL VALUES of A are the canonical values of T in
which no node C_i w has a recursive field w whose head C_l has B_l = [] in
H_i. For binary: even's handler is `\h. (S h) [] (\g. even (even g))
(\g. even (odd g))`, so even zero is not canonical.

For every canonical value v of A, A° v →β* v, and so A v →β* v.

Proof. By induction on v = C_i v_1 ... v_m. For a constructor with rebuild
handlers the step is Theorem 1's. For a handler of the second kind, Lemma 1's
first steps give (A° w) B'_1 ... B'_k, w the field it takes apart and B'_l
the B_l under the substitution of the knot. By the induction hypothesis
A° w →β* w, and by congruence the term reduces to w B'_1 ... B'_k. Since v
is canonical, w = C_l u_1 ... u_n with B_l not [], and w applied to the
branches reduces, by n + k beta steps, to B'_l u_1 ... u_n, which reduces by
n beta steps to C_i (C_l u_1 ... u_n) = C_i w = v. ∎

Corollary (idempotence, T4). For every canonical value v of A,
A (A v) and A v are beta equal: both reduce to v. As an equation lemma,
`X^(A @ (A @ X)) = X^(A @ X)`, the premise being that the reader reads X as a
finite canonical value of A, so the inner A @ X is the asserted argument
and the theorem applies to the outer one.

The theorem needs B_l to rebuild exactly C_i (C_l g_1 ... g_n), each g_j in
its place. A branch that rebuilds anything else (a handler that permutes
the fields, or wraps one in a further S) is outside it; the compiler can
check the shape syntactically when it reads the type_case rows.

## Length of the chains

The chain of Theorem 1 has at most 2m + k + 3 beta steps per constructor
of v with m fields (three to unfold the knot and take the argument, m + k
to take the constructor apart, m to rebuild it), and the chain of
Theorem 2 at most twice that, so both are finite and
linear in the size of v. A checker that accepts the equation F v = v for a
given v asserts the existence of a finite chain of beta steps, which is
what a node of `lambda_jit_derivation_kernel` means (its module comment,
A NODE MEANS): no eta step and no merge is used.

## The premise cannot be dropped

Both theorems need v to be a finite canonical value.

- An open argument: for a fresh atom p, F° p →β+ p B'_1 ... B'_k by (U),
  and p B'_1 ... B'_k is a normal form different from p, so by Boehm's
  theorem F p = p is not an equation of lambda beta eta. The same holds for
  any closed term that is not a value of T, for instance F° (\x. x).
- An infinite value: for a cyclic datum v = C_i v (built with a fixpoint
  combinator), the induction has no base, and F° v unfolds forever without
  reaching v syntactically. A checker must therefore read the argument as
  a finite tree of constructors, within a bound, and refuse it otherwise.

In particular the law is not the unconditional equation
F (assert_T x) = assert_T x for every x: outside the protocol, where x is
not built from T's constructors, assert_T x need not lack a head (a λ-definable
assertion can only confirm a member positively). The premise is the finite canonical
argument, checked on the argument itself.
