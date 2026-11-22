# The certificate extension `scott_binary_arithmetic` is sound

Written 2026-09-29. A hand proof, not machine-checked. The canonicity
argument of the definitional increment, plus and times on canonical Scott
binary naturals is that of the module comment of
`prolog/gezi/scott_binary_replacement.pl`; this document writes it out as a proof about beta equality and adds what the
checker needs around it.

## The rule

The checker is `prolog/gezi/certificate_extensions/scott_binary_arithmetic.pl`.
A node

    node(N, Term, Head, extension(scott_binary_arithmetic, Justification))

is accepted, for the operation `times` (the others below are alike), when
Justification is `times(Root, Function, Left, Right)` and all of the
following hold.

1. **The closure.** Root is a node checked before N whose term is
   `apply(TimesRoot, A)` and whose head is C, compared as Ids of the
   kernel's store. TimesRoot is the store term the checker builds from the
   definitional times term of this document (below), translated by
   `lambda_jit_surface:lambda_term/2` and `lambda_jit_defunctionalization:defunctionalized/2`
   exactly as the kernel builds a program's root. Function is a node
   checked before N whose head is C; its term F is the program's own
   function term, and Term is `apply(F, B)`. (F is C itself, by a value
   node, when the program holds the closure.)
2. **The operands are merge free and record free.** The checker walks the
   whole structure of A and of B in the store: every term layer, and every
   instruction of every code a closure among them holds. No layer is a
   solution set, a definition or a field selection, and no instruction is
   one.
3. **The operands are canonical binary naturals, read level by level.**
   Left is a list of nodes checked before N, one per level of A, and so is
   Right for B. With three atoms z, e and o fixed by the certificate for
   the operand (Left names them), the node of level i has the term
   `h_i z e o`, that is `apply(apply(apply(h_i, z), e), o)`, with h_0 = A,
   and its head is one of:
   - the atom z itself, and then level i is the last one;
   - `apply(e, h_{i+1})`, the atom e applied to exactly one argument;
   - `apply(o, h_{i+1})`, the atom o applied to exactly one argument.
   The three atoms are pairwise distinct and occur free in no h_i (the
   checker's walk of item 2 covers every h_i, which are subterms reached
   from the heads). An `e` level is never followed directly by the last
   level: the half of an even number is not zero.
4. **The head.** Head is the store term of the canonical numeral of n · m,
   built by the checker (below), n and m the naturals read in item 3.

The operations and their justifications:

| justification | Root's term | Term | Head |
|---|---|---|---|
| `increment(Root, Function, Left)` | IncrementRoot | `apply(F, A)` | ⟦n + 1⟧ |
| `plus(Root, Function, Left, Right)` | `apply(PlusRoot, A)` | `apply(F, B)` | ⟦n + m⟧ |
| `times(Root, Function, Left, Right)` | `apply(TimesRoot, A)` | `apply(F, B)` | ⟦n · m⟧ |

For increment, Root's head is C and its term is IncrementRoot itself; in
every row the Function premise's head is C.

## The meaning to preserve

Every node of the kernel means the following (`derivation_kernel.pl`, "A
NODE MEANS"): read through the readback of IR terms, with every atom read as
a free variable, Term reaches Head by a chain of lambda beta kappa delta
equations alternating with selections. There is no eta in a node's chain.

## Terms

The terms below are pure lambda terms. Z, E and O are the constructors of
the Scott binary naturals,

    Z = λz.λe.λo. z        E(h) = λz.λe.λo. e h        O(h) = λz.λe.λo. o h

with z, e, o not free in h. The canonical numeral ⟦n⟧ of a natural n is

    ⟦0⟧ = Z        ⟦2k⟧ = E(⟦k⟧) for k > 0        ⟦2k + 1⟧ = O(⟦k⟧)

so no canonical numeral holds `E(Z)`. Every ⟦n⟧ is closed and in beta
normal form.

The definitional terms are those of `corpora/contest_merge_dynamic.pl`
(increment_body/1, plus_body/2, times_body/3, doubled/3), which the checker
spells again for itself, and whose codes the gate compares with the
catalogue's (`doc/contest_api_catalogue.pl`, merge_api/4):

    IB      = λs.λn. n ⟦1⟧ (λh. O(h)) (λg. E(s s g))
    PB[i]   = λs.λa.λb. a b (λh1. b a (λk1. E(s s h1 k1)) (λk2. O(s s h1 k2)))
                            (λh2. b a (λk3. O(s s h2 k3)) (λk4. E(i (s s h2 k4))))
    D[z](x) = (λy. y z (λ_. E(y)) (λ_. E(y))) x
    TB[p, z] = λs.λa.λb. a z (λh1. D[z](s s h1 b)) (λh2. p b (D[z](s s h2 b)))

    Inc   = IB IB
    Plus  = PB[Inc] PB[Inc]
    Times = TB[Plus, Z] TB[Plus, Z]

    IncrementRoot = IB IB
    PlusRoot      = (λi. PB[i] PB[i]) (IB IB)
    TimesRoot     = (λi. (λp. (λz. TB[p, z] TB[p, z]) Z) (PB[i] PB[i])) (IB IB)

each binder of the two copies of a body renamed apart. Contracting the
outer redexes, IncrementRoot = Inc, PlusRoot →β Plus and TimesRoot →β*
Times.

## Lemma A (normalization of an application to a variable)

*If M x has a beta normal form, x a variable, then M has one.*

*Proof.* The leftmost reduction of M x reaches its normal form
(normalization theorem). While M is not in head normal form, M is
`(λy. P) Q R1 … Rk` and the leftmost redex of M x is M's head redex, so the
leftmost reduction of M x runs the head reduction of M, which therefore
ends, at a head normal form of M.
- If that head normal form is `y M1 … Mk`, the normal form of M x is
  `y N1 … Nk N'` with Mi →β* Ni, so every Mi has a normal form, and so has M.
- If it is `λy. P`, the leftmost reduction of M x goes on from `P[y := x]`,
  which therefore has a normal form. Substituting a variable for a variable
  creates no redex and removes none, so reductions of P and of `P[y := x]`
  correspond one to one, and P has a normal form; so has M. ∎

## Lemma B (the shape of a level)

*Let M be a pure lambda term, z, e, o pairwise distinct variables free
neither in M nor in H, and H a term with a beta normal form. If
M z e o =β e H, then M =β λz.λe.λo. e H. Likewise M z e o =β o H gives
M =β λz.λe.λo. o H, and M z e o =β z gives M =β λz.λe.λo. z.*

*Proof.* e nf(H) is a beta normal form and is beta equal to M z e o, so by
Church–Rosser M z e o →β* e nf(H). By Lemma A, applied three times, M has
a normal form N = λx1 … xk. y N1 … Nj, and N z e o →β* e nf(H).
- If k ≥ 3, N z e o reduces in three steps to
  λx4 … xk. (y N1 … Nj)[x1, x2, x3 := z, e, o], which is a normal form
  (substituting variables into a normal form leaves one). By uniqueness of
  normal forms it is e nf(H) up to α: k = 3, j = 1, y = x2 (a free y of N
  is free in M, so it is not e), and N1[x1, x2, x3 := z, e, o] ≡ nf(H).
  Since z, e, o are not free in H, hence not in nf(H), none of x1, x2, x3
  is free in N1, and N1 ≡ nf(H). So N ≡ λz.λe.λo. e nf(H) up to α, and
  M =β N =β λz.λe.λo. e H.
- If k < 3, N z e o reduces to (y N1 … Nj)[…] applied to the 3 − k atoms
  not taken, a normal form whose head is applied to j + 3 − k arguments.
  For it to be e nf(H), exactly one argument: k = 2, j = 0, and that
  argument, o, is nf(H); but o is not free in H. For k ≤ 1 there are at
  least two arguments.
The cases o and z are the same argument with the head x3, or x1 and j = 0.
∎

**Corollary (a read operand).** If the conditions of item 3 hold for A
with levels h_0 = A, …, h_L, the last level's head being z, then
A =β ⟦n⟧, n the natural read (an `e` level a bit 0, an `o` level a bit 1,
from the lowest bit up).

*Proof.* By induction from the last level up. h_L z e o =β z gives
h_L =β Z = ⟦0⟧ (Lemma B). If h_{i+1} =β ⟦k⟧, then h_{i+1} has a normal
form, and h_i z e o =β e h_{i+1} gives h_i =β E(h_{i+1}) =β E(⟦k⟧), which
is ⟦2k⟧ since k > 0 (item 3 rejects an `e` level above the last); the `o`
case gives ⟦2k + 1⟧. The premise nodes' chains are beta equations: the
terms they start from are merge free and record free (item 2), and beta
contraction of such a term leaves one, so the chains hold no selection, no
kappa and no delta step. ∎

## Lemma C (the definitional arithmetic)

*For all naturals n and m:*
1. *Inc ⟦n⟧ =β ⟦n + 1⟧;*
2. *Plus ⟦n⟧ ⟦m⟧ =β ⟦n + m⟧;*
3. *D\[Z](x) =β ⟦2k⟧ whenever x =β ⟦k⟧;*
4. *Times ⟦n⟧ ⟦m⟧ =β ⟦n · m⟧.*

*Proof.* Every step below is a beta contraction; ⟦n⟧ applied to three
arguments selects one branch.
1. Inc ⟦n⟧ →β ⟦n⟧ ⟦1⟧ (λh. O(h)) (λg. E(Inc g)). For n = 0 this is ⟦1⟧.
   For n = 2k, k > 0, it is O(⟦k⟧) = ⟦2k + 1⟧. For n = 2k + 1 it is
   E(Inc ⟦k⟧) =β E(⟦k + 1⟧) by induction (k < n), and that is ⟦2k + 2⟧
   since k + 1 > 0.
2. By induction on n. Plus ⟦n⟧ ⟦m⟧ →β ⟦n⟧ ⟦m⟧ X Y, X and Y the two branch
   functions with b := ⟦m⟧. For n = 0 it is ⟦m⟧. For n = 2h, h > 0, it is
   ⟦m⟧ ⟦n⟧ (λk1. E(Plus ⟦h⟧ k1)) (λk2. O(Plus ⟦h⟧ k2)): for m = 0, ⟦n⟧;
   for m = 2k, k > 0, E(Plus ⟦h⟧ ⟦k⟧) =β E(⟦h + k⟧) = ⟦n + m⟧, h + k > 0;
   for m = 2k + 1, O(⟦h + k⟧) = ⟦n + m⟧. For n = 2h + 1: for m = 0, ⟦n⟧;
   for m = 2k, k > 0, O(⟦h + k⟧) = ⟦n + m⟧; for m = 2k + 1,
   E(Inc (Plus ⟦h⟧ ⟦k⟧)) =β E(Inc ⟦h + k⟧) =β E(⟦h + k + 1⟧) (item 1) =
   ⟦n + m⟧, h + k + 1 > 0. The recursive calls have h < n.
3. D\[Z](x) →β x Z (λ_. E(x)) (λ_. E(x)) =β ⟦k⟧ Z (λ_. E(x)) (λ_. E(x)). For
   k = 0 it is Z = ⟦0⟧. For k > 0 it is E(x) =β E(⟦k⟧) = ⟦2k⟧.
4. By induction on n. Times ⟦n⟧ ⟦m⟧ →β ⟦n⟧ Z (λh1. D[Z](Times h1 ⟦m⟧))
   (λh2. Plus ⟦m⟧ (D[Z](Times h2 ⟦m⟧))). For n = 0 it is Z = ⟦0⟧. For
   n = 2h, D[Z](Times ⟦h⟧ ⟦m⟧) =β ⟦2hm⟧ by induction and item 3. For
   n = 2h + 1, Plus ⟦m⟧ (D[Z](Times ⟦h⟧ ⟦m⟧)) =β Plus ⟦m⟧ ⟦2hm⟧ =β
   ⟦m + 2hm⟧ = ⟦n · m⟧ by items 3 and 2. ∎

The terms returned where an argument is passed through unchanged (plus
returns b when a is zero) are the operands themselves; the Corollary gives
them as beta equal to canonical numerals, so no eta step enters.

## Lemma D (the head the checker builds)

*The store term the checker builds for ⟦n⟧ reads back as ⟦n⟧.*

The checker builds, with three fixed codes for each constructor,

    zero:  closure(Z1, [])        Z1 = code(closure(Z2, [argument]))
                                  Z2 = code(closure(Z3, [capture(0)]))
                                  Z3 = code(capture(0))
    even:  closure(E1, [K])       E1 = code(closure(E2, [capture(0)]))
                                  E2 = code(closure(E3, [argument, capture(0)]))
                                  E3 = code(apply(capture(0), capture(1)))
    odd:   closure(O1, [K])       O1 = code(closure(O2, [capture(0)]))
                                  O2 = code(closure(O3, [capture(0)]))
                                  O3 = code(apply(argument, capture(0)))

K the term built for the half, each code interned as a store layer
`code(Body)` whose inner closures name their codes by Id, as the kernel
stores codes.

*Proof.* By the readback of section 1 of the certificates design: a closure
`closure(C, Captures)` reads as an abstraction whose body is C's body read
with `argument` as the variable it binds and `capture(I)` as the readback of
the I-th capture. So `closure(Z1, [])` reads λx1. (λx2. (λx3. x1)), which is
Z up to α; `closure(E1, [K])` reads λx1. λx2. λx3. x2 K̄, with K̄ the
readback of K, which is E(K̄); and `closure(O1, [K])` reads
λx1. λx2. λx3. x3 K̄, which is O(K̄). By induction on the bits of n the
built term reads back as ⟦n⟧. The readback is the definition of what a
store term means; this lemma needs neither I1 nor I2. ∎

## The theorem

*If the kernel's nodes mean what the kernel says they mean, an accepted
node of this extension means it too: Term reaches Head by a chain, the
Function premise's chain followed by a beta equation.*

*Proof,* for times (increment and plus are alike, with Lemma C 1 and 2).
Root is a kernel node, so `TimesRoot′ A` =β C, where TimesRoot′ is the
readback of the term the checker built from the definitional term. By
Lemma I2 of the kernel (the readback of `defunctionalized/2`'s output is its
input), TimesRoot′ is TimesRoot. The chain of Root is a beta equation:
TimesRoot and A are merge free and record free (item 2, and the definitional
term holds no merge and no record), so it holds no selection, no kappa and
no delta. By the Corollary, A =β ⟦n⟧ and B =β ⟦m⟧. Then

    C B =β TimesRoot A B =β TimesRoot ⟦n⟧ ⟦m⟧ =β Times ⟦n⟧ ⟦m⟧ =β ⟦n · m⟧

by congruence (ν, μ), the reduction of TimesRoot to Times, and Lemma C 4;
and ⟦n · m⟧ is the readback of Head by Lemma D. The Function premise is a
kernel node: F reaches C by a chain, which may hold selections when F is
part of a program with merges. That chain made under `_ B` (selection and
every equation of the theory are congruences, as the kernel composes an
`application` node's premise under `_ Argument`) takes Term, `apply(F, B)`,
to `C B`, and the beta equation above takes `C B` to Head: a chain of the
kernel's meaning. ∎

**What the theorem rests on.** The readback of the premise nodes as chains
rests on the kernel's Lemmas I1 and I2, whose proofs are not written yet
(the FIXME of `derivation_kernel.pl`); the extension adds one more use of
I2, for the definitional root it builds, and none of I1. It does not rest
on anything the setting computes: the naturals n and m are read from the
premise nodes, and the product is Prolog's integer arithmetic.

**In a program with merges.** The extension's own step, `C B` to Head, is
a beta equation between merge free terms, which holds in Th(∅) and so in
any context (a finite beta reduction to a normal form); the selections of the node's chain are the Function
premise's, made in the program as the kernel's own nodes make them. So a
certificate of a program with merges may use the node wherever the kernel
would accept a node with the same term and head.
