# The certificate extension `congruence` is sound

Written 2026-10-01, a part of the rewriting framework's reference implementation. A
hand proof, not machine-checked. The template is
`certificate_extension_lemma_instance.md`.

## The rule

The checker is `prolog/gezi/certificate_extensions/congruence.pl`. A
node `node(N, Term, Head, extension(congruence, rewritten(M, Ps)))` is
accepted when all of these hold:
- M is a node checked before N, its term is Term, and its head is R;
- Ps is a list of nodes checked before N; write (t_P, h_P) for the term and
  head of P;
- the walk AGREES on the pair (R, Head), where the walk on a pair (A, B) of
  Ids of the kernel's store is:
  - A and B are the same Id: agree;
  - (A, B) is (t_P, h_P) for some P in Ps: agree;
  - otherwise A's and B's layers are `closure(c, [a1..an])` and
    `closure(c, [b1..bn])` with one code Id c, or `apply(a1, a2)` and
    `apply(b1, b2)`, or `definition(l, a1)` and `definition(l, b1)`, or
    `field_selection(a1, l)` and `field_selection(b1, l)`, or
    `merge([a1..an])` and `merge([b1..bn])`, and the walk
    agrees on every pair (ai, bi). Any other pair rejects.

A pair met twice is walked once; the memo changes nothing below, since the
walk on a pair is a function of the pair.

A node `node(N, Term, Head, extension(congruence, joined(L, R)))` is accepted
when L and R are nodes checked before N, L's term is Term, R's term is Head,
L and R have one head, and Head is SET-FREE: no layer of Head, and no
instruction of a code Head holds (inner closures' codes included), is a
merge.

## The meaning to preserve

Every node of the kernel means: read the terms through the readback of IR
terms, every atom read as a free variable; then Term reaches Head by a chain
of equations of lambda beta kappa delta and of selections, each selection
replacing one occurrence of a merge by one of its members
(`lambda_jit_derivation_kernel`, A NODE MEANS). Eta is no step of such a
chain.

## The readback as a context

The readback ⟦·⟧ of a store term is defined layer by layer:
⟦apply(f, a)⟧ = ⟦f⟧ ⟦a⟧, ⟦definition(l, v)⟧ = l : ⟦v⟧,
⟦field_selection(s, l)⟧ = ⟦s⟧.l, ⟦merge([e1..en])⟧ = ⟦e1⟧ ∪ … ∪ ⟦en⟧,
an atom is a free variable, and ⟦closure(c, [a1..an])⟧ is the lambda term of
the code c with its i-th capture replaced by ⟦ai⟧, capture-avoidingly (the
kernel's I2 and the readback of codes it rests on). In every case the
readback of a layer is a fixed CONTEXT, determined by the constructor and,
for a closure, by its code, applied to the readbacks of the subterms: a term
with holes, each hole filled by one subterm, a hole occurring once, several
times (a capture the code reads twice) or not at all (a capture it never
reads).

**Lemma 1 (the walk is a multi-hole context).** If the walk agrees on (A, B),
there are a context C with holes x1, …, xk and premises P1, …, Pk of Ps
such that ⟦A⟧ = C[t_P1, …, t_Pk] and ⟦B⟧ = C[h_P1, …, h_Pk].

*Proof.* By induction on the walk, which is finite: the store is acyclic
(terms are interned bottom-up), so every pair the walk enters is a pair of
strictly smaller terms. Equal Ids: C is ⟦A⟧ with no hole. A premise pair: C
is a single hole. Otherwise A and B have one layer context D (one
constructor, one code, one label, one length), and the induction hypothesis
gives a context Ci for each pair (ai, bi); C is D with its i-th hole filled
by Ci, the holes of the Ci renamed apart. A capture's hole may occur several
times in D or not at all; so does Ci in C, which leaves the equations
⟦A⟧ = C[t…] and ⟦B⟧ = C[h…] intact. ∎

**Lemma 2 (chains are closed under contexts).** If a chain leads from t to h,
then for every context C with one hole, possibly occurring several times or
under binders, a chain leads from C[t] to C[h].

*Proof.* Replace the occurrences one at a time, each by the chain from t to
h lifted into the context. A lifted equation step is an equation step: the
equations of lambda beta kappa delta form a congruence, the xi rule included,
and t and h have no free variable bound by C's binders, since a capture is
substituted capture-avoidingly into the code's body and atoms are never
bound. A lifted selection is a selection, because a selection may be made
under any constructor (the kernel's module comment). ∎

**Lemma 3 (a chain from a set-free term is an equation).** Let T be
set-free, and let a chain lead from T to X. Then T and X are equal in lambda
beta kappa delta, by a chain without selection.

*Proof.* Read merges as inert constructors: M1 + … + Mn is never a redex, nor
the function of a redex, nor the subject of a delta step. Lambda beta kappa
delta with inert constructors is an orthogonal combinatory reduction system,
so it is confluent (Klop, van Oostrom and van Raamsdonk, Combinatory
reduction systems: introduction and survey, Theoretical Computer Science
121, 1993, doi:10.1016/0304-3975(93)90091-7). A reduct of a set-free term
is set-free: a contraction builds its result from the redex's parts, and
code instantiation from the code's instructions, which hold no set either
(this is why the check walks the codes).

We show by induction along the chain T = T0, T1, …, Tn = X that every Ti is
beta equal to T. An equation step keeps it. Let Ti = C[S] become Ti+1 = C[Mj]
by a selection, S = M1 + … + Mm. By the hypothesis and confluence, Ti and T
have a common reduct R, and R is set-free because T is. So a reduction
sequence ρ leads from C[S] to R, and every residual of the occurrence S along
ρ is erased by the end, R holding no set. Follow ρ from C[Mj] instead,
dropping every step made inside a residual of S and replacing each residual
of S by the matching copy of Mj: since S is inert, no step of ρ has a residual
of S as its redex or its function, so every other step stays a step, and
every copy of Mj sits where a residual of S sat, which ρ erases. The
sequence ends at R. So Ti+1 =β R =β T. ∎

## The meta-theorem

**Theorem.** If the premises of a node the checker accepts are sound, so is
the node.

*Proof for `joined`.* L is sound, so Term reaches L's head, which is R's head
H. R is sound, so Head reaches H; Head is set-free, so by Lemma 3 Head and H
are equal by a chain without selection, and the reverse of that chain leads
from H to Head. Chains compose, so Term reaches Head. ∎

*Proof for `rewritten`.* M is sound, so Term reaches R. By Lemma 1, ⟦R⟧ = C[t_P1, …, t_Pk]
and ⟦Head⟧ = C[h_P1, …, h_Pk]. Each premise is sound, so t_Pi reaches h_Pi;
by Lemma 2, applied hole by hole with the other holes filled, a chain leads
from ⟦R⟧ to ⟦Head⟧. Chains compose, so Term reaches Head. ∎

The theorem rests on the kernel's own readback lemmas I1 and I2, which its
module comment marks unproved (FIXME of 2026-09-28). Beyond them, this
extension rests only on the confluence of orthogonal combinatory reduction
systems, which Lemma 3 cites.

## What it is for

The kernel's only congruence is the application's, which rewrites an
argument before it is planted. An induction lemma is certified by unfolding
it over the reader's finite tree: at a node C_i w of the tree, the
case's chain reaches the closure of C_i capturing F w, and the node of the
field w, checked before because the tree is unfolded bottom-up, proves that
F w reaches w. `rewritten` replaces the capture. The same justification
carries a lemma step at a position under a binder.

`joined` is the certificate side of the lemma step `joined(LeftSteps, RightSteps)`:
a lemma whose two sides only meet (fusion_binary), or one used from
right to left, is replayed as a node from each side to the meeting point.
The right side must be set-free because a selection cannot be reversed: from
a + b a chain reaches a, but no chain leads from a back to a + b.
