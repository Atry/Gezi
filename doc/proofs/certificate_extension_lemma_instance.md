# The certificate extension `lemma_instance` is sound

Written 2026-09-29, as the first extension of the certificate mechanism
and as its template. A hand proof, not machine-checked.

## The rule

The checker is `prolog/gezi/certificate_extensions/lemma_instance.pl`.
A node `node(N, Term, Head, extension(lemma_instance, instance(L, σ)))` is
accepted when both of these hold:
- L is a node checked before N;
- Term and Head are L's term and head with each parameter atom
  `atom(parameter(k))` named by σ replaced by the term σ(k).

Here σ is a finite map from numbers to terms of the certificate.

## The meaning to preserve

Every node of the kernel means the following (the kernel's module comment,
"A NODE MEANS"). Read the terms through the readback of IR terms, with every
atom read as a free variable. Then Term reaches Head by a chain of equations
of lambda beta kappa delta and of selections, each selection replacing one
occurrence of a merge by one of its members. Eta is no step of such a
chain; it enters only the readings of normal form certificates.

## The meta-theorem

**Lemma (substitution).** Let a chain lead from a term A to a term B, and let
σ substitute terms for free variables. Then a chain leads from A[σ] to B[σ].

*Proof.* Induction on the chain. The equations of lambda beta kappa delta
are closed under substitution:
- every rule (β, κ, δ, the congruences) holds for all terms;
- an equation M = N gives M[σ] = N[σ] by the same derivation with σ applied
  throughout: β commutes with capture-avoiding substitution, and κ
  (`(L : M) N = L : M`) and δ (`(L : M).L = M`) are schemes over all terms,
  so their instances under σ are instances again.

For a selection, let A = C[{M1, …, Mn}] become C[Mi]. The substitution maps
the occurrence to {M1[σ], …, Mn[σ]} in C[σ], a selection of Mi[σ] is
available there, and it gives C[Mi][σ]. The merges inside σ's terms are
not touched, on either side of the step. ∎

**Theorem.** If the lemma node L is sound, so is every instance node.

*Proof.* L is checked by the kernel, so its term reaches its head by a
chain. The parameter atoms are free variables of that chain. The instance's
term and head are L's under σ, by the check, so the lemma gives the
instance's chain. The IR readback commutes with the substitution:
- a parameter atom occurs only as a term of the store, never inside a code,
  since codes hold instructions only;
- replacing it in every capture, application, definition, selection and
  merge layer is therefore the substitution of the readback. ∎

## What the kernel still checks

The instance is only as good as the lemma. The lemma is an ordinary node,
checked by the kernel's own rules with its parameters as atoms. A lemma
whose chain uses a property of a parameter (its head, its shape) is
rejected when it is checked, because an atom has no head but itself. So an
instance never assumes anything of σ's terms. This is the difference from
the descending cycles of Theorem 4 of `certificate_meta_lemmas.md`, whose
case analysis on a data parameter needs the canonical-value check.
