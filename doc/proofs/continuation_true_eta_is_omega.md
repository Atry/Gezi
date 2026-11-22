# continuation_true_eta is Omega up to beta eta

A written proof, 2026-09-29: the two
conjectures of the point `continuation_true_eta` of
`corpora/contest_continuation_cycles.pl`, class continuation_both,

    boolean(true)    \a. M a y        (closed: \y. \a. M a y)
    boolean(false)   \a. M y a        (closed: \y. \a. M y a)

It uses one general theorem as a lemma, cited from its statement in the
design document: Omega is an easy term in lambda beta eta with sets
(`doc/proofs/omega_easy_beta_eta.md`, 2026-09-29: beta, eta and Omega -> N are confluent together, N any closed
term), so that lambda beta eta + (Omega = N) is consistent for every
closed N, also over the terms with sets.

## 1. The term

The point is M = Y G with (the corpus's `continuation_body/5` for
`continuation_true_eta`, and the prelude's `fixpoint`)

    Y = \g. (\p. g (p p)) (\q. g (q q))
    G = \x. \t. \f. x (\u. t u) f

## 2. M = Omega in lambda beta eta

G reduces to I = \z. z by three eta steps: \u. t u ->e t, then
\f. (x t) f ->e x t (f is not free in x t), then \t. x t ->e x:

    G ->e \x. \t. \f. x t f ->e \x. \t. x t ->e \x. x = I.

So M = Y G ->>e Y I, and

    Y I ->b (\p. I (p p)) (\q. I (q q))
        ->b (\p. p p) (\q. I (q q))
        ->b (\p. p p) (\q. q q) = Omega,

the last two steps contracting I (p p) -> p p and I (q q) -> q q inside
the two abstractions. Hence lambda beta eta proves M = Omega.

## 3. The claims

Let V be T = \t. \f. t or F = \t. \f. f. By the cited theorem,
lambda beta eta + (Omega = V) is consistent, and it proves M = Omega = V.
With M = T, M a y = T a y = a, so `\a. M a y = \x. x` holds and the
boolean(true) claim is consistent; with M = F, M y a = a, and the
boolean(false) claim is consistent. The closed programs
`\y. \a. M a y` and `\y. \a. M y a` equal `\y. \a. a` in the same
theories.

Over the terms with sets: the programs hold no set, so each
is in its own meaning (the clause pure), and it suffices that
Th({M = V}) is consistent over the terms with sets. Th proves M = Omega
by the steps of section 2 (beta and eta are among its rules), so
Th({M = V}) = Th({Omega = V}), consistent by the cited theorem, which is
stated for lambda beta eta with sets.

## 4. Scope

The argument uses only that G ->>be I. It covers every point of the
family whose G beta eta reduces to the identity, and no other. The other
five points of `contest_continuation_cycles.pl` do not: their G have the
beta eta normal forms \x. \t. x (\v. t) (continuation_true_constant),
\x. \t. x (\s. s t t) (continuation_true_pair),
\x. \t. \f. x t (\v. f) (continuation_false_constant),
\x. \t. \f. x (x t f) f (continuation_nested_true) and
\x. \t. \f. x t (x t f) (continuation_nested_false), none of them I, and
are left to `continuation_projection_collapse.md`.
