# The certificate cycle conjectures are consistent, for every cycle length

A written proof, 2026-09-28, for
the conjectures of the class CERTIFICATE CYCLE on the points

    typing_natural_cycle_three    (Count = 3)
    typing_natural_cycle_five     (Count = 5)

(`corpora/contest_certificate_cycles.pl`), each with the three scored
conjectures `member(1, natural)`, `member(2, natural)` and `member(2,
stream)`. The proof extends certificate_collapse
(`doc/proofs/certificate_ghost_solutions.md`, cited as THE CERTIFICATE
PROOF) from its two points, whose members form
cycles of length 1 (H22) and 2 (H24), to a cycle of any length Count >= 1.
Only the section of THE CERTIFICATE PROOF that names its points (section
2, the reduct M') depends on the point; this document gives that section
for a cycle, and shows that its reduct lies in the set S_W of section 3,
whose grammar already allows the nesting a cycle needs. Sections 1 and 3
to 7 of THE CERTIFICATE PROOF then apply unchanged.

THEOREM. For every Count >= 1 and every closed beta eta normal term W,
lambda beta eta + (M = V_W) is consistent, where M is the term of the
point with Count members and V_W = \sel. sel I W.

COROLLARY. All three claims of both points are consistent: W = \a. \b.
\c. c gives the two natural claims, W = \a. \b. \c. b the stream one
(THE CERTIFICATE PROOF, section 7, word for word). Since the judging
theory is now lambda beta, note that lambda beta + E is a
subtheory of lambda beta eta + E, so consistency in lambda beta eta gives
it in lambda beta.

## 1. The term

In `corpora/contest_certificate_cycles.pl` the judgment is H22's and
H24's, reused unchanged (`cycle_judgment_generator/2` is
`judgment_generator/2` of `contest_hard_clauses.pl` with the cycle's member
in place of the symbol or the pair):

    J   = (\l. JG (l l)) (\r. JG (r r))
    JG  = \judge. \s. (tag s) ((base s) N (judge ((method s) Member[judge]))) ((judge s) F)
    M   = (\judge. judge Member[judge]) J

and the member Member[judge] is the knot `(\l. CG (l l)) (\r. CG (r r))`
of the generator (`cycle_member_generator/3`, `chained_member/4`,
`member_passing/3`)

    CG  = \self. m_0
    m_i = (true, \that. identity_of (judge that) m_(i+1), false)   for i < Count - 1
    m_(Count-1) = (true, \that. identity_of (judge that) self, false)

so m_0 passes m_1, ..., and the last member passes self, the knot itself.
For Count = 1 this is H22's symbol generator SG, and for Count = 2 H24's
pair generator PG (THE CERTIFICATE PROOF, section 2).

## 2. The reduct M'

As in THE CERTIFICATE PROOF, contract inside every abstraction every
redex except the two self-applications of each knot: the selectors,
`identity_of` (`p T` after one step), the triples (`\sel. sel t m b`), JG
and CG applied to `l l`. The result is M' = u0 s0 with u0 = Jh Jh, s0 = K0
K0, s1 = K1 K1 and Jh exactly as there, and

    K0     = \y. tau_0
    tau_i  = \sel. sel T (\that. u0 that T tau_(i+1)) F    for i < Count - 1
    tau_(Count-1) = \sel. sel T (\that. u0 that T (y y)) F

(in K1, `l l` stands where K0 has u0). For Count = 1 this is THE
CERTIFICATE PROOF's K0 for H22, and for Count = 2 its K0 for H24. The
first beta step at the root gives `J Member[J]`, the others are inside,
so M ->>b M'.

## 3. M' is a member of S_W

In the grammar of THE CERTIFICATE PROOF, section 3,

    sigma  ::= y y | K K' | tau
    tau    ::= \sel. sel T Mth F
    Mth    ::= \that. MB[that]
    MB[t]  ::= u t T sigma | Obs[t] T sigma
    K      ::= \y. \sel. sel T (\that. MB_y[that]) F

"where in K the sigma of MB_y (and of the tau inside it, at any depth)
may be y y". Each `\that. u0 that T tau_(i+1)` is a Mth whose MB is the
first alternative `u t T sigma` with u = u0 (closed, a u) and sigma =
tau_(i+1); the innermost Mth has sigma = y y. So tau_(Count-1) is a tau
whose sigma is y y, each tau_i with i < Count - 1 is a tau whose sigma is
the tau tau_(i+1), and K0 = \y. tau_0 is a K, with y y at depth Count - 1
of the nested taus, which the clause "at any depth" admits. The same
holds for K1 with the u `l l` inside Jh. So s0 = K0 K0 is a sigma, and
M' = u0 s0 is a member by rule (C) (u closed, z = s0 a subject, since
every sigma is a subject).

Nothing else in sections 3 to 6 of THE CERTIFICATE PROOF refers to the
number of members: the closure under beta and eta (section 4) is proved
for the grammar, whose tau and K alternatives cover every depth; the
parsing and non-member facts (section 5) and the collapse (section 6) are
proved for the grammar as well. Hence S_W, with M' in it, satisfies the
hypotheses of the lemma of section 1, and lambda beta eta + {P = V_W | P
in S_W} is consistent and proves M = M' = V_W. Section 7 of THE
CERTIFICATE PROOF then gives the three claims. That ends the proof.

## 4. Scope

- Both points, and every Count >= 1, are covered by the same argument;
  settings succeeded on the three conjectures of
  typing_natural_cycle_three (local readings on c28404d5e: 27 to 56 ms)
  and were stopped on typing_natural_cycle_five.
- As in THE CERTIFICATE PROOF, the "trap" member(2, stream) is a scored
  claim here, consistent by the same theorem with the stream
  certificate's W.
