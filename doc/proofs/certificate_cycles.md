# The certificate cycles are consistent for every certificate

A written proof, 2026-09-28, for
the conjectures of the class CERTIFICATE CYCLE on the points

    typing_natural_cycle_three    (Count = 3)
    typing_natural_cycle_five     (Count = 5)

(`corpora/contest_certificate_cycles.pl`), and for every Count >= 1 the
corpus's `typing_cycle/2` builds. Each point has the three scored claims
`member(1, natural)`, `member(2, natural)` and `member(2, stream)`, whose
tests are those of H22 and H24:

    member(1, natural)   \a. M (\i. \w. i a)
    member(2, natural)   \a. M (\i. \w. w y1 y2 a)
    member(2, stream)    \a. M (\i. \w. w y1 a y2)

with y1, y2 free.

THEOREM. For every Count >= 1, with M the term `typing_cycle(Count, M)`
builds, and every closed beta eta normal term W, lambda beta eta +
(M = V_W) is consistent, where V_W = \sel. sel I W.

COROLLARY. The three claims of both points are consistent, by the
argument of section 7 of `doc/proofs/certificate_ghost_solutions.md`
(cited below as THE CERTIFICATE PROOF): W =
\a. \b. \c. c for the two natural claims and W = \a. \b. \c. b for the
stream claim.

The only proof it uses is THE CERTIFICATE PROOF. Other proofs of the same
conjectures are `doc/proofs/individual_certificate_cycles_consistency.md`.

The proof is THE CERTIFICATE PROOF with its section 2 replaced by
section 1 below. Count = 1 is H22's term and Count = 2 is H24's; the set
S_W of THE CERTIFICATE PROOF, section 3, already contains the reduct for
every Count, so its sections 3 to 7 apply unchanged (section 2 below).

## 1. The terms

In `corpora/contest_certificate_cycles.pl`, the judgment is H22's and
H24's with the member replaced (`cycle_judgment_generator/2`), and the
point is `(\judge. judge Member[judge]) J` (`typing_cycle/2`). So, with the
notation of THE CERTIFICATE PROOF, section 1:

    J   = (\l. JG (l l)) (\r. JG (r r))
    JG  = \judge. \s. (tag s) ((base s) N (judge ((method s) Member[judge]))) ((judge s) F)
    M   = (\judge. judge Member[judge]) J

where Member[judge] is the knot `(\l. CG (l l)) (\r. CG (r r))` of
`cycle_member_generator/3`: CG = \self. m_0, with the members

    m_i       = (true, \that. identity_of (judge that) m_(i+1), false)    for i < Count - 1
    m_(Count - 1) = (true, \that. identity_of (judge that) self, false)

built inside CG (`chained_member/4`, `member_passing/3`), so that m_0
passes m_1, ..., and the last member passes self.

THE REDUCT M'. Contract, inside every abstraction, every redex except the
two self-applications of each knot, as in THE CERTIFICATE PROOF, section
2. The result is M' = u0 s0 with

    u0 = Jh Jh        Jh = \l. \s. s Sel1 (s Sel3 N (l l (s Sel2 s1))) (l l s F)
    s0 = K0 K0        s1 = K1 K1

and, for a judgment u (u0 in K0, and `l l` in K1),

    K[u]  = \y. \sel. sel T (\that. u that T C_(Count - 1)[u]) F
    C_0[u]       = y y
    C_(j + 1)[u] = \sel. sel T (\that. u that T C_j[u]) F

K0 = K[u0] and K1 = K[l l]. For Count = 1 this is H22's K0 of THE
CERTIFICATE PROOF, section 2, and for Count = 2 it is H24's. The member
triples become `\sel. sel T Mth F` after the contractions of
`identity_of p = p T` and of the triple, exactly as there. So M ->>b M'.

## 2. M' is a member of S_W

S_W is the set of THE CERTIFICATE PROOF, section 3, unchanged. M' = u0 s0
is a member by the rule (C) when u0 is a closed u and s0 a subject. u0 =
Jh Jh is a closed u when Jh is a Jh of the grammar. s0 = K0 K0 is a sigma,
so a subject, when K0 is a K. Jh's body is an Obs_l over s whose Y is
`l l (s Sel2 s1)`, a `u E'` with u = `l l`, so it needs s1 = K1 K1 to be a
sigma, that is K1 a K, with u = `l l` inside Jh.

K[u] IS A K, for u a closed u or `l l` inside Jh. The grammar reads

    K      ::= \y. \sel. sel T (\that. MB_y[that]) F
    MB[t]  ::= u t T sigma | Obs[t] T sigma
    sigma  ::= y y | K K' | tau
    tau    ::= \sel. sel T Mth F
    Mth    ::= \that. MB[that]

"where in K the sigma of MB_y (and of the tau inside it, at any depth)
may be y y". By induction on j, C_j[u] is a sigma in which y y may stand:
C_0[u] = y y, the first alternative; C_(j + 1)[u] is a tau whose Mth is
`\that. u that T C_j[u]`, an MB of the first form with the sigma C_j[u].
So the body of K[u]'s method, `u that T C_(Count - 1)[u]`, is an MB_y, and
K[u] is a K. The depth of the nesting is Count - 1, which the words "at
any depth" admit for every Count.

The reductions of section 4 of THE CERTIFICATE PROOF that touch these
terms are `K K' -> tau`, which substitutes K' for y and turns the one y y
at the bottom of C_(Count - 1) into K' K', a sigma, and the steps inside
the taus, which are the steps of section 4 for a tau at any depth. So
sections 3 to 6 of THE CERTIFICATE PROOF hold for this S_W as written,
and by the lemma of its section 1, lambda beta eta + {P = V_W | P in S_W}
is consistent and proves M = M' = V_W. Section 7 of THE CERTIFICATE PROOF
then gives the three claims.

THE CYCLE (for orientation; the proof does not depend on it). u0 s0
reduces by weak head steps through the judgments of s0, of the method's
result on m_1, ..., of the member that passes s0 again, a cycle of Count
laps through the members, each subject a term `u0 x T sigma` whose head
is the judgment. The judgment reads only the first member of what it
gives back (`identity_of`), so the certificate's second member W is never
read, which is why every W is a solution.

## 3. A mechanical check

Not part of the proof: a script outside the repository, the one of THE
CERTIFICATE PROOF, section 8, with its builder of M' generalized to the
K[u] and C_j[u] of section 1,

- checked, for Count = 1, 2, 3 and 5, that M' as written in section 1 is
  the term obtained from the point's term (`lambda_term/2` of
  `typing_natural_symbol`, `typing_natural_pair`,
  `typing_natural_cycle_three` and `typing_natural_cycle_five`) by
  contracting every redex innermost first except self-applications: equal
  in all four cases;
- ran the membership test of THE CERTIFICATE PROOF's grammars,
  unchanged, on M': it accepts M' for Count = 3 (2777 nodes) with the
  natural W, and for Count = 5 (6305 nodes) with both W; with both W it
  rejects T, F, I and the two W.
