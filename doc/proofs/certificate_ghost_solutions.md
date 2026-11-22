# The certificate conjectures of H22 and H24 are consistent, and so is the stream trap

A written proof, 2026-09-28, for
the six conjectures of the class CERTIFICATE MEMBER on the points

    typing_natural_symbol    (H22)
    typing_natural_pair      (H24)

(`corpora/contest_hard_clauses.pl`). Each point has the scored claims
`member(1, natural)` and `member(2, natural)` and the trap `member(2,
stream)` (`corpora/contest_hard_claims.pl`). With M the point's term, the
tests are

    member(1, natural)   \a. M (\i. \w. i a)
    member(2, natural)   \a. M (\i. \w. w y1 y2 a)
    member(2, stream)    \a. M (\i. \w. w y1 a y2)

with y1, y2 free, and each claim says that lambda beta eta + (test =
\x. x) is consistent.

THEOREM. For each of the two points and every closed beta eta normal term
W, lambda beta eta + (M = V_W) is consistent, where

    V_W = \sel. sel I W                    (I = \x. x)

COROLLARY. All three claims of both points are consistent: the two scored
claims with W = \a. \b. \c. c (V_W is then the natural certificate), and
the trap with W = \a. \b. \c. b. So the trap `member(2, stream)` is not a
trap: its test is consistent (section 7).

The proof follows `doc/proofs/both_booleans_path_family.md` (cited as
THE PATH PROOF): a set S_W of closed terms that contains
a beta reduct of M and satisfies the hypotheses of the collapse lemma
(section 1), given by grammars (sections 2 and 3), checked in sections 4
to 6.

## 1. Notation and the lemma

Notation and the facts (F1) to (F5), (D1), (D2) are those of
`doc/proofs/false_only_small_cycles.md`, section 1. Application associates
to the left. The constants:

    T = \t. \f. t      F = \t. \f. f      I = \x. x
    Sel1 = \t. \m. \b. t      Sel2 = \t. \m. \b. m      Sel3 = \t. \m. \b. b
    N = \sel. sel I (\a. \b. \c. c)        (the natural certificate)

An object `(t, m, b)` of the corpus is `\sel. sel t m b`; its tag, method
and base are read by applying it to Sel1, Sel2, Sel3. Note that \i. \w. w,
the corpus's `(\i. \w. w)` in J's else branch, is F, and that
`identity_of p = p (\i. \w. i) = p T`.

THE LEMMA. The collapse lemma of `false_only_small_cycles.md`, section 2,
as restated in THE PATH PROOF, section 1, for a value V: its proof uses of
V only that it is a closed beta eta normal abstraction (for (D2) and for
the eta case "O is the eta redex itself"), and, in the paragraph THE
THEORY, that `true` and `false` are normal forms of ->bed: they are beta
eta normal and each of their closed subterms (T, F, I, all abstractions)
is V, which no collapse step rewrites, or, by (S3), not in S. V_W is a
closed beta normal abstraction for every closed normal W, and it is eta
normal (its body `sel I W` does not end with `sel` applied as the last
argument), and it is none of T, F, I. So:

LEMMA. Let W be closed and beta eta normal, and S a set of closed terms
with V_W in S, satisfying (S1) closure under ->b and ->e, (S2) closure
under collapse (replacing an S-occurrence of a member by V_W gives a
member), and (S3) V_W is the only abstraction in S. Then lambda beta eta +
{P = V_W | P in S} is consistent.

## 2. The terms

In `corpora/contest_hard_clauses.pl`, with `object_triple`,
`identity_of`, `symbol_generator`, `symbol_of`, `judgment_generator`,
`natural_judgment`, `pair_member_generator`, `pair_member_of`:

    J   = (\l. JG (l l)) (\r. JG (r r))
    JG  = \judge. \s. (tag s) ((base s) N (judge ((method s) Member[judge]))) ((judge s) F)
    M   = (\judge. judge Member[judge]) J

with `tag s = s Sel1`, `method s = s Sel2`, `base s = s Sel3` after one
beta step each, and Member[judge] the point's member built over the
variable judge: for H22 the symbol `(\l. SG (l l)) (\r. SG (r r))`,
`SG = \self. (true, \that. identity_of (judge that) self, false)`; for H24
the member a, `(\l. PG (l l)) (\r. PG (r r))`, `PG = \self. (true, \that.
identity_of (judge that) (true, \that. identity_of (judge that) self,
false), false)`.

THE REDUCT M'. Contract, inside every abstraction, every redex except the
two self-applications of each knot (the redexes `(\l. X (l l)) (\r. X (r
r))`): the selectors, `identity_of`, the triples, JG and SG (or PG)
applied to `l l`. The result is M' = u0 s0 with

    u0 = Jh Jh        Jh = \l. \s. s Sel1 (s Sel3 N (l l (s Sel2 s1))) (l l s F)
    s0 = K0 K0        s1 = K1 K1

where K1 is K0 with l l for judge, and, for H22,

    K0 = \y. \sel. sel T (\that. u0 that T (y y)) F

and for H24

    K0 = \y. \sel. sel T (\that. u0 that T (\sel. sel T (\that. u0 that T (y y)) F)) F

(in K1, `l l` stands where K0 has u0). So M ->>b M'. The first beta step
at the root gives `J Member[J]`, the others are inside.

THE CYCLE (for orientation; the proof does not depend on it). u0 s0
reduces by weak head steps to `u0 (u0 s0 T s0)`: the tag of s0 is T, its
base F, and its method applied to s0 is `u0 s0 T s0`. Every judgment of
a subject then reads the subject's tag, and the subject is `u0 s0 T s0`,
whose head is the judgment again: the weak head reduction of M never
ends, and the terms it passes through have the shapes of section 3.

## 3. The sets

THE FAMILIES. In the grammars below, a and a' range over ARBITRARY terms
whose free variables are among those bound around them, x and y, l, s,
sel, that are bound variables, and a primed letter is another member of
the same family, chosen independently.

Judgments, the first two alternatives closed, the third inside a Jh:

    u   ::= Jh Jh' | Lam          (closed)     |  l l   (inside Jh, l its variable)
    Jh  ::= \l. \s. Obs_l[s]
    Lam ::= \s. Obs[s]

Observations and subject expressions, over a variable subject s (bound by
Lam, Jh, or a method's `that`):

    E[s]   ::= s | E[s] Sel2 sigma
    Obs[s] ::= E[s] Sel1 X1[s] a
    X1[s]  ::= E[s] Sel3 a Y[s]
    Y[s]   ::= u E'[s] | Obs'[s]       with E'[s] not s itself (E'[s] = E[s] Sel2 sigma),
                                        Obs'[s] an Obs whose first E is such an E'

(Obs_l, E_l, X1_l, Y_l are the same with u = l l.)

Symbol values, with an optional variable y (inside a knot half):

    sigma  ::= y y | K K' | tau
    tau    ::= \sel. sel T Mth F
    Mth    ::= \that. MB[that]
    MB[t]  ::= u t T sigma | Obs[t] T sigma
    K      ::= \y. \sel. sel T (\that. MB_y[that]) F

where in K the sigma of MB_y (and of the tau inside it, at any depth) may
be y y, and elsewhere sigma is not y y. s0 and s1 are sigmas, K0 is a K,
u0 a u, and M' = u0 s0.

The selector chains, for Mth a closed Mth (the reducts of `tau Seli` other
than itself):

    R1 ::= Sel1 T Mth F | (\m. \b. T) Mth F | (\b. T) F | T
    R2 ::= Sel2 T Mth F | T Mth F | (\b. Mth) F | Mth
    R3 ::= Sel3 T Mth F | F Mth F | I F | F

(`Sel1 T = \m. \b. T`, `Sel2 T = \m. \b. m = T`, `Sel3 T = \m. \b. b =
F`, `F Mth = I`.)

Closed SUBJECTS:

    z ::= sigma | P T sigma | T I W sigma | F W sigma | I sigma | z Sel2 sigma | R2 sigma

with P a member (below). `V_W T sigma` is `P T sigma` with P = V_W; it
reduces through `T I W sigma`, `F W sigma` (T I = \f. I = F), `I sigma`
to sigma.

THE SET. S_W is the least set of terms closed under

    (V)   V_W
    (C)   u z                       u closed, z a subject
    (O1)  z Sel1 P a                z a subject, P in S_W
    (O3)  z Sel3 a P
    (D1)  R1 P a                    P in S_W
    (D3)  R3 a P
    (K)   (\f. P) a
    (I)   I P

Every rule builds a closed term from closed ones. M' = u0 s0 is a member
by (C).

## 4. (S1) and (S3)

(S3). Every rule other than (V) builds an application, so V_W is the only
abstraction in S_W.

(S1), beta. By induction on the derivation of a member, every one-step
beta reduct of a member is a member. A redex lies inside an argument a
(the reduct is another arbitrary term), inside a family member, inside a
member P a rule was applied to (induction), or at the head of a spine.

THE FAMILIES ARE CLOSED UNDER BETA:

- u: `Jh Jh' -> Lam`: substituting Jh' for l turns every `l l` into
  `Jh' Jh'`, a u, and every u-position of Obs_l into a closed u.
- Y[s]: `u E'` with u = Jh Jh' reduces inside u; with u = Lam,
  `Lam E' -> Obs[E']`, the second form (the subject variable of Lam's Obs
  becomes the subject expression E', and E[E'] is again a subject
  expression over s).
- MB[t]: `u t` with u = Lam gives `Obs[t]`, the second form.
- sigma: `K K' -> tau` (K' substituted for y turns y y into K' K', a
  sigma; MB_y becomes an MB).
- No other application of the grammars is a redex: the rest have a
  variable (s, l, sel, that, y) or an application at their head, or are
  the redexes listed.

THE SUBJECTS ARE CLOSED UNDER BETA: inside sigma, P, or z (the families,
the induction); `V_W T -> T I W`, `T I -> F`, `F W sigma -> I sigma`,
`I sigma -> sigma`; `tau Sel2 -> Sel2 T Mth F`, and along R2 to Mth;
`Mth sigma' -> MB[sigma']`, which is `u sigma' T sigma` or `Obs[sigma'] T
sigma`, of the form `P T sigma` with P = `u sigma'` (C) or P =
`Obs[sigma']` = `sigma' Sel1 X1[sigma'] a` (O1, since X1[sigma'] =
`sigma' Sel3 a Y[sigma']` is (O3) and Y[sigma'] is (C) or (O1)).

THE HEAD REDEXES OF THE MEMBERS:

- (C) u z with u = Lam: `Obs[z]` = `E[z] Sel1 X1[z] a`, (O1): E[z] is a
  subject (a subject followed by `Sel2 sigma` steps), X1[z] is (O3) over
  the member Y[z] ((C) or (O1)).
- (O1) z Sel1 P a, (O3) z Sel3 a P: a redex at the head of z is a subject
  step (above); when z = tau, `tau Sel1 -> Sel1 T Mth F` (D1),
  `tau Sel3 -> Sel3 T Mth F` (D3).
- (D1) along R1 to `T P a -> (\f. P) a` (K) `-> P`.
- (D3) along R3 to `F a P -> I P` (I) `-> P`.
- (K) -> P; (I) -> P.

So every beta reduct of a member is a member.

(S1), eta. The abstractions of the grammars and rules are V_W, T, F, I, the
selectors, Jh, Lam, Mth, K, tau, `\m. \b. T`, `\b. T`, `\b. Mth`, `\f. P`
and those inside arbitrary terms. None is an eta redex outside the
arbitrary terms: their bodies end with an argument other than the bound
variable (`l s F`, `a` in Obs where a may mention s but the operator does
too, `sigma` in MB, `F` in tau and K, `W` in V_W) or are not applications
(`\f. P`: P is closed, so it is not `Q f`). Eta steps inside arbitrary
terms give arbitrary terms.

## 5. The shape of members, and non-members

PARSING A SPINE. Every closed application is `h c1 ... cm` with h a closed
abstraction. We read the arguments of a member left to right in STATES:

- a CORE is the head with the arguments of one of the forms

      Jh Jh' z  |  Lam z                              -> member
      K K'  |  tau                                    -> subject
      V_W T sigma | T I W sigma | F W sigma | I sigma -> subject
      R2 sigma (as `Sel2 T Mth F sigma`, `T Mth F sigma`,
        `(\b. Mth) F sigma`, `Mth sigma`)             -> subject
      R1 P a (and the R1 chain) | R3 a P (and the R3 chain)
        | (\f. P) a | I P                             -> member
      V_W                                             -> member

- then STEPS: from a subject, `Sel1 P a` or `Sel3 a P` give a member, and
  `Sel2 sigma` gives a subject; from a member, `T sigma` gives a subject.

A term is a member exactly when it parses to a member: this is the
grammar of section 3 read along the spine (a subject `P T sigma` is a
member P followed by the step `T sigma`).

EVERY u, Lam, Mth AND sigma CONTAINS A BETA REDEX. A sigma is `K K'`, a
redex, or tau, which contains a Mth. A Mth's body is `u t T sigma` or
`Obs[t] T sigma`, and an Obs contains X1 and so a Y; following the second
alternative of Y down (each Obs' is smaller) ends at a Y of the form
`u E'`, and every closed u is a redex `Jh Jh'` or a Lam, and `Lam E'` is a
redex. So W, being normal, is none of them, and neither are T, F, I and
the selectors.

UNIQUENESS OF THE PARSE. THE HEADS. Write a closed abstraction as
`\x1. ... \xk. B` with B not an abstraction (k its leading abstractions,
B its body). The heads of the cores:

    head         k  body B
    Jh           2  x2 applied to Sel2 sigma pairs, then Sel1, X1, a
    \b. Mth      2  x2 applied to Sel2 sigma pairs, then Sel1, X1, a, T, sigma;
                    or a closed-headed application `u x2 T sigma`
    K            2  x2 applied to T, an abstraction, F
    T, F         2  the variable x1, x2
    Lam          1  x1 applied to Sel2 sigma pairs, then Sel1, X1, a
    Mth          1  x1 applied to Sel2 sigma pairs, then Sel1, X1, a, T, sigma;
                    or `u x1 T sigma`, headed by a closed term
    tau          1  x1 applied to T, Mth, F
    V_W          1  x1 applied to I, W
    \f. P        1  P itself, a closed application, when P is a member other
                    than V_W (members other than V_W are applications)
    \f. V_W      2  x2 applied to I, W
    I            1  the variable x1
    Sel1, 2, 3   3  the variable x1, x2, x3
    \b. T        3  the variable x2: this is Sel2 (the same term)
    \m. \b. T    4  the variable x3

Two heads with the same k are told apart by their bodies: a variable body
against an application; among applications, a variable head against a
closed head; among variable heads, by the arguments read from the left.
Jh against `\b. Mth` and Lam against Mth: both read the `Sel2 sigma`
pairs (the odd arguments up to the first Sel1 are Sel2, fixing the number
of pairs), then `Sel1 X1 a`, after which the Mth bodies have two more
arguments. K, tau, V_W have T, T, I as their first arguments, the others
Sel1 or Sel2. So each head is of exactly one row, except that `\b. T` IS
Sel2, taken up next.

THE CORES WITH A SHARED HEAD are told apart by their first two arguments:

- Sel2: `Sel2 T Mth F sigma` (R2, a subject) and `Sel2 F P a` (the R1 state
  `(\b. T) F P a`, a member): first argument T against F.
- T: `T I W sigma` (a subject), `T Mth F sigma` (R2), `T P a` (R1's last
  state): first argument I, a Mth, a member. I is not a Mth (a variable
  body), and neither I nor a Mth is a member (abstractions other than
  V_W, by (S3)).
- F: `F W sigma` (a subject), `F Mth F a P` (R3), `F a P` (R3's last
  state). The second argument is a sigma, F, a member respectively: F is
  not a sigma (it has no redex) and not a member (S3), and no sigma is a
  member (N1).
- I: `I sigma` (a subject), `I P` (a member), `I F a P` (R3): a sigma, a
  member, F, pairwise disjoint as above.
- V_W: `V_W` (a member) and `V_W T sigma` (a subject), which is the member
  V_W followed by the step `T sigma`: the same parse.

THE STEPS are told apart by their first argument: from a subject, Sel1,
Sel2 or Sel3; from a member, T. The positions of an arbitrary a are
consumed without looking at them, and the other arguments are checked
against their families (a sigma, a member). Since the parse is
deterministic left to right, the parse of a proper prefix of a spine is
the prefix of the parse of the spine, stopped where the prefix ends.

NON-MEMBERS. By induction on size:

- (N1) no sigma and no subject is a member: a sigma is `K K'`, whose parse
  ends in the subject state, or tau, an abstraction other than V_W; a
  subject's parse ends in the subject state, and by uniqueness it has no
  other parse.
- (N2) a proper prefix of a member's spine is a member exactly when the
  parse of the member is in the member state at the end of the prefix.
  Otherwise the prefix stops inside a core, inside a step, or in the
  subject state: `Jh Jh'` (a u), `P T`, `P T sigma`, `z Sel2`, `z Sel1 P`,
  `z Sel3 a`, `Sel1 T`, `Sel1 T Mth` and the like are not members.

## 6. (S2)

Let P be a member and O an S-occurrence in P holding a member Q != V_W.
Then O is one of:

- (a) P itself: the collapse gives V_W.
- (b) inside an arbitrary argument a: the result is another arbitrary
  term.
- (c) inside or at a member argument of a rule (the P of O1, O3, D1, D3,
  K, I, of a subject `P T sigma`): by induction on the derivation, the
  collapse gives a member there, and the rule applies again (with P =
  V_W the subject `V_W T sigma` is one of the subjects).
- (d) a proper prefix of P's spine, `h c1 ... cj` of `h c1 ... cm`: by
  (N2) the parse of P is in the member state after cj, so `c(j+1) ... cm`
  is a sequence of steps that the parse reads from the member state (each
  step reads only its own arguments). After the collapse the spine is
  `V_W c(j+1) ... cm`: V_W is a member core, and the same steps from the
  member state lead to the same final state as in P, the member state.
- (e) any other closed subterm of P: the closed subterms of the families
  other than arbitrary terms and members are abstractions (Jh, Lam, K,
  tau, Mth, T, F, I, the selectors, W and its subterms), not members
  unless V_W (a collapse of V_W is not a step), and the closed
  applications `Jh Jh'` (a u), `K K'` (a sigma), the subjects and their
  prefixes, the chain terms `Sel1 T Mth F` and their prefixes, all
  non-members by (N1) and (N2); `P T sigma` and its prefix `P T` are a
  subject and a prefix of one. W is closed and normal, so its closed
  subterms are abstractions (a closed normal application would have a
  variable at its head); none is V_W, since W is a proper subterm of V_W.

So every collapse of a member is a member: (S2) holds.

## 7. The claims

By sections 4 to 6, S_W satisfies the hypotheses of the lemma of section 1
and contains M' (section 3), so lambda beta eta + {P = V_W | P in S_W} is
consistent and proves M = M' = V_W (M ->>b M', section 2). In it, for all
terms y1, y2, a:

    M (\i. \w. i a)          = (\i. \w. i a) I W        = I a    = a
    M (\i. \w. w y1 y2 a)    = W y1 y2 a
    M (\i. \w. w y1 a y2)    = W y1 a y2

With W = \a. \b. \c. c the first two are a, and with W = \a. \b. \c. b
the first and the third are a. So each test equals \a. a in a consistent
extension of lambda beta eta, and each of the six claims (three per point)
is consistent. The trap `member(2, stream)` is therefore a consistent
test on both points: the stream certificate's second member is a ghost
solution of the cycle as the natural certificate is, and nothing in the
cycle tells the two apart, since the judgment only ever reads the first
member (`identity_of`) of what it gives back.

## 8. A mechanical check

Not part of the proof: a script outside the repository

- built M' as written in section 2 (from the definitions of Jh, K0, K1,
  u0, s0, for both points) and checked that it is the term obtained from
  the point's term (`lambda_term/2` of `contest_hard`) by contracting every
  redex innermost first except self-applications, so M ->>b M' by beta
  steps only;
- implemented the grammars of section 3 as a membership test and, for
  both points and both W (natural and stream), ran random walks of up to
  300 steps from M', taking the weak head step with probability 0.6 and
  otherwise a random beta, eta or collapse step of a proper subterm (H22:
  80 walks, 2139 terms, 117 collapses, and 60 walks weighted to collapses,
  1142 terms, 102 collapses; H24, whose terms grow faster: 52 walks, 1102
  terms, 13 collapses). Every term met was a member; T, F, I and the two
  W were not.
