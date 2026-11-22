# The FALSE ONLY conjectures of H29 and H30 are consistent

A written proof, 2026-09-28, for the
five scored conjectures of the class FALSE ONLY on the points

    probe_cycle_and_false    x = x false false
    probe_cycle_if_false     x = x false x
    probe_cycle_and_or       x = (x true x) false false
    value_map_two_cycle      x = x (\p. \q. true) false
    value_map_three_cycle    x = x (\p. \q. \r. \s. true) false

(`corpora/contest_hard_clauses.pl`, H29 and H30). Each point's term is
M = Y G, with Y the prelude's fixed point combinator and G the point's
body, and its scored claim is the template `boolean(false)`, the test
T = \a. M y a with y free (`corpora/contest_hard_claims.pl`). The claim is
that lambda beta eta + (T = \x. x) is consistent.

The proof has two parts: a general lemma (section 2), which turns a set of
closed terms with three properties into a consistent collapse onto a normal
form, and, for each point, an explicit set with those properties (section
3). Section 4 derives the claims.

## 1. Notation and the facts cited

Terms are the untyped lambda terms, taken modulo alpha conversion. A term
is CLOSED when it has no free variable. `true` = T = \t. \f. t and `false`
= F = \t. \f. f; I = \f. f. Y = \g. (\p. g (p p)) (\q. g (q q)), the
prelude's `fixpoint` (`corpora/prelude_clauses.pl`).

A POSITION of a term is a path to one of its subterm occurrences. For a
set S of closed terms, an S-OCCURRENCE of a term P is a position whose
subterm is a member of S; it is MAXIMAL when no other S-occurrence of P
lies strictly above it. Since members of S are closed, distinct maximal
S-occurrences are disjoint, and substitution into a term never changes a
subterm that is a member of S.

Reductions: ->b is one beta step, ->e one eta step (\z. P z -> P, z not
free in P). For a relation ->, ->> is its reflexive transitive closure and
->= its reflexive closure.

The facts cited:

- (F1) ->b is confluent, ->e is confluent and terminating, and ->>b
  commutes with ->>e: whenever P ->>b Q1 and P ->>e Q2 there is R with
  Q1 ->>e R and Q2 ->>b R (Barendregt, The Lambda Calculus, 1984,
  section 3.3).
- (F2) Hindley and Rosen: if two relations are confluent and their
  reflexive transitive closures commute, their union is confluent
  (Barendregt 1984, section 3.3).
- (F3) The Z property (Dehornoy and van Oostrom, "Z, proving confluence by
  monotonic single-step upperbound functions", 2008): a relation -> on a
  set is confluent when there is a map phi on that set such that every
  step P -> Q satisfies Q ->> phi(P) and phi(P) ->> phi(Q).
- (F4) Takahashi's complete development (Takahashi, "Parallel reductions
  in lambda-calculus", Information and Computation 118, 1995), P* defined
  by

      x* = x
      (\x. P)* = \x. P*
      ((\x. P) Q)* = P*[x := Q*]
      (P Q)* = P* Q*                  when P is not an abstraction

  satisfies: P ->>b P*, and P ->b Q implies Q ->>b P* and P* ->>b Q*.
- (F5) A lambda theory that does not equate `true` and `false` is
  consistent (it does not equate every pair of terms); and when a
  confluent relation generates a theory, two distinct normal forms of the
  relation are not equated by it.

Two small lemmas about complete development, each by induction on P
following the four clauses of (F4), with the substitution lemma
P[x := A][z := B] = P[z := B][x := A[z := B]] for closed B:

- (D1) If S is a closed term that is not an abstraction, then
  (P[z := S])* = P*[z := S*]. The only clause where the substitution could
  matter is (P1 P2) with P1 = z: P1[z := S] = S is not an abstraction, so
  no redex is created and the fourth clause applies on both sides.
- (D2) If V is a closed beta normal abstraction, then P*[z := V] ->>b
  (P[z := V])*. The one clause that differs is (z P2): (P[z := V])* =
  (V P2[z := V])* is the contraction of the redex V P2[z := V] with
  V's body left as it is (V is normal) and P2[z := V]* substituted,
  while P*[z := V] = V (P2*[z := V]) reaches it by that one beta step
  and the induction hypothesis on P2.

## 2. The collapse lemma

LEMMA. Let S be a set of closed terms and V a member of S that is a closed
beta eta normal form, such that

- (S1) S is closed under ->b and under ->e: a beta or eta step inside a
  member gives a member;
- (S2) S is closed under collapse: replacing any S-occurrence of a member
  by V gives a member;
- (S3) V is the only abstraction in S;
- (S4) `true` is not in S, and no closed subterm of `true` or of `false`
  other than V itself is in S.

Let ->d be the COLLAPSE step: replace one S-occurrence N with N != V by V.
Then ->bed = ->b U ->e U ->d is confluent, and when V = `false` the theory
lambda beta eta + {N = V | N in S} does not equate `true` and `false`.

PROOF. Three steps: ->bd is confluent by the Z property; ->e commutes with
->bd; Hindley and Rosen.

STEP 1: ->bd is confluent. For a term P let psi(P) be P with every maximal
S-occurrence replaced by V, and phi(P) = psi(P)* (F4). We show every step
P -> Q of ->bd satisfies Q ->>bd phi(P) and phi(P) ->>bd phi(Q), and
conclude by (F3).

Two observations used throughout.

- (O1) Q ->>d psi(P) whenever Q is obtained from P by a step that keeps
  every S-occurrence of P as an S-occurrence (possibly copied, possibly
  erased, possibly moved) and replaces the rest as psi does: each such
  occurrence is collapsed by a ->d step, or is V already.
- (O2) The COLLAPSE ARGUMENT. Let C[z1, ..., zm] be a term with distinct
  variables z1, ..., zm, each occurring once, and let E1, ..., Em be
  members of S. Then
  (C[E1, ..., Em])* ->>bd (C[V, ..., V])*. Proof: replace one Ei at a
  time. For Ei = V there is nothing to do. Otherwise Ei is not an
  abstraction (S3) and is closed, so by (D1)
  (C[..., Ei, ...])* = (C[..., zi, ...])*[zi := Ei*]; Ei* is a beta
  reduct of Ei, hence in S (S1), so each copy of it collapses to V by one
  ->d step (or is V), giving (C[..., zi, ...])*[zi := V], which reaches
  (C[..., V, ...])* by (D2).

The cases of a step P -> Q. Every step has its contracted redex, or its
collapsed occurrence, at one position p.

CASE A, p lies inside or at a maximal S-occurrence O of P (this covers
every ->d step, and every ->b step inside a member). Let N0 be the member
at O. The step changes N0 into N0', which is in S: by (S1) for a beta
step, and by (S2) for a collapse. Every other maximal S-occurrence of P is
unchanged in Q.

- Q ->>bd phi(P): by (O1), Q ->>d psi(P) (collapse N0' at O and every
  other maximal occurrence), and psi(P) ->>b psi(P)* = phi(P) (F4).
- phi(P) ->>bd phi(Q): in Q the occurrence O holds a member, but it may
  now lie strictly inside a larger maximal S-occurrence O+ of Q (a member
  E = K[N0'] whose context K surrounds O), which was not an S-occurrence
  of P. Only the subterms at O, inside it and above it differ between P
  and Q; those inside O lie in the member N0' at O, so every other maximal
  S-occurrence of Q is one of P.
  Hence psi(Q) is psi(P) with the subterm at O+ replaced by V, and that
  subterm of psi(P) is E with O and the maximal S-occurrences of P inside
  K collapsed to V: a member E0 by (S2). Writing psi(P) = C[E0] and
  psi(Q) = C[V], (O2) gives phi(P) = psi(P)* ->>bd psi(Q)* = phi(Q). When
  no larger occurrence appears, psi(Q) = psi(P) and phi(Q) = phi(P).

CASE B, a ->b step whose redex R = (\x. U) W lies in no S-occurrence of P
(R itself is not a member, and no member contains it). The members inside
U, inside W and outside R are the maximal S-occurrences, and none of them
is the redex's operator: that operator is an abstraction, which by (S3) is
an S-occurrence only if it is V, and V then stays V under psi. So psi(P)
has the redex R' = (\x. psi(U)) psi(W) at p, and contracting it gives
T0 = psi(P) with psi(U)[x := psi(W)] at p. Since members are closed,
T0 is exactly Q with every copy of every maximal S-occurrence of P
collapsed: the occurrences inside W are copied once per free occurrence of
x in U (or erased when there is none), and those in U and outside R are
kept.

- Q ->>bd phi(P): Q ->>d T0 by (O1), each copy of an occurrence of P being
  a member collapsed by a ->d step; and psi(P) ->b T0, so by (F4)
  T0 ->>b psi(P)* = phi(P).
- phi(P) ->>bd phi(Q): by (F4), phi(P) = psi(P)* ->>b T0*. Every
  maximal S-occurrence of Q is a copy of one of P, or a NEW region: one
  strictly inside the contractum, created by the substitution (for
  example, (\x. K (x x)) X contracts to K (X X), and X X may be a member
  though neither K nor X was), or one around the contractum (a member
  containing it); the positions outside the contractum and not above it
  hold the subterms they held in P. At a new region, T0 holds the member
  of Q found there with the copies of P's occurrences inside it collapsed,
  a member E0 by (S2). So psi(Q) is T0 with each new region E0 replaced by
  V, and (O2) gives T0* ->>bd psi(Q)* = phi(Q).

This exhausts the steps of ->bd. In the terms of the peaks: a beta/beta
peak is resolved by case B for both steps (outside the members) or case A
(inside); a beta/delta peak whose collapsed occurrence is copied or erased
by the beta step is case B, the copies being collapsed in (O1); a
beta/delta peak whose beta redex lies inside the collapsed member, or is
the member itself, is case A; a delta/delta peak is case A for both
steps, whether the two occurrences are disjoint or one contains the other.
The Z property needs only the single-step inequalities above for every
step, and yields confluence.

STEP 2: ->>e commutes with ->>bd. By (F1) ->>e commutes with ->>b; it
remains to show that ->>e commutes with ->>d, for which it suffices by
Hindley's lemma (Barendregt 1984, section 3.3: if every peak
Q1 <-1 P ->2 Q2 has R with Q1 ->>2 R and Q2 ->=1 R, then ->>1 and ->>2
commute), taking ->1 = ->d and ->2 = ->e, that every peak
Q1 <-d P ->e Q2 has R with Q1 ->e= R and Q2 ->d= R. Let the collapsed occurrence be O, holding
N in S, N != V, and the eta redex \z. U z at position p.

- O and p disjoint: the two steps commute, R the result of both.
- p inside O: the eta step is inside the member N, and gives N' in S by
  (S1). Q1 has V at O; Q2 has N' at O, which collapses to V (or is V).
  R = Q1.
- O inside U (the eta redex contains the member, not as the whole of U):
  after the eta step the member is still at its place in U; collapse it.
  Q1 ->e R and Q2 ->d R, R = P with the eta step made and N replaced by V.
- O is U itself, the redex being \z. N z, a term outside S whose eta
  reduct N lands in S: Q1 = P with \z. V z at p, and Q1 ->e P with V at p;
  Q2 = P with N at p, and Q2 ->d P with V at p. Both reach R = P with V
  at p.
- O is the eta redex itself: impossible, the redex is an abstraction
  other than V (V is eta normal), and S has no such member (S3).

STEP 3. ->b U ->d is confluent (step 1), ->e is confluent (F1), and their
reflexive transitive closures commute (step 2 and the commutation of
->>e with ->>b and with ->>d, which compose); by (F2), ->bed is confluent.

THE THEORY. ->bed generates the theory lambda beta eta + {N = V | N in S},
since every collapse is an instance of an equation N = V, and each
equation is a collapse step. `true` and `false` are ->bed normal: they are
beta and eta normal, `true` has no S-occurrence (S4: neither it nor its
one closed subterm, itself, is in S), and `false`'s closed subterms are
`false` = V, which no ->d step rewrites, and I, not in S (S4). They are
distinct, so by confluence and (F5) the theory does not equate them. END.

## 3. The five sets

For each point, G = \x. Body(x) and M = Y G. The fixed point combinator's
reducts are named once:

    W_g  = \q. g (q q)                    (g a variable)
    Y_k  = \g. g^k (W_g W_g)              k >= 0; Y_0 = Y (alpha)
    X    = \q. G (q q)                    = W_g with G for g
    X'   = \q. Body(q q)                  X with its one redex G (q q)
                                          contracted

Y_k has exactly one redex, W_g W_g, which gives Y_{k+1}. X' is beta
normal and X has only the redex G (q q), since each Body below is beta
normal and so are its closed constants. So

    Y_k G ->b Y_{k+1} G        (inside Y_k)
    Y_k G ->b G^k (X X)        (the root; for k = 0 the term X X)
    H H'  ->b H1 H' or H H1'   (inside: X to X')
    X H   ->b G (H H)          (the root)
    X' H  ->b Body(H H)        (the root)
    G N   ->b Body(N)          (the root)

for H, H' in {X, X'}. None of Y_k, W_g, X, X', G, and none of the point's
constants below, is an eta redex (their bodies are not of the form U z
with z not free in U), so the terms below have no eta redex at all and
(S1) for ->e holds vacuously.

In every point V = `false` = F. Each set S is the LEAST set of terms
closed under the listed rules; every rule builds a closed term from
closed ones, so S consists of closed terms. The common rules are

    (R0) F in S
    (R1) Y_k G in S for every k >= 0      (M = Y_0 G is in S)
    (R2) H H' in S for H, H' in {X, X'}
    (R3) if N in S then G N in S          (G^k (X X) is in S by R2, R3)

and each point adds the rules for the terms its Body builds.

PROBE_CYCLE_AND_FALSE, Body(x) = x F F.

    (R4) if N in S then N F F in S
    (R5) I F in S

PROBE_CYCLE_IF_FALSE, Body(x) = x F x.

    (R4) if N, N' in S then N F N' in S
    (R5) if N in S then I N in S

PROBE_CYCLE_AND_OR, Body(x) = (x T x) F F.

    (R4) if N, N' in S then (N T N') F F in S
    (R5) if N in S then (I N) F F in S
    (R6) if N in S then N F F in S
    (R7) I F in S

VALUE_MAP_TWO_CYCLE, Body(x) = x A F with A = \p. \q. T;
VALUE_MAP_THREE_CYCLE, the same with A = \p. \q. \r. \s. T.

    (R4) if N in S then N A F in S
    (R5) I F in S

CHECKING (S1) to (S4). The argument is the same for the five points; the
per-point steps are written out.

(S3) Every term the rules R1 to R7 build is an application; R0 builds F. So
F is the only abstraction in S.

(S4) `true`: every member is F or an application, and T is neither. I is
an abstraction other than F, so not in S by (S3). (The constants T and A
occur inside members but are not members.)

(S1), beta. By induction on the rule that puts a term in S, every one-step
beta reduct of a member is a member. A redex of a member lies either inside
a member it was built from (then the reduct is the same rule applied to a
reduct, a member by induction), or inside a constant (F, I, T, A, G, X, X',
Y_k: only X and Y_k have redexes, covered by the table above), or at the
root of the member or of one of its applications. The root redexes:

- R1, R2, R3: by the table, Y_k G gives Y_{k+1} G (R1) or G^k (X X) (R2,
  R3); X H gives G (H H) (R3 over R2); X' H gives Body(H H), and G N gives
  Body(N), which are built by the point's own rules (R4) from members
  (H H by R2, N by hypothesis).
- A member whose head is F applied to arguments: for and_false,
  N F F with N = F is F F F, whose one redex F F gives I, and I F is R5;
  I F gives F (R0). For if_false, F F N' gives I N' (R5), and I N' gives
  N' (a member). For and_or, (F T N') F F gives (I N') F F (R5), which
  gives N' F F (R6); F F F (R6 with N = F) gives I F (R7), and I F gives F.
  For value_map_two and value_map_three, F A F gives I F (R5), which gives
  F.
- No other root redex: every other application in these rules has as its
  operator a member that is not an abstraction (S3), or an application.

(S2), collapse. First, the S-occurrences of a member are the members it
was built from (and theirs, by induction) and the occurrences of the
constant F, which collapse to themselves. The other subterms of a member
are of three kinds, none a member:

- open terms (they contain q or g bound in X, X', W_g, Y_k, or x in G);
- the closed constants other than F: Y_k, X, X', G, I, T, A, \q. T (in
  A) and the like, all abstractions other than F (S3);
- a proper prefix of an application a rule builds: N F and I (in N F F
  and I F, and_false); N F and I (if_false); N T, N T N', (N T N') F, I N
  and (I N) F, N F and I (and_or); N A and I (value_map). None of these is
  a member. By (S3) I is not. For the others, a member's last argument
  is fixed by the rule that built it: G N and I N end with a member, H H'
  with X or X', Y_k G with G, and the point's own rules with F (and
  (N T N') F F with F too). A prefix ending with T, with A, or with the
  building member N' of if_false's N F N' (when N' is not F) matches no
  rule. A prefix ending with F, as N F, would have to be built by one of
  the point's rules as N0 F F, N0 F N0', (N0 T N0') F F, (I N0) F F,
  N0 A F or I F; comparing the spines, that needs N = N0 F (a member
  of the form N0 F, shorter), N = I, N = N0 T N0' or N = N0 A, none of
  which is a member, by induction on the size of the member for the first
  and by the last-argument argument for the others.

So collapsing an S-occurrence of a member collapses one of its building
members, or a member inside one of them. Collapsing a member N inside a term built by a rule
gives the same rule applied to V = F in place of N, a member by R0 and the
rule: G F (R3), F F F (R4), F F N' and N F F (if_false R4), (F T N') F F
and (N T F) F F (R4), (I F) F F (R5) and F F F (R6), F A F (R4); and for
I F, I N (R5), the argument F or N collapsed gives I F, a member. The
members built by R1 and R2 contain no member but F: their subterms Y_k, G,
X, X', W_g are abstractions other than F, and so not members (S3), and
their applications are open (they contain the bound q or g).

## 4. The claims

For each of the five points, M = Y_0 G is in its set S (R1), and V =
`false`. By the lemma, lambda beta eta + {N = F | N in S} is consistent,
and it proves M = F. In it, for every term y,

    T y = (\a. M y a) = \a. F y a = \a. a

by two beta steps (F y a ->b (\f. f) a ->b a). So it proves \y. T = \y. \x. x,
the universal closure of T = \x. x: lambda beta eta + (T = \x. x) is a
sub-theory of a consistent theory, hence consistent. The scored
conjecture `boolean(false)` holds on each of probe_cycle_and_false,
probe_cycle_if_false, probe_cycle_and_or, value_map_two_cycle and
value_map_three_cycle.

The lemma's form: consistency by confluence of beta, eta and a collapsing
rule, the collapse by the Z property.

## 5. A mechanical check of the sets

Not part of the proof: a script outside the repository enumerated, for
each of the five points, the first 4000 terms reached from M by beta steps
and collapse steps (breadth first, terms of at most 400 nodes), and
checked each against the rules of section 3. Every term reached was a
member, no closed subterm of a reached term was a member abstraction other
than `false`, and `true` and I were not members.
