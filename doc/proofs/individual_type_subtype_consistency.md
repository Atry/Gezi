# Consistency of both booleans on the two type-subtype points

Claim. For each of `type_periods_subtype_small` and `type_recomputed_index_subtype`, with M
the point's program, both scored tests are consistent with lambda beta eta:
boolean(true), T = \a. M a y, and boolean(false), T = \a. M y a (y free). As in the
other proofs of this directory it suffices that lambda beta eta + (M = v) is consistent for v = true
and for v = false.

## 1. The lemma and two standard facts

The lemma is the one of `individual_path_rebuilt_consistency.md`, Section 1: a set G of
closed terms that is closed under one-step beta eta (G1), whose members other than v are
applications (G2), and that is closed under replacing an occurrence of a member by v
(G3), makes lambda beta eta + {N = v : N in G} consistent. We give such a G(v)
containing M. Two standard facts are used to read off the shapes of reducts:

- (A) If a term U (open or closed) reduces to an abstraction, its weak head reduction
  reaches an abstraction, and every abstraction among the reducts of U is a reduct of the
  FIRST abstraction on that weak head reduction (eta postponement, Barendregt 1984
  15.1.6: an eta step never turns an application into an abstraction; then beta
  standardization). In particular if that weak head reduction stops at a term whose head
  is a variable, no reduct of U is an abstraction.
- (B) If W ->> W' then W[z := a] ->> W'[z := a] (substitution lemma).

## 2. The program

From `contest_clauses.pl` (subtype, section 4), `contest_hard_clauses.pl` and
`prelude_clauses.pl` (T = \t.\f. t, F = \t.\f. f, I = \x. x, And = \p.\q. p q F,
Nil = \n.\c. n, Cons = \h.\t.\n.\c. c h t, Pair = \l.\r.\p. p l r, Y the prelude's
fixpoint, Eq the prelude's natural_equal, Scott numerals). Types are Scott data:
Nat = \t.\b.\f.\r. b 0 and a record with field list L is \t.\b.\f.\r. r L; a field
list is a Scott list of `Pair label type`.

    Check = Y (\self. \x. \y. y T BC FC RC)
      BC = \n. x F (\s. Eq s n) (\a.\r. F) (\l. F)
      FC = \ya.\yr. x F (\n. F) (\xa.\xr. And (self ya xa) (self xr yr)) (\l. F)
      RC = \yl. x F K1 K2 (\xl. Every xl yl)            K1 = \n. F, K2 = \a.\r. F
    Every = Y (\es. \h. \w. w T (\fd.\rt. fd (\lb.\ty. And (Find h lb ty) (es h rt))))
    Find  = Y (\fs. \fl. \lb. \ty. fl F (\hv.\hr. hv (\hl.\ht.
                  Eq hl lb (self ht ty) (fs hr lb ty))))
    M = Check X Y

(Every and Find have `self` free; they are rebuilt under each unfolding of Check.)

The two points differ only in X and Y. Write [l1: A1, l2: A2] for the field list
`Cons (Pair l1 A1) (Cons (Pair l2 A2) Nil)`, and [l: A] for `Cons (Pair l A) Nil`.

- periods (a = 1 `value`, b = 0 `next`): X = Y (\s. R1) with Ri the record
  [a: Nat, b: R(i+1)], i = 1 .. 5, R6 = s; Y = Y (\s. S1) with Sj the record [b: S(j+1)],
  j = 1 .. 7, S8 = s.
- recomputed (a = 12 `head`, b = 13 `tail`): X = Op 3 with
  Op = Y (\s. \i. record [a: Nat, b: s (Pred (Succ i))]), Pred = \n. n 0 (\p. p);
  Y = Y (\s. record [a: Nat, b: s]).

In both, a /= b, every sub record type has the field list [a: Nat, b: X'] with X' again a
sub record type, and every super record type has the list [b: Y'] (periods) or
[a: Nat, b: Y'] (recomputed) with Y' again a super record type. The proof below uses only
this.

## 3. Components

Each component is the set of all beta eta reducts of the terms listed, hence closed under
reduction; parameters written with a variable give open components, and by (B) replacing
the variable by an element of the corresponding component maps an open component into
the closed one.

- Instances. QS: reducts of Check and of D D, where Check ->> ΦC (D D),
  D = \q. ΦC (q q), ΦC the body of Check's fixpoint. VS, FS: likewise for Every and Find
  with self := S0, S0 in QS.
- Types. XS (sub record types): periods, reducts of X, of Dx Dx and of Ri[s := Dx Dx]
  (Dx the fixpoint half of X); recomputed, reducts of O i with O a reduct of Op or of
  Do Do and i in Args, the least set containing 3 closed under beta eta and under
  i |-> Pred (Succ i). YS (super record types): likewise for Y. Nat is normal.
- Lists. LX: reducts of [a: Nat, b: X'], X' in XS; LX': reducts of [b: X']; LY: the
  super lists, reducts of [b: Y'] resp. [a: Nat, b: Y'] (Y' in YS); LY' (recomputed only):
  reducts of [b: Y']. Pairs: reducts of Pair l A. Labels: reducts of the numerals a, b.
- EQ(l1, l): reducts of Eq l1 l.
- Continuations (open): RR(x) reducts of RC (x and self := S0 substituted, yl bound);
  KR(W) reducts of `\xl. V xl W`; KF(h) reducts of the list continuation
  `\fd.\rt. fd (\lb.\ty. And (Fi h lb ty) (V h rt))`; KL(h, W') reducts of
  `\lb.\ty. And (Fi h lb ty) (V h W')`; KH(l, A) reducts of the pair-list continuation
  `\hv.\hr. hv (\hl.\ht. Eq hl l (Q ht A) (Fi hr l A))`; KX(l, A, L') reducts of
  `\hl.\ht. Eq hl l (Q ht A) (Fi L' l A)`; BB(x), FF(x) reducts of BC, FC.
- Auxiliary (closed calls that are not loops, each with a weak head normal form):
  DD, reducts of Q Nat Y0 (Y0 in YS) and of Fi Nil b Y0 (both reach F);
  CC, reducts of Fi L1 a Nat (L1 in LX; it reaches T: the a field's check Q Nat Nat
  reaches Eq 0 0, then T); EE, reducts of V L1 Nil (it reaches T).

Abstraction forms, by (A) (the first abstraction on each weak head reduction, and no eta
redex among them, since none ends in its bound variable): an abstraction in QS is
`\x. \y. y T B Fn R` (B in BB(x), Fn in FF(x), R in RR(x)); in VS `\h. \w. w T Kf`
(Kf in KF(h)); in FS `\fl. \lb. \ty. fl F Kh` (Kh in KH(lb, ty)); in XS
`\t.\b.\f.\r. r L1` (L1 in LX); in YS `\t.\b.\f.\r. r L2` (L2 in LY); a non-empty list
`\n. \c. c P L'` (P its first pair, L' its rest); a pair `\p. p l A`; the only
abstraction in EQ(a, b) is F and in EQ(b, b) is T; in DD it is F; in CC and EE it is T.

## 4. Stages

The CHAINS below list the stages of a call in weak head order. Each is read with its
parameters in the components named, OR with some of them variables (an OPEN stage); an
open stage whose operator is a variable has no root redex and ends its chain. So the
reducts of a continuation are its source's open stages under the binders, and, by (B),
applying it gives the closed stage with the argument substituted. A CALL POSITION of a
closed stage that holds a closed loop call (CHECK on XS x YS, EVERY on LX x (LY or LY'),
FIND on (LX or LX') x b x YS) is a SLOT, marked m; it admits any member of G(v).

CHECK(x0, y0), x0 in XS, y0 in YS:

    c1  Q x0 y0                                     Q in QS
    c2  (\y. y T B Fn R) y0                         B in BB(x0), Fn in FF(x0), R in RR(x0)
    c3  y0 T B Fn R
    c4  (\b.\f.\r. r L2) B Fn R, (\f.\r. r L2) Fn R, (\r. r L2) R
    c5  R L2
    c6  x0 F K1 K2 Kr                               Kr in KR(L2)
    c7  (\b.\f.\r. r L1) K1 K2 Kr, (\f.\r. r L1) K2 Kr, (\r. r L1) Kr
    c8  Kr L1                                       -> EVERY(L1, L2)

An element of RR(x0) is `\yl. S` with S an open stage c6 .. e3 (want list yl), or, once
x0 is a record, one of the eta reducts `V L1` and `\w. w T Kf` of `\yl. V L1 yl` and
`\yl. (\w. w T Kf) yl`; applied to L2 each gives a stage (c6 .. e3, resp. e1, e2).
An element of KR(L2) is `\xl. S` with S an open stage of EVERY(xl, L2).

EVERY(L1, W), L1 in LX, W in LY or LY' (first pair P = Pair l A, rest W'):

    e1  V L1 W                                      V in VS
    e2  (\w. w T Kf) W                              Kf in KF(L1)
    e3  W T Kf
    e4  (\c. c P W') Kf
    e5  Kf P W'
    e6  (\rt. P Kl) W'                              Kl in KL(L1, rt)
    e7  P Kl                                        Kl in KL(L1, W')
    e8  Kl l A
    e9  (\ty. S) A                                  S an open AND stage (lb := l)
    then the AND stages with (l, A):
      (l, A) = (b, Y'), W' = Nil:   AND m e | (\p. m p F) e | m e F       e in EE
      (l, A) = (a, Nat), W' in LY': AND c m | (\p. c p F) m | c m F | (\f. m) F
                                                                       c in CC

Here m is the loop call FIND(L1, b, Y') resp. EVERY(L1, W'). When W' is in LY'
(recomputed), KL(L1, W') holds the closed loop call EVERY(L1, W'); so its elements are
`\lb. \ty. S` with S among `AND f m | (\p. f p F) m | f m F`, f an open stage of
FIND(L1, lb, ty), m a slot. (f is never an abstraction, by (A): its weak head reduction
stops at Eq on the variable lb.)

FIND(L, b, Y0), L in LX or LX', Y0 in YS (first pair P1 = Pair l1 A1, rest L'):

    f1  Fi L b Y0                                   Fi in FS
    f2  (\lb. \ty. S) b Y0, (\ty. S) Y0             S an open stage f4 .. f11
    f4  L F Kh                                      Kh in KH(b, Y0)
    f5  (\c. c P1 L') Kh
    f6  Kh P1 L'
    f7  (\hr. P1 Kx) L'                             Kx in KX(b, Y0, hr)
    f8  P1 Kx                                       Kx as below
    f9  Kx l1 A1
    f10 (\ht. U C D) A1
    f11 the EQ stages:
      first pair, L in LX, (l1, A1) = (a, Nat), L' in LX':
        U d m | I m                         U in EQ(a, b), d in DD, m = FIND(L', b, Y0)
      second pair, L in LX', (l1, A1) = (b, X'), L' = Nil:
        U m d | (\f. m) d                   U in EQ(b, b), m = CHECK(X', Y0), d in DD

In f8 the continuation is `\hl. \ht. U C m` (first pair: U in EQ(hl, b),
C in reducts of Q ht Y0, m the slot FIND(L', b, Y0), which is closed once hr := L') or
`\hl. \ht. U C d` (second pair: d in DD). In f10, C[ht := Nat] is in DD, and
C[ht := X'] is a stage c1 .. c6 of CHECK(X', Y0) (C is an open stage of CHECK(ht, Y0),
which stops at `ht F K1 K2 Kr`).

## 5. The set G(v)

G(v) is the set of closed terms generated by

    m ::= a closed stage above (slots holding members m)
        | I m | (\f. m) d                  d in DD or d = F
        | v
        | e | (\f. e) F                    e in EE, only for v = true

M = Check X Y is the stage c1, so M is in G(v). A stage is (C) if its slot holds a (C)
term and (Z) otherwise (stages without a slot, and stages whose slot holds a (Z) term);
`I m`, `(\f. m) d` are as m; v, e, `(\f. e) F` are (C). Every stage has at most one slot.

## 6. (G1)

A redex lies inside a component (the result stays there; for a continuation, it is
another open stage under the binders, Section 4), inside a slot (induction on the term),
or at the root of a stage. The root steps are the transitions of the chains, read in
order: c1 -> c2 (Q = \x. \y. ...), c2 -> c3, c3 -> c4 -> c5 (y0 = \t.\b.\f.\r. r L2),
c5 -> c6 or e1 or e2 (the forms of R), c6 -> c7 -> c8 (x0 = \t.\b.\f.\r. r L1),
c8 -> an EVERY stage (Kr = \xl. S), e1 -> e2 -> e3 -> e4 -> e5 -> e6 -> e7 -> e8 -> e9 ->
an AND stage, f1 -> f2 -> f4 .. , f4 -> f5 -> f6 -> f7 -> f8 -> f9 -> f10 -> f11, each
by the abstraction form of its operator (Section 3) and the substitution rule of
Section 4; and

    AND m e -> (\p. m p F) e -> m e F      m e F with m = v:  T e F -> (\f. e) F -> e
                                                              F e F -> I F
    AND c m -> (\p. c p F) m -> c m F      c m F with c = T:  T m F -> (\f. m) F
    U d m with U = F: F d m -> I m         U m d with U = T:  T m d -> (\f. m) d
    I m -> m        (\f. m) d -> m         (\f. e) F -> e      e -> e' in EE

A stage whose operator is an auxiliary or EQ term has a root redex only when that term
is its only abstraction (T or F); `m e F` only when m = v, the only abstraction in
G(v). There is no eta redex at a stage: `\p. m p F`, `\p. c p F`, `\f. m`, `\f. e` and
the continuations do not end in their bound variable, except RR's two, listed.

## 7. (G2)

Every stage is an application, and so are `I m`, `(\f. m) d` and `(\f. e) F`; the only
abstraction in EE is T = v (v = true). So every member other than v is an application.

## 8. (G3)

Let N' be an occurrence in N of a member.

- (C) terms reduce to v: v; e ->> T; `(\f. e) F -> e`; `I m -> m`, `(\f. m) d -> m`;
  and a stage with a (C) slot follows its chain to the slot's collapse state: `m e F`
  gives `T e F ->> T` resp. `F e F ->> F`; `c m F ->> T m F ->> m`; `U d m ->> I m`,
  `U m d ->> (\f. m) d`; a stage whose slot sits in a continuation (e7 .. e9, f8 .. f10)
  reaches the AND or EQ stage first. So replacing N' by v is a beta eta reduction in
  place, and the result is in G(v) by (G1).
- (Z) terms have no weak head normal form: the weak head reduction of a (Z) stage runs
  along its chain (Section 6) to the next call, which is again a (Z) stage: c8 enters
  EVERY, e9 an AND stage whose weak head reduction is that of its slot (`m e F`) or,
  after c reaches T, the slot itself (`(\f. m) F -> m`), f10 an EQ stage whose U reaches
  F resp. T and then selects the slot (`I m -> m`, `(\f. m) d -> m`). So from every (Z)
  term the weak head reduction reaches, after at least one step, a (Z) term in head
  position; a (Z) term with the shortest weak head reduction to a normal form would give
  one with a shorter, a contradiction.

  Every closed subterm of a component element has a weak head normal form: instances
  (Y-built, one unfolding), types, lists, pairs, labels, Nat and the constants, the Eq
  calls on labels, the auxiliary calls (checks with a Nat side, finds on the empty list
  or for the label a, every on the empty list), and partial applications of these, whose
  heads are abstractions with more binders than arguments. The continuations hold loop
  calls only on their bound variables, except the two holding a closed loop call (KL
  with W' in LY', and the f8 continuation of the first pair), and there it is the slot.
  The parts of a stage other than its slot are component elements, constants, or partial
  applications with a weak head normal form, except `m e` in `m e F`, which is not a
  member (no production is a member applied to an element of EE: that would need
  `m' e' F` with e = F, and F is not in EE, whose elements reduce to T). So N' is N itself
  or sits at a slot, and a slot admits v.

## 9. Conclusion

For v = true and v = false, G(v) satisfies (G1) to (G3) and contains M, so
lambda beta eta + (M = v) is consistent, and both scored tests of
`type_periods_subtype_small` and `type_recomputed_index_subtype` are consistent. The
cycle context is the conjunction over the super record's fields: `m e F` with e the
empty conjunction (T), so T gives e ->> T and F gives F; in the recomputed point the head
field's check comes first, reaches T and selects the tail's conjunction. No atom and no
judge reading is used.
