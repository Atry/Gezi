# Consistency of the five false-only conjectures

Claims: the scored conjecture `boolean(false)` (class `false_only`) of the
five points

- `probe_cycle_and_false`, `probe_cycle_if_false`, `probe_cycle_and_or` (H29),
- `value_map_two_cycle`, `value_map_three_cycle` (H30).

For a point whose term is M, the published test is T0 = `\a. M y a`, y free
(`corpora/contest_hard_claims.pl`, template `boolean(false)`), and the claim
is that lambda beta eta + (T0 = \x. x) is consistent. It is enough to show
that lambda beta eta + (M = F) is consistent, F = `\t. \f. f`: that theory
proves T0 = `\a. F y a` = `\a. a` by beta, so adding T0 = \x. x adds nothing.

References: H. P. Barendregt, *The Lambda Calculus, Its Syntax and
Semantics*, revised edition (1984): section 3.2 (parallel reduction,
Tait and Martin-Löf), section 3.3 (commuting relations, the Hindley-Rosen
lemma, eta, and the commutation of beta and eta).

Notation. Terms are taken up to alpha. T = `\t. \f. t`, F = `\t. \f. f`,
I = `\f. f`. A *member* is an element of the set 𝒦 fixed below; "s occurs in
t" means an occurrence of s as a subterm of t.

## 1. A lemma: collapsing a set of closed terms to a normal form

**Lemma.** Let v be a closed term and 𝒦 a set of closed terms such that

- (C1) v ∈ 𝒦, v is in beta-eta normal form, and no proper subterm of v is a
  member;
- (C2) v is the only abstraction in 𝒦;
- (C3) if t ∈ 𝒦 and t →β t' in one step, then t' ∈ 𝒦;
- (C4) if t ∈ 𝒦 and s ∈ 𝒦 occurs in t, replacing that one occurrence of s
  by v gives a member;
- (C5) no member contains an eta redex;
- (C6) there is a closed beta-eta normal form N, different from v, none of
  whose subterms is a member.

Then the theory lambda beta eta + {s = v : s ∈ 𝒦} is consistent: it does
not prove N = v.

**Proof.** Write →ρ for the compatible closure of {s → v : s ∈ 𝒦}. Since
every member is closed, a ρ step replaces a closed subterm, and it commutes
with substitution for variables. Let →R be →β ∪ →ρ.

*(a) Parallel reduction.* Define t ⇒ t' by the rules

1. x ⇒ x;
2. from P ⇒ P': `\x. P` ⇒ `\x. P'`;
3. from P ⇒ P' and Q ⇒ Q': P Q ⇒ P' Q';
4. from P ⇒ P' and Q ⇒ Q': (`\x. P`) Q ⇒ P'[x := Q'];
5. if s ∈ 𝒦: s ⇒ v.

⇒ is reflexive (induction on the term, rules 1 to 3). A one-step β or ρ
reduction is a ⇒ step (the redex by rule 4 or 5, its context by rules 1 to
3 and reflexivity), and a ⇒ step is a finite sequence of β and ρ steps
(rule 4 contracts one redex after reducing its parts, rule 5 is one ρ
step). So the reflexive transitive closure of ⇒ is →R*.

*Substitution.* If P ⇒ P' and Q ⇒ Q', then P[x := Q] ⇒ P'[x := Q'].
By induction on P ⇒ P'. Rules 1 to 4 are Barendregt's cases (3.2.4). Rule 5:
P ∈ 𝒦 is closed, so P[x := Q] = P ⇒ v = v[x := Q'], v being closed.

*Members stay members.* If t ∈ 𝒦 and t ⇒ t', then t' ∈ 𝒦: t' is reached
from t by β steps, each keeping a member a member by (C3), and ρ steps,
each replacing one occurrence of a member by v and so keeping a member a
member by (C4).

*The target of a term.* Define t* by: t* = v if t ∈ 𝒦, and otherwise

    x* = x,    (\x. P)* = \x. P*,
    ((\x. P) Q)* = P*[x := Q*],    (P Q)* = P* Q*  when P is not an abstraction.

*Claim: t ⇒ t' implies t' ⇒ t*.* By induction on the derivation of
t ⇒ t'.

- If t ∈ 𝒦: t' ∈ 𝒦 (members stay members), so t' ⇒ v = t* by rule 5.
- Otherwise t ∉ 𝒦, so rule 5 was not used at the root, and t* is given by
  the structural clauses.
  - Rule 1: t = x = t' = t*.
  - Rule 2: t = `\x. P`, t' = `\x. P'`, P ⇒ P'. By induction P' ⇒ P*, so
    t' ⇒ `\x. P*` = t* by rule 2.
  - Rule 3 with P not an abstraction: t' = P' Q', and t* = P* Q*; by
    induction and rule 3.
  - Rule 4: t = (`\x. P`) Q, t' = P'[x := Q']. By induction P' ⇒ P* and
    Q' ⇒ Q*; by substitution t' ⇒ P*[x := Q*] = t*.
  - Rule 3 with P = `\x. P0` an abstraction: t' = R Q' with `\x. P0` ⇒ R
    and Q ⇒ Q', and t* = P0*[x := Q*]. Two cases for `\x. P0` ⇒ R.
    - By rule 2: R = `\x. P0'` with P0 ⇒ P0'. By induction P0' ⇒ P0* and
      Q' ⇒ Q*, and rule 4 gives t' = (`\x. P0'`) Q' ⇒ P0*[x := Q*] = t*.
    - By rule 5: `\x. P0` ∈ 𝒦, so `\x. P0` = v by (C2), and R = v. By (C1)
      P0 is beta normal (so contains no redex) and contains no member, so
      P0* = P0 (induction on P0: no clause other than the structural,
      redex-free ones applies). Then t' = v Q' = (`\x. P0`) Q' ⇒
      P0[x := Q*] = t* by rule 4, from P0 ⇒ P0 and Q' ⇒ Q*.

So ⇒ has the diamond property: t ⇒ t1 and t ⇒ t2 give t1 ⇒ t* and t2 ⇒ t*.
Hence ⇒*, which is →R*, is confluent: →R is Church-Rosser.

*(b) Adding eta.* →η is Church-Rosser, and →β* and →η* commute (Barendregt
3.3.7 and 3.3.8). We show that →ρ and →η commute in one step each, which
gives the commutation of →ρ* and →η* by tiling. Let t →ρ u replace an
occurrence of s ∈ 𝒦 by v, and t →η w contract an occurrence of `\x. P x`
(x not free in P) to P.

- By (C5) the eta redex is neither s nor inside s.
- If the two occurrences are disjoint, doing both steps in either order
  gives the same term w'.
- Otherwise s lies inside the eta redex, hence inside P x; s is closed and
  x is free in P x, so s is not P x and s lies inside P. Then u contains
  the eta redex `\x. P1 x` with P1 = P with s replaced by v; x is still not
  free in P1 (v is closed), so u →η P1; and w = P →ρ P1. Both give w' = P1.

So →ρ* and →η* commute. Since →β* and →η* commute too, →R* = (→β ∪ →ρ)*
commutes with →η* (each step of an →R sequence, β or ρ, is tiled against an
→η* sequence in turn). By the Hindley-Rosen lemma (Barendregt 3.3.5),
→R ∪ →η is Church-Rosser.

*(c) Consistency.* The convertibility generated by →R ∪ →η is a congruence
that contains beta, eta and every equation s = v with s ∈ 𝒦, so it contains
the theory. N contains no redex (it is beta-eta normal) and no member (C6),
so N has no one-step R-or-eta reduct. v is beta-eta normal, and the only
member occurring in it is v itself (C1), whose ρ step gives v again, so v
reduces only to v. By Church-Rosser, N and v are not convertible, and the
theory does not prove N = v. ∎

## 2. The five points

Each point is M = Y G (`corpora/contest_hard_clauses.pl`, H29 and H30), with
the prelude's fixpoint Y = `\g. (\p. g (p p)) (\q. g (q q))`
(`corpora/prelude_clauses.pl`) and G = `\x. B`, where B is beta normal and
contains no abstraction applied to anything. Let

- D = `\p. G (p p)`; `\q. G (q q)` is D up to alpha, so M →β D D;
- E = `\p. B[x := p p]`, the only one-step reduct of D (its only redex is
  G (p p)); E is beta normal, since in B the variable x stands only where
  p p, an application of two variables, creates no redex.

Throughout, Δ and Δ' range over {D, E}, and K, K1, K2 over 𝒦. In every case
v = F and N = T. 𝒦 is the least set closed under the clauses listed for the
point. Since D D ∈ 𝒦 by the first clause and M →β D D, the lemma's theory
proves M = D D = F, which is what the introduction needs.

Checks common to all five points:

- (C1) F is a member by a clause; it is beta-eta normal; its proper
  subterms `\f. f`, f are not members (I is not generated by any clause,
  and members are closed).
- (C6) T is beta-eta normal and different from F; its subterms T,
  `\f. t`, t are not members (T is not generated by any clause, the other
  two are open).
- (C2) Every clause other than the one for F builds an application, so F is
  the only abstraction in 𝒦.
- (C5) The terms written in the clauses are F, T, I, G, D, E, A and
  applications of members; none contains an eta redex. For G = `\x. B`,
  B is x applied to arguments whose last is not x, or (`probe_cycle_if_false`)
  `(x F) x`, where x is free in `x F`; D's body is G (p p), whose argument
  is p p, not p; E's body is B[x := p p], not of the form P p with p not
  free in P. T, F, I and A contain no application of the form P z at all.
  Members are built from these by application, so they contain no eta
  redex either.
- (C3) and (C4) are checked clause by clause below, by induction on how a
  member was generated. For (C4) the occurrences of members inside a member
  must be known exactly; for each point a *reading lemma* shows which
  subterms of a member are members.

A step inside a K position of a clause gives, by induction, a member K' in
that position, hence a member by the same clause; this case is not repeated
below. G, D's inner reduct aside, and the constants T, F, I, A are normal.

### 2.1 `probe_cycle_and_false`: G = `\x. x F F`

B = x F F, E = `\p. (p p) F F`. Clauses:

    (a) Δ Δ'      (b) G K      (c) K F F      (d) F      (e) I F

*Reading lemma.* For K ∈ 𝒦, K F ∉ 𝒦. By induction on K: K F is an
application with argument F; only (b) (with K = F), (c) and (e) build such
a term. (b) needs K = G and (e) needs K = I, neither a member. (c) needs
K F = (K0 F) F with K0 ∈ 𝒦, i.e. K = K0 F with K0 ∈ 𝒦 smaller than K; by
induction K0 F ∉ 𝒦, contradicting K ∈ 𝒦. Consequently the members occurring in a member are: the whole term;
the K positions of (b) and (c); and literal occurrences of F (in the
clauses, and inside G, D and E). The other subterms are open (inside G, D,
E), or constants that are not members (G, D, E, T, I), or K F (not a
member by the lemma).

(C3), one-step reducts:

- (a) D Δ' →β G (Δ' Δ'), by (b). E Δ' →β (Δ' Δ') F F, by (c). Inner: D →β
  E in either position, by (a).
- (b) G K →β K F F, by (c).
- (c) K F F = (K F) F: its root is not a redex (K F is an application). K F
  is a redex only when K is an abstraction, K = F by (C2): F F →β I, giving
  I F, by (e).
- (d) F is normal. (e) I F →β F, by (d).

(C4), one occurrence replaced by F: the whole term gives F (d); a literal F
gives the same term; K in (b) gives G F (b); K in (c) gives F F F (c).
Occurrences inside a K position give members by induction.

### 2.2 `probe_cycle_if_false`: G = `\x. x F x`

B = (x F) x, E = `\p. ((p p) F) (p p)`. Clauses:

    (a) Δ Δ'     (b) G K     (c) K1 F K2     (d) F     (e) I K

*Reading lemma.* For K ∈ 𝒦, K F ∉ 𝒦. By induction on K: a member of the
form K F is built by (b) with K = G, not a member; by (c) with K2 = F and
K = K0 F, K0 ∈ 𝒦 smaller than K, excluded by induction; or by (e) with
K = I, not a member. Also I ∉ 𝒦. So
the members occurring in a member are the whole term, the K positions of
(b), (c), (e), and literal F's.

(C3):

- (a) D Δ' →β G (Δ' Δ') (b); E Δ' →β (Δ' Δ') F (Δ' Δ') (c); D →β E inside
  (a).
- (b) G K →β K F K (c).
- (c) K1 F K2 = (K1 F) K2: not a root redex (K1 F is an application); K1 F
  is a redex only for K1 = F: F F →β I, giving I K2 (e).
- (e) I K →β K, a member.

(C4): the whole term gives F; K in (b) gives G F; K1 or K2 in (c) gives
F F K2 or K1 F F, both (c); K in (e) gives I F (e).

### 2.3 `probe_cycle_and_or`: G = `\x. (x T x) F F`

B = ((x T) x) F F, E = `\p. (((p p) T) (p p)) F F`. Clauses:

    (a) Δ Δ'     (b) G K     (c) (K1 T K2) F F     (d) F
    (e) (I K) F F     (f) K F F     (g) I F

*Reading lemma.* The clauses build: (a) an application whose function is
D or E; (b) one whose function is G; (d) F; and (c), (e), (f), (g) an
application whose argument is F, with function part (K1 T K2) F,
(I K) F, K F and I respectively. For K, K' ∈ 𝒦:

- (i) T ∉ 𝒦 and K T ∉ 𝒦: T is an abstraction other than F (C2), and no
  clause builds an application whose argument is T ((a) ends in Δ', (b) in
  a member, the others in F).
- (ii) K T K' ∉ 𝒦: this is (K T) K'. Its function part K T is not D, E or
  G, so not (a) or (b); if K' = F it would have to be one of the function
  parts (K1 T K2) F, (I K) F, K0 F, I of (c), (e), (f), (g), each of which
  is an abstraction or ends in the argument F, while K T ends in T.
- (iii) I K ∈ 𝒦 only for K = F: an application whose function is I is
  built only by (g).
- (iv) K F ∉ 𝒦, by induction on K. A member Z F with Z = K is built by
  (b) with K = G, not a member; by (g) with K = I, not a member; by (f)
  with K = K0 F, K0 ∈ 𝒦 smaller than K, excluded by induction; by (c)
  with K = (K1 T K2) F; or by (e) with K = (I K0) F. In the last two cases
  K would itself be a member of the form Z' F, so by one of (b), (c), (e),
  (f), (g), with Z' = K1 T K2 or Z' = I K0: Z' = G, (K1' T K2') F,
  (I K1') F or I is impossible (K1 T K2 and I K0 are applications whose
  arguments are K2 and K0, and matching (K1' T K2') F or (I K1') F would
  need K2 = F with K1 T equal to K1' T K2' or to I K1', which have different
  shapes), and Z' = K0' F with K0' ∈ 𝒦 needs K1 T K2 or I K0 to be of the
  form K0' F: for K1 T K2 that gives K0' = K1 T, not a member by (i); for
  I K0 it gives K0' = I, not a member.

By (i) to (iv), the subterms K1 T, K1 T K2, (K1 T K2) F of (c), (I K) F of
(e) and K F of (f) are not members, and I K of (e) is a member only when
K = F.

So the members occurring in a member are the whole term, the K positions,
literal F's, and, in (e) with K = F, the subterm I F (g).

(C3):

- (a) D Δ' →β G (Δ' Δ') (b); E Δ' →β ((Δ' Δ') T (Δ' Δ')) F F (c); D →β E
  inside (a).
- (b) G K →β (K T K) F F (c).
- (c) (K1 T K2) F F: none of (K1 T K2) F, K1 T K2, K1 T is an abstraction,
  so the only redex outside K1 and K2 is K1 T when K1 = F: F T →β I, giving
  (I K2) F F (e).
- (e) (I K) F F: the redex I K →β K gives K F F (f).
- (f) K F F: K F is a redex only for K = F: F F →β I, giving I F (g).
- (g) I F →β F (d).

(C4): the whole term gives F; K1 or K2 in (c) gives (F T K2) F F or
(K1 T F) F F (c); K in (b) gives G F; K in (e) gives (I F) F F (e); the
subterm I F of (I F) F F gives F F F (f); K in (f) gives F F F (f).

### 2.4 and 2.5 `value_map_two_cycle` and `value_map_three_cycle`: G = `\x. x A F`

A = `\p. \q. T` (two) or A = `\p. \q. \r. \s. T` (three), a closed normal
abstraction different from F. B = (x A) F, E = `\p. ((p p) A) F`. Clauses:

    (a) Δ Δ'     (b) G K     (c) K A F     (d) F     (e) I F

*Reading lemma.* A ∉ 𝒦 (C2) and T ∉ 𝒦. For K ∈ 𝒦, K A ∉ 𝒦: no clause builds
an application whose argument is A ((a) ends in Δ', (b) in a member, (c)
and (e) in F). So the members occurring in a member are the whole term,
the K positions and literal F's.

(C3):

- (a) D Δ' →β G (Δ' Δ') (b); E Δ' →β (Δ' Δ') A F (c); D →β E inside (a).
- (b) G K →β K A F (c).
- (c) K A F = (K A) F: not a root redex; K A is a redex only for K = F:
  F A →β I, giving I F (e).
- (e) I F →β F (d).

(C4): the whole term gives F; K in (b) gives G F; K in (c) gives F A F (c).

## 3. Conclusion

For each of the five points the lemma applies with its 𝒦, v = F and N = T,
so lambda beta eta + (M = F) is consistent, and so is lambda beta eta +
(`\a. M y a` = \x. x): the scored conjecture `boolean(false)` of each point
is consistent with lambda beta eta, as the judge's `is_identity` asks. The
trap `boolean(true)` of these points is refuted by the proof of the class
`false_only`, which this document does not touch.
