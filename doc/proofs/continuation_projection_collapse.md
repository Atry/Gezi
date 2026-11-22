# The continuation cycles collapse onto the Boolean they select

A written proof, 2026-09-29. It proves a theorem for a syntactic class of continuation
cycles M = Y G, and with it the five conjectures of
`corpora/contest_continuation_cycles.pl` that the first part
(`continuation_true_eta_is_omega.md`) does not cover:

    continuation_true_constant    boolean(false)
    continuation_true_pair        boolean(false)
    continuation_false_constant   boolean(true)
    continuation_nested_true      boolean(true), boolean(false)
    continuation_nested_false     boolean(true), boolean(false)

(seven claims). The two claims of continuation_true_eta are the first
part's.

Its structure (a rule set confluent together with beta and eta by Hindley
and Rosen) follows the general theorem `doc/proofs/omega_easy_beta_eta.md`;
that document proves a different claim (Omega is easy) and is cited, not
reused.

WHY THE COLLAPSE LEMMA DOES NOT APPLY AS IT STANDS (the corpus's comment).
The collapse lemma (`false_only_small_cycles.md`, section 2) collapses a
set of closed non-abstractions onto one normal form V. Here M = Y G
reduces to an abstraction other than V, and what loops is M A B for every
pair of continuations. The rule set below collapses M onto V, M A onto
the constant function V A reduces to, and M A B onto the argument V
selects, and allows the collapsed terms to be abstractions.

## 1. The class and the theorem

V is T = \t. \f. t or F = \t. \f. f. Write s for the variable V selects
(t for T, f for F), sel(X, Y) for the term V X Y beta reduces to (X for
T, Y for F), and K(X) for the term V X beta reduces to: K(X) = \z. X (z
not free in X) for T, and K(X) = I = \z. z for F. So V = \t. K(t),
V X ->b K(X) and K(X) Y ->b sel(X, Y).

THE CLASS C(V). G = \x. \t. \f. x P Q with

- (A1) P and Q beta eta normal, their free variables among x, t, f;
- (A2) every occurrence of x in P and in Q is the head of a subterm
  x t f, x applied to exactly t and then f;
- (A3) the SELECTED expression E_s (P for T, Q for F) is s or x t f;
- (A4) not both P = t and Q = f.

(A4) excludes the one G of the form above that eta reduces to I,
\x. \t. \f. x t f: for it, Y G = Omega in lambda beta eta, and both
claims are the first part's (`continuation_true_eta_is_omega.md`).
Every other G of the form has at most the one eta step G -> G_e below,
and G_e is eta normal: G_e = \x. \t. x P has an eta redex only when
P = t.

Y = \g. (\p. g (p p)) (\q. g (q q)), the prelude's `fixpoint`, and
W = \q. G (q q).

THEOREM. For G in C(V), lambda beta eta + (Y G = V) is consistent, and so
is the same theory over the terms with sets.

The six points (`continuation_body/5`), G = \x. \t. \f. x P Q:

| point | P | Q | in C(T) | in C(F) |
|---|---|---|---|---|
| continuation_true_constant | \v. t | f | no (trap) | yes |
| continuation_true_pair | \s. s t t | f | no (trap) | yes |
| continuation_false_constant | t | \v. f | yes | no (trap) |
| continuation_true_eta | \u. t u | f | no (P not eta normal) | no (P not eta normal) |
| continuation_nested_true | x t f | f | yes | yes |
| continuation_nested_false | t | x t f | yes | yes |

The three traps' selected expressions (\v. t, \s. s t t, \v. f) are not in
{s, x t f}, and the corpus refutes each of them. continuation_true_eta is
covered for both Booleans by the first part (G eta reduces to I).

## 2. The rules

A set 𝔉 of closed terms, the MEMBERS, is defined in section 3; V is a
member. The rules π, each closed under contexts:

    (pi-)   L         -> V            L in 𝔉, L != V
    (pi0)   L X       -> K(X)         L in 𝔉
    (pi2)   L X Y     -> sel(X, Y)    L in 𝔉
    (piV)   V X       -> K(X)
    (piK)   K(X) Y    -> sel(X, Y)

X and Y are metavariables, each occurring once on the left; each member
L is a ground constant of its rule, so every rule is left linear. (piV)
and (piK) are beta steps; for T, (piK) is every beta step
(\z. X) Y -> X with z not free in X. The two are in π so that π is
confluent by itself.

The theory. ->bep (beta, eta and π together) generates a theory that
contains lambda beta eta + (Y G = V), since Y G is a member (section 3)
and (pi-) rewrites it to V. It suffices to show that ->bep is confluent
and that T and F are two distinct normal forms of it (section 7).

## 3. The members and the selectors

Two relations, defined together as the least ones closed under the
clauses below.

SELECTORS. (E, C) in 𝒮, read "E selects C", for terms E and C:

- (R0) (C, C) for every term C;
- (R1) (L X Y, C) when L is a member and (sel(X, Y), C) is in 𝒮;
- (R2) (V X Y, C) and (K(X) Y, C) when (sel(X, Y), C) is in 𝒮;
- (R3) ((\f'. E) Y, C) when, for F, (E, f') is in 𝒮 and (Y, C) is in 𝒮;
  and, for T, (E, X') is in 𝒮 for a term X' in which f' is not free, and
  (X', C) is in 𝒮.

MEMBERS. 𝔉 is the set of closed terms of the forms

- (M1) Y G' with G' in {G, G_e}, where G_e is G's eta reduct when
  Q = f and f is not free in x P (G_e = \x. \t. x P), and G' = G
  otherwise;
- (M2) W1 W2 with W1, W2 in R(W), the beta eta reducts of W (listed
  below);
- (M3) G' L with G' as in (M1) and L a member;
- (M4) \t. \f. E with (E, s) in 𝒮;
- (M5) \t. D with f not free in D and (D f, s) in 𝒮;
- (M6) V (an instance of (M4): V = \t. \f. s and (s, s) is (R0)).

THE REDUCTS OF W. By (A1) and (A2), G' is beta normal, and
G (q q) ->b \t. \f. (q q) P<q q> Q<q q>, where P<N> is P[x := N]; in
P<q q> every x t f has become (q q) t f, which has no redex (q is a
variable), so this term is beta normal, and eta normal except for the
eta step of G (\f. (q q) P<q q> f with f not free when Q = f and f is
not free in x P). So R(W) consists of W = \q. G (q q), \q. G_e (q q),
W' = \q. \t. \f. (q q) P<q q> Q<q q> and its eta reduct
\q. \t. (q q) P<q q> in the case above. Each is \q. B with B either
G' (q q) or an abstraction whose body, after its binders, has the
variable q at the head of its spine.

LEMMA 3.1 (transitivity and substitution). If (E, C1) and (C1, C) are in
𝒮, so is (E, C). If (E, C) is in 𝒮, so is (E[z := N], C[z := N]) for
every variable z and term N (capture avoided as usual). By induction on
the derivation of (E, C1), and of (E, C): the members, V and the shape
K(.) are closed, or commute with substitution (K(X)[z := N] =
K(X[z := N])), and each clause is preserved.

LEMMA 3.1b (free variables). If (E, C) is in 𝒮 then every free variable
of C is free in E. By induction on the derivation: (R0) trivially; (R1)
and (R2), sel(X, Y) is a subterm of E; (R3), for F, Y is a subterm of E,
and for T, the free variables of X' are free in E and X' has no f', so
they are free in \f'. E.

LEMMA 3.2 (path). If (E, C) is in 𝒮 then E ->>π C. By induction: (R0)
none; (R1) one (pi2) step to sel(X, Y), then the hypothesis; (R2) (piV)
then (piK), or (piK), then the hypothesis; (R3) the hypothesis under the
binder takes \f'. E to \f'. f' = K(X) (F) or to \f'. X' = K(X') (T,
f' not free in X'), then (piK) gives Y (F) or X' (T), then the
hypothesis.

LEMMA 3.3 (normal members). V is the only member in beta eta normal
form. A member of (M1) to (M3) has a beta redex at its root (its operator
is an abstraction applied to an argument: Y, a term of R(W), or G'). For
(M4), \t. \f. E normal needs E a normal selector of s; by the clauses,
(R0) gives E = s and the member V, while a selector of (R1) is L X Y with
L X a beta redex (L an abstraction) or L a member of (M1) to (M3), which
holds a redex, and a selector of (R2) or (R3) is a beta redex. For (M5),
\t. D normal with (D f, s): (R1) gives D = L X, which holds a redex as
before; (R2) gives D = V X, a redex, or D = K(X), normal only when X is,
and then (sel(X, f), s) with X normal forces X = t for T (D = \z. t, the
member \t. \z. t = T) and nothing for F (D = I, the member \t. I = F);
(R3) gives D = \f'. E' with E' a normal selector of f' (F) or of a term
free of f' that selects t (T), so E' = f' or E' = t, the members F and T.
In each case the normal member is V.

LEMMA 3.4 (shape). No member is of the form L X with L a member.
The members that are applications are those of (M1) to (M3), whose
operators are Y, a term of R(W), and G'. None is a member:

- none is of the form (M4): Y's body after its binder is an application;
  a term \q. B of R(W) has, after two binders, either the application
  G' (q q) or an abstraction, and G' = \x. \t. \f. x P Q (or G_e) has
  after two binders an abstraction (G) or x P (G_e); none of these is a
  selector, since a selector is the variable s or an application whose
  spine head is a member, V, K(X) or an abstraction \f'. E applied to
  one argument, and x P has the variable x at its head;
- none is of the form (M5): for Y, D f = (\p. g (p p)) (\q. g (q q)) f
  has an operator that is an application of an open abstraction, which
  is no member (members are closed), not V, not K(X) (p occurs in
  g (p p)), and not an abstraction; for \q. G' (q q), D f = G' (q q) f
  has the operator G' (q q), an application; for the other terms of
  R(W), D f = (\t. \f. (q q) ...) f or (\t. (q q) P<q q>) f, whose
  operator \t. B' would need, by (R3), B' to select the fresh variable
  (F) or a term X' free of t that selects q (T), and B' is an
  abstraction or has the variable q at its head; for G', D f =
  (\t. \f. x P Q) f or (\t. x P) f, alike, with x at the head;
- none is V.

Nor is any member of the form V X or K(X) Y: those applications have the
operators V and K(X), and the operators of the members that are
applications are Y, a term of R(W) and G', none of them V, and none a
constant function or I (Y uses g, a term \q. B of R(W) uses q, and G'
uses x in its body).

## 4. 𝔉 and 𝒮 are closed under ->bep

Lemmas 4.1 and 4.2 are proved together, by induction on the size of the
term, a member inside a selector and a selector inside a member being
smaller than the term that holds it.

LEMMA 4.1 (selectors). If (E, C) is in 𝒮 and E -> E' by one step of
->bep, then (E', C') is in 𝒮, where C' = C unless the step is inside the
occurrence of C that the derivation selects, and then C -> C' by that
step. By induction on the derivation, the step being inside a clause's
parts or at its root:

- inside a member L of (R1): L -> L' with L' a member (Lemma 4.2); inside X or Y: the
  hypothesis on (sel(X, Y), C), or nothing when the part is discarded;
  inside E or Y of (R3): the hypothesis, with Lemma 3.1.
- at the root of (R1): (pi2) gives sel(X, Y), which selects C; (pi0) on
  L X gives K(X) Y, (R2); (pi-) on L gives V X Y, (R2). A beta step on
  L X when L is an abstraction: L is of (M4), (M5) or V.
  - (M4), L = \t'. \f'. E1 with (E1, s) in 𝒮: L X Y ->b
    (\f'. E1[X/t']) Y, which is (R3): for F, (E1[X/t'], f') by Lemma 3.1
    and (Y, C) since sel(X, Y) = Y; for T, (E1[X/t'], X) by Lemma 3.1,
    f' not free in X, and (X, C).
  - (M5), L = \t'. D with (D f, s): L X Y ->b D[X/t'] Y, and
    (D[X/t'] Y, sel(X, Y)) is in 𝒮 by Lemma 3.1 (substituting X for t'
    and Y for f), hence (D[X/t'] Y, C) by transitivity.
  - V: V X Y ->b K(X) Y, (R2).
- at the root of (R2): (piV) or the beta step on V X gives K(X) Y, and
  (piK) or the beta step on K(X) Y gives sel(X, Y).
- at the root of (R3): the beta step gives E[Y/f']; for F,
  (E[Y/f'], Y) by Lemma 3.1 and then (Y, C); for T, (E[Y/f'], X') (f'
  not free in X') and (X', C). An eta step \f'. H f' -> H (f' not free
  in H) inside (R3): (H f', f') or (H f', X') gives (H Y, Y) or
  (H Y, X') by Lemma 3.1, so H Y selects C. (piK) at the root, for
  \f'. E = K(X''): for F, E = f' and the result is Y; for T, E = X''
  with f' not free, and (E, X') with E = X'' gives, by (R0), X' = X'' as
  the selected term, so the result X'' selects C.

LEMMA 4.2 (members). If L is a member and L -> L' by one step of ->bep,
then L' is a member.

- (M1) Y G': the root beta step gives (\p. G' (p p)) (\q. G' (q q)),
  which is (M2) up to alpha. A step inside G': G -> G_e only (G is beta
  normal by (A1), (A2), and its closed subterms are normal, so none is a
  member other than V, Lemma 3.3). (pi-) gives V.
- (M2) W1 W2: the root beta step gives G' (W2 W2) (M3) when
  W1 = \q. G' (q q); when W1 = W' or its eta reduct it gives
  \t. \f. (W2 W2) P<W2 W2> Q<W2 W2> or \t. (W2 W2) P<W2 W2>, which is
  (M4), resp. (M5): the selector (W2 W2) P<W2 W2> Q<W2 W2> is (R1) with
  the member W2 W2, and sel(P<..>, Q<..>) = E_s<W2 W2> is s, (R0), or
  (W2 W2) t f, (R1) with sel(t, f) = s; this is where (A3) is used.
  Steps inside W1, W2 stay in R(W). (pi-) gives V.
- (M3) G' L: the root step gives \t. \f. L P<L> Q<L> or \t. L P<L>,
  (M4) or (M5) as for (M2). Inside L: a member (Lemma 4.2 on the smaller
  L). Inside G': G -> G_e. (pi-) gives V.
- (M4) \t. \f. E: a step inside E keeps (E', s), s being a bound variable
  that no step changes (Lemma 4.1). An eta step \f. H f -> H gives
  \t. H, (M5). (pi-) gives V.
- (M5) \t. D: inside D, Lemma 4.1 on (D f, s). The eta step when
  D = H t with t not free in H gives H, and H is a member or V: (H t f, s)
  is in 𝒮, and by the clauses the only derivations of it are (R1) with
  the member H applied to t and f (H t is not a member by Lemma 3.4,
  since t is no member), or (R2) with H = V; H t is an application, so
  neither K(X) nor an abstraction as (R3) needs. (pi-) gives V.

A (pi0), (pi2), (piV) or (piK) step at the root of a member would need
the member to be an application L X with L a member, V X or K(X) Y;
Lemma 3.4 excludes the first, and (M1) to (M3) have operators Y, R(W)
and G', none of them V or K(X) (Lemma 3.4's list).

## 5. π is confluent

TERMINATION. Every π step shortens the term, counting nodes (variables,
abstractions and applications). A closed term of at most three nodes is
\a. \b. a or \a. \b. b, both normal, and a member other than V is not
normal (Lemma 3.3), so it has at least four nodes and (pi-), which
replaces it by V of three, shrinks the term. (pi0) replaces L X, of
|L| + |X| + 1 nodes, by K(X), of |X| + 1 (T) or 2 (F) nodes. (pi2),
(piV) and (piK) replace their left side by a proper part of it or, for
(piV), by K(X), of fewer nodes than V X.

LOCAL CONFLUENCE. The critical pairs of π:

- a step inside a member L against (pi-), (pi0) or (pi2) at L, L X or
  L X Y: L -> L' a member (Lemma 4.2), and L' gives the same V, K(X) or
  sel(X, Y) by one step (or L' = V and (piV), (piK) finish);
- (pi-) at L inside L X against (pi0): V X ->piV K(X);
- (pi-) at L inside L X Y against (pi2): V X Y ->piV K(X) Y ->piK
  sel(X, Y);
- (pi0) at L X inside L X Y against (pi2): K(X) Y ->piK sel(X, Y);
- (pi0) or (pi2) with a member that is itself L X: excluded by Lemma
  3.4, so a term has at most one decomposition as a member applied to
  arguments;
- (piK) for T at (\z. X) Y where \z. X is a member: no member is a
  constant function for T, since the selector of an (M4) or (M5) member
  selects t and so, by Lemma 3.1b, holds t free (for (M5), t is free in
  D f and t is not f, so t is free in D), and V = T holds t; for F, (piK) is at
  I Y, and I is no member (Lemma 3.3: I is normal and not F);
- (piV) with V a member: (pi0) at V X gives the same K(X).

Steps inside the metavariables' instances are disjoint from the rule's
ground part and are kept or dropped by the step. By Newman's lemma π is
confluent.

## 6. π commutes with beta and with eta

By Hindley's lemma (Barendregt 1984, section 3.3: if every peak
Q1 <-1 P ->2 Q2 has R with Q1 ->>2 R and Q2 ->=1 R, then ->>1 and ->>2
commute), it suffices that every peak
X1 <-b X ->π X2 has X3 with X1 ->>π X3 and X2 ->b= X3, and every peak
X1 <-e X ->π X2 has X3 with X1 ->>π X3 and X2 ->e= X3. Let R be the
beta or eta redex and O the π redex.

LEMMA 6.1 (abstractions). For every member \t. U and every term X,
U[X/t] ->>π K(X).
- V: U[X/t] = K(X).
- (M4), U = \f. E with (E, s): (E[X/t], s[X/t]) by Lemma 3.1, and
  s[X/t] is X (T) or f (F); Lemma 3.2 under the binder gives \f. X =
  K(X) (f not free in X) or \f. f = K(X).
- (M5), U = D with (D f, s): the derivation of (D f, s) is (R1) with
  D = L X', (R2) with D = V X' or D = K(X'), or (R3) with
  D = \f'. E'. In the first three, D[X/t] ->π K(X'[X/t]) by (pi0),
  (piV), or already equals it; for F that is K(X); for T, sel(X', f) =
  X' selects t, so X'[X/t] ->>π X (Lemmas 3.1, 3.2) and K(X'[X/t])
  ->>π K(X). In the last, Lemma 3.2 under \f' gives K(.) as in (M4).

BETA PEAKS.
- (B1) R and O disjoint: each step survives the other.
- (B2) R inside the member L of O: L -> L', a member; X1 has O with L',
  which π rewrites to X2 (the right sides do not contain L).
- (B3) R inside an instance of X or Y of O: X1 ->π X3, O's contractum
  with the step made; X2 ->b= X3, the step made in the one copy the
  contractum keeps, or none when it drops the part (projections never
  copy).
- (B4) O inside the body U or the argument A of R = (\z. U) A: X1 holds
  O[A/z] once for each occurrence of O in U (a π redex still: members
  are closed, and the metavariables' instances take the substitution) or
  O once for each free z of U when O is in A; X1 ->>π X3 by contracting
  every copy, and X2 ->b X3 by contracting R.
- (B5) R = O: (piV) and (piK) are beta steps with the same contractum.
- (B6) the operator of R is the member L of O, an abstraction \t. U,
  R = L X:
  - O = L (pi-): X2 has V X, and X2 ->b X3 with K(X) there; X1 has
    U[X/t] ->>π K(X) by Lemma 6.1;
  - O = L X (pi0): X2 has K(X) = X3, and Lemma 6.1;
  - O = L X Y (pi2): X1 has U[X/t] Y ->>π K(X) Y ->piK sel(X, Y), which
    is X2.
- (B7) no other position: (L X) Y is not a beta redex (L X is an
  application), V has no redex, and a π left side that is an
  abstraction is a member (pi-), covered by (B6) when applied.

ETA PEAKS, R = \z. H z with z not free in H.
- (E1) disjoint; (E2) R inside the member of O: a member again
  (Lemma 4.2); (E3) R inside an instance of a metavariable: as (B3).
- (E4) O inside H: after the eta step O is still in H; the π contractum
  has no new free variable, so R stays an eta redex; X3 is both steps.
- (E5) O = H z, the body of R:
  - (pi0), H = L: X1 = L ->pi- V (or X1 = V), and X2 = \z. K(z) = V
    (\z. \z'. z = T, \z. \z'. z' = F);
  - (pi2), H = L X: X1 = L X ->pi0 K(X), and X2 = \z. sel(X, z) = K(X);
  - (piV), H = V: X1 = V = X2;
  - (piK), H = K(X): X1 = K(X) = \z. sel(X, z) = X2.
- (E6) O = R, a member \z. H z (pi-): X1 = H is a member (Lemma 4.2) or
  V, and H ->pi- V = X2.

So π commutes with beta and with eta, hence with ->be. beta and eta
together are confluent (Barendregt 1984, 3.3.9; over the terms with
sets, weakly orthogonal with the set as a constructor, as
`omega_easy_beta_eta.md` states), π is confluent (section 5), and by the
lemma of Hindley and Rosen ->bep is confluent.

## 7. The theory is consistent, and the claims

T and F are normal forms of ->bep: they hold no beta or eta redex and no
application, so no (pi0), (pi2), (piV) or (piK) redex; their closed
subterms are T, F and I, which are normal, and by Lemma 3.3 the only
normal member is V, so (pi-) rewrites none of them. They are distinct
normal forms of a confluent relation, so the theory it generates does not
equate them, and it contains lambda beta eta + (Y G = V). This proves the
theorem.

THE CLAIMS. With M = Y G = T, M a y = a, so `\a. M a y = \x. x` holds
and boolean(true) is consistent; with M = F, M y a = a, and
boolean(false) is consistent. By the table of section 1 this gives the
seven claims of the introduction: boolean(false) of
continuation_true_constant and continuation_true_pair (G in C(F)),
boolean(true) of continuation_false_constant (G in C(T)), and both claims
of continuation_nested_true and continuation_nested_false (G in C(T) and
in C(F)).

OVER THE TERMS WITH SETS. A set is a constructor with no
rule of its own: it adds no redex and no critical pair, members are pure
terms, and a metavariable's instance may hold sets without changing any
case above. The programs hold no set, so each is in its own meaning (the
clause pure), and the theory Th({M = V}) over the terms with sets is
contained in the
convertibility of ->bep over those terms, which is consistent by the same
argument.

## 8. What the claims layer checks

The claims layer's code for this class will check exactly the hypotheses of
section 1, and nothing else: M = Y G with Y the prelude's fixpoint term
for term; G = \x. \t. \f. x P Q in de Bruijn form; P and Q beta eta
normal (a finite check); every occurrence of x in P and Q applied to t
and then f and nowhere else; E_s equal to s or to x t f; and not both
P = t and Q = f (that G is the first part's, checked by its own code). A failed or
unfinished check leaves the claim to Inner.
