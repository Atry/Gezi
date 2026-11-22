# The arithmetic theorem searches are consistent with both Booleans

A written proof, 2026-09-29: the six
conjectures of the class both_booleans on the three theorem points of
`corpora/contest_arithmetic_theorems.pl`,

    arithmetic_double_at_least_itself
    arithmetic_plus_three_differs
    arithmetic_plus_two_commutes

each with the claims boolean(true), test `\a. M a y`, and boolean(false),
test `\a. M y a` (under the judgment of section 7 the closed programs `\y. \a. M a y` and
`\y. \a. M y a`, compared with `\y. \a. a`), and for every point of the
same family whose predicate is in the linear fragment of section 2 and
is found valid by the decision of section 3.

The proof uses the collapse lemma of `false_only_small_cycles.md`
(section 2, restated in `both_booleans_path_family.md`, section 1) and
standard facts of the lambda calculus, cited below.

The proof has three parts:

1. the API lemmas, by induction on the data (section 2);
2. the completeness of the decision of the linear fragment (section 3);
3. the collapse theorem, (S1) to (S3) of the collapse lemma for a set S
   that contains M, in lambda beta eta and in lambda beta eta with sets
   (sections 4 to 7).

## 1. Terms and standard facts

The prelude (`corpora/prelude_clauses.pl`) and the corpus give, up to
alpha:

    Y     = \g. (\p. g (p p)) (\q. g (q q))
    T     = \t. \f. t              F  = \t. \f. f
    Z     = \z. \s. z              Succ = \n. \z. \s. s n
    And   = \a. \b. a b F          Not = \b. b F T
    Or    = \a. \b. a T b
    Eq    = Y (\self. \m. \n. m (n T (\u. F)) (\m1. n F (\n1. self m1 n1)))
    Geq   = Y (\self. \m. \n. n T (\n1. m F (\m1. self m1 n1)))
    Double = Y (\self. \n. n Z (\n1. Succ (Succ (self n1))))
    Plus  = Y (\self. \m. \n. m n (\m1. Succ (self m1 n)))

`Eq` is `natural_equal`, `Geq` is `natural_at_least` (Geq m n is m >= n),
`Double` is `natural_double`, `Plus` is the corpus's `addition` (recursion
on its first argument), `And` is the corpus's `conjunction`, `Not` its
`negation`, `Or` the prelude's `or`. Note that Z and T are the same term.

NUMERALS. The Scott numerals are the normal forms n_0 = Z and
n_(k+1) = \z. \s. s n_k. The spelled numeral is `k` = Succ (Succ (... Z))
with k copies of Succ; `k` ->>b n_k, and Succ `k` is `k+1` literally. A
NUMERAL TERM is a closed term N with N ->>b n_k for some k, written
N ~ k. The set 𝒩 is the set of beta eta reducts of spelled numerals.

THE SEARCH. For a closed P,

    G  = \m. \n. And (P n) (m (Succ n))
    W  = \q. G (q q)          Φ = W W
    M  = Y G Z

Y G ->b (\p. G (p p)) W ->b G Φ, and Φ ->b G Φ, and G Φ ->b \n. B0 with

    B0 = And (P n) (Φ (Succ n)).

STANDARD FACTS (Barendregt, The Lambda Calculus, 1984):

- (CR) ->b and ->be are confluent (3.2.8, 3.3.9).
- (WH) Weak head reduction ->wh contracts the redex at the head of the
  application spine and stops at an abstraction or a neutral term
  x A1 ... Ak. (STANDARDIZATION, 11.4.7, applied to weak head reduction:)
  if X ->>b Y and Y is an abstraction, the weak head reduction of X
  terminates in an abstraction W0 and W0 ->>b Y by steps inside W0. If
  X ->>b x for a variable x, the weak head reduction of X terminates in x.
  A closed X HAS NO WHNF when its weak head reduction does not terminate;
  then no beta reduct of X is an abstraction.
- (ETA) eta postponement (15.1.6): X ->>be Y implies X ->>b X1 ->>e Y for
  some X1; an eta step never turns an application at the root into an
  abstraction. So a closed X with no whnf has no beta eta reduct that is
  an abstraction. And ->e commutes with ->b: if X ->e X' and X ->>b Y then
  X' ->>b Y' and Y ->>e Y' for some Y' (3.3.8); when Y is a variable,
  Y' = Y.
- (SUB) X ->>be Y implies X[x := Q] ->>be Y[x := Q].

## 2. The API lemmas

LEMMA 2.1. For numeral terms N1 ~ a and N2 ~ b:

- Eq N1 N2 ->>b T if a = b, and ->>b F otherwise;
- Geq N1 N2 ->>b T if a >= b, and ->>b F otherwise;
- Double N1 ->>b a numeral term ~ 2a;
- Plus N1 N2 ->>b a numeral term ~ a + b.

PROOF. Write H for the body under Y, and E = W_H W_H with
W_H = \q. H (q q), so Y H ->>b H E and E ->b H E. It suffices to show the
claims for E in place of Y H. By induction on a (and on b inside):

- Eq: E N1 N2 ->>b N1 (N2 T (\u. F)) (\m1. N2 F (\n1. E m1 n1)) ->>b
  n_a (...) (...). For a = 0 this is ->>b N2 T (\u. F) ->>b n_b T (\u. F),
  which is T for b = 0 and (\u. F) n_(b-1) ->b F otherwise. For a = a'+1
  it is ->>b N2 F (\n1. E n_a' n1) ->>b n_b F (...), which is F for b = 0
  and E n_a' n_(b-1) otherwise, T exactly when a' = b - 1, by induction.
- Geq: E N1 N2 ->>b n_b T (\n1. N1 F (\m1. E m1 n1)): T for b = 0
  (a >= 0); otherwise N1 F (\m1. E m1 n_(b-1)) ->>b n_a F (...), F for
  a = 0 (0 >= b false) and E n_(a-1) n_(b-1) otherwise, by induction.
- Double: E N1 ->>b n_a Z (\n1. Succ (Succ (E n1))): Z ~ 0 for a = 0,
  otherwise Succ (Succ (E n_(a-1))), a numeral term ~ 2 + 2(a-1) = 2a by
  induction (Succ X ~ k+1 when X ~ k).
- Plus: E N1 N2 ->>b n_a N2 (\m1. Succ (E m1 N2)): N2 ~ b for a = 0,
  otherwise Succ (E n_(a-1) N2) ~ 1 + (a - 1) + b, by induction.

The connectives: Not X ->>b F when X ->>b T and ->>b T when X ->>b F;
And X Y ->>b Y when X ->>b T and ->>b F when X ->>b F (F Y F ->>b F);
Or X Y ->>b T when X ->>b T and ->>b Y when X ->>b F. QED

THE LINEAR FRAGMENT. An EXPRESSION of the predicate's body is the variable
n, a numeral constant (a spelled numeral or a Scott numeral in normal
form), Plus e1 e2 or Double e; a FORMULA is Eq e1 e2, Geq e1 e2, Not f,
And f1 f2 or Or f1 f2. P = \n. f. Every expression denotes a function
e(k) = a k + b with naturals a, b (n: a = 1, b = 0; a constant c: a = 0,
b = c; Plus adds, Double doubles), and every formula a truth function
f(k).

COROLLARY 2.2. For every numeral term N ~ k, P N ->>b T when f(k) is true
and P N ->>b F when it is false. By induction on f, using Lemma 2.1 and
(SUB): P N ->b f[n := N], every expression e[n := N] is a numeral term
~ e(k) (Plus, Double and the constants by Lemma 2.1; N itself by
assumption), and every formula reduces to the Boolean of its value.

## 3. The decision

LEMMA 3.1 (completeness). Let f be a formula with atoms
e1 R e2 (R one of = and >=), ei(k) = ai k + bi, and let
B = max over the atoms of |b1 - b2|. Then f(k) = f(B + 1) for every
k > B. So f(k) is true for every natural k if and only if it is true for
k = 0, 1, ..., B + 1.

PROOF. For an atom, e1(k) - e2(k) = (a1 - a2) k + (b1 - b2). If a1 = a2
the difference is constant. Otherwise |a1 - a2| >= 1 and for k > B >=
|b1 - b2| the sign of the difference is the sign of a1 - a2, the same for
every such k. The truth of = and >= is a function of that sign (or of the
constant), so each atom is constant on k > B, and so is every Boolean
combination of atoms. QED

The layer evaluates the atoms with Prolog's integers at k = 0, ..., B + 1
and answers the theorem only when all are true. By Corollary 2.2 the
hypothesis of the collapse theorem, P N ->>b T for every numeral term N,
then holds.

## 4. The laps

From here on P is a predicate of the linear fragment of section 2,
P = \n. f, with

    (HYP) P N ->>b T for every numeral term N,

which by Corollary 2.2 holds when the decision of section 3 finds f
valid. Only Lemma 4.6 uses that P is in the linear fragment, and it needs
it: a closed P with (HYP) outside the fragment may hold a closed subterm
with no whnf (for instance a lap under an abstraction that discards its
argument), and then (S2)(a) below fails.

A SELECTING CONTEXT is a term C whose free variables are distinct holes
x1, ..., xj (j >= 1), each occurring once, with C ->>b xi for some i, the
SELECTED hole. (SUB) and (CR) give at once:

- (C-sub) substituting a closed term for a hole other than xi keeps C
  selecting xi; substituting a selecting context for xi gives a selecting
  context;
- (C-red) a beta or eta reduct of C selects a residual of xi (for eta,
  by the commutation in (ETA); the holes being variables, a reduct of
  C[x1, ..., xj] selects one copy of xi when the copies are renamed
  apart).

LEMMA 4.1 (selection). Let C select xi and let E1, ..., Ej be closed. The
weak head reduction of C[E1, ..., Ej] makes exactly the steps of the weak
head reduction of C, reaching Ei.

PROOF. By (WH) the weak head reduction of C ends in xi. Along it no hole
reaches the head position before the end: a hole at the head would stop
it at a neutral term headed by that hole, and a neutral term reduces only
to neutral terms with the same head and the same number of arguments, so
it could not reach xi alone. So the head redexes are those of C, and
substituting closed terms for the holes changes none of them. QED

LEMMA 4.2 (junk). Let C select xi, and let K be a closed subterm occurrence
of C with no whnf. Then C with that occurrence replaced by V selects xi,
for every closed V.

PROOF. Along the weak head reduction of C, the residuals of K are copies of
K (K is closed and nothing inside it is contracted while it is not at the
head). If a copy reached the head position the reduction would continue
with K's own weak head reduction, which does not terminate, and would not
reach xi. A copy of K is never the operator of a head redex (K is not an
abstraction). So the same steps reduce the replaced context to xi. QED

LEMMA 4.3 (laps have no whnf). For every k, Φ `k` has no whnf.

PROOF. Its weak head reduction is

    Φ `k` ->wh G Φ `k` ->wh (\n. B0) `k` ->wh And (P `k`) (Φ `k+1`)
          ->wh (\b. P `k` b F) (Φ `k+1`) ->wh P `k` (Φ `k+1`) F

and C0 = P `k` x F selects x: by (HYP), P `k` x F ->>b T x F ->>b x. By
Lemma 4.1 it continues to Φ `k+1` (recall Succ `k` = `k+1`), and so on for
ever. QED

THE LAP TERMS. Let 𝓕 be the set of beta eta reducts of Y G and of Φ. A
LAP is a term φ N with φ in 𝓕 and N in 𝒩.

LEMMA 4.4. No lap has a beta eta reduct that is an abstraction.

PROOF. φ =be Φ (Y G and Φ have the common reduct G Φ) and N =b `k` for
some k, so φ N =be Φ `k`. An abstraction reduct of φ N would give, by
(CR) and (ETA), an abstraction beta reduct of Φ `k`, against Lemma 4.3.
QED

LEMMA 4.5 (the root step). If φ = \n. B is in 𝓕 and N is in 𝒩, then B0
->>be B, so that B[n := N] is a beta eta reduct of

    B0[n := N] = And (P N) (Φ (Succ N)) = C0'[Φ (Succ N)],
    C0' = And (P N) x,

and C0' selects x (And (P N) x ->>b P N x F ->>b T x F ->>b x by (HYP)),
while Φ (Succ N) is a lap.

PROOF. By (ETA), Y G (or Φ) ->>b φ1 ->>e φ. φ1 is an abstraction (eta
steps do not make an abstraction out of an application), so by (WH) the
beta reduction reaches the whnf \n. B0 of Y G (of Φ) first and then works
inside: φ1 = \n. B1 with B0 ->>b B1. If no eta step of φ1 ->>e φ is at the
root, φ = \n. B with B1 ->>e B. If one is, it is \n. (U n) ->e U with
B1 ->>e U n, and U ->>e φ = \n. B, so U n ->>e (\n. B) n ->b B. Either way
B0 ->>be B, and (SUB) gives the rest. QED

LEMMA 4.6 (tame pieces). Every closed subterm occurrence of a member of 𝓕
or of 𝒩 has a whnf.

PROOF. A closed abstraction has a whnf, so only closed applications
matter. For 𝒩: a beta eta reduct of `k` is built from Succ, Z and the
abstractions \z. \s. s X of partially reduced numerals; its closed
subterms are Succ, Z, abstractions, and numeral terms Succ X, each with a
whnf. For 𝓕 we show the stronger invariant: every closed subterm of a
beta eta reduct of Y G or Φ that is not an abstraction is a beta eta
reduct of one of

- (i) a closed subterm of Y, G, W or P as written (all abstractions, or
  spelled numerals, or closed applications of the APIs to numeral
  constants, which by Lemma 2.1 have a normal form or are partial
  applications with a whnf);
- (ii) an unfolding of a fixpoint: W W, G (W W), (\p. G (p p)) W, Y G, and
  the same for the APIs' bodies H: W_H W_H, H (W_H W_H),
  (\p. H (p p)) W_H, Y H; each reaches an abstraction in at most two weak
  head steps;
- (iii) a state of an API applied to closed numeral terms: E N1 N2 or
  E N1 for an API unfolding E, or a body of H with its parameters
  instantiated by numeral terms, or a branch of it such as
  \m1. N2 F (\n1. E m1 n1); by Lemma 2.1 each has a normal form or is an
  abstraction;
- (iv) a numeral term.

Each has a whnf, and a beta eta reduct of a closed term with a whnf has a
whnf (CR and (WH)). A beta step (\x. U) Q -> U[x := Q] creates new closed
subterms only as U'[x := Q] with U' a subterm of U, Q closed and x the only
free variable of U'; every other closed subterm of the result is a reduct
of a closed subterm of the term before the step, and an eta step creates
none. The redexes with a closed argument inside a reduct of Y G or Φ are:
the fixpoint's `(\p. g (p p)) W` and `g` applied to its argument (new
closed subterms of kind (ii)); G applied to W W, whose body's application subterms with m as their
only free variable are m alone (every other one contains n; the
abstraction \n. And (P n) (m (Succ n)) becomes a closed abstraction),
giving W W (ii); an API unfolding or body applied to closed
numeral terms, giving kind (iii); a Scott numeral n_k or a numeral term's
reduct applied to closed branches, giving a branch applied to a numeral
term, kind (iii) or (iv). A lap's own argument n is never instantiated
inside φ: the only application of the abstraction \n. B0 or of a copy of
G's inner abstraction inside a reduct of Y G or Φ has an argument
Succ (... (Succ n)) with n free, so the laps inside φ stay open. So no
closed subterm of kind other than (i) to (iv) appears. QED

## 5. The set S

Fix V in {T, F}. Let S be the set of closed terms

    C[E1, ..., Ej]

where C is a selecting context and each Ei is V or a lap. (V itself is
x1[V]; a lap L is x1[L].)

INV. Every member X of S either weak head reduces exactly to V (the weak
head reduction of X terminates, and its result is V), or has no whnf. By
Lemma 4.1 the weak head reduction of C[E1, ..., Ej] reaches the selected
Ei: V in the first case; a lap in the second, whose weak head reduction
does not terminate (Lemma 4.4 and (WH)).

NORMAL MEMBERS. The only member in beta normal form is V: a lap is not
normal (its weak head reduction does not terminate), and a selecting
context other than a bare hole has a redex (it reduces to something else),
which stays a redex after the substitution.

### (S3) V is the only abstraction in S

A member x1[E1] is V or a lap, an application. A member C[E...] with C not
a hole is an application: C is not a variable, and not an abstraction (an
abstraction reduces only to abstractions, not to xi).

### (S1) S is closed under ->b and ->e

Let X = C[E1, ..., Ej] and X -> X'. By induction on the length of the
reduction that produced the φ of each lap (below, ROOT).

- A step inside a lap φ N, not at its root: φ -> φ' in 𝓕 or N -> N' in
  𝒩; the lap stays a lap.
- The root step of a lap φ N with φ = \n. B: X' has B[n := N] at that
  hole. By Lemma 4.5, B[n := N] is a reduct of C0'[Φ (Succ N)], a member.
  The reduction from C0'[Φ (Succ N)] to B[n := N] has its steps inside
  the lap Φ (Succ N) taken from the steps that produced φ inside \n. B0,
  so every lap it roots is produced by a strictly shorter reduction, and
  the induction gives that B[n := N] is a member,
  C1[E'1, ..., E'm]. Substituting C1 for the hole (C-sub) gives a
  selecting context for X'.
- A step of the context: the redex has as its parts subterms of C and
  hole contents. A hole content is never the operator of a beta redex
  unless it is V (laps are applications); V at a non-selected hole xl is
  first substituted into C (C-sub), and then the step is a step of that
  context. V at the selected hole is never an operator: C ->>b xi, so xi
  never occurs applied in C or in its reducts (an application xi Q keeps
  its residuals applied). So the step is a step C -> C'' with the holes
  inside the redex's argument copied or erased, and C'' selects a copy of
  xi by (C-red); X' = C''[...] with each copy of a hole holding a copy of
  its content.
- An eta step is at an abstraction, so it is inside a lap's φ or N
  (covered above) or a step of the context (C-red); the root of a lap is an
  application and a hole content is never a whole eta redex.

### (S2) S is closed under collapse

Let X = C[E1, ..., Ej] be a member, o an occurrence in X holding a member
K, and X' = X with o replaced by V. If o is the root, X' = V. Otherwise:

- (a) o lies in a hole content El. If El = V, then o is its root (its
  proper closed subterms are normal and not V, and V is the only normal
  member): X' = X. If El is a lap and o its root, X' has V at that hole,
  a member. If o is proper in the lap, K is a closed subterm of φ or N, so
  it has a whnf (Lemma 4.6); by INV, K weak head reduces to V, so
  X ->>b X' and X' is a member by (S1).
- (b) o is a closed subterm of C, disjoint from the holes. If K weak head
  reduces to V, X ->>b X', a member by (S1). Otherwise K has no whnf
  (INV), and by Lemma 4.2 C with o replaced by V still selects xi:
  X' = C'[E1, ..., Ej] is a member.
- (c) o contains holes. If the selected hole is not inside o, substitute
  the contents of the holes inside o into C (C-sub): o becomes a closed
  subterm of the new context and case (b) applies. If the selected hole
  xi is inside o, let Co be the subterm of C at o, so K = Co[E...], and
  let C# be C with o replaced by a fresh hole y. If K weak head reduces to
  V, X ->>b X', a member by (S1). Otherwise K has no whnf. Co is not an
  abstraction (K is not, (S3)), and its free variables are holes (K is
  closed). Along the weak head reduction of C, the residuals of Co are
  copies of it, untouched until one reaches the head position, and it
  must reach it, since xi comes from inside it and xi is the whole final
  term. Then the term is Co A1 ... Am. Co has no abstraction reduct (it
  would give one of K), so its weak head reduction ends, if at all, in a
  neutral term xl B1 ... Bp, and Co A1 ... Am ->>b xi forces l = i and
  p = m = 0. So the weak head reduction of C reaches Co alone, and the
  same steps take C# to y: C# selects y, and X' = C#[V, ...] with the
  other holes' contents is a member.

So (S1), (S2) and (S3) hold, V is in S, and M = Y G `0` is a lap, so M is
in S.

## 6. The theorem

THEOREM. Let P = \n. f be a predicate of the linear fragment of section 2
whose formula f the decision of section 3 finds valid, so that (HYP)
holds. For V = T and for V = F, lambda beta eta + (M = V) is consistent,
where M = Y G Z.

PROOF. The collapse lemma (`false_only_small_cycles.md`, section 2, as
restated in `both_booleans_path_family.md`, section 1: V is T or F, S a
set of closed terms with V in S satisfying (S1) to (S3); (S4) follows
from (S3), the closed subterms of T and F being T, F and I, all
abstractions) gives that lambda beta eta + {X = V | X in S} is consistent,
and M is in S. QED

THE CLAIMS. With M = T, M a y = T a y = a, so `\a. M a y = \x. x` holds in
the theory, and the boolean(true) claim is consistent; with M = F,
M y a = a, and the boolean(false) claim is consistent. The
closed programs of section 7, `\y. \a. M a y` and `\y. \a. M y a` equal `\y. \a. a` in
the same theories.

## 7. With sets

The judgment with sets asks, for the closed program Q of a claim,
whether `\y. \a. a` is in S(Q), the normal form solution set: whether some yield Q' in the meaning
⟦Q⟧ has Th({Q' = \y. \a. a}) consistent, Th being lambda beta eta over
the terms with sets. Q holds no set, so Q is in ⟦Q⟧ (the clause pure of
the meaning, with Q' = Q), and it suffices that Th({M = V}) is consistent
over the terms with sets.

The collapse lemma's proof (the Z property of ->bd, the commutation of
->e, Hindley and Rosen) goes through over the terms with sets unchanged:
a set is a constructor with no rule of its own, so it adds no redex and
no critical pair, the maps psi and phi of the proof act on it by the
congruence, and every member of S is a pure lambda term, so an
S-occurrence inside a set is handled as any other occurrence. The two
distinct normal forms `true` and `false` stay distinct normal forms of
->bed. So Th({M = V}) is consistent, and both claims hold under the
judgment with sets.

## 8. A mechanical check

Not part of the proof. A script outside the repository, run on main at c556fbea8 under `doc/contest_limited.sh`:

- for each of the three theorem points, built P `k` from
  `contest_arithmetic_theorems:predicate/2` and `numeral/2` for k = 0 to
  60, evaluated it under weak_head, applied the head to the atoms t and f,
  and read t every time (HYP on those k: 61 of 61 for each point);
- did the same for the three counterexample points at k = 0 to 20 and read
  f exactly at the family's least counterexamples and after: at 5 for
  double_differs_plus_five, at 8 to 20 for plus_seven_at_least_double, at
  11 for double_plus_one_differs_plus_twelve;
- the bounds of section 3 for the three theorems: B = 3 for
  plus_three_differs (Eq (Plus n 3) n: n + 3 against n, equal slopes),
  B = 0 for double_at_least_itself (Geq (Double n) n: 2n against n), and
  B = 0 for plus_two_commutes (Eq (Plus n 2) (Plus 2 n): n + 2 against
  n + 2); each formula is true at k = 0, ..., B + 1.
