# The BOTH BOOLEANS conjectures of the H5 path family are consistent

A written proof, 2026-09-28, for the
eight scored conjectures of the class BOTH BOOLEANS on the points

    path_rebuilt_by_identity           rebuild x = (\f. f) x
    path_rebuilt_by_plus_minus_small   rebuild x = x + 3 - 3
    path_rebuilt_by_plus_minus_tiny    rebuild x = x + 1 - 1
    path_eta_expanded                  rebuild x = \a. x a

(`corpora/contest_hard_clauses.pl`, H5 and H14). Each point's term M is
`safe (gen start)`, gen building an infinite path of good nodes, and its two
scored claims are the templates `boolean(true)`, the test \a. M a y, and
`boolean(false)`, the test \a. M y a, with y free
(`corpora/contest_hard_claims.pl`). Each claim is that lambda beta eta plus
(test = \x. x) is consistent.

The proof: for V = `true` and for V = `false`, a set S_V of closed terms that
contains a reduct of M and satisfies the hypotheses of the collapse lemma of
`doc/proofs/false_only_small_cycles.md` (section 2), so that lambda beta eta
+ (M = V) is consistent (sections 1 to 5); the claims follow (section 6).
The argument never looks inside the rebuild or the start, so one argument
serves the four points.

## 1. Notation and the lemma

Notation, the facts (F1) to (F5) and the lemmas (D1), (D2) are those of
`false_only_small_cycles.md`, section 1. Application associates to the left.
The prelude's constants (`corpora/prelude_clauses.pl`):

    T = \t. \f. t      F = \t. \f. f      I = \f. f
    Nil = \n. \c. n    (the same term as T, up to alpha)
    Cons = \h. \t. \n. \c. c h t          Or = \a. \b. a T b
    Y = \g. (\p. g (p p)) (\q. g (q q))

For a closed term P, `K(P)` is `\z. P`, z fresh. A closed term that is not an
abstraction is `h a1 ... am` with m >= 1 and h a closed abstraction, its
HEAD; its SPINE is h with the arguments a1 to am. For a closed abstraction h,
`lam(h)` is its number of leading abstractions: h = \z1. ... \zk. P with P
not an abstraction gives lam(h) = k (lam(T) = lam(F) = 2, lam(I) = 1,
lam(K(T)) = 3).

THE LEMMA FOR BOTH BOOLEANS. The collapse lemma of
`false_only_small_cycles.md` (section 2) is stated for a closed beta eta
normal member V of S; its proof uses V = `false` only in its last paragraph,
THE THEORY, and runs as well for V = `true`, which is a closed beta normal
abstraction, as (D2) needs. For V in {`true`, `false`} the hypothesis (S4)
follows from (S3): the closed subterms of `true` and `false` are T, F and I,
all abstractions, so by (S3) none of them other than V is in S. The
paragraph THE THEORY then reads: T and F are beta eta normal, and each of
their closed subterms is V, which no collapse step rewrites, or is not in S;
so T and F are distinct normal forms of the confluent ->bed, and lambda beta
eta + {N = V | N in S} does not equate them. This is the form used below:

LEMMA. Let V be `true` or `false`, and S a set of closed terms with V in S,
satisfying (S1) closure under ->b and ->e, (S2) closure under collapse, and
(S3) V is the only abstraction in S. Then lambda beta eta + {N = V | N in S}
is consistent.

## 2. The terms

In `corpora/contest_hard_clauses.pl` (`safe/1`, `generated_path/2`,
`eta_generated_path/1`), each point's term is

    M = Safe (Gen Z)
    Safe = Y (\self. \node. node (\bad. \s. bad F (Y AnyBody s)))
    AnyBody = \any. \list. list F (\h. \t. Or (self h) (any t))
    Gen = Y (\g. \x. \w. w F (Cons (g R[x]) Nil))

(s names the successors, w the node built by gen), with the start Z and the
rebuild R[x], a term whose only free variable is x:

    path_rebuilt_by_identity           Z = T (zero)   R[x] = (\f. f) x
    path_rebuilt_by_plus_minus_small   Z = T (zero)   R[x] = PlusMinus3 x
    path_rebuilt_by_plus_minus_tiny    Z = T (zero)   R[x] = PlusMinus1 x
    path_eta_expanded                  Z = I          R[x] = \a. x a

PlusMinusK is the closed term `plus_minus(K, _)` of the corpus; its shape
plays no part below. Define

    U0 = \y. \list. list F (\h. \t. x x h T (y y t))       (x free)
    W0 = \x. \node. node (\bad. \s. bad F (U0 U0 s))
    X0 = \y. \x. \w. w F (\n. \c. c (y y R[x]) Nil)
    M' = W0 W0 (X0 X0 Z)

M ->>b M'. In Safe, Y applied to its body contracts to
(\p. SafeBody (p p)) (\q. SafeBody (q q)); in each half, SafeBody (q q)
contracts to \node. node (\bad. \s. bad F (Y AnyBody' s)), AnyBody' being
AnyBody with q q for self; Y AnyBody' contracts to two halves, in each of
which AnyBody' (p' p') contracts to \list. list F (\h. \t. Or (q q h)
(p' p' t)), and the two beta steps of Or give q q h T (p' p' t). Renaming q
to x and p' to y, each half of Safe is W0 and each half of Y AnyBody' is U0.
In Gen the same unfolding of Y, and the two beta steps of Cons, which give
`\n. \c. c (g R[x]) Nil`, make each half X0. Every step is a beta step, some
under abstractions.

## 3. The sets

THE FAMILIES. The following grammars define sets of terms. In them, a and
a' range over ARBITRARY terms whose free variables are among those allowed
at their place: the x bound by the enclosing X, or by the enclosing second
form of G, and no other (none at all outside both), and s, t, h, x, y, list, node, w, n, c, bad are bound variables,
and a primed letter is another member of the same family.

    C       ::= W W' | \node. node B
    W       ::= \x. \node. node B°
    B       ::= \bad. \s. bad F Tail[s]
    Tail[t] ::= A t | t F K
    A       ::= U U' | \list. list F K
    U       ::= \y. \list. list F (\h. \t. H[h] T (y y t))
    K       ::= \h. \t. H[h] T Tail[t]
    H[h]    ::= C h | h B

    G       ::= X X' | \x. \w. w F (\n. \c. c D Nil)
    X       ::= \y. \x. \w. w F (\n. \c. c (y y a) Nil)
    D       ::= G a | \w. w F L
    L       ::= \n. \c. c D Nil

    E       ::= A Nil | Nil F K | K(F) K | F
    Q[s]    ::= F F Tail[s] | I Tail[s] | Tail[s]

B°, and the Tail°, A°, U°, K° it is built from, are the same grammars with
every H[h] replaced by `x x h`, x being the variable W binds. Inside W,
x x h is the only occurrence of x; when W W' contracts, x x h becomes
W' W' h = C h. So W0 is a W, U0 a U°, X0 an X (a = R[x]), X0 X0 a G, and
X0 X0 Z a D.

A TRAIL is a sequence of pairs; for a term P and members E1, ..., Ek of E,
`P<E1 ... Ek>` is P T E1 T E2 ... T Ek (P itself when k = 0).

THE SETS. For V in {`true`, `false`}, S_V is the least set of terms closed
under the rules

    (V)   V
    (B1)  C D                      (B2)  D B
    (B3)  B F L                    (B4)  (\s. Q[s]) L
    (B5)  F F N, N in S_V          (B6)  I N, N in S_V
    (B7)  A L                      (B8)  L F K
    (B9)  (\c. c D Nil) K          (B10) K D Nil
    (B11) (\t. N T Tail[t]) Nil, N in S_V
    (P)   N T E, N in S_V and E in E

and, for V = `true` only,

    (T1)  K(T) E  and  K(T) Nil    (T2)  (\t. K(T) Tail[t]) Nil

and, for V = `false` only,

    (F1)  E                        (F2)  (\t. I Tail[t]) Nil
    (F3)  (\t. Tail[t]) Nil

in which every family member is drawn from the families above. The terms of
the rules other than (V), (P), (F1) are BASES; every member is
V<E1 ... Ek> or P<E1 ... Ek> with P a base (or, for `false`, an E). Every
rule builds a closed term from closed ones. M' is a member of both sets,
by (B1).

The rules follow the weak head reduction of M': B1 to B10 are its states
around the cycle, B11 closes it (N T Tail[Nil] is the next B1 or B2 with one
more pair), B5, B6 and the decay rules T1, T2, F1 to F3 hold what collapse
leaves, and (P) the pairs T E the cycle accumulates.

## 4. Checking (S1) and (S3)

(S3). Every base is an application, and so is every term (P) builds; an E
other than F is an application. So V is the only abstraction in S_V.

(S1), beta. By induction on the derivation of a member, every one-step beta
reduct of a member is a member. A redex of a member lies inside an argument
a (the reduct is another arbitrary term there, with no new free variable),
inside a family member, inside a member N or E the rule was applied to (the
induction hypothesis), or at the head of the member's spine.

THE FAMILIES ARE CLOSED UNDER BETA. The redexes inside family members and
their contractions:

- C: W W' -> \node. node B (x x h becomes C h, see above).
- Tail[t]: A t with A = \list. list F K contracts to t F K.
- A: U U' -> \list. list F (\h. \t. H[h] T (U' U' t)), which is
  \list. list F K with Tail[t] = A' t, A' = U' U'.
- H[h]: C h with C = \node. node B contracts to h B.
- G: X X' -> \x. \w. w F (\n. \c. c (X' X' a) Nil), the second form of G
  with D = G' a, G' = X' X'.
- D: G a with G = \x. \w. w F (\n. \c. c D' Nil) contracts to
  \w. w F (\n. \c. c D'[x := a] Nil), the second form of D: substituting a
  for x changes only arguments, keeping their free variables allowed.
- E: A Nil with A = \list. list F K contracts to Nil F K; Nil F -> K(F),
  so Nil F K -> K(F) K; K(F) K -> F.
- Q[s]: F F -> I, so F F Tail[s] -> I Tail[s]; I Tail[s] -> Tail[s].

No other application of the grammars is a redex: every other one has as
its operator a variable (bad, list, c, w, y, x, t, h, node, s) or an
application that is not an abstraction (H[h] in H[h] T, F F in
F F Tail[s]). The same holds for B°, Tail°, A°, U°, K°, in which x x h has
no redex.

THE HEAD REDEXES of the members:

- B1 C D, C = \node. node B: -> D B (B2).
- B2 D B, D = \w. w F L: -> B F L (B3).
- B3 B F L: B F -> \s. F F Tail[s], giving (\s. F F Tail[s]) L (B4).
- B4 (\s. Q[s]) L -> Q[L]: F F Tail[L] (B5), I Tail[L] (B6), or Tail[L],
  which is A L (B7) or L F K (B8); both Tail[L] are members, so B5 and B6
  apply.
- B5 F F N: F F -> I, giving I N (B6). B6 I N -> N.
- B7 A L, A = \list. list F K: -> L F K (B8).
- B8 L F K: L F -> \c. c D Nil, giving B9. B9 -> K D Nil (B10).
- B10 K D Nil: K D -> \t. H[D] T Tail[t], giving (\t. H[D] T Tail[t]) Nil,
  which is B11 with N = H[D], that is C D (B1) or D B (B2).
- B11 (\t. N T Tail[t]) Nil -> N T Tail[Nil], and Tail[Nil] is A Nil or
  Nil F K, an E: rule (P).
- (P) N T E: N T is a redex only when N is an abstraction, that is N = V.
  For `true`: T T E -> K(T) E (T1). For `false`: F T E -> I E, which is B6
  since E is a member by (F1).
- T1: K(T) E -> T and K(T) Nil -> T. T2: -> K(T) Tail[Nil] (T1), and its
  inner K(T) Tail[t] -> T gives K(T) Nil (T1).
- B11 with N = T (`true`): the inner T T Tail[t] -> K(T) Tail[t] gives T2.
- F2: -> I Tail[Nil] (B6, Tail[Nil] being in S_false by F1); its inner
  I Tail[t] -> Tail[t] gives F3. F3: -> Tail[Nil] (F1).
- B11 with N = F (`false`): the inner F T Tail[t] -> I Tail[t] gives F2.

A trail adds no redex (its T and E are arguments), and a redex inside the
member N of B5, B6, B11 or (P), or inside the Q of B4, is covered by the
induction or by the family closure. So every beta reduct of a member is a
member.

(S1), eta. An eta redex is \z. P z with z not free in P. Going through the
abstractions of the grammars and rules, the body of each ends with an
argument other than its bound variable (node B, bad F Tail[s], list F K,
H[h] T Tail[t], H[h] T (y y t), w F (...), c D Nil, c (y y a) Nil, N T
Tail[t], K(T) Tail[t], I Tail[t]; T, F, I, K(T), K(F) are not of the form
P z), except two: \s. A s (B4 with Q[s] = Tail[s] = A s) and \t. A t (F3
with Tail[t] = A t). Their eta steps give A L (B7) and A Nil (an E, a
member of S_false by F1). Eta redexes inside arguments a give other
arbitrary terms. So every eta reduct of a member is a member.

## 5. Checking (S2)

THE PARITY LEMMA. Every member of S_V is V, or h a1 ... am with m and
lam(h) of the same parity. Proof: the bases, with their heads, lam of the
head, and number of arguments:

    base                 head                      lam   args
    B1 W W' D            W                          2     2
    B1 (\node...) D      \node. node B              1     1
    B2 X X' a B          X                          3     3
    B2 (\x. \w...) a B   \x. \w. w F L              2     2
    B2 (\w. w F L) B     \w. w F L                  1     1
    B3 B F L             B                          2     2
    B4                   \s. Q[s]                   1     1
    B5 F F N             F                          2     2
    B6 I N               I                          1     1
    B7 U U' L            U                          2     2
    B7 (\list...) L      \list. list F K            1     1
    B8 L F K             L                          2     2
    B9                   \c. c D Nil                1     1
    B10 K D Nil          K                          2     2
    B11, T2, F2, F3      \t. ...                    1     1
    T1 K(T) E, K(T) Nil  K(T)                       3     1
    (V) V                V                          2     0
    F1 U U' Nil          U                          2     2
    F1 (\list...) Nil    \list. list F K            1     1
    F1 Nil F K           T                          2     2
    F1 K(F) K            K(F)                       3     1

and (P) adds two arguments. END.

THE HEADS. Two rows of the table have the same head only when the same term
arises twice: \s. s F K (B4, Q[s] = Tail[s] = s F K) is \list. list F K
(B7, F1) and \t. t F K (F3); \s. A s (B4) is \t. A t (F3); \s. I Tail[s]
(B4) is \t. I Tail[t] (F2). Otherwise the heads are told apart by their
leading abstractions and their bodies (after the leading abstractions):
the bodies of T, F, K(T), K(F) and I are variables (T its first bound
variable, F its second, K(T) its second, K(F) its third, I its first); W's
body applies its second bound variable to one argument; the bodies of X,
\x. \w. w F L, U and L apply their last bound variable to two arguments,
the first F for X, \x. \w. w F L and U and a D (an application, or an
abstraction whose body is an application, so not F) for L; X has three
leading abstractions and the others two; the second argument is
\n. \c. c D Nil for \x. \w. w F L, whose body applies its second bound
variable, and \h. \t. H[h] T (y y t) for U, whose body has as its head its
first bound variable (H[h] = h B) or a closed term (H[h] = C h). In the
same way K (\h. \t. H[h] T Tail[t]) and B (\bad. \s. bad F Tail[s]) differ
from each other (three arguments against two, or a closed head) and from
the rest (their bodies' heads are their first bound variable or a closed
term). Among the heads with one leading abstraction, \node. node B applies
its variable to one argument, \w. w F L and \list. list F K apply it to F
and an L or a K (told apart as above), \c. c D Nil to a D and Nil, and the
bodies of the others have a closed head (F, I, K(T), an A's head, or an
N's head).

NON-MEMBERS. The closed subterms of a member that the rules do not make
members are not members:

- (N1) N T for N in S_V: it has one argument more than N, so the parity
  lemma excludes it.
- (N2) W W', U U', F F, T T, F T, Nil F, K D, L F, B F: one argument, a head
  with lam 2. Excluded by parity.
- (N3) X X' (a G of the first form): lam(X) = 3 and one argument, so parity
  allows it, but by THE HEADS the only members whose head is an X are
  B2's X X' a B<E1 ... Ek>, with at least three arguments.
- (N4) G a: head X with two arguments, or head \x. \w. w F L (lam 2) with
  one. Excluded by parity.
- (N5) For V = `true`, the members of E other than F: A Nil is U U' Nil or
  (\list. list F K) Nil. By THE HEADS, the members of S_true with a head U
  are B7's U U' L<E1 ... Ek>, and those with the head \list. list F K are
  B7's and B4's (\list. list F K) L<E1 ... Ek> (F1 and F3 are rules of
  S_false only); in each, the argument after U U', or the first, is an
  L = \n. \c. c D Nil, and Nil = \n. \c. n is not an L. Nil F K has the
  head T and the first argument F, while the only members of S_true with
  the head T are T<E1 ... Ek>, whose first argument is T. K(F) K has the
  head K(F), the head of no member of S_true (F1 is a rule of S_false
  only).

THE S-OCCURRENCES. Let N be a member and O an S-occurrence in N holding a
member P != V. Then O is one of:

- (a) N itself: the collapse gives V, a member.
- (b) inside an argument a: the collapse gives another arbitrary term with
  no new free variable, so the rule still applies.
- (c) inside, or at, a member the rule was applied to (the N of B5, B6,
  B11, (P), and for `false` an E of a trail, of F1, or of B6): by induction
  on the derivation the collapse gives a member there (V, when it is the
  whole of that member), and the same rule applies to it: F F V, I V,
  (\t. V T Tail[t]) Nil and V T E are B5, B6, B11, (P) with N = V; an E
  collapsed is F, an E.
- (d) a proper prefix of N's spine, h a1 ... aj of h a1 ... am, j < m. By
  the parity lemma m - j is even. If the prefix covers the base and the
  first pairs of the trail, the collapse gives V followed by the other
  pairs, V<E(i+1) ... Ek>, a member by (V) and (P). Otherwise the prefix
  lies inside a base with two or more arguments and drops an even number of
  them: W (from W W' D), X X' (from X X' a B), and the heads B, F, U, L, K,
  T, \x. \w. w F L alone. The heads are abstractions, not members unless
  they are V (then the collapse changes nothing and is not a collapse
  step), and X X' is not a member (N3).
- (e) any other closed subterm of N. These lie in the family members and in
  the decay bases. Going through the grammars, the closed subterms of a
  family member other than its arguments' subterms are abstractions (C's
  second form, W, B, U, K, X, G's second form, L, D's second form, \list.
  list F K, T, F, I, K(F), K(T)), not members unless V, and the closed
  applications W W', U U', X X', G a, F F (in Q) and, in E, A Nil, Nil F K,
  K(F) K and Nil F. Every other application of the grammars contains a
  bound variable. In the bases, the closed applications that are not
  family members, arguments, or the members of (c) are the spine prefixes
  of (d) and N T in B11 and (P). By (N1) to (N5), none of these is a
  member, except the E of an S_false member, covered by (c).

So every collapse of a member is a member: (S2) holds.

## 6. The claims

By sections 3 to 5, for V = `true` and for V = `false`, S_V satisfies the
hypotheses of the lemma of section 1, and contains M' (B1). So lambda beta
eta + {N = V | N in S_V} is consistent, and it proves M = M' = V (M ->>b M',
section 2). In it, for every term y,

    V = true:   (\a. M a y) = \a. T a y = \a. a
    V = false:  (\a. M y a) = \a. F y a = \a. a

by beta, so it proves the universal closure of each test's equation with
\x. x; lambda beta eta + (\a. M a y = \x. x) and lambda beta eta +
(\a. M y a = \x. x) are sub-theories of consistent theories, hence
consistent. The scored conjectures `boolean(true)` and `boolean(false)`
hold on each of path_rebuilt_by_identity, path_rebuilt_by_plus_minus_small,
path_rebuilt_by_plus_minus_tiny and path_eta_expanded.

Since the arguments a are arbitrary, the argument holds for every start Z
and every rebuild R[x] with no free variable but x; the point
path_rebuilt_by_plus_minus_large, which carries no claim, is covered as
well.

## 7. A mechanical check of the sets

Not part of the proof: a script outside the repository implemented the
grammars of section 3 as a membership test, computed M' as the result of
contracting M's redexes innermost first except self-applications, and, for
each of the four points and both values of V, checked that M' is a member,
explored the first 300 terms reached from M' by beta, eta and collapse
steps breadth first, and ran 60 random walks of up to 400 steps (weak head
steps preferred, so that the walks go around the cycle and build trails of
up to four pairs, and collapses of proper subterms). Every term reached was
a member, no closed abstraction other than V occurring in a reached term
was a member, T, F and I were not members except V, and every walk that
collapsed the whole term reached V.
