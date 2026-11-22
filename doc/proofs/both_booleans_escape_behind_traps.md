# The BOTH BOOLEANS conjectures of safety_escape_behind_traps are consistent

A written proof, 2026-09-28, for the
two scored conjectures of the class BOTH BOOLEANS on the point
`safety_escape_behind_traps` (`corpora/contest_hard_clauses.pl`, H4): its
term M, and the templates `boolean(true)`, the test \a. M a y, and
`boolean(false)`, the test \a. M y a (`corpora/contest_hard_claims.pl`).
Each claim is that lambda beta eta plus (test = \x. x) is consistent.

The proof reuses `doc/proofs/both_booleans_path_family.md`, cited below as THE PATH PROOF: its lemma (section 1), its
families and sets (section 3) with one more alternative for D, and its
checks (sections 4 and 5), which carry over with the additions of section 2
below. Section 3 shows that M beta reduces to a member of the extended
sets; section 4 derives the claims.

## 1. The term

In `corpora/contest_hard_clauses.pl` (`escape_behind_traps/3` with 12 traps
16 deep, `diamond_node/3`, `trap_chain/4`, `self_loop/1`, `good_node/2`,
`bad_leaf/1`), with Safe as in THE PATH PROOF, section 2:

    M       = (\trap. Safe Top) Trap
    Top     = Node_1
    Node_i  = \w. w F (Cons trap (Cons Node_(i+1) Nil))     1 <= i <= 12
    Node_13 = Loop = Y (\self. \w. w F (Cons self Nil))
    Trap    = the diamond node 16 deep over the bad leaf \w. w T Nil,
              written with one let (an applied abstraction) per layer

Contracting the lets of Trap and the two beta steps of each Cons gives the
closed terms

    One[a]    = \n. \c. c a Nil
    Two[a, b] = \n. \c. c a (One[b])
    P_0       = \w. w T Nil
    P_(d+1)   = \w. w F Two[P_d, P_d]

with Trap ->>b P_16, `Cons a Nil ->>b One[a]` and
`Cons a (Cons b Nil) ->>b Two[a, b]`.

## 2. The extended sets

Add to the families of THE PATH PROOF, section 3, the family of the loop's
halves and one alternative of D:

    O ::= \y. \w. w F (\n. \c. c (y y) Nil)
    D ::= G a | \w. w F L | O O'

(O has exactly one member.) Unfolding Y in Loop as in THE PATH PROOF,
section 2, gives Loop ->>b O O. S'_V is S_V with the extended families. The
checks of THE PATH PROOF carry over, with these additions:

- (S1), beta: O has no redex (its applications have a variable operator:
  w, c, y); O O' -> \w. w F (\n. \c. c (O' O') Nil), which is D's second
  form with the D of its L being O' O'. D = O O' as the D of B2 is a new
  head redex of the base, covered by this family step (B2's spine redex is
  still the one of D = \w. w F L). No other rule meets O.
- (S1), eta: O's abstractions end with the arguments (\n. \c. ...) and Nil,
  so O has no eta redex.
- (S3): unchanged; O O' is an application.
- The parity lemma: the new base shape is B2 with D = O O', the spine
  O O' B, head O with lam(O) = 2 and two arguments.
- THE HEADS: O applies its second bound variable to F and to
  \n. \c. c (y y) Nil, whose body applies its second bound variable to an
  application with a variable operator (y y); in \x. \w. w F L, the
  corresponding argument is a D, an application with a closed operator or
  an abstraction; in U, the second argument's body has its first bound
  variable or a closed term as its head; the other heads with two leading
  abstractions differ from O by their bodies' heads (THE PATH PROOF,
  section 5). So O is none of the heads that (N3) and (N5) name, and those
  facts stand.
- Non-members: O O' has one argument and a head with lam 2, excluded by
  parity, as in (N2). It is the only new closed application in the
  families; in case (d), the new prefix O of O O' B is an abstraction.

So S'_V satisfies (S1), (S2) and (S3), and the lemma of THE PATH PROOF,
section 1, applies to it.

## 3. M reduces to a member

LEMMA R (the traps are refuted). For every d and every B of the family B,
P_d B ->>b F. Hence C P_d ->>b F for every C (C ->>b \node. node B for some
B, and (\node. node B) P_d -> P_d B), and H[P_d] ->>b F for every H[h] (it
is C P_d or P_d B).

Proof, by induction on d. Write B = \bad. \s. bad F Tail[s], and recall
that Tail[t] ->>b t F K for some K (when Tail[t] = A t and A = U U', first
U U' -> \list. list F K).

- d = 0: P_0 B -> B T Nil ->> T F Tail[Nil] -> K(F) Tail[Nil] -> F.
- d + 1: P_(d+1) B -> B F Two[P_d, P_d] ->> F F Tail[Two[P_d, P_d]]
  ->> Tail[Two[P_d, P_d]] ->> Two[P_d, P_d] F K ->> K P_d One[P_d]
  ->> H[P_d] T Tail'[One[P_d]], where K = \h. \t. H[h] T Tail'[t]. By the
  induction hypothesis H[P_d] ->> F, and F T X ->> X, so this reaches
  Tail'[One[P_d]] ->> One[P_d] F K' ->> K' P_d Nil ->> H'[P_d] T Tail''[Nil]
  ->> Tail''[Nil], which is A Nil or Nil F K'', and both reduce to F
  (A Nil ->> Nil F K'' -> K(F) K'' -> F). END.

THE CHAIN. Write N_i for Node_i with Trap for trap and every Cons
contracted, so N_i = \w. w F Two[P_16, N_(i+1)] for i <= 12, and
N_13 = O O. First M -> Safe Top[trap := Trap] ->>b C0 N_1 with
C0 = W0 W0 (THE PATH PROOF, section 2), contracting the lets, the Cons and
the unfoldings of Y inside. Then, for i <= 12, every H[N_i] followed by a
trail reduces to H'[N_(i+1)] followed by the same trail and one more pair:
H[N_i] ->> N_i B for some B (as in Lemma R), and

    N_i B -> B F Two[P_16, N_(i+1)] ->> Tail[Two[P_16, N_(i+1)]]
          ->> K P_16 One[N_(i+1)] ->> H[P_16] T Tail'[One[N_(i+1)]]
          ->> F T Tail'[One[N_(i+1)]]                  (Lemma R)
          ->> Tail'[One[N_(i+1)]] ->> K' N_(i+1) Nil
          ->> H'[N_(i+1)] T Tail''[Nil]

with the steps of Lemma R's proof; Tail''[Nil] is A Nil or Nil F K, a
member of E, and the reduction happens at the head, so the trail after it
is kept. Starting from C0 N_1 (an H[N_1] with the empty trail), twelve such
passes give

    M ->>b H[O O] <E1 ... E12>

with every Ei in E, and H[O O] is C (O O) (B1) or (O O) B (B2), D = O O.
So M reduces to a member of S'_V, for V = `true` and for V = `false`.

## 4. The claims

By the lemma of THE PATH PROOF, section 1, applied to S'_V (section 2),
lambda beta eta + {N = V | N in S'_V} is consistent, and it proves M = V
(section 3). As in THE PATH PROOF, section 6, it proves \a. M a y = \a. a
when V = `true` and \a. M y a = \a. a when V = `false`, so both scored
conjectures `boolean(true)` and `boolean(false)` hold on
safety_escape_behind_traps. The argument uses the numbers 12 and 16 only
to name the nodes, so it holds for every number of traps and every trap
depth.

## 5. A mechanical check

Not part of the proof: the script of THE PATH PROOF, section 7, with O
added to D, run on `escape_behind_traps(2, 2, _)` and
`escape_behind_traps(3, 3, _)` (the point itself is 12 traps 16 deep, whose
trap written without lets is exponentially large). The head reduction of
each, after the unfoldings of Y, reached a member (I (A L) followed by a
trail, B6 over B7) after 253 and 791 steps, for both values of V; 40
random walks of up to 300 beta, eta and collapse steps from it, for each
instance and each V, met only members, with trails of up to seven pairs.
