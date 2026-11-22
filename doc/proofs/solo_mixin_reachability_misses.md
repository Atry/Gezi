# A node that no edge enters is never reached: the mixin reachability misses yield nothing

A written proof, 2026-09-30: the trap
conjecture `conjecture(no_yield)` of the class REACHABILITY MISSES of
`corpora/contest_mixin_traps.pl`, both booleans, holds. Each test yields
nothing, so both trap claims are false.

The module comment of `corpora/contest_mixin_traps.pl` argues this
statement but stops short of the cycles ("not proved along the unbounded
unfolding of the cycles"), and proves the diamond trap there, a different
statement. The proof uses, as a lemma, the argument of the MIXIN port that a
sequence of choices reaching a pure term chooses, at every read, a wrapper
that defines the slot read.

## 1. The programs

The encoding is `corpora/contest_mixin_library.pl` (MIXIN below):

- A **wrapper** of slot k of a hierarchy of width W is
  `\self. \c1. ... \cW. ck b`, b its body.
- A **read** of slot k of an object O is `O O c1 ... cW`, where ck is the
  handler (`\v. v`, or `\v. v a1 ... aj` when the read heads an
  application) and every other cj is the empty set `{}`. When O is not a
  variable, the read is written `(\o. o o c1 ... cW) O`.

A point of the class is given by a graph (V, E), a source s0 in V, and
one more node z not in V. In `contest_mixin_claims.pl`, graph_surface/3
builds `isolated(Graph)` as V' = V ∪ {z}, adding z to the nodes and no
edge. So:

    (H1) no edge enters z: there is no x with x -> z in E;
    (H2) z ≠ s0.

The program is

    P = Read_{is_z}( Read_{reachable}( Read_{s0}( Mod ) ) )

The parts are:

- Mod = { W_x | x in V' } is the module, a set of module wrappers. The
  module hierarchy has one slot per node, width |V'|.
- W_x is the wrapper of the module's slot x. Its body is the class
  C_x[S] of node x, over the module's self S.
- C_x[S] = { Mk_x, Re_x[S], Ne_x[S], Th_x }, a set of four wrappers of the
  node hierarchy. That hierarchy's slots are is_y for every y in V', then
  reachable, next and two_hop.
  - Mk_x is the wrapper of slot is_x, body the Church true.
  - Re_x[S] is the wrapper of slot reachable. Its body is the set
    U_x[S] = { R_y[S] | x -> y } ∪ { K_y[S] | x -> y }, where
    K_y[S] = Read_y(S) reads the module's slot y (the class of y) and
    R_y[S] = Read_{reachable}(K_y[S]).
  - Ne_x[S] is the wrapper of slot next. Th_x is the wrapper of slot
    two_hop, whose body reads next twice on its self.
  - The order in which the union lists its members does not matter below.

The claims' tests are `\a. P a y` (boolean(true)) and `\a. P y a`
(boolean(false)). As the judgment asks them, they are the closed programs
`\y. \a. P a y` and `\y. \a. P y a`.

## 2. What is to be shown

By lemma 2b of `doc/proofs/certificate_meta_lemmas.md`, every yield of a
term T equals a pure term reached from T by a finite sequence of
reductions and choices (choosing a member for an occurrence of a set). So
it suffices to show:

    (G) no finite sequence of reductions and choices from either test
        program reaches a pure term.

Then ⟦test⟧ = ∅ and S(test) = ∅. The curried identity is not in it, so
both trap claims are false.

## 3. The lemma

The argument of the MIXIN port: a read chooses a wrapper for the
first occurrence of its object, and a wrapper of another slot applies the
empty set to its body. A term with `{}` at its head has no member to
choose and no redex at its head, so no reduction or choice ever makes it
pure. Hence:

    (L) a sequence that reaches a pure term chooses, at every read it
        resolves, a wrapper that defines the slot read.

## 4. The proof

Suppose σ is a finite sequence of reductions and choices from a test
program that reaches a pure term. We derive a contradiction.

**The final read.**
- The body of the test program is `P a y` (or `P y a`). The head of P's
  spine is the read of is_z on the object `O0 = Read_{reachable}(Read_{s0}(Mod))`.
- A pure term has no read left at its head, so σ resolves this read.
- By (L), σ chooses for it a wrapper of slot is_z of the node hierarchy.
  In P, the only wrapper of slot is_z is Mk_z. It occurs only in C_z, and
  C_z occurs only in the body of W_z.

**The object.** We show that σ never delivers Mk_z as the chosen element
of the is_z read, by describing every element σ can choose there.

1. *The source's class.* σ resolves the read of the module's slot s0
   (it lies on the head's path). By (L) it chooses W_{s0}, whose body is
   C_{s0}[S0], S0 a copy of Mod with whatever choices σ makes in it. The
   read of reachable on C_{s0}[S0] chooses, by (L), Re_{s0}[S0], whose
   body is the set U_{s0}[S0]. So O0 becomes U_{s0}[S0].
2. *Elements of a union.* The is_z read applies the first occurrence of
   its object to the second and to the handlers. The chosen element is a
   member of U_x[S] for some node x, either K_y[S] or R_y[S] with x -> y.
3. *A class element.* An element K_y[S] = Read_y(S) is a read of the
   module's slot y. By (L), σ chooses W_y for it, and its result is the
   set C_y[S′]. This set now stands in the is_z read's head position, so
   σ chooses one of its members Mk_y, Re_y, Ne_y, Th_y. By (L) that
   member must define is_z. But Mk_y defines is_y, and y ≠ z by (H1),
   since x -> y. The other three define reachable, next and two_hop.
   None defines is_z, so this branch contradicts (L).
4. *An unfolding.* An element R_y[S] = Read_{reachable}(K_y[S]) first
   resolves the read of slot y (step 3's first half: W_y, then C_y[S′]).
   It then resolves a read of reachable on C_y[S′], which by (L) chooses
   Re_y[S′] and yields U_y[S′]. That set stands where the element stood,
   so σ again chooses one of its members, a K or an R of a successor of y
   (step 2).

**Induction on the reads σ resolves.** Let e0, e1, e2, ... be the
elements σ chooses at the is_z read's head position, each obtained from
the previous one by step 4.
- Each step 4 resolves at least two reads of σ: the read of the module's
  slot y and the read of reachable.
- σ is finite, so it resolves finitely many reads, and the chain is
  finite.
- Its last element is a K_y[S] (step 3, a contradiction), or an R whose
  reads σ does not resolve. In the second case the is_z read keeps an
  unresolved read at its head and σ does not reach a pure term, again a
  contradiction.
- Every node y in the chain is reached from s0 by edges, and none of them
  is z, since no edge enters z (H1). So no element of the chain is Mk_z,
  and no step delivers it.

So σ cannot resolve the is_z read with a wrapper defining is_z, against
(L). No such σ exists, which proves (G).

**Where the cycles went.** The module comment of
`contest_mixin_traps.pl` leaves open "the unbounded unfolding of the
cycles". A cycle lets step 4 repeat without bound, but a sequence that
reaches a pure term is finite. The induction is on that sequence's reads,
not on the graph, so the cycles need no separate argument. (H2) is not
used beyond making the source's class a class of V: z is not the source,
so no read of the module's slot z occurs in P at all.

## 5. The points covered

Each of the following is `graph_surface(isolated(Graph), reaches(Source, z), Term)`
(`miss_term/2` of `corpora/contest_mixin_traps.pl`). isolated/1 appends z
with no edge, so (H1) holds, and z is none of the sources below, so (H2)
holds:

| point | graph | source |
|---|---|---|
| `mixin_ring_three_misses` | ring(3) | n0 |
| `mixin_ring_twenty_misses` | ring(20) | n0 |
| `mixin_ring_forty_misses` | ring(40) | n0 |
| `mixin_two_rings_misses` | two_rings | n0 |
| `mixin_chord_ring_misses` | chord_ring | n0 |
| `mixin_lasso_misses` | lasso | t0 |
| `mixin_double_successor_ring_misses` | double_successor_ring | n0 |

The proof does not depend on the order of the union in Re_x
(recursive_first or direct_first), on the handler's form, or on the number
of nodes. Whether a node is reached from the source is not needed either:
the argument only uses that the successors of every node differ from z.
