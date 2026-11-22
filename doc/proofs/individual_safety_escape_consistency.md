# Consistency of both booleans on safety_escape_behind_traps

Claim. With M the program of `safety_escape_behind_traps`, both scored tests,
boolean(true) (T = \a. M a y) and boolean(false) (T = \a. M y a), are consistent with
lambda beta eta; it suffices that lambda beta eta + (M = v) is consistent for v = true
and v = false.

This proof extends `individual_path_rebuilt_consistency.md` (same lemma, same safe
program, same notation: T, F, Nil, Cons, Or, I, Y, Safe = Y S with A inside, and the
safe-code components P, C, C1, Z, H, W, K, O with their abstraction forms). Only the
graph and the productions it adds are described here.

## 1. The graph

From `contest_hard_clauses.pl` (`escape_behind_traps(12, 16, _)`):

    M      = (\Trap. Safe N12) TrapTerm
    Ni     = \n. n F (Cons Trap (Cons N(i-1) Nil))      i = 12 .. 1, N0 = Loop
    Loop   = Y (\self. \n. n F (Cons self Nil))
    TrapTerm: the top of a let-bound diamond of good nodes 16 deep over the bad leaf
    Leaf   = \n. n T Nil

Safe applied to a trap node reduces to F in finitely many steps (every path ends in the
bad leaf: Safe on the leaf gives T F (any Nil) ->> F, and on a diamond node any over its
two successors gives F by induction on depth). Write theta for the term at the trap
position: the variable Trap (inside the let's body, before the let is contracted) or a
reduct of TrapTerm.

## 2. Components added (for each theta)

- NC(theta): reducts of Ni[Trap := theta'], theta' a reduct of theta, i = 1 .. 12; an
  abstraction in it is `\n. n F (Cons theta'' (Cons N' Nil))` or a reduct of that list,
  with N' in NC(theta) or in NL.
- NL: reducts of Loop; an abstraction in it is `\n. n F (Cons Loop' Nil)`, Loop' in NL.
- The lists: reducts of `Cons theta' (Cons N' Nil)` and of `Cons N' Nil`; their
  abstraction forms `\n. \c. c h0 t0` with (h0, t0) = (theta'', a two-element tail's
  reduct) resp. (N'', Nil).
- TR(theta): reducts of `Q theta'` (Q in P), the trap computations. For theta closed,
  every element reduces to F and the only abstraction in TR(theta) is F; for theta the
  variable Trap, every element is stuck on the variable (`Trap C0` and its reducts) and
  none is an abstraction.
- TT: reducts of TrapTerm (finite data; every closed subterm has a weak head normal
  form).

## 3. The set G(v)

G(v) is the set of closed terms generated as in the path_rebuilt proof (Section 4
there), with N now NC(theta) U NL and the lists above, and these additions:

    m ::= ...                                   (the path_rebuilt productions)
        | O0 Y0 m | (\b. Y0 T b) m | Y0 T m      Y0 in TR(theta)     (Z or C, as m)
        | (\Trap. u) TT0                       TT0 in TT, u in G(v, Trap)   (Z or C)

    H-one ::= ... | \t. O0 Y0 W0 | \t. (\b. Y0 T b) W0 | \t. Y0 T W0

Here G(v, theta) is the same grammar with theta as the trap position; G(v) collects its
closed terms for theta a reduct of TrapTerm, plus the let production, whose body u is a
term of G(v, Trap) (open in Trap only). The slot m in `O0 Y0 m` holds the any-call over
the rest of a chain node's successor list, `Cons N' Nil`, which is a member (it reaches
the call on N'); in path_rebuilt that position held a K0.

M is the let production: u = Safe N12 is the production `Q N0` of G(v, Trap), TT0 =
TrapTerm.

## 4. (G1)

The path_rebuilt table applies, with these transitions added:

    L0 F H0 -> (\c. c h0 t0) H0 -> H0 h0 t0 -> H1 t0      (a list of either length)
    H1 t0   -> O0 m K0 ...                                (h0 a node, t0 = Nil: as before)
            -> O0 Y0 m ...                                (h0 = theta'', the trap: the
                                                           call on it is Y0 = Q theta'',
                                                           in TR; t0 the rest list, and
                                                           W0[t := t0], a reduct of Z t0,
                                                           is `Z0 t0` or `t0 F H0'`, a
                                                           production: the slot)
    O0 Y0 m     -> (\b. Y0 T b) m -> Y0 T m               (as for O0 m K0; eta on \b)
    Y0 T m      -> I m                                    (Y0 = F: F T -> I)
    (\Trap. u) TT0 -> u[Trap := TT0]                      in G(v, TT0): substituting
                                                           theta := TT0 maps each
                                                           component of G(v, Trap) into
                                                           the same component for TT0

`Y0 T m` has a root redex only when Y0 is an abstraction, that is Y0 = F, theta closed
(for theta = Trap no element of TR is an abstraction). No new production-level eta
redex (`\b. Y0 T b` is listed; `\t. O0 Y0 W0` ends in W0, never t).

## 5. (G2)

Every added production is an application.

## 6. (G3)

As in path_rebuilt. The added collapse states (`O0 Y0 m`, `(\b. Y0 T b) m`, `Y0 T m`,
`I m` with a (C) slot, and the let with a (C) body) reduce to v: Y0 reduces to F, then
`F T m ->> m ->> v`; the let contracts. A (Z) term has no weak head normal form: from a
call on a chain node the weak head reduction evaluates the trap call (finitely, to F),
then selects `m`, whose weak head reduction reaches the call on the next node; from a
call on a loop node it reaches the call on the next loop node; so the shortest-reduction
argument of path_rebuilt applies. Every closed subterm of a component element has a weak
head normal form (the added ones: nodes, lists, trap computations reaching F, TrapTerm's
data), and a (Z) occurrence is therefore the whole term or a slot. Inside the let body u
the closed members are the calls on loop nodes (a call on a chain node contains the
variable Trap); they occur at slots of G(v, Trap), which admit v.

## 7. Conclusion

For v = true and v = false, G(v) satisfies (G1) to (G3) and contains M; so both scored
tests of `safety_escape_behind_traps` are consistent. The cycle context is the loop's
`m T K0` (T T K0 ->> T, F T K0 ->> K0 ->> F); before the loop, each chain node gives the
value of the call on the next node through `F T m ->> m`, the trap having been refuted.
