# Meta-lemmas for cyclic certificates over lambda beta eta with sets

Written 2026-09-29. Hand proofs, not machine-checked. Theorems 1, 2, 4, 5 and 9, Lemmas 2a, 2b
and 6, Propositions 3 and 8, and Corollary 7a are proved here. The proofs of Theorem 2,
Lemma 6 and Proposition 8 use cited results: the consistency of H* and its
characterisation by Böhm trees up to η-expansion (Barendregt 1984, chapters
16 and 19), and Böhm-out (chapter 10).

FIXME (2026-10-04): the formal definition no longer defines S through the meaning ⟦T⟧ https://github.com/Atry/private-overlay/issues/2014
(since 90beebf2b and 11f945f06); the
results below are about the yield-based judgment and are to be redone, where they
still matter, under the equations U of 0, + and ∥ (since 19f71383c).

The judgment is the yield-based one: terms Λ⁺ (λ terms with sets `{M1, …, Mn}`), the theory
Th(E), the meaning ⟦T⟧ ⊆ Λ of a term (the least relation D ⊆ Λ⁺ × Λ closed
under pure terms, Th(∅) equality, and set occurrences: an occurrence in any
one-hole context stands for the union over its members), and

    S(T) = { N ∈ NF | ∃ T′ ∈ ⟦T⟧. Th({T′ = N}) is consistent }.

The elements of ⟦T⟧ are T's *yields*. A term is *pure* when it contains no set.
A *member replacement* U ▷ U′ replaces one set occurrence by one of its
members: U = C[{M1, …, Mn}] and U′ = C[Mi], C a one-hole context. It is a
device of the proofs below, not a step of the semantics: the set condition
of ⟦·⟧ says exactly that ⟦U′⟧ ⊆ ⟦U⟧ whenever U ▷ U′. β ∪ η on Λ⁺ is
confluent, sets being constructors.

The questions answered:

- which equational reasoning a certificate may use, and where, so that the
  kernel's acceptance implies N ∈ S(T);
- whether cycles in a certificate (knots, assumptions confirmed by returning to
  them) are sound, in the two forms guarded and descending;
- whether Böhm-tree reasoning is sound for lambda with sets.

## 1. Sets add no equations

Th(E) is the least set of equations closed under its rules, so each of its
members has a finite DERIVATION: a finite tree of rule applications whose
leaves are equations of E, B, H or R. Fix such a derivation D. For each
n ≥ 0 such that a set with n members occurs in D, choose a variable c_n that
occurs in no term of D, the c_n distinct. They exist, since Var is countably
infinite and D mentions finitely many variables. Relative to D, define the
translation t from Λ⁺ to Λ by

    t(x) = x    t(λx. M) = λx. t(M)    t(M N) = t(M) t(N)
    t({M1, …, Mn}) = c_n (λz. z t(M1) … t(Mn))        z not free in any Mi

**Theorem 1 (c_n chosen relative to a derivation).** Let D be a derivation of
A = B in Th(E), E_D the equations of E at its leaves, and t the translation
relative to D. Then λβη + t(E_D) proves t(A) = t(B), where
t(E_D) = { t(L) = t(R) | L = R ∈ E_D }. Hence:
- if Th(E) is inconsistent, then so is λβη + t(E_D) for a derivation D of
  λx.λy. x = λx.λy. y;
- for a set E of pure equations, t(E_D) = E_D ⊆ E, and t fixes pure terms,
  so Th(E) ∩ (Λ × Λ) = Th_Λ(E), the closure of E in pure λβη; in particular
  Th(E) is consistent exactly when λβη + E is.

*Proof.* The c_n occur nowhere in D, so no step of D binds them or
substitutes for them, and t commutes with the substitutions D performs:
t(M[x := N]) = t(M)[x := t(N)], because c_n is never bound and z is bound and
fresh. FV(t(M)) is FV(M) together with some c_n, so for every variable x of D,
x ∉ FV(M) iff x ∉ FV(t(M)). Induction on D:
- A leaf in E maps to an equation of t(E_D).
- β maps to β, and η maps to η, with the same side condition.
- Reflexivity, symmetry, transitivity, ν, μ and ξ map to themselves.
- The set rule σ maps to μ, then ξ, then ν and μ inside c_n (λz. z …).

The translation fixes λx.λy. x and λx.λy. y. For pure E, a pure equation
A = B derived in Th(E) is derived in λβη + E over terms whose only other
variables are the c_n, which are variables of Var; that is Th_Λ(E). The
converse inclusion Th_Λ(E) ⊆ Th(E) holds because Th(E) ∩ (Λ × Λ) contains E
and the pure equations of B, H and R, and is closed under the rules
restricted to Λ. ∎

Theorem 1 answers the question as item 8 of the label-free design states it.
Let B⁺ be the set of equations A = B with BT(t(A)) = BT(t(B)), t chosen with
c_n occurring in neither A nor B: Böhm-tree equality with a set read as a head
constructor and its operands compared by position. The choice does not
matter, since renaming a variable that occurs in neither side renames both
Böhm trees alike. B⁺ is consistent, since B is: a derivation of
λx.λy. x = λx.λy. y from finitely many equations of B⁺ translates, with c_n
fresh for all of them, into one from equations of B. Proposition 3 shows that this is the
wrong question: consistency of B⁺ does not make Böhm-tree reasoning sound for S.

## 2. Reasoning in H* is sound on set-free terms

FIXME (2026-10-01): this section argues soundness through H*, which is ruled https://github.com/Atry/private-overlay/issues/2014
out as a basis: every lemma rests on S, not on H*. H* identifies every unsolvable term,
while collapse equations that hold by S do not; this argument is no ground
for admission until it is replaced by one stated in S.

H* is the λ theory of Hyland and Wadsworth: M = N when, for every context C,
C[M] is solvable exactly when C[N] is. It is consistent, contains β and η, and
equates two terms exactly when their Böhm trees are equal up to possibly
infinite η-expansion (Barendregt 1984, chapter 16; the theory of D∞).

**Theorem 2.** Let T′ ∈ ⟦T⟧ and N ∈ NF. If T′ and N are equal in H*, then
N ∈ S(T).

*Proof.* T′ is pure, since ⟦T⟧ ⊆ Λ. λβη + {T′ = N} is contained in H*, which is
consistent. By Theorem 1, Th({T′ = N}) is consistent. ∎

The theorem needs the whole equation T′ = N to be an equation of H*. Whether
replacing a subterm by an H*-equal one preserves S is open: it follows if the dual
reading of D-infinity is complete for S, a paper proof not in this repository. Ω and
Y K, both unsolvable and so equal in H*, both have every closed beta-eta normal form
as a solution, although Y K = λx. x
is inconsistent as an equation (it gives λx. x = Y K = λy. Y K = λy. λx. x).

## 2a. Yields are reached forward

Write →c for one β step, one η step or one member replacement. A *descendant* of an
occurrence s along a reduction is a residual of s; a set is never part of a
redex pattern, so its descendants are sets with the same number of
members. A descendant may lie inside a member of another descendant, when a
self application copies s into itself.

**Lemma 2a (replay).** Let U →* R by β and η steps, let s be an occurrence of a
set {M1, …, Mn} in U, n ≥ 1, and let U′ be U with s replaced by Mi. Let Rᵢ be
R with every descendant of s replaced by its i-th member, outermost first.
Then U′ →* Rᵢ, and R reaches Rᵢ by member replacements, outermost first.

*Proof.* Replay the reduction of U on U′, keeping the invariant that each
descendant {N1, …, Nn} of s in the reduct of U stands in the reduct of U′ as
its i-th member Ni, with the descendants inside Ni replaced in turn:
- a step inside a member j ≠ i is not mirrored;
- a step inside member i is mirrored;
- a step outside the descendants is mirrored, and the replacement commutes
  with the substitution;
- η keeps its side condition, since FV(Ni) ⊆ FV({N1, …, Nn}).

No redex pattern examines a set as a whole, since a set is not an
abstraction. At the end the reduct of U′ is Rᵢ. The member replacements from R
to Rᵢ exist, since each descendant has an i-th member. ∎

**Lemma 2b (yields are reached forward).**
1. If U = V in Th(∅) and V ▷ V′, then U →c* A for some A with A = V′ in Th(∅).
2. If T →c A, then ⟦A⟧ ⊆ ⟦T⟧; terms equal in Th(∅) have equal meanings.
3. For every w ∈ ⟦T⟧ there is a pure P with T →c* P and P = w in Th(∅).

*Proof.*
1. By confluence U →* R and V →* R. Let V′ replace the occurrence s by its
   member i. By Lemma 2a, V′ →* Rᵢ and R reaches Rᵢ by member replacements.
   So U →c* Rᵢ, and Rᵢ = V′ in Th(∅).
2. A β or η step is an equation of Th(∅), so the th condition gives
   ⟦A⟧ ⊆ ⟦T⟧, and both inclusions for equal terms, Th(∅) being symmetric. A
   member replacement is the set condition.
3. Induction on the derivation of (T, w) ∈ D.
   - *pure:* T = w is pure; take P = T.
   - *th:* T = U in Th(∅), and (U, w) is derived before. By the induction
     hypothesis U →c* Q with Q pure and Q = w. Lift this sequence to T,
     keeping a term A with T →c* A and A = the current term in Th(∅): a β or
     η step keeps the equation; a member replacement is part 1. At the end
     A = Q in Th(∅); by confluence A and Q have a common reduct P, which is
     pure because Q is and reduction creates no set. So T →c* P and P = w.
   - *set:* T = C[{M1, …, Mn}], and (C[Mi], w) is derived before. Then
     T ▷ C[Mi], and the induction hypothesis gives C[Mi] →c* P. ∎

Lemma 2b.1 is Lemma A of the yield lemma, sketched for the contest's judgment
of rounds up to 34, proved here for λβη with sets.

## 3. Böhm-tree reasoning on terms with sets is unsound

Let Θ = (λa. λb. b (a a b)) (λa. λb. b (a a b)), Turing's fixed point combinator,
and define

    J  = Θ (λj. λx. λy. x (j y))           J x →* λy. x (J y)
    G  = Θ (λj. λm. λx. λy. x (j m y))     G m x →* λy. x (G m y)

J is Wadsworth's term, equal to λx. x in H* and not β-convertible to it. G m
carries m along forever without ever putting it at a head, so BT(G M) = BT(J)
for every M.

**Proposition 3.** λx. x ∈ S(J), and S(G {}) = ∅. Yet G {} and J have the same
Böhm tree: BT(t(G {})) = BT(J), and t(G {}) = t(J) in H*.

*Proof.*

*S(J).* J is pure, so J ∈ ⟦J⟧. J = λx. x holds in H*, so λx. x ∈ S(J) by
Theorem 2.

*S(G {}).* Call a term λI when every abstraction in it binds a variable that
occurs free in its body.
- G {} is λI; Θ and every abstraction in G bind used variables.
- β on a λI term erases nothing, since the argument is copied at least once.
  η erases only the bound variable. So every βη-reduct of G {} is λI and
  contains an occurrence of {}.
- Reduction creates no set. So every set in a reduct of G {} descends from
  the one {} and is itself {}.

By Lemma 2b, every yield of G {} is Th(∅)-equal to a pure P with G {} →c* P.
- No member replacement is possible along the way, since the only sets are {}.
- So P is a reduct of G {}, and it contains {}: a contradiction.
- Hence ⟦G {}⟧ = ∅.

*Böhm trees.* t(G {}) = G (c₀ (λz. z)). G carries its first argument without
putting it at a head, so the Böhm tree is BT(J). ∎

Consequences:

1. **Böhm-tree matching is settled negatively for lambda with sets.**
   - A symbolic matcher applies two closures to atoms and ties knots on pairs
     already being compared. It establishes Böhm-tree equality.
   - Such a matcher would match the closure λm. G m against λm. J; both are pure.
   - A replacement answering for λm. J then answers λx. x on the program
     (λm. G m) {}, whose S is empty: a false positive.
   - The set that causes it is in the program around the matched closures, not
     in them. So restricting matching to pure closures is not enough.
2. **The same holds for any knot-tying prover.** A prover that proves an
   equation between terms that still contain sets, by returning to an assumed
   pair, can prove G {} = λx. x. So guarded cycles are sound only on pure terms,
   on set-free terms (section 4).
3. **The proposition uses an empty set that is never erased, but the
   restriction to sets without {} does not help (Proposition 8).**
4. **What remains sound.**
   - Matching whose knots descend on data (Corollary 4a) is sound everywhere.
   - Guarded matching is sound on set-free programs (Theorems 2 and 5).

## 4. Cyclic certificates

A *cyclic certificate* for an equation is a finite graph of nodes. Each node
carries an equation between terms with free variables, called parameters. Each
node is either a rule application with edges to its premises, or a *back-link*
to another node together with a substitution of parameters. Parameters are
*plain* or *data*. A data parameter has a data type D, given by:
- constructors con_1, …, con_r with arities, and which of their fields are
  recursive;
- canonical values V_D: closed terms, each with a size in ℕ;
- the requirement that every v ∈ V_D is Th(∅)-equal to con_i w₁ … w_k for some
  i, with the recursive wⱼ in V_D of smaller size and the other wⱼ closed.

Scott and Church numerals, Scott binary numbers and lists are data types.

Rules:

- **(conversion)** from A′ = B′ infer A = B, where A = A′ and B = B′ in λβη,
  given as a finite derivation;
- **(head)** from Mᵢ = Nᵢ for i = 1…k infer λx₁…xₚ. y M₁ … M_k =
  λx₁…xₚ. y N₁ … N_k, where y is a variable that is either among the xᵢ or a
  plain parameter; used on pure terms only;
- **(case)** for a data parameter n of type D, from E[n := con_i a⃗_i] for every
  constructor i, with fresh parameters a⃗_i, infer E; a recursive field of
  con_i is a data parameter of type D;
- **(congruence)** the rules ν, μ, ξ and the set rule of Th;
- **(lemma)** an instance of an equation certified separately.

A *trace* along a path follows one data parameter:
- through a back-link's substitution when that substitution maps the parameter
  to a data parameter;
- through (case) from n to a recursive field a of con_i, where it *progresses*;
- unchanged through every other rule.

A path is *guarded infinitely often* when it passes (head) infinitely often. It
*descends* when some trace on a tail of it progresses infinitely often.

**Theorem 4 (descending cycles are induction).** Let a cyclic certificate use
no (head), and let every infinite path descend. Then, for every instance of the
root equation that puts canonical values at the data parameters, the instance is
in Th(∅). Sets may occur anywhere.

*Proof.* Instances leave plain parameters as variables; Th(∅) is closed under
substitution. Suppose some root instance ρ₀ is not in Th(∅). Build an infinite
path of nodes and instances, each instance not in Th(∅):

- *Conversion and congruence* are sound rules of Th(∅). If the conclusion
  instance is not in Th(∅), some premise instance is not either.
- *Case.* The data parameter n holds a canonical value v, which is Th(∅)-equal
  to con_i w⃗. Instantiate the premise for constructor i with a⃗_i := w⃗. Its
  equation is Th(∅)-equal to the conclusion instance, so it is not in Th(∅).
  The trace from n to a recursive field goes to a value of smaller size.
- *Back-link.* The target node's instance composes the substitution with the
  current instance. It is the same equation, and the trace keeps its value.

Along every trace the size of the carried value never increases, and it
decreases at each progress. The path is infinite, so it descends. Then some
size decreases infinitely often in ℕ, a contradiction. ∎

Each instance has a finite Th(∅) derivation, obtained by unrolling. So a
descending certificate may be used anywhere a Th(∅) step may, on terms with
sets as well.

Soundness requires the value put at a data parameter to be canonical. The
kernel must check an instantiation's argument against V_D by its full structure
(for a closure, its code together with every capture), not by a code address.
This is the check that the capture traps (`problems/api_capture_traps`) test.

**Corollary 4a (symbolic matching by induction).** A symbolic matcher compares
a candidate closure C with an API's definitional closure D by evaluating both,
in the bootstrapped runtime, on parameters. It must satisfy three conditions:
- it splits every data parameter by its constructors, instead of evaluating
  on it as a neutral atom;
- it ties a knot only by a back-link along which a data trace progresses, and
  it compares heads and arguments by congruence;
- it evaluates with exact beta and eta steps.

Then the comparison is a certificate of Theorem 4. For canonical values v⃗ at
the data parameters and arbitrary terms at the plain parameters, including
terms with sets, C v⃗ and D v⃗ are Th(∅)-equal. A replacement that answers
for C by D's answer is therefore exact in every context: it changes no meaning
and no S, sets included.

The replacement must check that every argument at a data parameter is a
canonical value, by its full structure, and fall back otherwise.
Proposition 3 does not apply, because no step of such a certificate is an
H* step. Two weaker restrictions do not suffice:
- *restricting a guarded matcher to set-free closures:* the set in
  Proposition 3's program is in the context;
- *restricting it to canonical data arguments:* λz. λs. s (G z p) equals the
  Scott numeral λz. λs. s p in H*, but applied to {} and K its meaning is
  empty, while the numeral's is {λw. p}.

**Lemma 6 (depth).** For pure terms define:
- M ~₀ N always;
- M ~ₖ₊₁ N when either both are unsolvable, or, after equalising binder prefixes
  and argument counts by finitely many η-expansions, M =βη λx⃗. y M₁ … Mₘ and
  N =βη λx⃗. y N₁ … Nₘ with the same variable y and Mᵢ ~ₖ Nᵢ.

M = N in H* if and only if M ~ₖ N for every k.

*Proof sketch.* Both directions use the characterisation of H* by Böhm trees
up to possibly infinite η-expansion (Barendregt 1984, 16.2.7 and 19.2.9).
- *If.* At each node, the η-expansion that equalises the two sides is unique:
  expand the shorter prefix to the longer one. So the expansions chosen for
  different k agree, and the relations ~ₖ for all k together give one common,
  possibly infinite, η-expansion of BT(M) and BT(N). By the characterisation,
  M = N in H*.
- *Only if.* Let M = N in H*.
  - If one side is unsolvable, so is the other: H* is sensible and consistent,
    and it separates a solvable term from an unsolvable one. So M ~ₖ N for
    every k.
  - Otherwise the characterisation gives, after finitely many η-expansions at
    the root, the same head variable and the same number of arguments, and
    pairwise H*-equal arguments.
  - Induction on k gives M ~ₖ N. ∎

**Theorem 5 (guarded and mixed cycles).** Let a cyclic certificate have pure
terms at every node, let no cycle pass a congruence node, and let every
infinite path be guarded infinitely often or descend. Then every instance of the root equation (canonical values at data
parameters, plain parameters kept as variables) is an equation of H*.

*Proof.* Suppose an instance is not in H*. By Lemma 6 (if) there is a least k with
the two sides not ~ₖ; call k the instance's *level* (k ≥ 1). Build an infinite
path of instances outside H*, keeping the level from increasing:

- *Conversion.* ~ₖ is defined through =βη, so a premise instance has the same
  level.
- *Head.* If every premise instance were ~ₖ₋₁, the conclusion would be ~ₖ by
  the definition. So some premise instance is not ~ₖ₋₁. By Lemma 6 (only if)
  it is outside H*, and its level is at most k − 1: the level strictly
  decreases.
- *Congruence* lies on no cycle (the condition below), so the path passes it
  finitely often; from the last such pass on, the level never increases. A
  premise instance outside H* exists because ν, μ, ξ and the set rule
  preserve H*.
- *Lemma.* A separately certified equation has no instance outside H*, so the
  path never ends at one.

The condition on congruence is needed. ν and μ can raise the level: with
A = λx. x (λy. y P), B = λx. x (λy. y Q) and P, Q differing at the root, A and B
differ first at depth two, while A Z and B Z for Z = λf. f (λu. u) reduce to P
and Q and differ at depth zero. A cycle through ν or μ could therefore climb
back after each (head). So the kernel accepts a certificate for Theorem 5 only
when no cycle of it passes a congruence node; (head) already covers congruence
under a head. An infinite path in a finite graph ends in one strongly connected
component, which then contains no congruence node.

Along the path the level never increases and strictly decreases at each
(head); data values never increase along a trace. The path is infinite, so it
is guarded infinitely often or descends. Either way a quantity in ℕ decreases
infinitely often, a contradiction. ∎

Guarded-only certificates are Böhm-tree bisimulations up to βη, the head normal
form bisimulation of Lassen (MFPS 1999), extended by η-expansion at nodes.
Descending-only ones are Theorem 4. Theorem 5 allows the two on one cycle.

## 5. What a certificate may claim

**Theorem 7 (certificate soundness).** Suppose a certificate for N ∈ S(T) has
two segments:
1. a yield segment: steps of Th(∅) and member replacements from T to a pure T′. The Th(∅)
   steps may use descending certificates (Theorem 4).
2. an equation T′ = N proved by a certificate satisfying Theorem 5.

Then N ∈ S(T).

*Proof.* T′ ∈ ⟦T⟧: T′ ∈ ⟦T′⟧ by the pure condition, and each step of the first
segment, read from its end, is the th condition (an equation) or the set
condition (a member replacement). T′ = N
holds in H* by Theorem 5. Then N ∈ S(T) by Theorem 2. ∎

This replaces the meta-lemma of the second phase of the certificate design
("confirmed assumptions are consistent with λβ"):
- an assumption is the target of a back-link;
- "confirmed" is the cycle condition of Theorem 5;
- the syntactic conditions guessed there (assumptions only on re-entered terms,
  captureless closures) are not needed.

Proposition 3 shows that the restriction to the second segment is necessary: a
guarded cycle in the first segment can prove a false claim.

**Proposition 8 (Böhm-tree reasoning on terms with sets is unsound without empty
sets too).** Let true = λp. λq. p, false = λp. λq. q, not = λb. b false true,
D = λy. λu. λv. v, and define, by Θ, the two families

    X′(b) = λx. λy. x (b {X′(not b) y, D y} {D y, X′(not b) y})
    X(b)  = λx. λy. x {b (X(not b) y) (D y), b (D y) (X(not b) y)}

Neither contains {}. For each Boolean b the Böhm trees of t(X′(b)) and t(X(b))
are equal: at every level the node is a binary set whose operands are, in
this order, the next level and D y when b is true, and D y and the next level
when b is false. Yet λx. x ∈ S(X′(true)) and λx. x ∉ S(X(true)).

*Proof.*

*X′.* X′ has two set occurrences in its generator. Replace the first by its
first member and the second by its second member, inside the generator (an
occurrence under λ is an occurrence in a one-hole context). The result is
pure, and it is a yield of X′(true). With b true the level is
λx. λy. x (X′(false) y), and with b false it is λx. λy. x (X′(true) y). So both
levels unfold as J does, the term has the Böhm tree of J, and it equals λx. x
in H*. By Theorem 2, λx. x ∈ S(X′(true)).

*X.* X has one set occurrence in its generator.
- By Lemma 2b, every yield of X(true) is Th(∅)-equal to a pure term W with
  X(true) →c* W: finitely many reductions and member replacements, each made
  on the reduct reached so far. Such a sequence unfolds only finitely many
  levels, and its member replacements pick operands at the copies exposed so
  far.
- The occurrence left in the generator must be replaced too, since W is pure. Choosing its
  first operand makes every later level with b false read D y. Choosing its
  second makes every later level with b true read D y. Levels of both parities
  lie beyond any finite unfolding.
- So BT(W) has a node λu. λv. v at a finite depth, where the η-expansion of
  the identity has a node headed by the variable y.
- Two Böhm trees that differ at a finite node in their head variables, both
  non-empty there and not by η, belong to separable terms (Böhm-out,
  Barendregt 1984, chapter 10). Hence W = λx. x is inconsistent.
- Th(∅)-equal terms have one Böhm tree, so no yield of X(true) is consistent
  with λx. x. ∎

The two families differ only in whether a Boolean case analysis is applied
outside two sets or inside one: application does not distribute over
sets in Th. A Böhm tree records which operands a set has at each position,
but not which positions share one choice. So Böhm-tree reasoning, and the
guarded knots that establish it, is unsound on terms that still contain
sets, with or without empty sets. The kernel accepts (head) nodes and
guarded back-links only on pure terms.

Corollary 7a turns this restriction into a procedure. It was added
2026-09-30, from the observation that sets can be expanded statically by
distributivity, like templates. Th has no distributive equation; what
distributes is the meaning, by its set condition, and that is all the
corollary uses.

Call P a *k-step instance* of T when P is pure and T →c* P by a sequence with
at most k β or η steps. A *static instance* is a 0-step instance: every set
occurrence of T itself, under λ included, is replaced by one of its members,
outer occurrences before the occurrences inside their chosen members. T has
finitely many static instances, one per choice of a member at each occurrence.

**Corollary 7a (expand, then reason on pure instances).**
1. Every k-step instance P of T is a yield of T. So if P = N in H*, by a
   certificate satisfying Theorem 5 or by any other argument, then
   N ∈ S(T).
2. Every yield of T is Th(∅)-equal to a k-step instance of T for some k.
   Static instances alone do not suffice.

*Proof.*
1. P ∈ ⟦P⟧ by the pure condition. Read the sequence T →c* P from its end: a β
   or η step is an equation of Th(∅), and a member replacement is the set
   condition, so ⟦P⟧ ⊆ ⟦T⟧ by Lemma 2b.2 and P ∈ ⟦T⟧. Theorem 2 gives
   N ∈ S(T). This is Theorem 7 with a first segment of member replacements
   and at most k single β or η steps.
2. Lemma 2b.3 gives, for every yield w, a pure P with T →c* P and P = w in
   Th(∅); k is the number of β and η steps of that sequence. For the second
   sentence take T = (λx. x x) {a, b} with a and b distinct variables, the
   example of the formal definition of the normal form solution sets. Its static instances are (λx. x x) a and
   (λx. x x) b, which reduce to a a and b b. ⟦T⟧ also holds a b and b a,
   reached with k = 1: contract the redex, then replace the two copies of the
   set separately. a a, a b, b a and b b are four distinct normal forms, so by
   Theorem 1 and confluence a b and b a are Th(∅)-equal to no static
   instance. ∎

Checked against the two counterexamples:
- (λm. G m) {} of Proposition 3 has no k-step instance for any k: every
  reduct still holds {} (the proof of Proposition 3), and {} has no member to
  replace it by. This agrees with its empty meaning. The false positive there
  came from matching inside a term that still held {}.
- The static instances of X(true) in Proposition 8 are the two pure terms its
  proof considers once the generator's occurrence is replaced; each is
  separable from λx. x at a finite depth. One static instance of X′(true) is
  the yield its proof exhibits, equal to λx. x in H*.

Consequences:
- *For a replacement by a matcher.* A guarded matcher (case B) may be used on a program with
  sets when the reading first expands the sets to a pure instance and then
  matches, and replaces, only inside that instance: every normal form it then
  reads is in S(T) by part 1. Matching inside a term that still holds a set
  stays unsound (Propositions 3 and 8). This answers, under the current
  definition of S, whether guarded matching may be used on programs with
  sets, with that restriction.
- *Soundness does not depend on which instances are read.* A setting may read
  only static instances, a bounded k, or deepen k step by step. Only
  completeness depends on it, and part 2 shows that deepening reaches every
  yield. The static instances can miss yields in which copies of one
  occurrence choose differently (the example of part 2), the independent
  choice at each read that the mixin encoding relies on.
- The number of static instances is the product of the member counts of T's
  set occurrences, so expansion can be exponential in their number.

## 6. More operands never remove a solution

The intuition is the Liskov substitution principle: an added set never
removes a solution.

Write T ≼ T′ when T′ is T with some set occurrences enlarged. An occurrence
{M1, …, Mn} of T is enlarged by adding operands, so that it stands in T′ as
{M1, …, Mn, M′1, …, M′m} with the Mi in their positions, and every added M′j
has FV(M′j) ⊆ FV({M1, …, Mn}).

**Theorem 9 (substitution by a richer set).**
1. If T ≼ T′, then ⟦T⟧ ⊆ ⟦T′⟧, and so S(T) ⊆ S(T′).
2. If T′ is T with one occurrence of a subterm M replaced by a set that has M
   among its operands, then ⟦T⟧ ⊆ ⟦T′⟧ and S(T) ⊆ S(T′), whatever the other
   operands are.

*Proof of 2.* T′ ▷ T replaces that occurrence by M, so ⟦T⟧ ⊆ ⟦T′⟧ by the set
condition.

*Proof of 1.* First a fact.

*(a) Reductions and member replacements of T are mirrored in T′.* Let T → A
be one β step, one η step or one member replacement. Then T′ → A′ for some A′
with A ≼ A′:
- *β:* contract the same redex. An enlarged occurrence inside the argument is
  copied with its enlargement. Enlargement commutes with substitution.
- *η:* contract the same redex λx. M x. The side condition x ∉ FV(M) holds in
  T′ as well, because an enlargement adds no free variable to its occurrence.
- *Member replacement* by the member Mi of an occurrence: replace the
  corresponding occurrence of T′ by the same member Mi, wherever the
  enlargement placed it. The rest of the term is unchanged.

Now let w ∈ ⟦T⟧. By Lemma 2b.3, T →c* P with P pure and P = w in Th(∅).
Mirror the sequence by (a): T′ →c* P′ with P ≼ P′. P has no set occurrence to
enlarge, so P′ = P. By Lemma 2b.2, ⟦P⟧ ⊆ ⟦T′⟧, and w ∈ ⟦P⟧ by the pure and th
conditions. So w ∈ ⟦T′⟧. S(T) ⊆ S(T′) follows, since S is monotone in ⟦·⟧. ∎

The condition on free variables serves only the η case of (a): in
λx. {A} x, an added operand mentioning x would block the η step. Theorem 9.2
needs no such condition.

Consequences:
- *For settings and knowledge bases.* Dropping operands of a set is a sound
  approximation: every normal form a setting reads after replacing a set by a
  set with fewer members, or by one of its operands, is in S of the original term. A
  knowledge base may therefore answer for "several implementations in one set" by
  reading one implementation.
- *For certificates.* A certificate may justify a step from T to T′ ≽ T.
  A member replacement is the special case of Theorem 9.2 read backwards: it
  claims about the smaller term.
- Theorem 9 does not repair Propositions 3 and 8. Those compare terms that are
  not related by ≼, and the added operands there would have to be supplied by
  the replacement, not by the program.

## References

- H. P. Barendregt, The Lambda Calculus: Its Syntax and Semantics, 1984,
  chapters 16 and 19 (Böhm trees, H*, the model D∞).
- J. Brotherston and A. Simpson, Sequent calculi for induction and infinite
  descent, Journal of Logic and Computation, 2011 (cyclic proofs, the trace
  condition).
- S. B. Lassen, Bisimulation in untyped lambda calculus: Böhm trees and
  bisimulation up to context, MFPS XV, ENTCS 20, 1999.
- V. van Oostrom and F. van Raamsdonk, Weak orthogonality implies confluence:
  the higher-order case, LFCS 1994, LNCS 813.
- C. P. Wadsworth, The relation between computational and denotational
  properties for Scott's D∞-models of the lambda-calculus, SIAM Journal on
  Computing, 1976.
