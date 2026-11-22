# A search for a counterexample to a true theorem yields nothing: the mixin true-theorem searches

A written proof, 2026-09-30: the trap
conjecture `conjecture(no_yield)` of the class TRUE-THEOREM SEARCHES of
`corpora/contest_mixin_traps.pl`, both booleans, holds. Each test yields
nothing, so both trap claims are false.

The programs are those of `corpora/contest_mixin_traps.pl`,
`corpora/contest_reduction_mixin_theorems.pl` and
`corpora/contest_mixin_library.pl`. The proof uses, as a lemma, the argument of
the MIXIN port that a sequence of choices reaching a pure term chooses, at
every read, a wrapper that defines the slot read, and follows the structure
of the proof of the reachability misses
([solo_mixin_reachability_misses.md](solo_mixin_reachability_misses.md)).

## 1. The programs

The encoding is MIXIN (`corpora/contest_mixin_library.pl`):

- A **wrapper** of slot k: `\self. \c1. ... \cW. ck b`.
- A **read** of slot k of O: `O O c1 ... cW`, with ck the handler (`\v. v`,
  or `\v. v a1 ... aj` when the read heads an application,
  `slot_applied/5`) and every other cj the empty set `{}`.

**The library `natural`** is a module, one module wrapper per file and
class the file contributes to. Reading the module's class c yields the
union of the files' contributions to c. Its classes are true, false, zero
and successor. For each (class, slot) pair exactly one file contributes a
wrapper:

| slot | true | false | zero | successor |
|---|---|---|---|---|
| church | `\t. \f. t` | `\t. \f. f` | | |
| not | the class false | the class true | | |
| conjunction | `\o. o` | `\o. false` | | |
| accept | | | `\z. \s. z` | `\z. \s. s self.predecessor` |
| equality | | | `\o. o.accept(true, \p. false)` | `\o. o.accept(false, \p. self.predecessor.equality(p))` |

The table lists only the slots used below; plus and scott are not read by
these programs. A number object is `0̂` (the class zero) or
`succ(X) = {successor, predecessor : X}`, and `succ^k(0̂)` is written n̂ for
n = k.

**The search** (`contest_reduction_mixin_theorems.pl`, proposition_surface/2
with stepped(Step, Check), or Step = 1) is a module of two classes,
counterexample_search and periodic:

- `found(X)` abbreviates `{counterexample_search, n : X}.found`. Its body is
  `check(self.n).church(T, found(self.n + Step))`: the Boolean check of the
  proposition at self.n chooses, as its church, between T (the library's
  true class) and the next round. The next round's n is Step successor
  classes around self.n.
- The class periodic has the slots n, even and the three residues. Each is
  defined by recursion on n's accept: at zero, even is true and
  residue_zero true; a successor's even is the negation of its
  predecessor's even, and its residue follows its predecessor's,
  0 -> 1 -> 2 -> 0.

The program is `P = found(0̂).church`, read with the identity handler at
the outside. The claims' tests are `\a. P a y` and `\a. P y a`. As the judgment
asks them, they are the closed programs `\y. \a. P a y` and
`\y. \a. P y a`.

## 2. What is to be shown

By lemma 2b of `doc/proofs/certificate_meta_lemmas.md`, it suffices to show

    (G) no finite sequence of reductions and choices from either test
        program reaches a pure term.

## 3. Reads in a successful sequence

Call a finite sequence of reductions and choices that reaches a pure term
a successful sequence. By the argument of the MIXIN port:

    (L) a successful sequence chooses, at every read it resolves, a wrapper
        that defines the slot read (another slot's wrapper applies {} to
        its body, and {} at the head is never removed).

In a successful sequence, therefore, a read of slot ℓ on an object built
as an instance of a class resolves to the one wrapper that the class
contributes for ℓ. The table above has one such wrapper per (class, slot).

Define: an object O **denotes the Boolean b** when every read of church,
not or conjunction on O that a successful sequence resolves resolves to
b's wrapper for that slot. O **denotes the number n** when every read of
accept or equality on O that a successful sequence resolves resolves as n̂'s
does. Here n̂'s accept selects its zero argument when n = 0 and applies its
successor argument to an object denoting n - 1 otherwise.

## 4. Library lemmas

Each follows from (L) and the table.

- **(B)** The class true denotes true and the class false denotes false.
  If O denotes b, then O.not denotes the negation of b. If O denotes true,
  O.conjunction(Q) resolves to Q; if O denotes false, it resolves to the
  class false.
- **(N)** 0̂ denotes 0. If X denotes n, then succ(X) denotes n + 1: its
  accept applies the successor argument to self.predecessor, whose read
  resolves to X, the only predecessor wrapper.
- **(E)** If X denotes n and Y denotes m, then X.equality(Y) denotes the
  Boolean n = m. The proof is by induction on n.
  - For n = 0: zero's equality is Y.accept(true, \p. false), which
    resolves to the class true when m = 0 and to the class false otherwise.
  - For n + 1: successor's equality is Y.accept(false, \p. X′.equality(p)),
    X′ = self.predecessor denoting n. It resolves to false when m = 0, and
    to X′.equality(Y′) with Y′ denoting m - 1 otherwise, which denotes
    n = m - 1 by the hypothesis.
- **(Q)** If X denotes n, then `{periodic, n : X}` has even denoting "n is
  even" and residue_r denoting "n ≡ r (mod 3)". The proof is by induction
  on n through accept, as the recursions above state: 0 is even with
  residue 0; the successor of an even number is odd, of an odd number even;
  the residue advances 0 -> 1 -> 2 -> 0.

## 5. The theorem

**Theorem.** Suppose that for every k ≥ 0 and every X denoting Step·k, the
check of the proposition at X denotes false. Then (G) holds.

**Proof.** Let σ be a successful sequence from a test program; we derive a
contradiction.

1. The head of the test body's spine is P's outer read of church. σ
   resolves it, so by (L) it chooses a church wrapper of a Boolean class.
   That wrapper must come from the object `found(0̂)`.
2. We show by induction on k that, for every k ≥ 0, the elements σ can
   deliver at that head are those of `found(X_k)` with X_k denoting Step·k.
   - k = 0: X_0 = 0̂ denotes 0 by (N).
   - Step: σ resolves the read of found on `{counterexample_search, n : X_k}`,
     which by (L) chooses the found wrapper. Its body is
     `check(X_k).church(T, found(X_k + Step))`.
   - The check at X_k denotes false by the hypothesis. So the church read
     resolves to `\t. \f. f`, which selects the second argument,
     `found(X_k + Step)`.
   - X_k + Step is Step successor classes around a read of self.n. That
     read resolves to X_k (the only n wrapper), so by (N) it denotes
     Step·(k + 1).
3. The true branch T, the only Boolean class a round can deliver, is never
   selected. So no element σ delivers at the head is a church wrapper: each
   is another found read.
4. Each round resolves at least one read of σ, the read of found. σ is
   finite, so it passes finitely many rounds. It leaves the head holding an
   unresolved found read, which is not pure. This contradicts (L) at the
   head.

## 6. The points covered

Each is `theorem_term(Point, Term)` of `corpora/contest_mixin_traps.pl`,
with the proposition below. The table checks the theorem's hypothesis for
every k ≥ 0, n = Step·k, with X denoting n:

| point | Step | check at X | it denotes, by |
|---|---|---|---|
| `mixin_successor_never_zero` | 1 | succ(X).equality(0̂) | n + 1 = 0: false (E, N) |
| `mixin_zero_never_successor` | 1 | 0̂.equality(succ(X)) | 0 = n + 1: false (E, N) |
| `mixin_zero_then_successor_not_both_zero` | 1 | (X = 0̂).conjunction(succ(X) = 0̂) | n = 0: true.conjunction(false) = false; n > 0: false.conjunction(…) = false (B, E) |
| `mixin_successor_then_zero_not_both_zero` | 1 | (succ(X) = 0̂).conjunction(X = 0̂) | false.conjunction(…) = false (B, E) |
| `mixin_twice_is_even` | 2 | not(even of X) | n = 2k is even, so not true = false (Q, B) |
| `mixin_four_times_is_even` | 4 | not(even of X) | n = 4k is even: false (Q, B) |
| `mixin_three_times_is_divisible` | 3 | not(residue_zero of X) | n = 3k ≡ 0: false (Q, B) |
| `mixin_six_times_is_divisible` | 6 | not(residue_zero of X) | n = 6k ≡ 0: false (Q, B) |

Each check reads self.n anew at every occurrence (`natural_term/4` and the
periodic reads). Every such read resolves to X, so each occurrence denotes
the same number, and the table's evaluations hold.

**Where the unbounded rounds went.** The module comment leaves open "the
unbounded rounds". As for the reachability misses, the induction is on the
reads of a finite sequence, so the unbounded rounds need no separate
argument. The premise that carries the induction is the invariant of step
2: X_k denotes Step·k, and at that number the check is false.
