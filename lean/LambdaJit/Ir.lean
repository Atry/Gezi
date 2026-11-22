/-!
# The defunctionalised IR as a flat store of thunk layers

This module holds the object language of the verification: the IR layer grammar of
design decision D1. A term is not a
de Bruijn tree but a finite store of layers keyed by address, together with a root
address; every layer refers to its operands by address, so a store is a flat system of
equations and sharing is never lost.

A layer is a thunk with holes, an application, a binary choice, or a parallel.
A thunk names the code of the body of a lambda chain; its holes list, in the order of the
lambdas, the slot each binder occupies (`ignored` when the binder does not occur in the
body), and its fillings are the values of the other slots, in slot order. A closure is a
thunk with holes and has no code of its own; a library name is a label on the address of
its layer, not a layer.

An address is an opaque key with one layer per address: the trie handle in the process, a key
of the OpenTheory article's dictionary in the export (D7). Nothing here depends on how keys are
made.

The solution of a flat system is a finite term (D1: "这里的解是有限项"): `FiniteTerm` is
the tree a store unfolds to at an address, with codes written out. The judging theory
(module `Theory`) is a relation on finite terms, and two addresses of a store are equal
when their solutions are (`Store.Equal`). The theory is stated on the solutions rather
than on the addresses of one store because a step of the theory may pass through a term
that the store does not hold: the instance of a lemma side matched up to the classes of
a trace, the application a filled thunk reads as (D6), or the common reduct of the two
sides of a beta law. A relation on the addresses of one fixed store would lack those
steps, and a lemma stated as an axiom over every store would then be false of the stores
that lack them.
-/

namespace LambdaJit

/-- An address: an opaque key naming one layer or one code of a store (D1, D7). -/
structure Address where
  key : Nat
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- Where the binder of one lambda of a thunk's chain goes (D1). -/
inductive Hole where
  /-- The binder occupies slot `index` of the code. -/
  | slot (index : Nat)
  /-- The binder does not occur in the body. -/
  | ignored
  deriving DecidableEq, Repr, Inhabited

/-- One layer of the IR (D1). Every operand is an address into the same store. -/
inductive Layer where
  /-- The closure of a lambda chain: the address of its code, the slots of the binders
  still unfilled in lambda order, and the values of the other slots in slot order. -/
  | thunk (code : Address) (holes : List Hole) (fillings : List Address)
  /-- An application of `function` to `argument`. -/
  | apply (function argument : Address)
  /-- The binary choice of two sides: a chain of several members is right-nested. The
  theory has congruence for it and no other law: which numbered equations the IR theory needs as
  rules, and in what form, is open (module `Theory`). -/
  | choice (left right : Address)
  /-- A parallel of two sides. The theory has congruence for it and no other law: which numbered
  equations the IR theory needs as rules, and in what form, is open (module `Theory`). -/
  | parallel (left right : Address)
  deriving DecidableEq, Repr, Inhabited

/-- The code of a thunk (D1): the body of a lambda chain whose binders and maximal closed
subterms are numbered slots, in order of first occurrence. A code has no names, no
closed subterms, and no distinction between arguments and captured values. A nested
thunk carries its own code written out: a store keys a code by address, and two
addresses with one code tree are one code, as the hash_consing handle of a code is
(the export interns codes as layers, D7). -/
inductive Code where
  /-- Slot `index` of the enclosing thunk. -/
  | slot (index : Nat)
  /-- An application of one code to another. -/
  | apply (function argument : Code)
  /-- A nested thunk whose fillings are codes of the enclosing thunk. -/
  | thunk (code : Code) (holes : List Hole) (fillings : List Code)
  /-- The binary choice of two codes. -/
  | choice (left right : Code)
  /-- A parallel of two codes. -/
  | parallel (left right : Code)
  -- No `DecidableEq`: Lean 4.30's deriving handler does not apply to the nested inductive
  -- `Code` (measured 2026-10-02 and again 2026-10-04). `Code.equal` below is the
  -- comparison `EndToEnd.fillChecked` uses, with its soundness theorem.
  deriving Repr, Inhabited

namespace Code

mutual
/-- Structural equality of two codes, as a Boolean the kernel can evaluate. -/
def equal : Code → Code → Bool
  | .slot index, .slot otherIndex => index == otherIndex
  | .apply function argument, .apply otherFunction otherArgument =>
      equal function otherFunction && equal argument otherArgument
  | .thunk code holes fillings, .thunk otherCode otherHoles otherFillings =>
      equal code otherCode && holes == otherHoles && equalList fillings otherFillings
  | .choice left right, .choice otherLeft otherRight =>
      equal left otherLeft && equal right otherRight
  | .parallel left right, .parallel otherLeft otherRight =>
      equal left otherLeft && equal right otherRight
  | _, _ => false

/-- Structural equality of two lists of codes, element by element. -/
def equalList : List Code → List Code → Bool
  | [], [] => true
  | code :: codes, otherCode :: otherCodes => equal code otherCode && equalList codes otherCodes
  | _, _ => false
end

mutual
theorem equality_of_equal : ∀ {left right : Code}, equal left right = true → left = right
  | .slot index, .slot otherIndex, holds => by
      simp only [equal, beq_iff_eq] at holds
      rw [holds]
  | .apply function argument, .apply otherFunction otherArgument, holds => by
      simp only [equal, Bool.and_eq_true] at holds
      rw [equality_of_equal holds.1, equality_of_equal holds.2]
  | .thunk code holes fillings, .thunk otherCode otherHoles otherFillings, holds => by
      simp only [equal, Bool.and_eq_true, beq_iff_eq] at holds
      rw [equality_of_equal holds.1.1, holds.1.2, equality_of_equalList holds.2]
  | .choice left right, .choice otherLeft otherRight, holds => by
      simp only [equal, Bool.and_eq_true] at holds
      rw [equality_of_equal holds.1, equality_of_equal holds.2]
  | .parallel left right, .parallel otherLeft otherRight, holds => by
      simp only [equal, Bool.and_eq_true] at holds
      rw [equality_of_equal holds.1, equality_of_equal holds.2]
  | .slot _, .apply _ _, holds | .slot _, .thunk _ _ _, holds | .slot _, .choice _ _, holds
  | .slot _, .parallel _ _, holds | .apply _ _, .slot _, holds | .apply _ _, .thunk _ _ _, holds
  | .apply _ _, .choice _ _, holds
  | .apply _ _, .parallel _ _, holds | .thunk _ _ _, .slot _, holds
  | .thunk _ _ _, .apply _ _, holds | .thunk _ _ _, .choice _ _, holds
  | .thunk _ _ _, .parallel _ _, holds | .choice _ _, .slot _, holds | .choice _ _, .apply _ _, holds
  | .choice _ _, .thunk _ _ _, holds
  | .choice _ _, .parallel _ _, holds | .parallel _ _, .slot _, holds
  | .parallel _ _, .apply _ _, holds | .parallel _ _, .thunk _ _ _, holds
  | .parallel _ _, .choice _ _, holds => by simp [equal] at holds

theorem equality_of_equalList : ∀ {left right : List Code}, equalList left right = true → left = right
  | [], [], _ => rfl
  | code :: codes, otherCode :: otherCodes, holds => by
      simp only [equalList, Bool.and_eq_true] at holds
      rw [equality_of_equal holds.1, equality_of_equalList holds.2]
  | [], _ :: _, holds => by simp [equalList] at holds
  | _ :: _, [], holds => by simp [equalList] at holds
end

end Code

/-- A finite term: the solution of a store at an address (D1), each layer with its
operands' solutions in place of their addresses and its code written out. -/
inductive FiniteTerm where
  /-- A thunk: its code, its holes in lambda order, its fillings in slot order. -/
  | thunk (code : Code) (holes : List Hole) (fillings : List FiniteTerm)
  /-- An application. -/
  | apply (function argument : FiniteTerm)
  /-- A binary choice. -/
  | choice (left right : FiniteTerm)
  /-- A parallel. -/
  | parallel (left right : FiniteTerm)
  deriving Repr, Inhabited

/-- The position, among the fillings of a thunk whose holes are `holes`, of the filled
slot `slot`: how many slots below it are no hole. The fillings are the values of the
non-hole slots in slot order (D1); the same count as `filling_position/3` of
`lambda_jit_defunctionalization`. -/
def fillingPosition (holes : List Hole) (slot : Nat) : Nat :=
  ((List.range slot).filter (fun lower => !holes.contains (Hole.slot lower))).length

/-- The fillings of a thunk after its first hole `hole` takes `argument`, the remaining
holes being `holes` (D1: partial application fills the first hole): the argument goes
in at its slot's position among the filled slots, and an `ignored` hole drops it. The
same operation as `hole_filled/5` of `lambda_jit_weak_head`. -/
def fill {α : Type} (hole : Hole) (holes : List Hole) (fillings : List α) (argument : α) :
    List α :=
  match hole with
  | .ignored => fillings
  | .slot index =>
      let position := fillingPosition holes index
      fillings.take position ++ argument :: fillings.drop position

theorem map_fill {α β : Type} (function : α → β) (hole : Hole) (holes : List Hole)
    (fillings : List α) (argument : α) :
    (fill hole holes fillings argument).map function
      = fill hole holes (fillings.map function) (function argument) := by
  cases hole with
  | ignored => rfl
  | slot index => simp [fill, List.map_take, List.map_drop]

namespace Code

mutual
/-- The instance of a code under the values of its slots (D2's second beta clause): each
slot reads its value, and a nested thunk's fillings are instances of the enclosing
code. Undefined when the code reads a slot that has no value. -/
def instantiate (slots : List FiniteTerm) : Code → Option FiniteTerm
  | .slot index => slots[index]?
  | .apply function argument => do
      let functionTerm ← instantiate slots function
      let argumentTerm ← instantiate slots argument
      pure (.apply functionTerm argumentTerm)
  | .thunk code holes fillings => do
      let fillingTerms ← instantiateList slots fillings
      pure (.thunk code holes fillingTerms)
  | .choice left right => do
      let leftTerm ← instantiate slots left
      let rightTerm ← instantiate slots right
      pure (.choice leftTerm rightTerm)
  | .parallel left right => do
      let leftTerm ← instantiate slots left
      let rightTerm ← instantiate slots right
      pure (.parallel leftTerm rightTerm)

/-- The instances of a list of codes under the same slot values. -/
def instantiateList (slots : List FiniteTerm) : List Code → Option (List FiniteTerm)
  | [] => some []
  | code :: codes => do
      let term ← instantiate slots code
      let terms ← instantiateList slots codes
      pure (term :: terms)
end

end Code

/-- A store: finite maps from addresses to layers and to codes, kept as association lists
so that lookup is total and decidable without any library beyond the core. -/
structure Store where
  layers : List (Address × Layer)
  codes : List (Address × Code)
  deriving Repr, Inhabited

namespace Store

/-- The layer stored at `address`, if any. -/
def lookup (store : Store) (address : Address) : Option Layer :=
  (store.layers.find? (fun entry => entry.1 == address)).map Prod.snd

/-- The code stored at `address`, if any. -/
def lookupCode (store : Store) (address : Address) : Option Code :=
  (store.codes.find? (fun entry => entry.1 == address)).map Prod.snd

/-- The solution of `store` at `address` within `fuel` layers of depth: the finite term
the flat system unfolds to there, or nothing when an address on the way has no layer, a
code address has no code, or the fuel runs out (a cycle never resolves). -/
def solution (store : Store) : Nat → Address → Option FiniteTerm
  | 0, _ => none
  | fuel + 1, address =>
      match store.lookup address with
      | some (.thunk codeAddress holes fillings) => do
          let code ← store.lookupCode codeAddress
          let fillingTerms ← fillings.mapM (store.solution fuel)
          pure (.thunk code holes fillingTerms)
      | some (.apply function argument) => do
          let functionTerm ← store.solution fuel function
          let argumentTerm ← store.solution fuel argument
          pure (.apply functionTerm argumentTerm)
      | some (.choice left right) => do
          let leftTerm ← store.solution fuel left
          let rightTerm ← store.solution fuel right
          pure (.choice leftTerm rightTerm)
      | some (.parallel left right) => do
          let leftTerm ← store.solution fuel left
          let rightTerm ← store.solution fuel right
          pure (.parallel leftTerm rightTerm)
      | none => none

end Store

/-- A term together with the store that interprets its addresses (D1: a term is a finite,
acyclic store and a root address). -/
structure StoredTerm where
  store : Store
  root : Address
  deriving Repr, Inhabited

end LambdaJit
