import LambdaJit.Theory
import LambdaJit.Semantics
import LambdaJit.LatticeEtaDerivability
import LambdaJit.TermSubstitution

/-!
# The readback from the IR to the terms of the calculus

This module holds the readback of design decision D3
(`lean/README.md`, "Design decisions"), from the finite terms of the IR (module `Ir`) to
the terms of the calculus (module `Terms`), and the soundness direction of D3's item 4:
every step of ⊢^{defunctionalized}_{λ-lattice-η} (module `Theory`) between two finite terms
that read back is a derivation by ⊢_{λ-lattice-η} between the readbacks, under any
hypotheses (`readbackSound`).

## The readback

`readback` is partial: a code may read a slot that has no value. An application reads back as
an application, a parallel as a parallel and a choice as a choice. A thunk with holes
`[h1, …, hk]` reads back as the chain of k abstractions around its code's body, the body read
under a list of slot values: the fillings, with each hole filled in lambda order by the bound
variable of its lambda, by the same operation `fill` that the first clause of the
defunctionalized β rule uses
(`finalSlots`). Slot `index` of the body reads the value at position `index` of that list; a
nested thunk of the code reads its fillings, codes of the enclosing thunk, under the enclosing
list, and its own body under the list its own holes make, so de Bruijn indices are counted by
the abstractions passed (`Term.shift` on the values carried under a lambda).

On a thunk whose holes are distinct slots (`DistinctSlots`) and whose fills place every
argument at its slot (`NoClamping`: the position of each hole's slot among the filled slots is
at most the number of fillings), such as the thunks of D1's numbering (slots from 0 in order of
first occurrence, each slot that is no hole filled), this is D3's reading (`finalSlotsStatic`):
the slot of the i-th hole holds the bound variable of the i-th lambda, and any other slot holds
its filling, at its position among the filled slots (`fillingPosition`), carried under the
lambdas (`staticSlot`). On other thunks the two readings differ, and only the one defined here
makes the first clause of the defunctionalized β rule a beta step, because `fill` places an argument at the end of the
fillings when its slot's position lies beyond them. The witness, with the code
`apply (slot 5) (slot 7)` and no fillings: `thunk(code, [slot 7, slot 5], [])` and
`thunk(code, [slot 5, slot 7], [])`, applied to K and then to I (each a thunk without
fillings), both reach `thunk(code, [], [K, I])` by the first clause of the defunctionalized β rule, so the
two
applications are equal in λ-lattice-η on defunctionalized terms; D3's reading takes the
first thunk to λx.λy. y x and the second to λx.λy. x y, so the applications would read back to
terms that ⊢_{λ-lattice-η} equates with I K = K and with K I = K*, two terms it does not
equate unless ⊢_{λ-lattice-η} is inconsistent. Here neither thunk has a
readback: slots 5 and 7 read no value. Namespace `Witness` below checks each of these facts.

## The proof

The proof goes through a total interpretation, `interpretation`, which is `readback` where the
readback is defined (`interpretationOfReadback`) and gives every finite term a term: a slot
without a value reads the last value of its list (the empty
choice when the list is empty), decisions on which no rule of
⊢^{defunctionalized}_{λ-lattice-η} depends but the defunctionalized η rule. The last value is
the one that rule needs when its hole's slot lies beyond the fillings: `fill` then puts the
hole's variable at the end. Every rule of ⊢^{defunctionalized}_{λ-lattice-η} is sound for
the interpretation (`interpretationSound`): the first clause of the defunctionalized β rule is
one beta step, its second clause is no step (both sides have one interpretation), the
defunctionalized η rule is one eta step, a congruence on a thunk's filling
is a beta expansion, an argument congruence and a beta step, and the other congruences are
congruences. Transitivity then needs no condition on the middle term, which a statement about
the partial readback alone would need: a chain of ⊢^{defunctionalized}_{λ-lattice-η} may
pass through terms without a readback, such as a thunk with a slot its code reads and no filling gives.
-/

namespace LambdaJit.Readback

open LambdaJit.Semantics

/-! ## Substitution and shifting on de Bruijn terms -/

/-- `shiftIterate count term` places `term` under `count` more abstractions: `Term.shift` applied
`count` times. -/
def shiftIterate : Nat → Term → Term
  | 0, term => term
  | count + 1, term => shiftIterate count (Term.shift term)

/-- Substituting into a list of shifted terms at index 0 gives the list back. -/
theorem substituteShiftedList (replacement : Term) : ∀ terms : List Term,
    (terms.map Term.shift).map (Term.substitute 0 replacement) = terms
  | [] => rfl
  | term :: terms => by
      simp only [List.map_cons, Term.shift, Term.substituteShiftFromCancel term 0 replacement]
      exact congrArg _ (substituteShiftedList replacement terms)

/-! ## The readback -/

/-- `abstractions count body` is `body` under `count` abstractions. -/
def abstractions : Nat → Term → Term
  | 0, body => body
  | count + 1, body => .abstraction (abstractions count body)

/-- The values of the slots of a thunk's code under its lambda chain: `slots` holds the values
of the filled slots, and each hole in lambda order is filled by `fill`, the operation of the
first clause of the defunctionalized β rule, with the bound variable of its lambda, index 0 under that lambda, every
value already in the list being carried under the lambda by `Term.shift`. -/
def finalSlots : List Hole → List Term → List Term
  | [], slots => slots
  | hole :: holes, slots =>
      finalSlots holes (fill hole holes (slots.map Term.shift) (.boundVariable 0))

mutual
/-- The readback of a code whose slots have the values `slots`: undefined when the code reads a
slot that has no value. -/
def readbackCode : List Term → Code → Option Term
  | slots, .slot index => slots[index]?
  | slots, .apply function argument => do
      let functionTerm ← readbackCode slots function
      let argumentTerm ← readbackCode slots argument
      pure (.application functionTerm argumentTerm)
  | slots, .thunk code holes fillings => do
      let fillingTerms ← readbackCodeList slots fillings
      let body ← readbackCode (finalSlots holes fillingTerms) code
      pure (abstractions holes.length body)
  | slots, .choice left right => do
      let leftTerm ← readbackCode slots left
      let rightTerm ← readbackCode slots right
      pure (.choice leftTerm rightTerm)
  | slots, .parallel left right => do
      let leftTerm ← readbackCode slots left
      let rightTerm ← readbackCode slots right
      pure (.parallel leftTerm rightTerm)

/-- The readbacks of a list of codes under the same slot values. -/
def readbackCodeList : List Term → List Code → Option (List Term)
  | _, [] => some []
  | slots, code :: codes => do
      let term ← readbackCode slots code
      let terms ← readbackCodeList slots codes
      pure (term :: terms)
end

mutual
/-- The readback of a finite term to a term of the calculus (D3). Undefined on a thunk whose
code reads a slot that has no value. -/
def readback : FiniteTerm → Option Term
  | .thunk code holes fillings => do
      let fillingTerms ← readbackList fillings
      let body ← readbackCode (finalSlots holes fillingTerms) code
      pure (abstractions holes.length body)
  | .apply function argument => do
      let functionTerm ← readback function
      let argumentTerm ← readback argument
      pure (.application functionTerm argumentTerm)
  | .choice left right => do
      let leftTerm ← readback left
      let rightTerm ← readback right
      pure (.choice leftTerm rightTerm)
  | .parallel left right => do
      let leftTerm ← readback left
      let rightTerm ← readback right
      pure (.parallel leftTerm rightTerm)

/-- The readbacks of a list of finite terms. -/
def readbackList : List FiniteTerm → Option (List Term)
  | [] => some []
  | term :: terms => do
      let head ← readback term
      let tail ← readbackList terms
      pure (head :: tail)
end

/-! ## The total interpretation used by the proof -/

/-- The value at `index`, or the last value when `index` lies beyond the values, or `default`
when there is none. -/
def readClamped {α : Type} (default : α) (values : List α) (index : Nat) : α :=
  match values[index]? with
  | some value => value
  | none => values.getLast?.getD default

/-- λx. x, the value of a slot read beyond an empty list of values: `readSlot` needs some term
there, and any closed one serves, since a code that reads back reads no slot beyond its values and
no proof reads this one. -/
def defaultSlotValue : Term := .abstraction (.boundVariable 0)

/-- The value of slot `index`: the value at that position, or the last value when the position
lies beyond the list, or `defaultSlotValue` when the list is empty. -/
def readSlot (slots : List Term) (index : Nat) : Term :=
  readClamped defaultSlotValue slots index

mutual
/-- `readbackCode` made total by `readSlot`. -/
def interpretCode : List Term → Code → Term
  | slots, .slot index => readSlot slots index
  | slots, .apply function argument =>
      .application (interpretCode slots function) (interpretCode slots argument)
  | slots, .thunk code holes fillings =>
      abstractions holes.length
        (interpretCode (finalSlots holes (interpretCodeList slots fillings)) code)
  | slots, .choice left right => .choice (interpretCode slots left) (interpretCode slots right)
  | slots, .parallel left right => .parallel (interpretCode slots left) (interpretCode slots right)

/-- `interpretCode` on each code of a list. -/
def interpretCodeList : List Term → List Code → List Term
  | _, [] => []
  | slots, code :: codes => interpretCode slots code :: interpretCodeList slots codes
end

/-- The interpretation of a thunk of code `code` and holes `holes` whose fillings have the
values `slots`. -/
def thunkTerm (code : Code) (holes : List Hole) (slots : List Term) : Term :=
  abstractions holes.length (interpretCode (finalSlots holes slots) code)

mutual
/-- `readback` made total: a slot without a value reads the last value of its list. -/
def interpretation : FiniteTerm → Term
  | .thunk code holes fillings => thunkTerm code holes (interpretationList fillings)
  | .apply function argument => .application (interpretation function) (interpretation argument)
  | .choice left right => .choice (interpretation left) (interpretation right)
  | .parallel left right => .parallel (interpretation left) (interpretation right)

/-- `interpretation` on each term of a list. -/
def interpretationList : List FiniteTerm → List Term
  | [] => []
  | term :: terms => interpretation term :: interpretationList terms
end

theorem interpretationListMap : ∀ terms : List FiniteTerm,
    interpretationList terms = terms.map interpretation
  | [] => rfl
  | term :: terms => by
      simp only [interpretationList, List.map_cons, interpretationListMap terms]

theorem interpretCodeListMap (slots : List Term) : ∀ codes : List Code,
    interpretCodeList slots codes = codes.map (interpretCode slots)
  | [] => rfl
  | code :: codes => by
      simp only [interpretCodeList, List.map_cons, interpretCodeListMap slots codes]

/-! ## The interpretation extends the readback -/

theorem readSlotOfSome {slots : List Term} {index : Nat} {term : Term}
    (found : slots[index]? = some term) : readSlot slots index = term := by
  simp only [readSlot, readClamped, found]

mutual
theorem interpretCodeOfReadbackCode : ∀ (code : Code) (slots : List Term) (term : Term),
    readbackCode slots code = some term → interpretCode slots code = term
  | .slot index, slots, term, readBack => by
      simp only [readbackCode] at readBack
      simp only [interpretCode, readSlotOfSome readBack]
  | .apply function argument, slots, term, readBack => by
      cases functionReadback : readbackCode slots function with
      | none => simp [readbackCode, functionReadback, bind, Option.bind] at readBack
      | some functionTerm =>
        cases argumentReadback : readbackCode slots argument with
        | none =>
            simp [readbackCode, functionReadback, argumentReadback, bind, Option.bind] at readBack
        | some argumentTerm =>
            simp only [readbackCode, functionReadback, argumentReadback, bind, Option.bind, pure,
              Option.some.injEq] at readBack
            subst readBack
            simp only [interpretCode,
              interpretCodeOfReadbackCode function slots functionTerm functionReadback,
              interpretCodeOfReadbackCode argument slots argumentTerm argumentReadback]
  | .thunk code holes fillings, slots, term, readBack => by
      cases fillingsReadback : readbackCodeList slots fillings with
      | none => simp [readbackCode, fillingsReadback, bind, Option.bind] at readBack
      | some fillingTerms =>
        cases bodyReadback : readbackCode (finalSlots holes fillingTerms) code with
        | none =>
            simp [readbackCode, fillingsReadback, bodyReadback, bind, Option.bind] at readBack
        | some body =>
            simp only [readbackCode, fillingsReadback, bodyReadback, bind, Option.bind, pure,
              Option.some.injEq] at readBack
            subst readBack
            simp only [interpretCode,
              interpretCodeListOfReadbackCodeList fillings slots fillingTerms fillingsReadback,
              interpretCodeOfReadbackCode code _ body bodyReadback]
  | .choice left right, slots, term, readBack => by
      cases leftReadback : readbackCode slots left with
      | none => simp [readbackCode, leftReadback, bind, Option.bind] at readBack
      | some leftTerm =>
        cases rightReadback : readbackCode slots right with
        | none => simp [readbackCode, leftReadback, rightReadback, bind, Option.bind] at readBack
        | some rightTerm =>
            simp only [readbackCode, leftReadback, rightReadback, bind, Option.bind, pure,
              Option.some.injEq] at readBack
            subst readBack
            simp only [interpretCode,
              interpretCodeOfReadbackCode left slots leftTerm leftReadback,
              interpretCodeOfReadbackCode right slots rightTerm rightReadback]
  | .parallel left right, slots, term, readBack => by
      cases leftReadback : readbackCode slots left with
      | none => simp [readbackCode, leftReadback, bind, Option.bind] at readBack
      | some leftTerm =>
        cases rightReadback : readbackCode slots right with
        | none => simp [readbackCode, leftReadback, rightReadback, bind, Option.bind] at readBack
        | some rightTerm =>
            simp only [readbackCode, leftReadback, rightReadback, bind, Option.bind, pure,
              Option.some.injEq] at readBack
            subst readBack
            simp only [interpretCode,
              interpretCodeOfReadbackCode left slots leftTerm leftReadback,
              interpretCodeOfReadbackCode right slots rightTerm rightReadback]

theorem interpretCodeListOfReadbackCodeList : ∀ (codes : List Code) (slots : List Term)
    (terms : List Term), readbackCodeList slots codes = some terms →
      interpretCodeList slots codes = terms
  | [], slots, terms, readBack => by
      simp only [readbackCodeList, Option.some.injEq] at readBack
      subst readBack
      rfl
  | code :: codes, slots, terms, readBack => by
      cases headReadback : readbackCode slots code with
      | none => simp [readbackCodeList, headReadback, bind, Option.bind] at readBack
      | some head =>
        cases tailReadback : readbackCodeList slots codes with
        | none =>
            simp [readbackCodeList, headReadback, tailReadback, bind, Option.bind] at readBack
        | some tail =>
            simp only [readbackCodeList, headReadback, tailReadback, bind, Option.bind, pure,
              Option.some.injEq] at readBack
            subst readBack
            simp only [interpretCodeList,
              interpretCodeOfReadbackCode code slots head headReadback,
              interpretCodeListOfReadbackCodeList codes slots tail tailReadback]
end

mutual
/-- Where the readback is defined, the interpretation is the readback. -/
theorem interpretationOfReadback : ∀ (finiteTerm : FiniteTerm) (term : Term),
    readback finiteTerm = some term → interpretation finiteTerm = term
  | .thunk code holes fillings, term, readBack => by
      cases fillingsReadback : readbackList fillings with
      | none => simp [readback, fillingsReadback, bind, Option.bind] at readBack
      | some fillingTerms =>
        cases bodyReadback : readbackCode (finalSlots holes fillingTerms) code with
        | none => simp [readback, fillingsReadback, bodyReadback, bind, Option.bind] at readBack
        | some body =>
            simp only [readback, fillingsReadback, bodyReadback, bind, Option.bind, pure,
              Option.some.injEq] at readBack
            subst readBack
            simp only [interpretation, thunkTerm,
              interpretationListOfReadbackList fillings fillingTerms fillingsReadback,
              interpretCodeOfReadbackCode code _ body bodyReadback]
  | .apply function argument, term, readBack => by
      cases functionReadback : readback function with
      | none => simp [readback, functionReadback, bind, Option.bind] at readBack
      | some functionTerm =>
        cases argumentReadback : readback argument with
        | none =>
            simp [readback, functionReadback, argumentReadback, bind, Option.bind] at readBack
        | some argumentTerm =>
            simp only [readback, functionReadback, argumentReadback, bind, Option.bind, pure,
              Option.some.injEq] at readBack
            subst readBack
            simp only [interpretation,
              interpretationOfReadback function functionTerm functionReadback,
              interpretationOfReadback argument argumentTerm argumentReadback]
  | .choice left right, term, readBack => by
      cases leftReadback : readback left with
      | none => simp [readback, leftReadback, bind, Option.bind] at readBack
      | some leftTerm =>
        cases rightReadback : readback right with
        | none => simp [readback, leftReadback, rightReadback, bind, Option.bind] at readBack
        | some rightTerm =>
            simp only [readback, leftReadback, rightReadback, bind, Option.bind, pure,
              Option.some.injEq] at readBack
            subst readBack
            simp only [interpretation,
              interpretationOfReadback left leftTerm leftReadback,
              interpretationOfReadback right rightTerm rightReadback]
  | .parallel left right, term, readBack => by
      cases leftReadback : readback left with
      | none => simp [readback, leftReadback, bind, Option.bind] at readBack
      | some leftTerm =>
        cases rightReadback : readback right with
        | none => simp [readback, leftReadback, rightReadback, bind, Option.bind] at readBack
        | some rightTerm =>
            simp only [readback, leftReadback, rightReadback, bind, Option.bind, pure,
              Option.some.injEq] at readBack
            subst readBack
            simp only [interpretation,
              interpretationOfReadback left leftTerm leftReadback,
              interpretationOfReadback right rightTerm rightReadback]

theorem interpretationListOfReadbackList : ∀ (finiteTerms : List FiniteTerm) (terms : List Term),
    readbackList finiteTerms = some terms → interpretationList finiteTerms = terms
  | [], terms, readBack => by
      simp only [readbackList, Option.some.injEq] at readBack
      subst readBack
      rfl
  | finiteTerm :: finiteTerms, terms, readBack => by
      cases headReadback : readback finiteTerm with
      | none => simp [readbackList, headReadback, bind, Option.bind] at readBack
      | some head =>
        cases tailReadback : readbackList finiteTerms with
        | none => simp [readbackList, headReadback, tailReadback, bind, Option.bind] at readBack
        | some tail =>
            simp only [readbackList, headReadback, tailReadback, bind, Option.bind, pure,
              Option.some.injEq] at readBack
            subst readBack
            simp only [interpretationList,
              interpretationOfReadback finiteTerm head headReadback,
              interpretationListOfReadbackList finiteTerms tail tailReadback]
end

/-! ## Substitution commutes with the interpretation of a code -/

theorem readSlotMap (function : Term → Term) (preserves : function defaultSlotValue = defaultSlotValue)
    (slots : List Term) (index : Nat) :
    readSlot (slots.map function) index = function (readSlot slots index) := by
  unfold readSlot readClamped
  rw [List.getElem?_map]
  cases found : slots[index]? with
  | some term => rfl
  | none =>
      simp only [Option.map_none, List.getLast?_map]
      cases last : slots.getLast? with
      | none => simp [preserves]
      | some term => rfl

theorem substituteAbstractions : ∀ (count depth : Nat) (replacement body : Term),
    Term.substitute depth replacement (abstractions count body) =
      abstractions count (Term.substitute (depth + count) (shiftIterate count replacement) body)
  | 0, _, _, _ => rfl
  | count + 1, depth, replacement, body => by
      simp only [abstractions, Term.substitute,
        substituteAbstractions count (depth + 1) (Term.shift replacement) body]
      have reordered : depth + 1 + count = depth + (count + 1) := by omega
      rw [reordered]
      rfl

/-- Substitution carried through the holes of a thunk: substituting at `depth` into the values
of the filled slots, then filling the holes, is filling the holes and then substituting at
`depth` plus the number of holes, with the replacement shifted once per hole. -/
theorem finalSlotsSubstitute : ∀ (holes : List Hole) (slots : List Term) (depth : Nat)
    (replacement : Term),
    (finalSlots holes slots).map
        (Term.substitute (depth + holes.length) (shiftIterate holes.length replacement)) =
      finalSlots holes (slots.map (Term.substitute depth replacement))
  | [], slots, depth, replacement => rfl
  | hole :: holes, slots, depth, replacement => by
      have inner := finalSlotsSubstitute holes
        (fill hole holes (slots.map Term.shift) (.boundVariable 0)) (depth + 1)
        (Term.shift replacement)
      have reordered : depth + (hole :: holes).length = depth + 1 + holes.length := by
        simp only [List.length_cons]
        omega
      have shifted : (slots.map Term.shift).map
            (Term.substitute (depth + 1) (Term.shift replacement)) =
          (slots.map (Term.substitute depth replacement)).map Term.shift := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro term _
        exact Term.substituteShiftFromCommute term 0 depth replacement (Nat.zero_le depth)
      have variableKept : Term.substitute (depth + 1) (Term.shift replacement)
          (.boundVariable 0) = .boundVariable 0 := by
        simp [Term.substitute]
      simp only [finalSlots]
      rw [reordered]
      show List.map (Term.substitute (depth + 1 + holes.length)
        (shiftIterate holes.length (Term.shift replacement))) _ = _
      rw [inner, map_fill, shifted, variableKept]

mutual
/-- Substitution commutes with the interpretation of a code: substituting into the
interpretation is interpreting under the substituted slot values. -/
theorem interpretCodeSubstitute : ∀ (code : Code) (slots : List Term) (depth : Nat)
    (replacement : Term),
    Term.substitute depth replacement (interpretCode slots code) =
      interpretCode (slots.map (Term.substitute depth replacement)) code
  | .slot index, slots, depth, replacement => by
      simp only [interpretCode]
      exact (readSlotMap _ (by simp [defaultSlotValue, Term.substitute]) slots index).symm
  | .apply function argument, slots, depth, replacement => by
      simp only [interpretCode, Term.substitute,
        interpretCodeSubstitute function slots depth replacement,
        interpretCodeSubstitute argument slots depth replacement]
  | .thunk code holes fillings, slots, depth, replacement => by
      simp only [interpretCode]
      rw [substituteAbstractions, interpretCodeSubstitute code, finalSlotsSubstitute,
        interpretCodeListSubstitute fillings slots depth replacement]
  | .choice left right, slots, depth, replacement => by
      simp only [interpretCode, Term.substitute,
        interpretCodeSubstitute left slots depth replacement,
        interpretCodeSubstitute right slots depth replacement]
  | .parallel left right, slots, depth, replacement => by
      simp only [interpretCode, Term.substitute,
        interpretCodeSubstitute left slots depth replacement,
        interpretCodeSubstitute right slots depth replacement]

theorem interpretCodeListSubstitute : ∀ (codes : List Code) (slots : List Term) (depth : Nat)
    (replacement : Term),
    (interpretCodeList slots codes).map (Term.substitute depth replacement) =
      interpretCodeList (slots.map (Term.substitute depth replacement)) codes
  | [], _, _, _ => rfl
  | code :: codes, slots, depth, replacement => by
      simp only [interpretCodeList, List.map_cons,
        interpretCodeSubstitute code slots depth replacement,
        interpretCodeListSubstitute codes slots depth replacement]
end

theorem thunkTermSubstitute (code : Code) (holes : List Hole) (slots : List Term) (depth : Nat)
    (replacement : Term) :
    Term.substitute depth replacement (thunkTerm code holes slots) =
      thunkTerm code holes (slots.map (Term.substitute depth replacement)) := by
  simp only [thunkTerm]
  rw [substituteAbstractions, interpretCodeSubstitute, finalSlotsSubstitute]

/-! ## The rules of ⊢^{defunctionalized}_{λ-lattice-η} under the interpretation -/

/-- The first clause of the defunctionalized β rule is one beta step: the interpretation of the application is the
redex (λ. body) A and the interpretation of the filled thunk is its contractum. -/
theorem interpretationBetaFill (code : Code) (hole : Hole) (holes : List Hole)
    (fillings : List FiniteTerm) (argument : FiniteTerm) :
    interpretation (.apply (.thunk code (hole :: holes) fillings) argument) =
        .application
          (.abstraction (thunkTerm code holes
            (fill hole holes ((interpretationList fillings).map Term.shift) (.boundVariable 0))))
          (interpretation argument) ∧
      interpretation (.thunk code holes (fill hole holes fillings argument)) =
        Term.instantiate
          (thunkTerm code holes
            (fill hole holes ((interpretationList fillings).map Term.shift) (.boundVariable 0)))
          (interpretation argument) := by
  constructor
  · rfl
  · have variableReplaced : Term.substitute 0 (interpretation argument) (.boundVariable 0) =
        interpretation argument := by
      simp [Term.substitute]
    simp only [interpretation, Term.instantiate, thunkTermSubstitute, map_fill,
      substituteShiftedList, variableReplaced, interpretationListMap]

mutual
/-- The second clause of the defunctionalized β rule is no step: the instance of a code under the fillings has the
interpretation of the code under the fillings' interpretations. -/
theorem interpretationInstantiate : ∀ (code : Code) (fillings : List FiniteTerm)
    (instantiated : FiniteTerm), code.instantiate fillings = some instantiated →
      interpretation instantiated = interpretCode (interpretationList fillings) code
  | .slot index, fillings, instantiated, instantiation => by
      simp only [Code.instantiate] at instantiation
      have found : (interpretationList fillings)[index]? = some (interpretation instantiated) := by
        simp [interpretationListMap, instantiation]
      simp only [interpretCode, readSlotOfSome found]
  | .apply function argument, fillings, instantiated, instantiation => by
      cases functionInstance : Code.instantiate fillings function with
      | none => simp [Code.instantiate, functionInstance, bind, Option.bind] at instantiation
      | some functionTerm =>
        cases argumentInstance : Code.instantiate fillings argument with
        | none =>
            simp [Code.instantiate, functionInstance, argumentInstance, bind,
              Option.bind] at instantiation
        | some argumentTerm =>
            simp only [Code.instantiate, functionInstance, argumentInstance, bind, Option.bind,
              pure, Option.some.injEq] at instantiation
            subst instantiation
            simp only [interpretation, interpretCode,
              interpretationInstantiate function fillings functionTerm functionInstance,
              interpretationInstantiate argument fillings argumentTerm argumentInstance]
  | .thunk code holes codeFillings, fillings, instantiated, instantiation => by
      cases fillingsInstance : Code.instantiateList fillings codeFillings with
      | none => simp [Code.instantiate, fillingsInstance, bind, Option.bind] at instantiation
      | some fillingTerms =>
          simp only [Code.instantiate, fillingsInstance, bind, Option.bind, pure,
            Option.some.injEq] at instantiation
          subst instantiation
          simp only [interpretation, interpretCode, thunkTerm,
            interpretationListInstantiate codeFillings fillings fillingTerms fillingsInstance]
  | .choice left right, fillings, instantiated, instantiation => by
      cases leftInstance : Code.instantiate fillings left with
      | none => simp [Code.instantiate, leftInstance, bind, Option.bind] at instantiation
      | some leftTerm =>
        cases rightInstance : Code.instantiate fillings right with
        | none =>
            simp [Code.instantiate, leftInstance, rightInstance, bind, Option.bind] at instantiation
        | some rightTerm =>
            simp only [Code.instantiate, leftInstance, rightInstance, bind, Option.bind, pure,
              Option.some.injEq] at instantiation
            subst instantiation
            simp only [interpretation, interpretCode,
              interpretationInstantiate left fillings leftTerm leftInstance,
              interpretationInstantiate right fillings rightTerm rightInstance]
  | .parallel left right, fillings, instantiated, instantiation => by
      cases leftInstance : Code.instantiate fillings left with
      | none => simp [Code.instantiate, leftInstance, bind, Option.bind] at instantiation
      | some leftTerm =>
        cases rightInstance : Code.instantiate fillings right with
        | none =>
            simp [Code.instantiate, leftInstance, rightInstance, bind, Option.bind] at instantiation
        | some rightTerm =>
            simp only [Code.instantiate, leftInstance, rightInstance, bind, Option.bind, pure,
              Option.some.injEq] at instantiation
            subst instantiation
            simp only [interpretation, interpretCode,
              interpretationInstantiate left fillings leftTerm leftInstance,
              interpretationInstantiate right fillings rightTerm rightInstance]

theorem interpretationListInstantiate : ∀ (codes : List Code) (fillings : List FiniteTerm)
    (instantiated : List FiniteTerm), Code.instantiateList fillings codes = some instantiated →
      interpretationList instantiated = interpretCodeList (interpretationList fillings) codes
  | [], fillings, instantiated, instantiation => by
      simp only [Code.instantiateList, Option.some.injEq] at instantiation
      subst instantiation
      rfl
  | code :: codes, fillings, instantiated, instantiation => by
      cases headInstance : Code.instantiate fillings code with
      | none => simp [Code.instantiateList, headInstance, bind, Option.bind] at instantiation
      | some head =>
        cases tailInstance : Code.instantiateList fillings codes with
        | none =>
            simp [Code.instantiateList, headInstance, tailInstance, bind,
              Option.bind] at instantiation
        | some tail =>
            simp only [Code.instantiateList, headInstance, tailInstance, bind, Option.bind, pure,
              Option.some.injEq] at instantiation
            subst instantiation
            simp only [interpretationList, interpretCodeList,
              interpretationInstantiate code fillings head headInstance,
              interpretationListInstantiate codes fillings tail tailInstance]
end

/-- The thunk of the second clause of the defunctionalized β rule and the instance have one interpretation. -/
theorem interpretationBetaInstance {code : Code} {fillings : List FiniteTerm}
    {instantiated : FiniteTerm} (instantiation : code.instantiate fillings = some instantiated) :
    interpretation (.thunk code [] fillings) = interpretation instantiated := by
  rw [interpretationInstantiate code fillings instantiated instantiation]
  rfl

theorem fillingPositionNil (index : Nat) : fillingPosition [] index = index := by
  have kept : (List.range index).filter
      (fun lower => !([] : List Hole).contains (Hole.slot lower)) = List.range index :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simp only [fillingPosition, kept, List.length_range]

/-- The position of filled slot `position` among the fillings of a thunk with the one hole
`slot hole`: the slots below it, less the hole when the hole is below it. -/
theorem fillingPositionSingletonCount (hole : Nat) : ∀ position : Nat,
    fillingPosition [.slot hole] position = if position ≤ hole then position else position - 1
  | 0 => by simp [fillingPosition]
  | position + 1 => by
      have inner := fillingPositionSingletonCount hole position
      unfold fillingPosition at inner ⊢
      rw [List.range_succ, List.filter_append, List.length_append, inner]
      by_cases atHole : position = hole
      · subst atHole
        simp
      · by_cases below : position < hole
        · have belowOrAt : position ≤ hole := by omega
          have nextBelowOrAt : position + 1 ≤ hole := by omega
          simp [atHole, belowOrAt, nextBelowOrAt]
        · have notBelowOrAt : ¬ position ≤ hole := by omega
          have notNextBelowOrAt : ¬ position + 1 ≤ hole := by omega
          simp [atHole, notBelowOrAt, notNextBelowOrAt]
          omega

theorem fillingPositionSingleton {position hole : Nat} (distinct : position ≠ hole) :
    fillingPosition [.slot hole] position = if position < hole then position else position - 1 := by
  rw [fillingPositionSingletonCount hole position]
  by_cases below : position < hole
  · have belowOrAt : position ≤ hole := by omega
    simp [below, belowOrAt]
  · have notBelowOrAt : ¬ position ≤ hole := by omega
    simp [below, notBelowOrAt]

/-- The value `fill` inserted at `position` is read there, even when `position` lies beyond the
values (the inserted value then sits last). -/
theorem readClampedInserted {α : Type} (default : α) (values : List α) (position : Nat)
    (inserted : α) :
    readClamped default (values.take position ++ inserted :: values.drop position) position =
      inserted := by
  unfold readClamped
  by_cases within : position ≤ values.length
  · have lengthTaken : (values.take position).length = position := by
      simp [List.length_take, within]
    rw [List.getElem?_append_right (by omega), lengthTaken, Nat.sub_self]
    rfl
  · have taken : values.take position = values := List.take_of_length_le (by omega)
    have dropped : values.drop position = [] := List.drop_of_length_le (by omega)
    rw [taken, dropped]
    have beyond : (values ++ [inserted])[position]? = none := by
      apply List.getElem?_eq_none
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    simp [beyond]

/-- Beside the position `fill` inserted at, a value is read from its place before the insertion.
-/
theorem readClampedBesideInserted {α : Type} (default : α) (values : List α)
    (position index : Nat) (inserted value : α) (distinct : index ≠ position)
    (found : values[if index < position then index else index - 1]? = some value) :
    readClamped default (values.take position ++ inserted :: values.drop position) index =
      value := by
  unfold readClamped
  by_cases below : index < position
  · simp only [below, if_true] at found
    have withinValues : index < values.length := (List.getElem?_eq_some_iff.mp found).1
    have withinTaken : index < (values.take position).length := by
      simp [List.length_take]
      omega
    rw [List.getElem?_append_left withinTaken, List.getElem?_take]
    simp [below, found]
  · simp only [below, if_false] at found
    have withinValues : index - 1 < values.length := (List.getElem?_eq_some_iff.mp found).1
    have positionWithin : position ≤ values.length := by omega
    have lengthTaken : (values.take position).length = position := by
      simp [List.length_take]
      omega
    rw [List.getElem?_append_right (by omega), lengthTaken]
    have offset : index - position = (index - 1 - position) + 1 := by omega
    rw [offset, List.getElem?_cons_succ, List.getElem?_drop]
    have restored : position + (index - 1 - position) = index - 1 := by omega
    rw [restored, found]

/-- The value of a slot after `fill` put `inserted` at position `position`: the inserted value
at `position` itself, even when `position` lies beyond the list (the value then sits last). -/
theorem readSlotInserted (values : List Term) (position : Nat) (inserted : Term) :
    readSlot (values.take position ++ inserted :: values.drop position) position = inserted :=
  readClampedInserted defaultSlotValue values position inserted

/-- The value of another slot after the insertion: the value at its position in the list
before the insertion, counted past the inserted one. -/
theorem readSlotBesideInserted (values : List Term) (position index : Nat) (inserted : Term)
    (value : Term) (distinct : index ≠ position)
    (found : values[if index < position then index else index - 1]? = some value) :
    readSlot (values.take position ++ inserted :: values.drop position) index = value :=
  readClampedBesideInserted defaultSlotValue values position index inserted value distinct
    found

/-- The defunctionalized η rule is one eta step: the interpretation of the thunk is λ. (shift F) 0, F being the
interpretation of the filling. -/
theorem interpretationEta {function hole : Nat} {fillings : List FiniteTerm}
    {filling : FiniteTerm} (distinct : function ≠ hole)
    (found : fillings[fillingPosition [.slot hole] function]? = some filling) :
    interpretation (.thunk (.apply (.slot function) (.slot hole)) [.slot hole] fillings) =
      .abstraction (.application (Term.shift (interpretation filling)) (.boundVariable 0)) := by
  have shiftedFound : ((interpretationList fillings).map Term.shift)[
      if function < hole then function else function - 1]? =
        some (Term.shift (interpretation filling)) := by
    rw [← fillingPositionSingleton distinct]
    simp [interpretationListMap, found]
  simp only [interpretation, thunkTerm, finalSlots, List.length_singleton, abstractions, interpretCode, fill,
    fillingPositionNil,
    readSlotInserted, readSlotBesideInserted _ hole function _ _ distinct shiftedFound]

/-! ## Agreement with D3's reading on thunks whose fills place every argument at its slot -/

theorem fillingPositionSuccessor (holes : List Hole) (index : Nat) :
    fillingPosition holes (index + 1) =
      fillingPosition holes index + (if Hole.slot index ∈ holes then 0 else 1) := by
  unfold fillingPosition
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases member : Hole.slot index ∈ holes <;> simp [member]

theorem fillingPositionMonotone (holes : List Hole) {lower upper : Nat} (ordered : lower ≤ upper) :
    fillingPosition holes lower ≤ fillingPosition holes upper := by
  induction upper with
  | zero =>
      have atZero : lower = 0 := by omega
      rw [atZero]
      exact Nat.le_refl _
  | succ upper inner =>
      rcases Nat.lt_or_ge lower (upper + 1) with below | atTop
      · have step := fillingPositionSuccessor holes upper
        have previous := inner (by omega)
        omega
      · have equal : lower = upper + 1 := by omega
        rw [equal]
        exact Nat.le_refl _

/-- A filled slot comes before every slot above it. -/
theorem fillingPositionStrict (holes : List Hole) {lower upper : Nat} (ordered : lower < upper)
    (filled : Hole.slot lower ∉ holes) :
    fillingPosition holes lower < fillingPosition holes upper := by
  have step := fillingPositionSuccessor holes lower
  simp only [filled, if_false] at step
  have rest := fillingPositionMonotone holes (show lower + 1 ≤ upper by omega)
  omega

theorem fillingPositionIgnored (holes : List Hole) : ∀ index : Nat,
    fillingPosition (.ignored :: holes) index = fillingPosition holes index
  | 0 => rfl
  | index + 1 => by
      rw [fillingPositionSuccessor, fillingPositionSuccessor, fillingPositionIgnored holes index]
      simp

/-- Below or at a hole's slot, the hole does not count among the filled slots. -/
theorem fillingPositionBelowHole (hole : Nat) (holes : List Hole) : ∀ index : Nat,
    index ≤ hole → fillingPosition holes index = fillingPosition (.slot hole :: holes) index
  | 0, _ => rfl
  | index + 1, ordered => by
      rw [fillingPositionSuccessor, fillingPositionSuccessor,
        fillingPositionBelowHole hole holes index (by omega)]
      have distinct : index ≠ hole := by omega
      simp [distinct]

/-- Above a hole's slot, the hole counts once more among the filled slots of the other holes. -/
theorem fillingPositionAboveHole (hole : Nat) (holes : List Hole)
    (absent : Hole.slot hole ∉ holes) : ∀ index : Nat,
    hole < index → fillingPosition holes index = fillingPosition (.slot hole :: holes) index + 1
  | 0, ordered => absurd ordered (Nat.not_lt_zero hole)
  | index + 1, ordered => by
      rw [fillingPositionSuccessor, fillingPositionSuccessor]
      by_cases atHole : index = hole
      · subst atHole
        rw [← fillingPositionBelowHole index holes index (Nat.le_refl index)]
        simp [absent]
      · rw [fillingPositionAboveHole hole holes absent index (by omega)]
        simp [atHole]
        omega

/-- The position, in lambda order, of the hole whose slot is `index`, if any. -/
def holePosition : List Hole → Nat → Option Nat
  | [], _ => none
  | hole :: holes, index =>
      if hole = .slot index then some 0 else (holePosition holes index).map (· + 1)

theorem holePositionAbsent : ∀ (holes : List Hole) (index : Nat),
    Hole.slot index ∉ holes → holePosition holes index = none
  | [], _, _ => rfl
  | hole :: holes, index, absent => by
      have notHead : hole ≠ .slot index := by
        intro equal
        exact absent (equal ▸ List.mem_cons_self)
      have notTail : Hole.slot index ∉ holes := fun member => absent (List.mem_cons_of_mem _ member)
      simp [holePosition, notHead, holePositionAbsent holes index notTail]

theorem absentOfHolePosition : ∀ (holes : List Hole) (index : Nat),
    holePosition holes index = none → Hole.slot index ∉ holes
  | [], _, _ => List.not_mem_nil
  | hole :: holes, index, noPosition => by
      by_cases atHead : hole = .slot index
      · simp [holePosition, atHead] at noPosition
      · simp only [holePosition, atHead, if_false, Option.map_eq_none_iff] at noPosition
        intro member
        rcases List.mem_cons.mp member with equal | inTail
        · exact atHead equal.symm
        · exact absentOfHolePosition holes index noPosition inTail

/-- D3's reading of slot `index` of the body of a thunk with holes `holes` whose filled slots
have the values `slots`: the bound variable of the hole whose slot it is, counted at the body
under the thunk's lambdas, or the value at its position among the filled slots, carried under
the lambdas; none when that position lies beyond the values. -/
def staticSlot (holes : List Hole) (slots : List Term) (index : Nat) : Option Term :=
  match holePosition holes index with
  | some position => some (.boundVariable (holes.length - 1 - position))
  | none => (slots[fillingPosition holes index]?).map (shiftIterate holes.length)

/-- No slot is the slot of two holes. -/
def DistinctSlots : List Hole → Prop
  | [] => True
  | hole :: holes => (∀ index, hole = .slot index → Hole.slot index ∉ holes) ∧ DistinctSlots holes

/-- Every hole's slot has its position among the filled slots at most `count`, the number of
values: filling the holes in lambda order never places an argument beyond the values. -/
def NoClamping (holes : List Hole) (count : Nat) : Prop :=
  ∀ index, Hole.slot index ∈ holes → fillingPosition holes index ≤ count

theorem shiftIterateBoundVariable : ∀ (count index : Nat),
    shiftIterate count (.boundVariable index) = .boundVariable (index + count)
  | 0, _ => rfl
  | count + 1, index => by
      simp only [shiftIterate, Term.shift, Term.shiftFrom, Nat.not_lt_zero, if_false]
      rw [shiftIterateBoundVariable count (index + 1)]
      congr 1
      omega

theorem insertedBelow (values : List Term) (position index : Nat) (inserted : Term)
    (below : index < position) (within : position ≤ values.length) :
    (values.take position ++ inserted :: values.drop position)[index]? = values[index]? := by
  have withinTaken : index < (values.take position).length := by
    simp [List.length_take]
    omega
  rw [List.getElem?_append_left withinTaken, List.getElem?_take]
  simp [below]

theorem insertedAt (values : List Term) (position : Nat) (inserted : Term)
    (within : position ≤ values.length) :
    (values.take position ++ inserted :: values.drop position)[position]? = some inserted := by
  have lengthTaken : (values.take position).length = position := by
    simp [List.length_take]
    omega
  rw [List.getElem?_append_right (by omega), lengthTaken, Nat.sub_self]
  rfl

theorem insertedAbove (values : List Term) (position index : Nat) (inserted : Term)
    (above : position ≤ index) (within : position ≤ values.length) :
    (values.take position ++ inserted :: values.drop position)[index + 1]? = values[index]? := by
  have lengthTaken : (values.take position).length = position := by
    simp [List.length_take]
    omega
  rw [List.getElem?_append_right (by omega), lengthTaken]
  have offset : index + 1 - position = (index - position) + 1 := by omega
  rw [offset, List.getElem?_cons_succ, List.getElem?_drop]
  have restored : position + (index - position) = index := by omega
  rw [restored]

/-- On a thunk whose holes are distinct slots and whose fills place every argument at its slot,
the values under which `readback` reads the body are D3's reading: slot `index` holds the bound
variable of its hole, or the filling at its position among the filled slots. -/
theorem finalSlotsStatic : ∀ (holes : List Hole) (slots : List Term), DistinctSlots holes →
    NoClamping holes slots.length →
      ∀ index, (finalSlots holes slots)[index]? = staticSlot holes slots index
  | [], slots, _, _, index => by
      simp only [finalSlots, staticSlot, holePosition, fillingPositionNil, shiftIterate]
      cases slots[index]? <;> rfl
  | .ignored :: holes, slots, distinct, noClamping, index => by
      have shiftedNoClamping : NoClamping holes (slots.map Term.shift).length := by
        intro slotIndex member
        rw [List.length_map, ← fillingPositionIgnored holes slotIndex]
        exact noClamping slotIndex (List.mem_cons_of_mem _ member)
      have inner := finalSlotsStatic holes (slots.map Term.shift) distinct.2 shiftedNoClamping
        index
      simp only [finalSlots, fill]
      rw [inner]
      simp only [staticSlot, holePosition, fillingPositionIgnored, List.length_cons]
      have notSlot : Hole.ignored ≠ Hole.slot index := by simp
      simp only [notSlot, if_false]
      cases found : holePosition holes index with
      | some position =>
          simp only [Option.map_some]
          congr 2
          omega
      | none =>
          simp only [Option.map_none, List.getElem?_map, Option.map_map]
          rfl
  | .slot hole :: holes, slots, distinct, noClamping, index => by
      have absent : Hole.slot hole ∉ holes := distinct.1 hole rfl
      have holeWithin : fillingPosition holes hole ≤ (slots.map Term.shift).length := by
        rw [List.length_map, fillingPositionBelowHole hole holes hole (Nat.le_refl hole)]
        exact noClamping hole List.mem_cons_self
      have filledLength : (fill (.slot hole) holes (slots.map Term.shift)
          (.boundVariable 0)).length = slots.length + 1 := by
        simp only [fill, List.length_append, List.length_take, List.length_cons,
          List.length_drop, List.length_map] at holeWithin ⊢
        omega
      have filledNoClamping : NoClamping holes
          (fill (.slot hole) holes (slots.map Term.shift) (.boundVariable 0)).length := by
        intro slotIndex member
        rw [filledLength]
        have bound := noClamping slotIndex (List.mem_cons_of_mem _ member)
        rcases Nat.lt_or_ge hole slotIndex with above | belowOrAt
        · rw [fillingPositionAboveHole hole holes absent slotIndex above]
          omega
        · rw [fillingPositionBelowHole hole holes slotIndex belowOrAt]
          omega
      have inner := finalSlotsStatic holes
        (fill (.slot hole) holes (slots.map Term.shift) (.boundVariable 0)) distinct.2
        filledNoClamping index
      simp only [finalSlots]
      rw [inner]
      by_cases atHole : index = hole
      · subst atHole
        simp only [staticSlot, holePosition, if_true, holePositionAbsent holes index absent,
          List.length_cons, fill]
        rw [insertedAt _ _ _ holeWithin]
        simp only [Option.map_some, shiftIterateBoundVariable]
        congr 2
        omega
      · have notSlot : Hole.slot hole ≠ Hole.slot index := by
          intro equal
          exact atHole (Hole.slot.inj equal).symm
        cases found : holePosition holes index with
        | some position =>
            simp only [staticSlot, holePosition, notSlot, if_false, found, Option.map_some,
              List.length_cons]
            congr 2
            omega
        | none =>
            have filledIndex : Hole.slot index ∉ Hole.slot hole :: holes := by
              intro member
              rcases List.mem_cons.mp member with equal | inTail
              · exact notSlot equal.symm
              · exact absentOfHolePosition holes index found inTail
            simp only [staticSlot, holePosition, notSlot, if_false, found, Option.map_none,
              List.length_cons, fill]
            rcases Nat.lt_or_ge index hole with below | above
            · rw [fillingPositionBelowHole hole holes index (by omega)]
              have before : fillingPosition (.slot hole :: holes) index <
                  fillingPosition holes hole := by
                rw [fillingPositionBelowHole hole holes hole (Nat.le_refl hole)]
                exact fillingPositionStrict _ below filledIndex
              rw [insertedBelow _ _ _ _ before holeWithin, List.getElem?_map, Option.map_map]
              rfl
            · have strictlyAbove : hole < index := by omega
              rw [fillingPositionAboveHole hole holes absent index strictlyAbove]
              have after :
                  fillingPosition holes hole ≤ fillingPosition (.slot hole :: holes) index := by
                rw [fillingPositionBelowHole hole holes hole (Nat.le_refl hole)]
                exact fillingPositionMonotone _ (by omega)
              rw [insertedAbove _ _ _ _ after holeWithin, List.getElem?_map, Option.map_map]
              rfl

/-! ## The witness against D3's reading on thunks whose fills clamp

The two thunks of the module docstring, Lean-checked: their applications to K and then to I are
equal in λ-lattice-η on defunctionalized terms, their slot values under D3's reading are
those of λx.λy. y x and λx.λy. x y, under which ⊢_{λ-lattice-η} equates the applications
with K and with K*, and neither satisfies
`NoClamping` nor has a readback. -/

namespace Witness

/-- The code `apply (slot 5) (slot 7)`. -/
def code : Code := .apply (.slot 5) (.slot 7)

/-- K, `\x. \y. x`, as a thunk without fillings. -/
def first : FiniteTerm := .thunk (.slot 0) [.slot 0, .ignored] []

/-- I, `\x. x`, as a thunk without fillings. -/
def identity : FiniteTerm := .thunk (.slot 0) [.slot 0] []

/-- The thunk whose first hole is slot 7. -/
def slotSevenFirst : FiniteTerm := .thunk code [.slot 7, .slot 5] []

/-- The thunk whose first hole is slot 5. -/
def slotFiveFirst : FiniteTerm := .thunk code [.slot 5, .slot 7] []

/-- Both applications reach `thunk(code, [], [K, I])` by the first clause of the defunctionalized
β rule. -/
theorem applicationsEqual :
    Equal (.apply (.apply slotSevenFirst first) identity)
      (.apply (.apply slotFiveFirst first) identity) := by
  have sevenFirst : Equal (.apply (.apply slotSevenFirst first) identity)
      (.thunk code [] [first, identity]) :=
    .transitive (.congruenceApply (Equal.betaFill (code := code) (hole := .slot 7)
        (holes := [.slot 5]) (fillings := []) (argument := first)) (.reflexive identity))
      (Equal.betaFill (code := code) (hole := .slot 5) (holes := []) (fillings := [first])
        (argument := identity))
  have fiveFirst : Equal (.apply (.apply slotFiveFirst first) identity)
      (.thunk code [] [first, identity]) :=
    .transitive (.congruenceApply (Equal.betaFill (code := code) (hole := .slot 5)
        (holes := [.slot 7]) (fillings := []) (argument := first)) (.reflexive identity))
      (Equal.betaFill (code := code) (hole := .slot 7) (holes := []) (fillings := [first])
        (argument := identity))
  exact .transitive sevenFirst (.symmetric fiveFirst)

/-- Under D3's reading, the thunk whose first hole is slot 7 reads slot 5 as the inner bound
variable and slot 7 as the outer one: its body is y x. -/
theorem slotSevenFirstStatic :
    staticSlot [.slot 7, .slot 5] [] 5 = some (.boundVariable 0) ∧
      staticSlot [.slot 7, .slot 5] [] 7 = some (.boundVariable 1) := by
  decide

/-- Under D3's reading, the thunk whose first hole is slot 5 reads slot 5 as the outer bound
variable and slot 7 as the inner one: its body is x y. -/
theorem slotFiveFirstStatic :
    staticSlot [.slot 5, .slot 7] [] 5 = some (.boundVariable 1) ∧
      staticSlot [.slot 5, .slot 7] [] 7 = some (.boundVariable 0) := by
  decide

/-- K and I as terms of the calculus. -/
def firstTerm : Term := .abstraction (.abstraction (.boundVariable 1))
def identityTerm : Term := .abstraction (.boundVariable 0)

/-- D3's reading of the first application, (λx.λy. y x) K I, equals K by ⊢_{λ-lattice-η}.
-/
theorem slotSevenFirstReading {hypotheses : Term → Term → Prop} :
    DerivableLatticeEta hypotheses
      (.application (.application (.abstraction (.abstraction
        (.application (.boundVariable 0) (.boundVariable 1)))) firstTerm) identityTerm)
      Semantics.first :=
  .transitive (.congruenceFunction _ (.beta _ _)) (.transitive (.beta _ _) (.beta _ _))

/-- D3's reading of the second application, (λx.λy. x y) K I, equals K* by
⊢_{λ-lattice-η}. -/
theorem slotFiveFirstReading {hypotheses : Term → Term → Prop} :
    DerivableLatticeEta hypotheses
      (.application (.application (.abstraction (.abstraction
        (.application (.boundVariable 1) (.boundVariable 0)))) firstTerm) identityTerm)
      Semantics.second :=
  .transitive (.congruenceFunction _ (.beta _ _)) (.transitive (.beta _ _) (.beta _ _))

/-- Neither thunk satisfies `NoClamping`: slot 7 has position 6 among the filled slots of
either, and there is no filling. -/
theorem clamped :
    ¬ NoClamping [.slot 7, .slot 5] 0 ∧ ¬ NoClamping [.slot 5, .slot 7] 0 := by
  constructor
  · intro noClamping
    have bound := noClamping 7 (by simp)
    have position : fillingPosition [.slot 7, .slot 5] 7 = 6 := by decide
    omega
  · intro noClamping
    have bound := noClamping 7 (by simp)
    have position : fillingPosition [.slot 5, .slot 7] 7 = 6 := by decide
    omega

/-- Neither thunk has a readback. -/
theorem noReadback : readback slotSevenFirst = none ∧ readback slotFiveFirst = none := by
  decide

end Witness

/-! ## Soundness of ⊢^{defunctionalized}_{λ-lattice-η} for the interpretation, and for the
readback -/

variable {hypotheses : Term → Term → Prop}

/-- Equal terms placed at index 0 of one body give equal instances: a beta expansion, an
argument congruence, and a beta step. -/
theorem derivableInstantiate (body : Term) {left right : Term}
    (equal : DerivableLatticeEta hypotheses left right) :
    DerivableLatticeEta hypotheses (Term.instantiate body left) (Term.instantiate body right) :=
  .transitive (.symmetric (.beta body left))
    (.transitive (.congruenceArgument _ equal) (.beta body right))

/-- A thunk whose fillings have the values `before ++ value :: after` is the instance, at
`value`, of the thunk whose fillings have index 0 in place of `value`. -/
theorem thunkTermInstance (code : Code) (holes : List Hole) (before after : List Term)
    (value : Term) :
    thunkTerm code holes (before ++ value :: after) =
      Term.instantiate
        (thunkTerm code holes (before.map Term.shift ++ .boundVariable 0 :: after.map Term.shift))
        value := by
  have variableReplaced : Term.substitute 0 value (.boundVariable 0) = value := by
    simp [Term.substitute]
  simp only [Term.instantiate, thunkTermSubstitute, List.map_append, List.map_cons,
    substituteShiftedList, variableReplaced]

/-- A congruence on one filling of a thunk: a beta expansion, an argument congruence and a beta
step (`derivableInstantiate`). -/
theorem thunkTermCongruence (code : Code) (holes : List Hole) (before after : List Term)
    {left right : Term} (equal : DerivableLatticeEta hypotheses left right) :
    DerivableLatticeEta hypotheses (thunkTerm code holes (before ++ left :: after))
      (thunkTerm code holes (before ++ right :: after)) := by
  rw [thunkTermInstance code holes before after left,
    thunkTermInstance code holes before after right]
  exact derivableInstantiate _ equal

/-- Every rule of ⊢^{defunctionalized}_{λ-lattice-η} is sound for the interpretation, under
any hypotheses. -/
theorem interpretationSound {left right : FiniteTerm} (equal : Equal left right) :
    DerivableLatticeEta hypotheses (interpretation left) (interpretation right) := by
  induction equal with
  | reflexive term => exact .reflexive _
  | symmetric _ inner => exact .symmetric inner
  | transitive _ _ leftInner rightInner => exact .transitive leftInner rightInner
  | congruenceThunk _ inner =>
      simp only [interpretation, interpretationListMap, List.map_append, List.map_cons]
      exact thunkTermCongruence _ _ _ _ inner
  | congruenceApply _ _ functionInner argumentInner =>
      simp only [interpretation]
      exact .transitive (.congruenceFunction _ functionInner)
        (.congruenceArgument _ argumentInner)
  | congruenceChoice _ _ leftInner rightInner =>
      simp only [interpretation]
      exact .transitive (.congruenceChoiceLeft _ leftInner) (.congruenceChoiceRight _ rightInner)
  | congruenceParallel _ _ leftInner rightInner =>
      simp only [interpretation]
      exact .transitive (.congruenceParallelLeft _ leftInner) (.congruenceParallelRight _ rightInner)
  | betaFill =>
      rw [(interpretationBetaFill _ _ _ _ _).1, (interpretationBetaFill _ _ _ _ _).2]
      exact .beta _ _
  | betaInstance instantiation =>
      rw [interpretationBetaInstance instantiation]
      exact .reflexive _
  | eta distinct found =>
      rw [interpretationEta distinct found]
      exact .eta _

/-- D3's item 4, the soundness direction: two finite terms equal in λ-lattice-η on
defunctionalized terms whose readbacks are defined have readbacks whose equation is derivable by
⊢_{λ-lattice-η}, under any hypotheses. -/
theorem readbackSound {left right : FiniteTerm} {leftTerm rightTerm : Term}
    (equal : Equal left right) (leftReadback : readback left = some leftTerm)
    (rightReadback : readback right = some rightTerm) :
    DerivableLatticeEta hypotheses leftTerm rightTerm := by
  rw [← interpretationOfReadback left leftTerm leftReadback,
    ← interpretationOfReadback right rightTerm rightReadback]
  exact interpretationSound equal

/-- The first clause of the defunctionalized β rule on terms that read back: the readbacks are a beta redex and its
contractum. -/
theorem readbackBetaFill {code : Code} {hole : Hole} {holes : List Hole}
    {fillings : List FiniteTerm} {argument : FiniteTerm} {leftTerm rightTerm : Term}
    (leftReadback :
      readback (.apply (.thunk code (hole :: holes) fillings) argument) = some leftTerm)
    (rightReadback : readback (.thunk code holes (fill hole holes fillings argument)) =
      some rightTerm) :
    ∃ body argumentTerm, leftTerm = .application (.abstraction body) argumentTerm ∧
      rightTerm = Term.instantiate body argumentTerm := by
  rw [← interpretationOfReadback _ _ leftReadback, ← interpretationOfReadback _ _ rightReadback]
  exact ⟨_, _, (interpretationBetaFill code hole holes fillings argument).1,
    (interpretationBetaFill code hole holes fillings argument).2⟩

/-- The second clause of the defunctionalized β rule on terms that read back: the readbacks are one term. -/
theorem readbackBetaInstance {code : Code} {fillings : List FiniteTerm}
    {instantiated : FiniteTerm} {leftTerm rightTerm : Term}
    (instantiation : code.instantiate fillings = some instantiated)
    (leftReadback : readback (.thunk code [] fillings) = some leftTerm)
    (rightReadback : readback instantiated = some rightTerm) :
    leftTerm = rightTerm := by
  rw [← interpretationOfReadback _ _ leftReadback, ← interpretationOfReadback _ _ rightReadback]
  exact interpretationBetaInstance instantiation

/-- The defunctionalized η rule on terms that read back: the readbacks are an eta redex λ. (shift F) 0 and F. -/
theorem readbackEta {function hole : Nat} {fillings : List FiniteTerm} {filling : FiniteTerm}
    {leftTerm rightTerm : Term} (distinct : function ≠ hole)
    (found : fillings[fillingPosition [.slot hole] function]? = some filling)
    (leftReadback :
      readback (.thunk (.apply (.slot function) (.slot hole)) [.slot hole] fillings) =
        some leftTerm)
    (rightReadback : readback filling = some rightTerm) :
    leftTerm = .abstraction (.application (Term.shift rightTerm) (.boundVariable 0)) := by
  rw [← interpretationOfReadback _ _ leftReadback, ← interpretationOfReadback _ _ rightReadback]
  exact interpretationEta distinct found

end LambdaJit.Readback
