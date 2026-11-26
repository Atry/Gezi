import LambdaJit.Readback

/-!
# The front end's defunctionalization of a source program

This module holds, in Lean, the front end's defunctionalization of design decision D1
(`lean/README.md`, "Design decisions"): `thunk_instruction/2` of
`gezi/prolog/gezi/defunctionalization.pl`, from a source program (`Program`: a closed
de Bruijn term over `variable/1`, `lambda/1`, `apply/2`, the binary choice, `parallel/2` and
`constant/1`) to a finite term of the IR (module `Ir`), every handle being the
finite term of its layer. It proves link (i) of D6 for this definition (`readbackThunkInstruction`)
and, from it, D3's item 3 and the converse of item 2 for the defunctionalization of a term of the
calculus, and gives the witness of item 5.

## The canonical numbering

The definitions follow the Prolog clause by clause, with the canonical numbering of D1: a chain of
abstractions `λx1 … λxk. B`, B no abstraction, is one thunk; its code is B with every binder, every
variable of the context outside the chain and every maximal closed subprogram replaced by a slot,
numbered from 0 in order of first occurrence in preorder, equal closed subprograms (`==/2` on the
source terms, `Program.equal` here) sharing one slot; its holes list, for x1 to xk in lambda
order, the slot of each binder or `ignored` when B does not read it; its fillings are the values
of the other slots, in slot order. A chain inside B that is not closed is a nested thunk of the code
whose fillings are slots of the enclosing code. A choice converts to a choice of its two sides'
conversions, as a parallel does.

| Prolog                    | Lean                   |
| ------------------------- | ---------------------- |
| `closed_under/2`          | `closedUnder`          |
| `chain/3`                 | `chainLength`, `chainBody`, and the chain mode of `bodyCode` |
| `body_thunk/5`            | `bodyCode`             |
| `member_thunk/5`          | `membersCode`          |
| `slot_of/4`               | `slotOf`               |
| `holes/3`                 | `holes`                |
| `inner_fillings/5`        | `innerFillings`        |
| `closed_fillings/2`       | `closedFillings`       |
| `converted/2`             | `converted`, `convertedList` |
| `thunk_instruction/2`     | `thunkInstruction`     |

A constant `constant(Handle)` converts in the Prolog to the bare Handle, the handle of the layer
the compiler made from the define's term by `thunk_instruction/2` (`define_address/5` of
`gezi/prolog/gezi/standard_library.pl`); the finite term of that handle is the finite
term of the define's term. Here a constant carries the define's source program, and converts to the
finite term of its definition (none when the definition is not closed). Two constants are one
closed subprogram when their definitions are one program; in the Prolog, when their handles are one
handle, which holds when the definitions are one term, since a handle is the hash_consing handle of
the definition's instruction (a test that writes Prolog programs in Lean names one definition per
handle).

The Prolog's walk of a chain, `chain/3` followed by `body_thunk/5` on the chain's body, is one
function here, `bodyCode`, whose flag `continuesChain` says that an abstraction met continues the
chain being stripped; this keeps every recursive call on a strict subprogram, so that the kernel
evaluates the definition (`rfl` and `decide` below). For the same reason a slot of a closed
subprogram carries the subprogram's conversion, computed where the slot is made from the
conversions of the subprogram's own subprograms (`applicationConversion` and its siblings, the
clauses of `converted/2`), and `closedFillings` reads the fillings off the slots. Where the Prolog
throws on a program that is not closed, `thunkInstruction` has no value.

A term of the calculus (module `Terms`) is the source program `Program.ofTerm` of it, which has no
constant; its defunctionalization `defunctionalize` is
`thunkInstruction` of that program, and δ of that program is the term (`deltaOfTerm`).

## What is proved

- Link (i) of D6 for `thunkInstruction` (`readbackThunkInstruction`): a closed program whose
  constants' definitions are closed (`definitionsClosed`) has a finite term, and its readback is
  δ of the program (`delta`: every constant replaced by δ of its definition), equal as de Bruijn
  terms. `thunkInstruction` has a value on no
  other program (`thunkInstructionDefined`), so `readbackOfThunkInstruction` states link (i) for
  every finite term `thunkInstruction` gives, with no hypothesis.
- D3's item 3 (`readbackDefunctionalize`): a closed term has a defunctionalization, and its
  readback is the term itself.
- The converse of D3's item 2 (`defunctionalizeInjective`). With de Bruijn indices, α-equivalent
  terms of the paper's named syntax are one term (module `Terms`, its formulation choices), so
  item 2, α-equivalent terms have one defunctionalization, holds by construction: `defunctionalize`
  is a function of the term. Its converse, which the canonical numbering is there to ensure, follows
  from item 3: two closed terms with one defunctionalization are one term. So, with one layer per
  address (D1), the root address of a defunctionalization determines the α-class of the term and
  conversely. The correspondence between named terms up to α-equivalence and de Bruijn terms is the
  standard adequacy of de Bruijn indices, which module `Semantics` takes and does not prove.
- `defunctionalizeDefined`: a term has a defunctionalization exactly when it is closed, as
  `thunk_instruction/2` accepts exactly the closed terms.
- D3's item 5 (`Witness.addressesFinerThanAlpha`): D3's example, the thunk of
  `λx1.λx2. x2 (x1 c)` applied to a closed `a`. The first clause of the defunctionalized β rule
  fills the hole and gives a thunk that is not the defunctionalization of its own readback
  `λx2. x2 (a c)`: the canonical numbering hoists the closed subterm `a c` into one slot, while the
  filled thunk keeps `a` and `c` in two. So two different finite terms, two addresses, read back
  to one term.

What is not proved is that the front end, `Defunctionalization.thunkInstruction` of the Scala
project `frontend`, computes `thunkInstruction` (the FIXME in the section on the agreement with the
Prolog below).
-/

namespace LambdaJit.Defunctionalization

open LambdaJit.Semantics
open LambdaJit.Readback

/-! ## Source programs -/

/-- A source program, the input of `thunk_instruction/2`: a de Bruijn term over `variable/1`,
`lambda/1`, `apply/2`, the binary choice, `parallel/2` and `constant/1`.
A constant is a reference to a library define and carries that define's source program, as the
handle of `constant(Handle)` names the layer the compiler made from the define's term
(`define_address/5` of `gezi/prolog/gezi/standard_library.pl`); the references between
defines form no cycle (`recursive_reference`), so a constant's definition is a finite tree. -/
inductive Program where
  /-- `variable(Index)`: an occurrence of a variable by its de Bruijn index. -/
  | boundVariable (index : Nat)
  /-- `lambda(Body)`. -/
  | abstraction (body : Program)
  /-- `apply(Function, Argument)`. -/
  | application (function argument : Program)
  /-- The binary choice of two programs. -/
  | choice (left right : Program)
  /-- `parallel(Left, Right)`. -/
  | parallel (left right : Program)
  /-- `constant(Handle)`: a reference to the define whose source program is `definition`. -/
  | constant (definition : Program)
  -- `Program.equal` below is the comparison, with its soundness theorem, as for `Code`.
  deriving Repr, Inhabited

namespace Program

/-- Structural equality of two programs, `==/2` of the Prolog on the source terms, as a Boolean
the kernel can evaluate. -/
def equal : Program → Program → Bool
  | .boundVariable index, .boundVariable otherIndex => index == otherIndex
  | .abstraction body, .abstraction otherBody => equal body otherBody
  | .application function argument, .application otherFunction otherArgument =>
      equal function otherFunction && equal argument otherArgument
  | .choice left right, .choice otherLeft otherRight =>
      equal left otherLeft && equal right otherRight
  | .parallel left right, .parallel otherLeft otherRight =>
      equal left otherLeft && equal right otherRight
  | .constant definition, .constant otherDefinition => equal definition otherDefinition
  | _, _ => false

theorem equality_of_equal : ∀ {left right : Program}, equal left right = true → left = right
  | .boundVariable index, right, holds => by
      cases right <;> simp_all [equal]
  | .abstraction body, right, holds => by
      cases right with
      | abstraction otherBody =>
          simp only [equal] at holds
          rw [equality_of_equal holds]
      | _ => simp [equal] at holds
  | .application function argument, right, holds => by
      cases right with
      | application otherFunction otherArgument =>
          simp only [equal, Bool.and_eq_true] at holds
          rw [equality_of_equal holds.1, equality_of_equal holds.2]
      | _ => simp [equal] at holds
  | .choice left right, other, holds => by
      cases other with
      | choice otherLeft otherRight =>
          simp only [equal, Bool.and_eq_true] at holds
          rw [equality_of_equal holds.1, equality_of_equal holds.2]
      | _ => simp [equal] at holds
  | .parallel left right, other, holds => by
      cases other with
      | parallel otherLeft otherRight =>
          simp only [equal, Bool.and_eq_true] at holds
          rw [equality_of_equal holds.1, equality_of_equal holds.2]
      | _ => simp [equal] at holds
  | .constant definition, right, holds => by
      cases right with
      | constant otherDefinition =>
          simp only [equal] at holds
          rw [equality_of_equal holds]
      | _ => simp [equal] at holds

theorem equal_self : ∀ program : Program, equal program program = true
  | .boundVariable _ => decide_eq_true rfl
  | .abstraction body => by simp only [equal, equal_self body]
  | .application function argument => by
      simp only [equal, equal_self function, equal_self argument, Bool.and_self]
  | .choice left right => by simp only [equal, equal_self left, equal_self right, Bool.and_self]
  | .parallel left right => by simp only [equal, equal_self left, equal_self right, Bool.and_self]
  | .constant definition => by simp only [equal, equal_self definition]

instance : DecidableEq Program := fun left right =>
  if holds : equal left right = true then isTrue (equality_of_equal holds)
  else isFalse (fun equalPrograms => holds (equalPrograms ▸ equal_self left))

/-- A term of the calculus as a source program. -/
def ofTerm : Term → Program
  | .boundVariable index => .boundVariable index
  | .abstraction body => .abstraction (ofTerm body)
  | .application function argument => .application (ofTerm function) (ofTerm argument)
  | .choice left right => .choice (ofTerm left) (ofTerm right)
  | .parallel left right => .parallel (ofTerm left) (ofTerm right)

end Program

/-- δ of link (i) of D6: the source program as a term of the calculus, every constant replaced by
δ of its define's source program. -/
def delta : Program → Term
  | .boundVariable index => .boundVariable index
  | .abstraction body => .abstraction (delta body)
  | .application function argument => .application (delta function) (delta argument)
  | .choice left right => .choice (delta left) (delta right)
  | .parallel left right => .parallel (delta left) (delta right)
  | .constant definition => delta definition

/-! ## The definitions -/

/-- `closedUnder depth program`: no variable of `program` is bound outside its `depth` enclosing
binders, `closed_under/2`; a constant is closed, whatever its definition. -/
def closedUnder : Nat → Program → Bool
  | depth, .boundVariable index => decide (index < depth)
  | depth, .abstraction body => closedUnder (depth + 1) body
  | depth, .application function argument =>
      closedUnder depth function && closedUnder depth argument
  | depth, .choice left right => closedUnder depth left && closedUnder depth right
  | depth, .parallel left right => closedUnder depth left && closedUnder depth right
  | _, .constant _ => true

/-- Every constant of a program has a closed definition, whose constants have closed definitions
in turn: the defines of the library are closed terms, which `thunk_instruction/2` checked when the
compiler made their layers. -/
def definitionsClosed : Program → Bool
  | .boundVariable _ => true
  | .abstraction body => definitionsClosed body
  | .application function argument => definitionsClosed function && definitionsClosed argument
  | .choice left right => definitionsClosed left && definitionsClosed right
  | .parallel left right => definitionsClosed left && definitionsClosed right
  | .constant definition => closedUnder 0 definition && definitionsClosed definition

/-- The number of abstractions at the root of a program, the Count of `chain/3`. -/
def chainLength : Program → Nat
  | .abstraction body => chainLength body + 1
  | _ => 0

/-- The program under the abstractions at the root of a program, the Body of `chain/3`. -/
def chainBody : Program → Program
  | .abstraction body => chainBody body
  | program => program

/-- What a slot of a chain's body reads, the entries of `body_thunk/5`'s slot list. -/
inductive Source where
  /-- The chain's variable of de Bruijn index `index` at the body, `bound(Index)`. -/
  | bound (index : Nat)
  /-- The variable of index `index` of the context outside the chain, `free(Index)`. -/
  | free (index : Nat)
  /-- A maximal closed subprogram, `closed(Term)`. -/
  | closed (program : Program)
  deriving DecidableEq, Repr

/-- A slot of a chain's body: its source and, for a closed subprogram, the subprogram's
conversion. -/
structure Slot where
  source : Source
  conversion : Option FiniteTerm

/-- The position of the first slot whose source is `source`. -/
def slotPosition (source : Source) : List Slot → Option Nat
  | [] => none
  | slot :: slots =>
      if slot.source = source then some 0 else (slotPosition source slots).map (· + 1)

/-- The slot of `source`, appended with `conversion` when new, `slot_of/4`. -/
def slotOf (source : Source) (conversion : Option FiniteTerm) (slots : List Slot) :
    Nat × List Slot :=
  match slotPosition source slots with
  | some index => (index, slots)
  | none => (slots.length, slots ++ [⟨source, conversion⟩])

/-- The source of the variable of index `index` at the body of a chain of `count` binders. -/
def variableSource (count index : Nat) : Source :=
  if index < count then .bound index else .free (index - count)

/-- The hole of the chain's variable of index `index` at the body, `hole/3`. -/
def holeOf (slots : List Slot) (index : Nat) : Hole :=
  match slotPosition (.bound index) slots with
  | some slot => .slot slot
  | none => .ignored

/-- The holes of a chain of `count` binders in lambda order, outermost first, the binder of
lambda position `p` being the variable of index `count - 1 - p` at the body, `holes/3`. -/
def holes (slots : List Slot) : Nat → List Hole
  | 0 => []
  | count + 1 => holeOf slots count :: holes slots count

/-- The fillings of an inner chain as slots of the enclosing body of `count` binders, appended to
`slots`, `inner_fillings/5`: a closed subprogram is a slot of the enclosing body too, and the inner
chain's outer variable `index` is the enclosing body's variable `index`. -/
def innerFillings (count : Nat) : List Slot → List Slot → List Code × List Slot
  | [], slots => ([], slots)
  | ⟨.bound _, _⟩ :: innerSlots, slots => innerFillings count innerSlots slots
  | ⟨.closed program, conversion⟩ :: innerSlots, slots =>
      let (index, slots) := slotOf (.closed program) conversion slots
      let (fillings, slots) := innerFillings count innerSlots slots
      (.slot index :: fillings, slots)
  | ⟨.free index, _⟩ :: innerSlots, slots =>
      let (slot, slots) := slotOf (variableSource count index) none slots
      let (fillings, slots) := innerFillings count innerSlots slots
      (.slot slot :: fillings, slots)

/-- The fillings of a chain outside any body, `closed_fillings/2`: the conversion of each closed
slot in slot order; none when a slot reads a variable outside the chain. -/
def closedFillings : List Slot → Option (List FiniteTerm)
  | [] => some []
  | ⟨.bound _, _⟩ :: slots => closedFillings slots
  | ⟨.closed _, conversion⟩ :: slots => do
      let filling ← conversion
      let fillings ← closedFillings slots
      pure (filling :: fillings)
  | ⟨.free _, _⟩ :: _ => none

/-- The thunk of a chain of `count` binders outside any body whose body has code `code` and slots
`slots`, the clause of `converted/2` for an abstraction. -/
def thunkConversion (count : Nat) (code : Code) (slots : List Slot) : Option FiniteTerm :=
  (closedFillings slots).map (.thunk code (holes slots count))

/-- The clause of `converted/2` for an application. -/
def applicationConversion (function argument : Option FiniteTerm) : Option FiniteTerm := do
  let functionTerm ← function
  let argumentTerm ← argument
  pure (.apply functionTerm argumentTerm)

/-- The clause of `converted/2` for a parallel. -/
def parallelConversion (left right : Option FiniteTerm) : Option FiniteTerm := do
  let leftTerm ← left
  let rightTerm ← right
  pure (.parallel leftTerm rightTerm)

/-- The clause of `converted/2` for a choice. -/
def choiceConversion (left right : Option FiniteTerm) : Option FiniteTerm := do
  let leftTerm ← left
  let rightTerm ← right
  pure (.choice leftTerm rightTerm)

/-- The slot of a closed subprogram, appended with its conversion when new. -/
def closedSlot (program : Program) (conversion : Option FiniteTerm) (slots : List Slot) :
    Code × List Slot :=
  let (index, slots) := slotOf (.closed program) conversion slots
  (.slot index, slots)

mutual
/-- `body_thunk/5`, with `chain/3` as its chain mode: the code of `program` at the body of a chain
of `count` binders, and the slots after `slots` have been extended by those it reads. When
`continuesChain` holds, an abstraction continues the chain: its binder is one more binder of the
chain, and the code is that of the chain's body. A constant is closed and is a slot, as the first
clause of `body_thunk/5` makes it; the slot's value is the conversion of its definition. -/
def bodyCode (count : Nat) (slots : List Slot) (continuesChain : Bool) :
    Program → Code × List Slot
  | .boundVariable index =>
      let (slot, slots) := slotOf (variableSource count index) none slots
      (.slot slot, slots)
  | .abstraction inner =>
      if continuesChain then bodyCode (count + 1) slots true inner
      else
        let (innerCode, innerSlots) := bodyCode 1 [] true inner
        if closedUnder 0 (.abstraction inner) then
          closedSlot (.abstraction inner)
            (thunkConversion (chainLength inner + 1) innerCode innerSlots) slots
        else
          let (fillings, slots) := innerFillings count innerSlots slots
          (.thunk innerCode (holes innerSlots (chainLength inner + 1)) fillings, slots)
  | .application function argument =>
      if closedUnder 0 (.application function argument) then
        closedSlot (.application function argument)
          (applicationConversion (converted function) (converted argument)) slots
      else
        let (functionCode, slots) := bodyCode count slots false function
        let (argumentCode, slots) := bodyCode count slots false argument
        (.apply functionCode argumentCode, slots)
  | .choice left right =>
      if closedUnder 0 (.choice left right) then
        closedSlot (.choice left right)
          (choiceConversion (converted left) (converted right)) slots
      else
        let (leftCode, slots) := bodyCode count slots false left
        let (rightCode, slots) := bodyCode count slots false right
        (.choice leftCode rightCode, slots)
  | .parallel left right =>
      if closedUnder 0 (.parallel left right) then
        closedSlot (.parallel left right)
          (parallelConversion (converted left) (converted right)) slots
      else
        let (leftCode, slots) := bodyCode count slots false left
        let (rightCode, slots) := bodyCode count slots false right
        (.parallel leftCode rightCode, slots)
  | .constant definition =>
      closedSlot (.constant definition)
        (if closedUnder 0 definition then converted definition else none) slots

/-- `converted/2`: the finite term of a closed program, every handle being the finite term of its
layer; none on a variable. A constant's finite term is that of its definition, the layer
`thunk_instruction/2` made of the define's term, and none when the definition is not closed. -/
def converted : Program → Option FiniteTerm
  | .boundVariable _ => none
  | .abstraction inner =>
      let (code, slots) := bodyCode 1 [] true inner
      thunkConversion (chainLength inner + 1) code slots
  | .application function argument =>
      applicationConversion (converted function) (converted argument)
  | .choice left right => choiceConversion (converted left) (converted right)
  | .parallel left right => parallelConversion (converted left) (converted right)
  | .constant definition => if closedUnder 0 definition then converted definition else none
end

/-- Whether a hole is `ignored`. -/
def ignoredHole : Hole → Bool
  | .ignored => true
  | .slot _ => false

/-- The thunk of code `code`, holes `holes` and fillings `fillings`, folded where it is the
conversion of a chain whose body is a constant naming a thunk with holes: `converted` makes
`λ_ … λ_. c`, c a constant, the thunk `thunk(slot 0, [ignored, …], [C])` with C the finite term of
c's definition, while the same program with c's definition written in place continues the chain.
When C is `thunk(code, inner, fillings)` with `inner` not empty, the folded thunk is
`thunk(code, [ignored, …] ++ inner, fillings)`, the conversion of the program written in place; any
other thunk is left as it is. -/
def foldedThunk : Code → List Hole → List FiniteTerm → FiniteTerm
  | .slot 0, outer@(_ :: _), [.thunk code inner@(_ :: _) fillings] =>
      if outer.all ignoredHole then .thunk code (outer ++ inner) fillings
      else .thunk (.slot 0) outer [.thunk code inner fillings]
  | code, holes, fillings => .thunk code holes fillings

mutual
/-- Every thunk of a finite term folded by `foldedThunk`, its fillings first. -/
def folded : FiniteTerm → FiniteTerm
  | .thunk code holes fillings => foldedThunk code holes (foldedList fillings)
  | .apply function argument => .apply (folded function) (folded argument)
  | .choice left right => .choice (folded left) (folded right)
  | .parallel left right => .parallel (folded left) (folded right)

/-- `folded` on each finite term of a list. -/
def foldedList : List FiniteTerm → List FiniteTerm
  | [] => []
  | term :: terms => folded term :: foldedList terms
end

/-- `thunk_instruction/2`, every handle being the finite term of its layer: the finite term of a
closed program, none when the program is not closed. A chain whose body is a constant naming a
thunk with holes is folded into that thunk (`folded`), so a name and the term it names give one
finite term in every context: a name and the literal term it names are one instruction. -/
def thunkInstruction (program : Program) : Option FiniteTerm :=
  if closedUnder 0 program then (converted program).map folded else none

/-- The defunctionalization of a closed term of the calculus: `thunkInstruction` of the term as a
source program, whose choices have two members or none and which has no constant. -/
def defunctionalize (term : Term) : Option FiniteTerm :=
  thunkInstruction (Program.ofTerm term)

/-! ## Closedness -/

/-- `termClosedUnder depth term`: no variable of the term of the calculus `term` is bound outside
its `depth` enclosing binders. -/
def termClosedUnder : Nat → Term → Bool
  | depth, .boundVariable index => decide (index < depth)
  | depth, .abstraction body => termClosedUnder (depth + 1) body
  | depth, .application function argument =>
      termClosedUnder depth function && termClosedUnder depth argument
  | depth, .choice left right => termClosedUnder depth left && termClosedUnder depth right
  | depth, .parallel left right => termClosedUnder depth left && termClosedUnder depth right


/-- `termClosedUnder depth` holds exactly when no index from `depth` up occurs free. -/
theorem termClosedUnderIff : ∀ (term : Term) (depth : Nat),
    termClosedUnder depth term = true ↔ ∀ index, depth ≤ index → ¬ Term.OccursFree index term
  | .boundVariable variableIndex, depth => by
      simp only [termClosedUnder, decide_eq_true_eq, Term.OccursFree]
      constructor
      · intro below index atLeast equal
        omega
      · intro absent
        by_cases below : variableIndex < depth
        · exact below
        · exact absurd rfl (absent variableIndex (by omega))
  | .abstraction body, depth => by
      simp only [termClosedUnder, Term.OccursFree]
      rw [termClosedUnderIff body (depth + 1)]
      constructor
      · intro absent index atLeast
        exact absent (index + 1) (by omega)
      · intro absent index atLeast
        have shifted := absent (index - 1) (by omega)
        have restored : index - 1 + 1 = index := by omega
        rw [restored] at shifted
        exact shifted
  | .application function argument, depth => by
      simp only [termClosedUnder, Bool.and_eq_true, Term.OccursFree, not_or]
      rw [termClosedUnderIff function depth, termClosedUnderIff argument depth]
      constructor
      · intro ⟨functionAbsent, argumentAbsent⟩ index atLeast
        exact ⟨functionAbsent index atLeast, argumentAbsent index atLeast⟩
      · intro absent
        exact ⟨fun index atLeast => (absent index atLeast).1,
          fun index atLeast => (absent index atLeast).2⟩
  | .choice left right, depth => by
      simp only [termClosedUnder, Bool.and_eq_true, Term.OccursFree, not_or]
      rw [termClosedUnderIff left depth, termClosedUnderIff right depth]
      constructor
      · intro ⟨leftAbsent, rightAbsent⟩ index atLeast
        exact ⟨leftAbsent index atLeast, rightAbsent index atLeast⟩
      · intro absent
        exact ⟨fun index atLeast => (absent index atLeast).1,
          fun index atLeast => (absent index atLeast).2⟩
  | .parallel left right, depth => by
      simp only [termClosedUnder, Bool.and_eq_true, Term.OccursFree, not_or]
      rw [termClosedUnderIff left depth, termClosedUnderIff right depth]
      constructor
      · intro ⟨leftAbsent, rightAbsent⟩ index atLeast
        exact ⟨leftAbsent index atLeast, rightAbsent index atLeast⟩
      · intro absent
        exact ⟨fun index atLeast => (absent index atLeast).1,
          fun index atLeast => (absent index atLeast).2⟩

/-- `termClosedUnder 0` is `Term.Closed`, FV(term) = ∅. -/
theorem termClosedUnderZeroIff (term : Term) :
    termClosedUnder 0 term = true ↔ Term.Closed term := by
  rw [termClosedUnderIff term 0]
  exact ⟨fun absent index => absent index (Nat.zero_le index),
    fun closed index _ => closed index⟩

/-- A term whose variables are all bound below `depth` is unchanged by a shift from any cutoff at
least `depth`. -/
theorem shiftFromClosedUnder : ∀ (term : Term) (depth cutoff : Nat), depth ≤ cutoff →
    termClosedUnder depth term = true → Term.shiftFrom cutoff term = term
  | .boundVariable index, depth, cutoff, ordered, closed => by
      simp only [termClosedUnder, decide_eq_true_eq] at closed
      have below : index < cutoff := by omega
      simp [Term.shiftFrom, below]
  | .abstraction body, depth, cutoff, ordered, closed => by
      simp only [termClosedUnder] at closed
      simp only [Term.shiftFrom,
        shiftFromClosedUnder body (depth + 1) (cutoff + 1) (by omega) closed]
  | .application function argument, depth, cutoff, ordered, closed => by
      simp only [termClosedUnder, Bool.and_eq_true] at closed
      simp only [Term.shiftFrom, shiftFromClosedUnder function depth cutoff ordered closed.1,
        shiftFromClosedUnder argument depth cutoff ordered closed.2]
  | .choice left right, depth, cutoff, ordered, closed => by
      simp only [termClosedUnder, Bool.and_eq_true] at closed
      simp only [Term.shiftFrom, shiftFromClosedUnder left depth cutoff ordered closed.1,
        shiftFromClosedUnder right depth cutoff ordered closed.2]
  | .parallel left right, depth, cutoff, ordered, closed => by
      simp only [termClosedUnder, Bool.and_eq_true] at closed
      simp only [Term.shiftFrom, shiftFromClosedUnder left depth cutoff ordered closed.1,
        shiftFromClosedUnder right depth cutoff ordered closed.2]

/-- A closed term is unchanged by being carried under any number of abstractions. -/
theorem shiftIterateClosed {term : Term} (closed : termClosedUnder 0 term = true) :
    ∀ count, shiftIterate count term = term
  | 0 => rfl
  | count + 1 => by
      have shifted : Term.shift term = term :=
        shiftFromClosedUnder term 0 0 (Nat.le_refl 0) closed
      simp only [shiftIterate, shifted, shiftIterateClosed closed count]

/-- A term closed under `depth` binders is closed under more. -/
theorem termClosedUnderMonotone {term : Term} {depth larger : Nat} (ordered : depth ≤ larger)
    (closed : termClosedUnder depth term = true) : termClosedUnder larger term = true := by
  rw [termClosedUnderIff] at closed ⊢
  exact fun index atLeast => closed index (Nat.le_trans ordered atLeast)

/-- δ of a program closed under `depth` binders, whose constants' definitions are closed, is closed
under `depth` binders. -/
theorem deltaClosedUnder : ∀ (program : Program) (depth : Nat),
    closedUnder depth program = true → definitionsClosed program = true →
      termClosedUnder depth (delta program) = true
  | .boundVariable _, _, closed, _ => by
      simpa [closedUnder, delta, termClosedUnder] using closed
  | .abstraction body, depth, closed, definitions => by
      simp only [closedUnder] at closed
      simp only [definitionsClosed] at definitions
      simp only [delta, termClosedUnder]
      exact deltaClosedUnder body (depth + 1) closed definitions
  | .application function argument, depth, closed, definitions => by
      simp only [closedUnder, Bool.and_eq_true] at closed
      simp only [definitionsClosed, Bool.and_eq_true] at definitions
      simp only [delta, termClosedUnder, Bool.and_eq_true]
      exact ⟨deltaClosedUnder function depth closed.1 definitions.1,
        deltaClosedUnder argument depth closed.2 definitions.2⟩
  | .choice left right, depth, closed, definitions => by
      simp only [closedUnder, Bool.and_eq_true] at closed
      simp only [definitionsClosed, Bool.and_eq_true] at definitions
      simp only [delta, termClosedUnder, Bool.and_eq_true]
      exact ⟨deltaClosedUnder left depth closed.1 definitions.1,
        deltaClosedUnder right depth closed.2 definitions.2⟩
  | .parallel left right, depth, closed, definitions => by
      simp only [closedUnder, Bool.and_eq_true] at closed
      simp only [definitionsClosed, Bool.and_eq_true] at definitions
      simp only [delta, termClosedUnder, Bool.and_eq_true]
      exact ⟨deltaClosedUnder left depth closed.1 definitions.1,
        deltaClosedUnder right depth closed.2 definitions.2⟩
  | .constant definition, depth, _, definitions => by
      simp only [definitionsClosed, Bool.and_eq_true] at definitions
      simp only [delta]
      exact termClosedUnderMonotone (Nat.zero_le depth)
        (deltaClosedUnder definition 0 definitions.1 definitions.2)

/-- A term as a source program has δ the term itself. -/
theorem deltaOfTerm : ∀ term : Term, delta (Program.ofTerm term) = term
  | .boundVariable _ => rfl
  | .abstraction body => by simp only [Program.ofTerm, delta, deltaOfTerm body]
  | .application function argument => by
      simp only [Program.ofTerm, delta, deltaOfTerm function, deltaOfTerm argument]
  | .choice left right => by
      simp only [Program.ofTerm, delta, deltaOfTerm left, deltaOfTerm right]
  | .parallel left right => by
      simp only [Program.ofTerm, delta, deltaOfTerm left, deltaOfTerm right]

/-- A term as a source program is closed where the term is. -/
theorem closedUnderOfTerm : ∀ (term : Term) (depth : Nat),
    closedUnder depth (Program.ofTerm term) = termClosedUnder depth term
  | .boundVariable _, _ => rfl
  | .abstraction body, depth => by
      simp only [Program.ofTerm, closedUnder, termClosedUnder, closedUnderOfTerm body (depth + 1)]
  | .application function argument, depth => by
      simp only [Program.ofTerm, closedUnder, termClosedUnder, closedUnderOfTerm function depth,
        closedUnderOfTerm argument depth]
  | .choice left right, depth => by
      simp only [Program.ofTerm, closedUnder, termClosedUnder,
        closedUnderOfTerm left depth, closedUnderOfTerm right depth]
  | .parallel left right, depth => by
      simp only [Program.ofTerm, closedUnder, termClosedUnder, closedUnderOfTerm left depth,
        closedUnderOfTerm right depth]

/-- A term as a source program has no constant. -/
theorem definitionsClosedOfTerm : ∀ term : Term, definitionsClosed (Program.ofTerm term) = true
  | .boundVariable _ => rfl
  | .abstraction body => by
      simp only [Program.ofTerm, definitionsClosed, definitionsClosedOfTerm body]
  | .application function argument => by
      simp only [Program.ofTerm, definitionsClosed, definitionsClosedOfTerm function,
        definitionsClosedOfTerm argument, Bool.and_self]
  | .choice left right => by
      simp only [Program.ofTerm, definitionsClosed,
        definitionsClosedOfTerm left, definitionsClosedOfTerm right, Bool.and_self]
  | .parallel left right => by
      simp only [Program.ofTerm, definitionsClosed, definitionsClosedOfTerm left,
        definitionsClosedOfTerm right, Bool.and_self]

/-! ## Chains -/

/-- δ of a program is δ of its chain's body under its chain's abstractions. -/
theorem abstractionsChain : ∀ program : Program,
    abstractions (chainLength program) (delta (chainBody program)) = delta program
  | .abstraction body => by
      simp only [chainLength, chainBody, abstractions, abstractionsChain body, delta]
  | .boundVariable _ => rfl
  | .application _ _ => rfl
  | .choice _ _ => rfl
  | .parallel _ _ => rfl
  | .constant _ => rfl

/-! ## Slot lists -/

/-- The value a slot's source reads at the body of a chain of `depth` binders. -/
def meaning (depth : Nat) : Source → Term
  | .bound index => .boundVariable index
  | .free index => .boundVariable (index + depth)
  | .closed program => delta program

/-- `values` holds, at the position of every slot of `slots`, the value the slot reads at the
body of a chain of `depth` binders. -/
def Extends (depth : Nat) (slots : List Slot) (values : List Term) : Prop :=
  ∀ (index : Nat) (slot : Slot), slots[index]? = some slot →
    values[index]? = some (meaning depth slot.source)

/-- A slot of the body of a chain of `depth` binders inside a context of `limit` variables: a
binder of the chain, a variable of the context, or a closed subprogram whose δ is closed, with its
conversion, whose readback is that δ. -/
def SlotValid (depth limit : Nat) (slot : Slot) : Prop :=
  match slot.source with
  | .bound index => index < depth
  | .free index => index < limit
  | .closed program => termClosedUnder 0 (delta program) = true ∧
      ∃ finiteTerm, slot.conversion = some finiteTerm ∧ readback finiteTerm = some (delta program)

/-- The slots of the body of a chain of `depth` binders inside a context of `limit` variables:
every slot is the first of its source, and every slot is valid. -/
structure Valid (depth limit : Nat) (slots : List Slot) : Prop where
  first : ∀ (index : Nat) (slot : Slot), slots[index]? = some slot →
    slotPosition slot.source slots = some index
  each : ∀ (index : Nat) (slot : Slot), slots[index]? = some slot → SlotValid depth limit slot

theorem slotPositionSome : ∀ {source : Source} {slots : List Slot} {index : Nat},
    slotPosition source slots = some index →
      ∃ slot, slots[index]? = some slot ∧ slot.source = source
  | _, [], _, found => by simp [slotPosition] at found
  | source, slot :: slots, index, found => by
      by_cases atHead : slot.source = source
      · simp only [slotPosition, atHead, if_true, Option.some.injEq] at found
        subst found
        exact ⟨slot, rfl, atHead⟩
      · simp only [slotPosition, atHead, if_false, Option.map_eq_some_iff] at found
        obtain ⟨position, inner, shifted⟩ := found
        subst shifted
        obtain ⟨found, entry, sameSource⟩ := slotPositionSome inner
        exact ⟨found, by simpa using entry, sameSource⟩

theorem slotPositionAppendSome : ∀ {source : Source} {slots more : List Slot} {index : Nat},
    slotPosition source slots = some index → slotPosition source (slots ++ more) = some index
  | _, [], _, _, found => by simp [slotPosition] at found
  | source, slot :: slots, more, index, found => by
      by_cases atHead : slot.source = source
      · simpa [slotPosition, atHead] using found
      · simp only [slotPosition, atHead, if_false, Option.map_eq_some_iff] at found
        obtain ⟨position, inner, shifted⟩ := found
        simp only [List.cons_append, slotPosition, atHead, if_false,
          slotPositionAppendSome inner, Option.map_some, shifted]

theorem slotPositionAppendNew : ∀ {source : Source} {slots : List Slot} {slot : Slot},
    slotPosition source slots = none → slot.source = source →
      slotPosition source (slots ++ [slot]) = some slots.length
  | _, [], _, _, sameSource => by simp [slotPosition, sameSource]
  | source, head :: slots, slot, absent, sameSource => by
      by_cases atHead : head.source = source
      · simp [slotPosition, atHead] at absent
      · simp only [slotPosition, atHead, if_false, Option.map_eq_none_iff] at absent
        simp only [List.cons_append, slotPosition, atHead, if_false,
          slotPositionAppendNew absent sameSource, Option.map_some, List.length_cons]

theorem getElemAppendOfSome {slots extra : List Slot} {index : Nat} {slot : Slot}
    (found : slots[index]? = some slot) : (slots ++ extra)[index]? = some slot := by
  obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp found
  rw [List.getElem?_append_left within, found]

theorem Valid.monotone {depth larger limit : Nat} {slots : List Slot}
    (valid : Valid depth limit slots) (ordered : depth ≤ larger) : Valid larger limit slots := by
  refine ⟨valid.first, fun index slot found => ?_⟩
  have slotValid := valid.each index slot found
  unfold SlotValid at slotValid ⊢
  cases source : slot.source with
  | bound bound => rw [source] at slotValid; simp only at slotValid ⊢; omega
  | free free => rw [source] at slotValid; exact slotValid
  | closed closed => rw [source] at slotValid; exact slotValid

theorem Valid.empty (depth limit : Nat) : Valid depth limit [] :=
  ⟨fun _ _ found => by simp at found, fun _ _ found => by simp at found⟩

theorem Valid.append {depth limit : Nat} {slots : List Slot} {slot : Slot}
    (valid : Valid depth limit slots) (absent : slotPosition slot.source slots = none)
    (slotValid : SlotValid depth limit slot) : Valid depth limit (slots ++ [slot]) := by
  constructor
  · intro index entry found
    rcases Nat.lt_or_ge index slots.length with within | beyond
    · rw [List.getElem?_append_left within] at found
      exact slotPositionAppendSome (valid.first index entry found)
    · rw [List.getElem?_append_right beyond] at found
      have atEnd : index = slots.length := by
        cases equal : index - slots.length with
        | zero => omega
        | succ _ => simp [equal] at found
      subst atEnd
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact slotPositionAppendNew absent rfl
  · intro index entry found
    rcases Nat.lt_or_ge index slots.length with within | beyond
    · rw [List.getElem?_append_left within] at found
      exact valid.each index entry found
    · rw [List.getElem?_append_right beyond] at found
      cases equal : index - slots.length with
      | zero =>
          simp only [equal, List.getElem?_cons_zero, Option.some.injEq] at found
          subst found
          exact slotValid
      | succ _ => simp [equal] at found

theorem Extends.prefix {depth : Nat} {slots extra : List Slot} {values : List Term}
    (valuesExtend : Extends depth (slots ++ extra) values) : Extends depth slots values :=
  fun index slot found => valuesExtend index slot (getElemAppendOfSome found)

/-- `slotOf` keeps the slots before it, keeps them valid, and returns a slot of the source. -/
theorem slotOfCorrect {depth limit : Nat} {source : Source} {conversion : Option FiniteTerm}
    {slots slotsAfter : List Slot} {index : Nat}
    (valid : Valid depth limit slots) (sourceValid : SlotValid depth limit ⟨source, conversion⟩)
    (result : slotOf source conversion slots = (index, slotsAfter)) :
    (∃ extra, slotsAfter = slots ++ extra) ∧ Valid depth limit slotsAfter ∧
      ∃ slot, slotsAfter[index]? = some slot ∧ slot.source = source := by
  unfold slotOf at result
  cases found : slotPosition source slots with
  | some position =>
      rw [found] at result
      simp only [Prod.mk.injEq] at result
      obtain ⟨equalIndex, equalSlots⟩ := result
      subst equalIndex
      subst equalSlots
      exact ⟨⟨[], by simp⟩, valid, slotPositionSome found⟩
  | none =>
      rw [found] at result
      simp only [Prod.mk.injEq] at result
      obtain ⟨equalIndex, equalSlots⟩ := result
      subst equalIndex
      subst equalSlots
      exact ⟨⟨_, rfl⟩, valid.append found sourceValid, ⟨⟨source, conversion⟩, by simp, rfl⟩⟩

/-- The slot `slotOf` returns reads its source's value. -/
theorem readSlotOf {depth : Nat} {slots : List Slot} {values : List Term} {index : Nat}
    {source : Source} (found : ∃ slot, slots[index]? = some slot ∧ slot.source = source)
    (valuesExtend : Extends depth slots values) :
    readbackCode values (.slot index) = some (meaning depth source) := by
  obtain ⟨slot, entry, sameSource⟩ := found
  simp only [readbackCode]
  rw [valuesExtend index slot entry, sameSource]

theorem meaningVariableSource (count index : Nat) :
    meaning count (variableSource count index) = .boundVariable index := by
  unfold variableSource
  by_cases below : index < count
  · simp [below, meaning]
  · simp only [below, if_false, meaning]
    congr 1
    omega

theorem variableSourceValid {count limit index : Nat} (below : index < count + limit)
    (conversion : Option FiniteTerm) :
    SlotValid count limit ⟨variableSource count index, conversion⟩ := by
  unfold SlotValid variableSource
  by_cases bound : index < count
  · simp only [bound, if_true]
  · simp only [bound, if_false]
    omega

/-! ## The holes of a chain -/

theorem slotPositionUnique {first second : Source} {slots : List Slot} {index : Nat}
    (firstFound : slotPosition first slots = some index)
    (secondFound : slotPosition second slots = some index) : first = second := by
  obtain ⟨firstSlot, firstEntry, firstSource⟩ := slotPositionSome firstFound
  obtain ⟨secondSlot, secondEntry, secondSource⟩ := slotPositionSome secondFound
  rw [firstEntry, Option.some.injEq] at secondEntry
  rw [← firstSource, ← secondSource, secondEntry]

theorem holeOfSlot {slots : List Slot} {index slot : Nat} :
    holeOf slots index = .slot slot ↔ slotPosition (.bound index) slots = some slot := by
  unfold holeOf
  cases slotPosition (.bound index) slots <;> simp

theorem holesLength (slots : List Slot) : ∀ count, (holes slots count).length = count
  | 0 => rfl
  | count + 1 => by simp [holes, holesLength slots count]

theorem memHoles (slots : List Slot) (slot : Nat) : ∀ count,
    Hole.slot slot ∈ holes slots count ↔
      ∃ index, index < count ∧ slotPosition (.bound index) slots = some slot
  | 0 => by simp [holes]
  | count + 1 => by
      simp only [holes, List.mem_cons, memHoles slots slot count]
      rw [eq_comm, holeOfSlot]
      constructor
      · rintro (atHead | ⟨index, below, found⟩)
        · exact ⟨count, by omega, atHead⟩
        · exact ⟨index, by omega, found⟩
      · rintro ⟨index, below, found⟩
        by_cases atHead : index = count
        · subst atHead
          exact Or.inl found
        · exact Or.inr ⟨index, by omega, found⟩

theorem holePositionHoles {slots : List Slot} {bound slot : Nat}
    (found : slotPosition (.bound bound) slots = some slot) :
    ∀ count, bound < count → holePosition (holes slots count) slot = some (count - 1 - bound)
  | 0, below => absurd below (Nat.not_lt_zero bound)
  | count + 1, below => by
      simp only [holes, holePosition]
      by_cases atHead : bound = count
      · subst atHead
        have head : holeOf slots bound = .slot slot := holeOfSlot.mpr found
        simp only [head, if_true]
        congr 1
        omega
      · have notHead : holeOf slots count ≠ .slot slot := by
          intro head
          have equal := slotPositionUnique (holeOfSlot.mp head) found
          injection equal with equalIndex
          exact atHead equalIndex.symm
        simp only [notHead, if_false, holePositionHoles found count (by omega), Option.map_some]
        congr 1
        omega

theorem distinctHoles (slots : List Slot) : ∀ count, DistinctSlots (holes slots count)
  | 0 => trivial
  | count + 1 => by
      refine ⟨fun slot head member => ?_, distinctHoles slots count⟩
      obtain ⟨index, below, found⟩ := (memHoles slots slot count).mp member
      have equal := slotPositionUnique (holeOfSlot.mp head) found
      injection equal with equalIndex
      omega

/-- On valid slots, a slot is a hole exactly when it reads a binder of the chain. -/
theorem memHolesValid {count limit : Nat} {slots : List Slot} (valid : Valid count limit slots)
    {index : Nat} {slot : Slot} (found : slots[index]? = some slot) :
    Hole.slot index ∈ holes slots count ↔ ∃ bound, slot.source = .bound bound := by
  rw [memHoles]
  constructor
  · rintro ⟨bound, _, position⟩
    obtain ⟨entry, entryFound, entrySource⟩ := slotPositionSome position
    rw [found, Option.some.injEq] at entryFound
    exact ⟨bound, entryFound ▸ entrySource⟩
  · rintro ⟨bound, source⟩
    have position := valid.first index slot found
    have slotValid := valid.each index slot found
    unfold SlotValid at slotValid
    rw [source] at position slotValid
    exact ⟨bound, slotValid, position⟩

theorem memHolesLength {count : Nat} {slots : List Slot} {index : Nat}
    (member : Hole.slot index ∈ holes slots count) : index < slots.length := by
  obtain ⟨_, _, position⟩ := (memHoles slots index count).mp member
  obtain ⟨_, entry, _⟩ := slotPositionSome position
  exact (List.getElem?_eq_some_iff.mp entry).1

/-! ## The fillings a chain's body reads -/

/-- The value a slot that is no hole of its chain takes from outside the chain: a variable of the
context is that variable, a closed subprogram is its δ. -/
def outerTerm : Source → Option Term
  | .bound _ => none
  | .free index => some (.boundVariable index)
  | .closed program => some (delta program)

/-- The values of the slots of a chain's body that are no holes, in slot order. -/
def outerTerms (slots : List Slot) : List Term :=
  slots.filterMap (fun slot => outerTerm slot.source)

theorem outerTermsAppend (slots more : List Slot) :
    outerTerms (slots ++ more) = outerTerms slots ++ outerTerms more := by
  simp [outerTerms, List.filterMap_append]

/-- The position of a filled slot among the filled slots is the number of slots before it that
are no holes. -/
theorem fillingPositionHoles {count limit : Nat} {slots : List Slot}
    (valid : Valid count limit slots) : ∀ index, index ≤ slots.length →
      fillingPosition (holes slots count) index = (outerTerms (slots.take index)).length
  | 0, _ => by simp [fillingPosition, outerTerms]
  | index + 1, within => by
      have found : slots[index]? = some slots[index] := List.getElem?_eq_getElem (by omega)
      rw [fillingPositionSuccessor, fillingPositionHoles valid index (by omega),
        List.take_add_one, found, outerTermsAppend, List.length_append]
      have member := memHolesValid valid found
      cases source : slots[index].source with
      | bound bound =>
          have isHole : Hole.slot index ∈ holes slots count := member.mpr ⟨bound, source⟩
          simp [isHole, outerTerms, outerTerm, source]
      | free free =>
          have notHole : Hole.slot index ∉ holes slots count := by
            rw [member]
            rintro ⟨_, sourceBound⟩
            rw [source] at sourceBound
            cases sourceBound
          simp [notHole, outerTerms, outerTerm, source]
      | closed closed =>
          have notHole : Hole.slot index ∉ holes slots count := by
            rw [member]
            rintro ⟨_, sourceBound⟩
            rw [source] at sourceBound
            cases sourceBound
          simp [notHole, outerTerms, outerTerm, source]

theorem outerTermsAt {slots : List Slot} {index : Nat} {slot : Slot} {term : Term}
    (found : slots[index]? = some slot) (outer : outerTerm slot.source = some term) :
    (outerTerms slots)[(outerTerms (slots.take index)).length]? = some term := by
  obtain ⟨within, entry⟩ := List.getElem?_eq_some_iff.mp found
  have split : slots = slots.take index ++ slot :: slots.drop (index + 1) := by
    conv => lhs; rw [← List.take_append_drop (index + 1) slots]
    rw [List.take_add_one, found]
    simp
  have decomposed : outerTerms slots =
      outerTerms (slots.take index) ++ term :: outerTerms (slots.drop (index + 1)) := by
    conv => lhs; rw [split]
    rw [outerTermsAppend]
    simp [outerTerms, outer]
  rw [decomposed, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem outerTermsTakeLength (slots : List Slot) (index : Nat) :
    (outerTerms (slots.take index)).length ≤ (outerTerms slots).length := by
  conv => rhs; rw [← List.take_append_drop index slots]
  rw [outerTermsAppend, List.length_append]
  omega

/-- The slot values under which `readback` reads the body of a chain whose fillings are its
slots' outer values extend the slots: each binder's slot holds its variable, and each other slot
its value, carried under the chain's binders. -/
theorem finalSlotsExtends {count limit : Nat} {slots : List Slot}
    (valid : Valid count limit slots) :
    Extends count slots (finalSlots (holes slots count) (outerTerms slots)) := by
  have noClamping : NoClamping (holes slots count) (outerTerms slots).length := by
    intro index member
    rw [fillingPositionHoles valid index (Nat.le_of_lt (memHolesLength member))]
    exact outerTermsTakeLength slots index
  intro index slot found
  rw [finalSlotsStatic _ _ (distinctHoles slots count) noClamping index]
  have slotValid := valid.each index slot found
  have member := memHolesValid valid found
  have within : index ≤ slots.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.mp found).1
  unfold staticSlot
  unfold SlotValid at slotValid
  cases source : slot.source with
  | bound bound =>
      rw [source] at slotValid
      have position := valid.first index slot found
      rw [source] at position
      rw [holePositionHoles position count slotValid, holesLength]
      simp only [meaning]
      congr 2
      omega
  | free free =>
      have notHole : Hole.slot index ∉ holes slots count := by
        rw [member]
        rintro ⟨_, sourceBound⟩
        rw [source] at sourceBound
        cases sourceBound
      have outer : outerTerm slot.source = some (.boundVariable free) := by
        rw [source]
        rfl
      rw [holePositionAbsent _ _ notHole, fillingPositionHoles valid index within,
        outerTermsAt found outer, holesLength]
      simp only [Option.map_some, shiftIterateBoundVariable, meaning]
  | closed closed =>
      rw [source] at slotValid
      have notHole : Hole.slot index ∉ holes slots count := by
        rw [member]
        rintro ⟨_, sourceBound⟩
        rw [source] at sourceBound
        cases sourceBound
      have outer : outerTerm slot.source = some (delta closed) := by
        rw [source]
        rfl
      rw [holePositionAbsent _ _ notHole, fillingPositionHoles valid index within,
        outerTermsAt found outer, holesLength]
      simp only [Option.map_some, shiftIterateClosed slotValid.1, meaning]

/-- The fillings of an inner chain, as slots of the enclosing body, keep the enclosing slots
before them, keep them valid, and read the inner chain's outer values. -/
theorem innerFillingsCorrect {count limit innerCount : Nat} : ∀ (innerSlots slots : List Slot)
    (fillings : List Code) (slotsAfter : List Slot),
    (∀ (index : Nat) (slot : Slot), innerSlots[index]? = some slot →
      SlotValid innerCount (count + limit) slot) →
    Valid count limit slots →
    innerFillings count innerSlots slots = (fillings, slotsAfter) →
    (∃ extra, slotsAfter = slots ++ extra) ∧ Valid count limit slotsAfter ∧
      ∀ values, Extends count slotsAfter values →
        readbackCodeList values fillings = some (outerTerms innerSlots)
  | [], slots, fillings, slotsAfter, _, valid, result => by
      simp only [innerFillings, Prod.mk.injEq] at result
      obtain ⟨equalFillings, equalSlots⟩ := result
      subst equalFillings
      subst equalSlots
      exact ⟨⟨[], by simp⟩, valid, fun _ _ => rfl⟩
  | ⟨.bound bound, conversion⟩ :: innerSlots, slots, fillings, slotsAfter, innerValid, valid,
      result => by
      simp only [innerFillings] at result
      have restValid : ∀ (index : Nat) (slot : Slot), innerSlots[index]? = some slot →
          SlotValid innerCount (count + limit) slot :=
        fun index slot found => innerValid (index + 1) slot (by simpa using found)
      have inner := innerFillingsCorrect innerSlots slots fillings slotsAfter restValid valid result
      simpa [outerTerms, outerTerm] using inner
  | ⟨.closed closed, conversion⟩ :: innerSlots, slots, fillings, slotsAfter, innerValid, valid,
      result => by
      have restValid : ∀ (index : Nat) (slot : Slot), innerSlots[index]? = some slot →
          SlotValid innerCount (count + limit) slot :=
        fun index slot found => innerValid (index + 1) slot (by simpa using found)
      have headValid := innerValid 0 ⟨.closed closed, conversion⟩ rfl
      simp only [innerFillings] at result
      cases slotResult : slotOf (.closed closed) conversion slots with
      | mk index slotsMiddle =>
      cases restResult : innerFillings count innerSlots slotsMiddle with
      | mk restFillings restSlots =>
      rw [slotResult, restResult] at result
      simp only [Prod.mk.injEq] at result
      obtain ⟨equalFillings, equalSlots⟩ := result
      subst equalFillings
      subst equalSlots
      have closedValid : SlotValid count limit ⟨.closed closed, conversion⟩ := headValid
      obtain ⟨⟨middleExtra, middlePrefix⟩, middleValid, middleFound⟩ :=
        slotOfCorrect valid closedValid slotResult
      obtain ⟨⟨restExtra, restPrefix⟩, restValidAfter, restReadback⟩ :=
        innerFillingsCorrect innerSlots slotsMiddle restFillings restSlots restValid middleValid
          restResult
      refine ⟨⟨middleExtra ++ restExtra, by rw [restPrefix, middlePrefix, List.append_assoc]⟩,
        restValidAfter, fun values valuesExtend => ?_⟩
      have middleExtends : Extends count slotsMiddle values := by
        rw [restPrefix] at valuesExtend
        exact valuesExtend.prefix
      simp only [readbackCodeList, readSlotOf middleFound middleExtends,
        restReadback values valuesExtend, bind, Option.bind, pure]
      simp [outerTerms, outerTerm, meaning]
  | ⟨.free free, conversion⟩ :: innerSlots, slots, fillings, slotsAfter, innerValid, valid,
      result => by
      have restValid : ∀ (index : Nat) (slot : Slot), innerSlots[index]? = some slot →
          SlotValid innerCount (count + limit) slot :=
        fun index slot found => innerValid (index + 1) slot (by simpa using found)
      have headValid := innerValid 0 ⟨.free free, conversion⟩ rfl
      simp only [SlotValid] at headValid
      simp only [innerFillings] at result
      cases slotResult : slotOf (variableSource count free) none slots with
      | mk index slotsMiddle =>
      cases restResult : innerFillings count innerSlots slotsMiddle with
      | mk restFillings restSlots =>
      rw [slotResult, restResult] at result
      simp only [Prod.mk.injEq] at result
      obtain ⟨equalFillings, equalSlots⟩ := result
      subst equalFillings
      subst equalSlots
      obtain ⟨⟨middleExtra, middlePrefix⟩, middleValid, middleFound⟩ :=
        slotOfCorrect valid (variableSourceValid headValid none) slotResult
      obtain ⟨⟨restExtra, restPrefix⟩, restValidAfter, restReadback⟩ :=
        innerFillingsCorrect innerSlots slotsMiddle restFillings restSlots restValid middleValid
          restResult
      refine ⟨⟨middleExtra ++ restExtra, by rw [restPrefix, middlePrefix, List.append_assoc]⟩,
        restValidAfter, fun values valuesExtend => ?_⟩
      have middleExtends : Extends count slotsMiddle values := by
        rw [restPrefix] at valuesExtend
        exact valuesExtend.prefix
      simp only [readbackCodeList, readSlotOf middleFound middleExtends, meaningVariableSource,
        restReadback values valuesExtend, bind, Option.bind, pure]
      simp [outerTerms, outerTerm]

/-- The fillings of a chain outside any body, every slot valid in an empty context, are the
conversions of its closed subprograms, which read back to their δ. -/
theorem closedFillingsCorrect {depth : Nat} : ∀ slots : List Slot,
    (∀ (index : Nat) (slot : Slot), slots[index]? = some slot → SlotValid depth 0 slot) →
      ∃ fillings, closedFillings slots = some fillings ∧
        readbackList fillings = some (outerTerms slots)
  | [], _ => ⟨[], rfl, rfl⟩
  | ⟨.bound bound, conversion⟩ :: slots, each => by
      obtain ⟨fillings, closedResult, readBack⟩ :=
        closedFillingsCorrect slots (fun index slot found => each (index + 1) slot (by simpa using found))
      exact ⟨fillings, closedResult, by simpa [outerTerms, outerTerm] using readBack⟩
  | ⟨.closed closed, conversion⟩ :: slots, each => by
      obtain ⟨fillings, closedResult, readBack⟩ :=
        closedFillingsCorrect slots (fun index slot found => each (index + 1) slot (by simpa using found))
      have headValid := each 0 ⟨.closed closed, conversion⟩ rfl
      simp only [SlotValid] at headValid
      obtain ⟨_, finiteTerm, conversionIs, finiteReadback⟩ := headValid
      subst conversionIs
      refine ⟨finiteTerm :: fillings, ?_, ?_⟩
      · simp [closedFillings, closedResult, bind, Option.bind, pure]
      · simp only [readbackList, finiteReadback, readBack, bind, Option.bind, pure]
        simp [outerTerms, outerTerm]
  | ⟨.free free, conversion⟩ :: slots, each => by
      have headValid := each 0 ⟨.free free, conversion⟩ rfl
      simp only [SlotValid] at headValid
      omega

/-- The thunk of a chain outside any body reads back to the chain's abstractions around the
readback of its body. -/
theorem thunkConversionCorrect {count : Nat} {code : Code} {slots : List Slot} {body : Term}
    (valid : Valid count 0 slots)
    (bodyReadback : ∀ values, Extends count slots values → readbackCode values code = some body) :
    ∃ finiteTerm, thunkConversion count code slots = some finiteTerm ∧
      readback finiteTerm = some (abstractions count body) := by
  obtain ⟨fillings, closedResult, fillingsReadback⟩ := closedFillingsCorrect slots valid.each
  refine ⟨.thunk code (holes slots count) fillings, ?_, ?_⟩
  · simp [thunkConversion, closedResult]
  · simp only [readback, fillingsReadback, bodyReadback _ (finalSlotsExtends valid), holesLength,
      bind, Option.bind, pure]

/-! ## The readback of the front end -/

/-- The depth of the body whose code `bodyCode` makes: in chain mode, the binders of the chain
are added. -/
def chainDepth (continuesChain : Bool) (count : Nat) (program : Program) : Nat :=
  if continuesChain then count + chainLength program else count

/-- The program whose code `bodyCode` makes: in chain mode, the chain's body. -/
def chainResult (continuesChain : Bool) (program : Program) : Program :=
  if continuesChain then chainBody program else program

/-- The slot of a closed subprogram whose conversion reads back to its δ reads that δ. -/
theorem closedSlotCorrect {count limit : Nat} {program : Program} {conversion : Option FiniteTerm}
    {slots slotsAfter : List Slot} {code : Code} (valid : Valid count limit slots)
    (closed : termClosedUnder 0 (delta program) = true)
    (converts : ∃ finiteTerm, conversion = some finiteTerm ∧
      readback finiteTerm = some (delta program))
    (result : closedSlot program conversion slots = (code, slotsAfter)) :
    (∃ extra, slotsAfter = slots ++ extra) ∧ Valid count limit slotsAfter ∧
      ∀ values, Extends count slotsAfter values →
        readbackCode values code = some (delta program) := by
  unfold closedSlot at result
  cases slotResult : slotOf (.closed program) conversion slots with
  | mk index slotsMiddle =>
  rw [slotResult] at result
  simp only [Prod.mk.injEq] at result
  obtain ⟨equalCode, equalSlots⟩ := result
  subst equalCode
  subst equalSlots
  have slotValid : SlotValid count limit ⟨.closed program, conversion⟩ := ⟨closed, converts⟩
  obtain ⟨keepsPrefix, validAfter, found⟩ := slotOfCorrect valid slotValid slotResult
  exact ⟨keepsPrefix, validAfter, fun values valuesExtend => readSlotOf found valuesExtend⟩

theorem chainDepthOfNotAbstraction {program : Program} (continuesChain : Bool) (count : Nat)
    (notAbstraction : chainLength program = 0) :
    chainDepth continuesChain count program = count := by
  cases continuesChain <;> simp [chainDepth, notAbstraction]

theorem chainResultOfNotAbstraction {program : Program} (continuesChain : Bool)
    (notAbstraction : chainBody program = program) :
    chainResult continuesChain program = program := by
  cases continuesChain <;> simp [chainResult, notAbstraction]

mutual
/-- Link (i) for the front end of this module, by induction on the program: a closed program whose
constants' definitions are closed converts to a finite term that reads back to its δ, and the code
`bodyCode` makes for any program whose variables lie in the chain or the context reads back, under
any values that extend the slots, to its δ (or, in chain mode, to δ of the chain's body). -/
theorem bodyCodeCorrect : ∀ program : Program,
    (closedUnder 0 program = true → definitionsClosed program = true →
      ∃ finiteTerm, converted program = some finiteTerm ∧
        readback finiteTerm = some (delta program)) ∧
    ∀ (count limit : Nat) (slots : List Slot) (continuesChain : Bool) (code : Code)
      (slotsAfter : List Slot),
      Valid count limit slots → closedUnder (count + limit) program = true →
      definitionsClosed program = true →
      bodyCode count slots continuesChain program = (code, slotsAfter) →
      (∃ extra, slotsAfter = slots ++ extra) ∧
      Valid (chainDepth continuesChain count program) limit slotsAfter ∧
      ∀ values, Extends (chainDepth continuesChain count program) slotsAfter values →
        readbackCode values code = some (delta (chainResult continuesChain program))
  | .boundVariable index => by
      refine ⟨fun closed => by simp [closedUnder] at closed, ?_⟩
      intro count limit slots continuesChain code slotsAfter valid closed _ result
      rw [chainDepthOfNotAbstraction continuesChain count rfl,
        chainResultOfNotAbstraction continuesChain rfl]
      simp only [closedUnder, decide_eq_true_eq] at closed
      simp only [bodyCode] at result
      cases slotResult : slotOf (variableSource count index) none slots with
      | mk slot slotsMiddle =>
      rw [slotResult] at result
      simp only [Prod.mk.injEq] at result
      obtain ⟨equalCode, equalSlots⟩ := result
      subst equalCode
      subst equalSlots
      obtain ⟨keepsPrefix, validAfter, found⟩ :=
        slotOfCorrect valid (variableSourceValid closed none) slotResult
      exact ⟨keepsPrefix, validAfter, fun values valuesExtend => by
        rw [readSlotOf found valuesExtend, meaningVariableSource]; rfl⟩
  | .abstraction inner => by
      have innerBody := (bodyCodeCorrect inner).2
      have abstractionConverts : ∀ (code : Code) (slots : List Slot),
          bodyCode 1 [] true inner = (code, slots) →
          closedUnder 0 (.abstraction inner) = true →
          definitionsClosed (.abstraction inner) = true →
          ∃ finiteTerm, thunkConversion (chainLength inner + 1) code slots = some finiteTerm ∧
            readback finiteTerm = some (delta (.abstraction inner)) := by
        intro code slots chainCode closed definitions
        obtain ⟨_, chainValid, chainReadback⟩ :=
          innerBody 1 0 [] true code slots (Valid.empty 1 0) closed definitions chainCode
        have depthIs : chainDepth true 1 inner = chainLength inner + 1 := by
          simp only [chainDepth, if_true]
          omega
        rw [depthIs] at chainValid chainReadback
        obtain ⟨finiteTerm, conversion, readBack⟩ :=
          thunkConversionCorrect chainValid chainReadback
        refine ⟨finiteTerm, conversion, ?_⟩
        rw [readBack]
        have chain := abstractionsChain (.abstraction inner)
        simp only [chainLength, chainBody] at chain
        simp only [chainResult, if_true, chain]
      refine ⟨fun closed definitions => ?_, ?_⟩
      · cases chainCode : bodyCode 1 [] true inner with
        | mk code slots =>
        simp only [converted, chainCode]
        exact abstractionConverts code slots chainCode closed definitions
      intro count limit slots continuesChain code slotsAfter valid closed definitions result
      cases continuesChain with
      | true =>
          simp only [bodyCode, if_true] at result
          have closedInner : closedUnder (count + 1 + limit) inner = true := by
            have reordered : count + 1 + limit = count + limit + 1 := by omega
            rw [reordered]
            exact closed
          have depthEqual : chainDepth true count (.abstraction inner) =
              chainDepth true (count + 1) inner := by
            simp only [chainDepth, if_true, chainLength]
            omega
          have resultEqual : chainResult true (.abstraction inner) = chainResult true inner := by
            simp only [chainResult, if_true, chainBody]
          rw [depthEqual, resultEqual]
          exact innerBody (count + 1) limit slots true code slotsAfter
            (valid.monotone (by omega)) closedInner definitions result
      | false =>
          simp only [bodyCode, Bool.false_eq_true, if_false] at result
          cases chainCode : bodyCode 1 [] true inner with
          | mk innerCode innerSlots =>
          rw [chainCode] at result
          have depthIs : chainDepth false count (.abstraction inner) = count := rfl
          rw [depthIs]
          cases closedAbstraction : closedUnder 0 (.abstraction inner) with
          | true =>
              simp only [closedAbstraction, if_true] at result
              exact closedSlotCorrect valid
                (deltaClosedUnder _ 0 closedAbstraction definitions)
                (abstractionConverts innerCode innerSlots chainCode closedAbstraction definitions)
                result
          | false =>
              simp only [closedAbstraction, Bool.false_eq_true, if_false] at result
              cases fillingsResult : innerFillings count innerSlots slots with
              | mk fillings slotsMiddle =>
              rw [fillingsResult] at result
              simp only [Prod.mk.injEq] at result
              obtain ⟨equalCode, equalSlots⟩ := result
              subst equalCode
              subst equalSlots
              have closedInner : closedUnder (1 + (count + limit)) inner = true := by
                have reordered : 1 + (count + limit) = count + limit + 1 := by omega
                rw [reordered]
                exact closed
              obtain ⟨_, innerValid, innerReadback⟩ :=
                innerBody 1 (count + limit) [] true innerCode innerSlots
                  (Valid.empty 1 (count + limit)) closedInner definitions chainCode
              have innerDepthIs : chainDepth true 1 inner = chainLength inner + 1 := by
                simp only [chainDepth, if_true]
                omega
              rw [innerDepthIs] at innerValid innerReadback
              obtain ⟨keepsPrefix, validAfter, fillingsReadback⟩ :=
                innerFillingsCorrect innerSlots slots fillings slotsMiddle innerValid.each valid
                  fillingsResult
              refine ⟨keepsPrefix, validAfter, fun values valuesExtend => ?_⟩
              have chain := abstractionsChain (.abstraction inner)
              simp only [chainLength, chainBody] at chain
              simp only [readbackCode, fillingsReadback values valuesExtend,
                innerReadback _ (finalSlotsExtends innerValid), holesLength, bind, Option.bind,
                pure, chainResult, Bool.false_eq_true, if_false, if_true, chain]
  | .application function argument => by
      have applicationConverts : closedUnder 0 (.application function argument) = true →
          definitionsClosed (.application function argument) = true →
          ∃ finiteTerm, applicationConversion (converted function) (converted argument) =
            some finiteTerm ∧
              readback finiteTerm = some (delta (.application function argument)) := by
        intro closed definitions
        simp only [closedUnder, Bool.and_eq_true] at closed
        simp only [definitionsClosed, Bool.and_eq_true] at definitions
        obtain ⟨functionTerm, functionConverted, functionReadback⟩ :=
          (bodyCodeCorrect function).1 closed.1 definitions.1
        obtain ⟨argumentTerm, argumentConverted, argumentReadback⟩ :=
          (bodyCodeCorrect argument).1 closed.2 definitions.2
        refine ⟨.apply functionTerm argumentTerm, ?_, ?_⟩
        · simp [applicationConversion, functionConverted, argumentConverted]
        · simp [readback, functionReadback, argumentReadback, delta]
      refine ⟨fun closed definitions => by
        simpa [converted] using applicationConverts closed definitions, ?_⟩
      intro count limit slots continuesChain code slotsAfter valid closed definitions result
      rw [chainDepthOfNotAbstraction continuesChain count rfl,
        chainResultOfNotAbstraction continuesChain rfl]
      simp only [bodyCode] at result
      cases closedApplication : closedUnder 0 (.application function argument) with
      | true =>
          simp only [closedApplication, if_true] at result
          exact closedSlotCorrect valid (deltaClosedUnder _ 0 closedApplication definitions)
            (applicationConverts closedApplication definitions) result
      | false =>
          simp only [closedApplication, Bool.false_eq_true, if_false] at result
          simp only [closedUnder, Bool.and_eq_true] at closed
          simp only [definitionsClosed, Bool.and_eq_true] at definitions
          cases functionResult : bodyCode count slots false function with
          | mk functionCode slotsMiddle =>
          cases argumentResult : bodyCode count slotsMiddle false argument with
          | mk argumentCode slotsLast =>
          rw [functionResult, argumentResult] at result
          simp only [Prod.mk.injEq] at result
          obtain ⟨equalCode, equalSlots⟩ := result
          subst equalCode
          subst equalSlots
          obtain ⟨⟨middleExtra, middlePrefix⟩, middleValid, functionReadback⟩ :=
            (bodyCodeCorrect function).2 count limit slots false functionCode slotsMiddle valid
              closed.1 definitions.1 functionResult
          obtain ⟨⟨lastExtra, lastPrefix⟩, lastValid, argumentReadback⟩ :=
            (bodyCodeCorrect argument).2 count limit slotsMiddle false argumentCode slotsLast
              middleValid closed.2 definitions.2 argumentResult
          refine ⟨⟨middleExtra ++ lastExtra, by rw [lastPrefix, middlePrefix, List.append_assoc]⟩,
            lastValid, fun values valuesExtend => ?_⟩
          have middleExtends : Extends count slotsMiddle values := by
            rw [lastPrefix] at valuesExtend
            exact valuesExtend.prefix
          simp only [readbackCode, functionReadback values middleExtends,
            argumentReadback values valuesExtend, bind, Option.bind, pure, chainResult,
            Bool.false_eq_true, if_false, delta]
  | .choice left right => by
      have choiceConverts : closedUnder 0 (.choice left right) = true →
          definitionsClosed (.choice left right) = true →
          ∃ finiteTerm, choiceConversion (converted left) (converted right) =
            some finiteTerm ∧ readback finiteTerm = some (delta (.choice left right)) := by
        intro closed definitions
        simp only [closedUnder, Bool.and_eq_true] at closed
        simp only [definitionsClosed, Bool.and_eq_true] at definitions
        obtain ⟨leftTerm, leftConverted, leftReadback⟩ :=
          (bodyCodeCorrect left).1 closed.1 definitions.1
        obtain ⟨rightTerm, rightConverted, rightReadback⟩ :=
          (bodyCodeCorrect right).1 closed.2 definitions.2
        refine ⟨.choice leftTerm rightTerm, ?_, ?_⟩
        · simp [choiceConversion, leftConverted, rightConverted]
        · simp [readback, leftReadback, rightReadback, delta]
      refine ⟨fun closed definitions => by
        simpa [converted] using choiceConverts closed definitions, ?_⟩
      intro count limit slots continuesChain code slotsAfter valid closed definitions result
      rw [chainDepthOfNotAbstraction continuesChain count rfl,
        chainResultOfNotAbstraction continuesChain rfl]
      simp only [bodyCode] at result
      cases closedChoice : closedUnder 0 (.choice left right) with
      | true =>
          simp only [closedChoice, if_true] at result
          exact closedSlotCorrect valid (deltaClosedUnder _ 0 closedChoice definitions)
            (choiceConverts closedChoice definitions) result
      | false =>
          simp only [closedChoice, Bool.false_eq_true, if_false] at result
          simp only [closedUnder, Bool.and_eq_true] at closed
          simp only [definitionsClosed, Bool.and_eq_true] at definitions
          cases leftResult : bodyCode count slots false left with
          | mk leftCode slotsMiddle =>
          cases rightResult : bodyCode count slotsMiddle false right with
          | mk rightCode slotsLast =>
          rw [leftResult, rightResult] at result
          simp only [Prod.mk.injEq] at result
          obtain ⟨equalCode, equalSlots⟩ := result
          subst equalCode
          subst equalSlots
          obtain ⟨⟨middleExtra, middlePrefix⟩, middleValid, leftReadback⟩ :=
            (bodyCodeCorrect left).2 count limit slots false leftCode slotsMiddle valid closed.1
              definitions.1 leftResult
          obtain ⟨⟨lastExtra, lastPrefix⟩, lastValid, rightReadback⟩ :=
            (bodyCodeCorrect right).2 count limit slotsMiddle false rightCode slotsLast middleValid
              closed.2 definitions.2 rightResult
          refine ⟨⟨middleExtra ++ lastExtra, by rw [lastPrefix, middlePrefix, List.append_assoc]⟩,
            lastValid, fun values valuesExtend => ?_⟩
          have middleExtends : Extends count slotsMiddle values := by
            rw [lastPrefix] at valuesExtend
            exact valuesExtend.prefix
          simp only [readbackCode, leftReadback values middleExtends,
            rightReadback values valuesExtend, bind, Option.bind, pure, chainResult,
            Bool.false_eq_true, if_false, delta]
  | .parallel left right => by
      have parallelConverts : closedUnder 0 (.parallel left right) = true →
          definitionsClosed (.parallel left right) = true →
          ∃ finiteTerm, parallelConversion (converted left) (converted right) =
            some finiteTerm ∧ readback finiteTerm = some (delta (.parallel left right)) := by
        intro closed definitions
        simp only [closedUnder, Bool.and_eq_true] at closed
        simp only [definitionsClosed, Bool.and_eq_true] at definitions
        obtain ⟨leftTerm, leftConverted, leftReadback⟩ :=
          (bodyCodeCorrect left).1 closed.1 definitions.1
        obtain ⟨rightTerm, rightConverted, rightReadback⟩ :=
          (bodyCodeCorrect right).1 closed.2 definitions.2
        refine ⟨.parallel leftTerm rightTerm, ?_, ?_⟩
        · simp [parallelConversion, leftConverted, rightConverted]
        · simp [readback, leftReadback, rightReadback, delta]
      refine ⟨fun closed definitions => by
        simpa [converted] using parallelConverts closed definitions, ?_⟩
      intro count limit slots continuesChain code slotsAfter valid closed definitions result
      rw [chainDepthOfNotAbstraction continuesChain count rfl,
        chainResultOfNotAbstraction continuesChain rfl]
      simp only [bodyCode] at result
      cases closedParallel : closedUnder 0 (.parallel left right) with
      | true =>
          simp only [closedParallel, if_true] at result
          exact closedSlotCorrect valid (deltaClosedUnder _ 0 closedParallel definitions)
            (parallelConverts closedParallel definitions) result
      | false =>
          simp only [closedParallel, Bool.false_eq_true, if_false] at result
          simp only [closedUnder, Bool.and_eq_true] at closed
          simp only [definitionsClosed, Bool.and_eq_true] at definitions
          cases leftResult : bodyCode count slots false left with
          | mk leftCode slotsMiddle =>
          cases rightResult : bodyCode count slotsMiddle false right with
          | mk rightCode slotsLast =>
          rw [leftResult, rightResult] at result
          simp only [Prod.mk.injEq] at result
          obtain ⟨equalCode, equalSlots⟩ := result
          subst equalCode
          subst equalSlots
          obtain ⟨⟨middleExtra, middlePrefix⟩, middleValid, leftReadback⟩ :=
            (bodyCodeCorrect left).2 count limit slots false leftCode slotsMiddle valid closed.1
              definitions.1 leftResult
          obtain ⟨⟨lastExtra, lastPrefix⟩, lastValid, rightReadback⟩ :=
            (bodyCodeCorrect right).2 count limit slotsMiddle false rightCode slotsLast middleValid
              closed.2 definitions.2 rightResult
          refine ⟨⟨middleExtra ++ lastExtra, by rw [lastPrefix, middlePrefix, List.append_assoc]⟩,
            lastValid, fun values valuesExtend => ?_⟩
          have middleExtends : Extends count slotsMiddle values := by
            rw [lastPrefix] at valuesExtend
            exact valuesExtend.prefix
          simp only [readbackCode, leftReadback values middleExtends,
            rightReadback values valuesExtend, bind, Option.bind, pure, chainResult,
            Bool.false_eq_true, if_false, delta]
  | .constant definition => by
      have constantConverts : definitionsClosed (.constant definition) = true →
          ∃ finiteTerm, (if closedUnder 0 definition then converted definition else none) =
            some finiteTerm ∧ readback finiteTerm = some (delta (.constant definition)) := by
        intro definitions
        simp only [definitionsClosed, Bool.and_eq_true] at definitions
        obtain ⟨finiteTerm, definitionConverted, definitionReadback⟩ :=
          (bodyCodeCorrect definition).1 definitions.1 definitions.2
        exact ⟨finiteTerm, by simp [definitions.1, definitionConverted], definitionReadback⟩
      refine ⟨fun _ definitions => by simpa [converted] using constantConverts definitions, ?_⟩
      intro count limit slots continuesChain code slotsAfter valid _ definitions result
      rw [chainDepthOfNotAbstraction continuesChain count rfl,
        chainResultOfNotAbstraction continuesChain rfl]
      simp only [bodyCode] at result
      exact closedSlotCorrect valid (deltaClosedUnder _ 0 rfl definitions)
        (constantConverts definitions) result

end

/-! ## The fold does not change the readback -/

/-- `count + more` abstractions are `count` abstractions around `more`. -/
theorem abstractionsAdd (body : Term) : ∀ count more : Nat,
    abstractions (count + more) body = abstractions count (abstractions more body)
  | 0, more => by simp [abstractions]
  | count + 1, more => by
      rw [Nat.succ_add]
      simp only [abstractions, abstractionsAdd body count more]

/-- A body closed under `depth + count` binders is closed under `depth` once `count` abstractions
bind it. -/
theorem termClosedUnderAbstractions (body : Term) : ∀ (count depth : Nat),
    termClosedUnder (depth + count) body = true →
      termClosedUnder depth (abstractions count body) = true
  | 0, depth, closed => closed
  | count + 1, depth, closed => by
      simp only [abstractions, termClosedUnder]
      exact termClosedUnderAbstractions body count (depth + 1) (by
        rw [show depth + 1 + count = depth + (count + 1) by omega]
        exact closed)

/-- A shift from any cutoff carries a term closed under `depth` binders to one closed under one
more. -/
theorem termClosedUnderShiftFrom : ∀ (term : Term) (depth cutoff : Nat),
    termClosedUnder depth term = true → termClosedUnder (depth + 1) (Term.shiftFrom cutoff term) = true
  | .boundVariable index, depth, cutoff, closed => by
      simp only [termClosedUnder, decide_eq_true_eq] at closed
      by_cases below : index < cutoff
      · simp only [Term.shiftFrom, below, if_true, termClosedUnder, decide_eq_true_eq]
        omega
      · simp only [Term.shiftFrom, below, if_false, termClosedUnder, decide_eq_true_eq]
        omega
  | .abstraction body, depth, cutoff, closed => by
      simp only [termClosedUnder] at closed
      simp only [Term.shiftFrom, termClosedUnder]
      exact termClosedUnderShiftFrom body (depth + 1) (cutoff + 1) closed
  | .application function argument, depth, cutoff, closed => by
      simp only [termClosedUnder, Bool.and_eq_true] at closed
      simp only [Term.shiftFrom, termClosedUnder, Bool.and_eq_true]
      exact ⟨termClosedUnderShiftFrom function depth cutoff closed.1,
        termClosedUnderShiftFrom argument depth cutoff closed.2⟩
  | .choice left right, depth, cutoff, closed => by
      simp only [termClosedUnder, Bool.and_eq_true] at closed
      simp only [Term.shiftFrom, termClosedUnder, Bool.and_eq_true]
      exact ⟨termClosedUnderShiftFrom left depth cutoff closed.1,
        termClosedUnderShiftFrom right depth cutoff closed.2⟩
  | .parallel left right, depth, cutoff, closed => by
      simp only [termClosedUnder, Bool.and_eq_true] at closed
      simp only [Term.shiftFrom, termClosedUnder, Bool.and_eq_true]
      exact ⟨termClosedUnderShiftFrom left depth cutoff closed.1,
        termClosedUnderShiftFrom right depth cutoff closed.2⟩

/-- An element of the fillings after a hole is filled is one of the fillings or the argument. -/
theorem memFill {α : Type} {hole : Hole} {holes : List Hole} {fillings : List α} {argument value : α}
    (member : value ∈ fill hole holes fillings argument) : value ∈ fillings ∨ value = argument := by
  cases hole with
  | ignored => exact Or.inl member
  | slot index =>
      simp only [fill, List.mem_append, List.mem_cons] at member
      rcases member with taken | equal | dropped
      · exact Or.inl (List.mem_of_mem_take taken)
      · exact Or.inr equal
      · exact Or.inl (List.mem_of_mem_drop dropped)

/-- The slot values under a thunk's lambda chain are closed under its binders when the fillings
are closed under `depth`. -/
theorem finalSlotsClosed : ∀ (holes : List Hole) (depth : Nat) (slots : List Term),
    (∀ slot, slot ∈ slots → termClosedUnder depth slot = true) →
      ∀ slot, slot ∈ finalSlots holes slots → termClosedUnder (depth + holes.length) slot = true
  | [], depth, slots, closed => by simpa [finalSlots] using closed
  | hole :: holes, depth, slots, closed => by
      intro slot member
      simp only [finalSlots] at member
      have filled : ∀ value, value ∈ fill hole holes (slots.map Term.shift) (.boundVariable 0) →
          termClosedUnder (depth + 1) value = true := by
        intro value valueMember
        rcases memFill valueMember with shifted | boundVariable
        · obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp shifted
          rw [← equal]
          exact termClosedUnderShiftFrom original depth 0 (closed original originalMember)
        · rw [boundVariable]
          simp [termClosedUnder]
      have result := finalSlotsClosed holes (depth + 1) _ filled slot member
      rw [show depth + (hole :: holes).length = depth + 1 + holes.length by
        simp only [List.length_cons]; omega]
      exact result

mutual
/-- The readback of a code whose slot values are closed under `depth` is closed under `depth`. -/
theorem readbackCodeClosed : ∀ (code : Code) (depth : Nat) (slots : List Term) (term : Term),
    (∀ slot, slot ∈ slots → termClosedUnder depth slot = true) →
      readbackCode slots code = some term → termClosedUnder depth term = true
  | .slot index, depth, slots, term, closed, readBack => by
      simp only [readbackCode] at readBack
      exact closed term (List.mem_of_getElem? readBack)
  | .apply function argument, depth, slots, term, closed, readBack => by
      simp only [readbackCode, bind, Option.bind] at readBack
      cases functionReadback : readbackCode slots function with
      | none => simp [functionReadback] at readBack
      | some functionTerm =>
          cases argumentReadback : readbackCode slots argument with
          | none => simp [functionReadback, argumentReadback] at readBack
          | some argumentTerm =>
              simp only [functionReadback, argumentReadback, pure, Option.some.injEq] at readBack
              rw [← readBack]
              simp only [termClosedUnder, Bool.and_eq_true]
              exact ⟨readbackCodeClosed function depth slots functionTerm closed functionReadback,
                readbackCodeClosed argument depth slots argumentTerm closed argumentReadback⟩
  | .thunk code holes fillings, depth, slots, term, closed, readBack => by
      simp only [readbackCode, bind, Option.bind] at readBack
      cases fillingsReadback : readbackCodeList slots fillings with
      | none => simp [fillingsReadback] at readBack
      | some fillingTerms =>
          cases bodyReadback : readbackCode (finalSlots holes fillingTerms) code with
          | none => simp [fillingsReadback, bodyReadback] at readBack
          | some body =>
              simp only [fillingsReadback, bodyReadback, pure, Option.some.injEq] at readBack
              rw [← readBack]
              have fillingsClosed :=
                readbackCodeListClosed fillings depth slots fillingTerms closed fillingsReadback
              exact termClosedUnderAbstractions body holes.length depth
                (readbackCodeClosed code (depth + holes.length) _ body
                  (finalSlotsClosed holes depth fillingTerms fillingsClosed) bodyReadback)
  | .choice left right, depth, slots, term, closed, readBack => by
      simp only [readbackCode, bind, Option.bind] at readBack
      cases leftReadback : readbackCode slots left with
      | none => simp [leftReadback] at readBack
      | some leftTerm =>
          cases rightReadback : readbackCode slots right with
          | none => simp [leftReadback, rightReadback] at readBack
          | some rightTerm =>
              simp only [leftReadback, rightReadback, pure, Option.some.injEq] at readBack
              rw [← readBack]
              simp only [termClosedUnder, Bool.and_eq_true]
              exact ⟨readbackCodeClosed left depth slots leftTerm closed leftReadback,
                readbackCodeClosed right depth slots rightTerm closed rightReadback⟩
  | .parallel left right, depth, slots, term, closed, readBack => by
      simp only [readbackCode, bind, Option.bind] at readBack
      cases leftReadback : readbackCode slots left with
      | none => simp [leftReadback] at readBack
      | some leftTerm =>
          cases rightReadback : readbackCode slots right with
          | none => simp [leftReadback, rightReadback] at readBack
          | some rightTerm =>
              simp only [leftReadback, rightReadback, pure, Option.some.injEq] at readBack
              rw [← readBack]
              simp only [termClosedUnder, Bool.and_eq_true]
              exact ⟨readbackCodeClosed left depth slots leftTerm closed leftReadback,
                readbackCodeClosed right depth slots rightTerm closed rightReadback⟩

/-- `readbackCodeClosed` on each code of a list. -/
theorem readbackCodeListClosed : ∀ (codes : List Code) (depth : Nat) (slots : List Term)
    (terms : List Term),
    (∀ slot, slot ∈ slots → termClosedUnder depth slot = true) →
      readbackCodeList slots codes = some terms →
        ∀ term, term ∈ terms → termClosedUnder depth term = true
  | [], depth, slots, terms, _, readBack => by
      simp only [readbackCodeList, Option.some.injEq] at readBack
      rw [← readBack]
      simp
  | code :: codes, depth, slots, terms, closed, readBack => by
      simp only [readbackCodeList, bind, Option.bind] at readBack
      cases headReadback : readbackCode slots code with
      | none => simp [headReadback] at readBack
      | some headTerm =>
          cases tailReadback : readbackCodeList slots codes with
          | none => simp [headReadback, tailReadback] at readBack
          | some tailTerms =>
              simp only [headReadback, tailReadback, pure, Option.some.injEq] at readBack
              rw [← readBack]
              intro term member
              rcases List.mem_cons.mp member with equal | rest
              · rw [equal]
                exact readbackCodeClosed code depth slots headTerm closed headReadback
              · exact readbackCodeListClosed codes depth slots tailTerms closed tailReadback term rest
end

mutual
/-- A finite term's readback, where it has one, is closed. -/
theorem readbackClosed : ∀ (finiteTerm : FiniteTerm) (term : Term),
    readback finiteTerm = some term → termClosedUnder 0 term = true
  | .thunk code holes fillings, term, readBack => by
      simp only [readback, bind, Option.bind] at readBack
      cases fillingsReadback : readbackList fillings with
      | none => simp [fillingsReadback] at readBack
      | some fillingTerms =>
          cases bodyReadback : readbackCode (finalSlots holes fillingTerms) code with
          | none => simp [fillingsReadback, bodyReadback] at readBack
          | some body =>
              simp only [fillingsReadback, bodyReadback, pure, Option.some.injEq] at readBack
              rw [← readBack]
              have fillingsClosed := readbackListClosed fillings fillingTerms fillingsReadback
              exact termClosedUnderAbstractions body holes.length 0
                (readbackCodeClosed code (0 + holes.length) _ body
                  (finalSlotsClosed holes 0 fillingTerms fillingsClosed) bodyReadback)
  | .apply function argument, term, readBack => by
      simp only [readback, bind, Option.bind] at readBack
      cases functionReadback : readback function with
      | none => simp [functionReadback] at readBack
      | some functionTerm =>
          cases argumentReadback : readback argument with
          | none => simp [functionReadback, argumentReadback] at readBack
          | some argumentTerm =>
              simp only [functionReadback, argumentReadback, pure, Option.some.injEq] at readBack
              rw [← readBack]
              simp only [termClosedUnder, Bool.and_eq_true]
              exact ⟨readbackClosed function functionTerm functionReadback,
                readbackClosed argument argumentTerm argumentReadback⟩
  | .choice left right, term, readBack => by
      simp only [readback, bind, Option.bind] at readBack
      cases leftReadback : readback left with
      | none => simp [leftReadback] at readBack
      | some leftTerm =>
          cases rightReadback : readback right with
          | none => simp [leftReadback, rightReadback] at readBack
          | some rightTerm =>
              simp only [leftReadback, rightReadback, pure, Option.some.injEq] at readBack
              rw [← readBack]
              simp only [termClosedUnder, Bool.and_eq_true]
              exact ⟨readbackClosed left leftTerm leftReadback,
                readbackClosed right rightTerm rightReadback⟩
  | .parallel left right, term, readBack => by
      simp only [readback, bind, Option.bind] at readBack
      cases leftReadback : readback left with
      | none => simp [leftReadback] at readBack
      | some leftTerm =>
          cases rightReadback : readback right with
          | none => simp [leftReadback, rightReadback] at readBack
          | some rightTerm =>
              simp only [leftReadback, rightReadback, pure, Option.some.injEq] at readBack
              rw [← readBack]
              simp only [termClosedUnder, Bool.and_eq_true]
              exact ⟨readbackClosed left leftTerm leftReadback,
                readbackClosed right rightTerm rightReadback⟩

/-- `readbackClosed` on each finite term of a list. -/
theorem readbackListClosed : ∀ (finiteTerms : List FiniteTerm) (terms : List Term),
    readbackList finiteTerms = some terms → ∀ term, term ∈ terms → termClosedUnder 0 term = true
  | [], terms, readBack => by
      simp only [readbackList, Option.some.injEq] at readBack
      rw [← readBack]
      simp
  | finiteTerm :: finiteTerms, terms, readBack => by
      simp only [readbackList, bind, Option.bind] at readBack
      cases headReadback : readback finiteTerm with
      | none => simp [headReadback] at readBack
      | some headTerm =>
          cases tailReadback : readbackList finiteTerms with
          | none => simp [headReadback, tailReadback] at readBack
          | some tailTerms =>
              simp only [headReadback, tailReadback, pure, Option.some.injEq] at readBack
              rw [← readBack]
              intro term member
              rcases List.mem_cons.mp member with equal | rest
              · rw [equal]
                exact readbackClosed finiteTerm headTerm headReadback
              · exact readbackListClosed finiteTerms tailTerms tailReadback term rest
end

/-- Ignored holes in front of a thunk's holes leave closed slot values as they are: each only
carries the values under its lambda, and a closed value is unchanged by a shift. -/
theorem finalSlotsIgnoredClosed : ∀ (outer holes : List Hole) (slots : List Term),
    outer.all ignoredHole = true → (∀ slot, slot ∈ slots → termClosedUnder 0 slot = true) →
      finalSlots (outer ++ holes) slots = finalSlots holes slots
  | [], holes, slots, _, _ => rfl
  | .slot _ :: _, _, _, allIgnored, _ => by simp [ignoredHole] at allIgnored
  | .ignored :: outer, holes, slots, allIgnored, closed => by
      simp only [List.all_cons, ignoredHole, Bool.true_and] at allIgnored
      have unshifted : slots.map Term.shift = slots := by
        conv => rhs; rw [← List.map_id slots]
        exact List.map_congr_left (fun slot member =>
          shiftFromClosedUnder slot 0 0 (Nat.le_refl 0) (closed slot member))
      simp only [List.cons_append, finalSlots, fill, unshifted]
      exact finalSlotsIgnoredClosed outer holes slots allIgnored closed

/-- The fold of a thunk has the thunk's readback. -/
theorem foldedThunkReadback (code : Code) (holes : List Hole) (fillings : List FiniteTerm) :
    readback (foldedThunk code holes fillings) = readback (.thunk code holes fillings) := by
  unfold foldedThunk
  split
  · rename_i outerHead outerTail innerCode innerHead innerTail innerFillings
    split
    · rename_i allIgnored
      simp only [readback, readbackList, bind, Option.bind]
      cases fillingsReadback : readbackList innerFillings with
      | none => simp
      | some fillingTerms =>
          have fillingsClosed := readbackListClosed innerFillings fillingTerms fillingsReadback
          dsimp only
          rw [finalSlotsIgnoredClosed _ _ fillingTerms allIgnored fillingsClosed]
          cases bodyReadback :
              readbackCode (finalSlots (innerHead :: innerTail) fillingTerms) innerCode with
          | none => simp
          | some body =>
              have innerClosed : termClosedUnder 0
                  (abstractions (innerHead :: innerTail).length body) = true :=
                readbackClosed (.thunk innerCode (innerHead :: innerTail) innerFillings) _ (by
                  simp [readback, fillingsReadback, bodyReadback, bind, Option.bind, pure])
              have slotsClosed : ∀ slot,
                  slot ∈ [abstractions (innerHead :: innerTail).length body] →
                    termClosedUnder 0 slot = true := by
                intro slot member
                rw [List.mem_singleton.mp member]
                exact innerClosed
              have outerSlots := finalSlotsIgnoredClosed (outerHead :: outerTail) []
                [abstractions (innerHead :: innerTail).length body] allIgnored slotsClosed
              rw [List.append_nil] at outerSlots
              simp only [pure, readbackCode]
              rw [outerSlots]
              simp only [finalSlots, List.getElem?_cons_zero, List.length_append, abstractionsAdd]
    · rfl
  · rfl

mutual
/-- `folded` keeps the readback of every finite term. -/
theorem foldedReadback : ∀ finiteTerm : FiniteTerm, readback (folded finiteTerm) = readback finiteTerm
  | .thunk code holes fillings => by
      simp only [folded, foldedThunkReadback]
      simp only [readback, foldedListReadback fillings]
  | .apply function argument => by
      simp only [folded, readback, foldedReadback function, foldedReadback argument]
  | .choice left right => by
      simp only [folded, readback, foldedReadback left, foldedReadback right]
  | .parallel left right => by
      simp only [folded, readback, foldedReadback left, foldedReadback right]

/-- `foldedReadback` on each finite term of a list. -/
theorem foldedListReadback : ∀ finiteTerms : List FiniteTerm,
    readbackList (foldedList finiteTerms) = readbackList finiteTerms
  | [] => rfl
  | finiteTerm :: finiteTerms => by
      simp only [foldedList, readbackList, foldedReadback finiteTerm, foldedListReadback finiteTerms]
end

/-- Link (i) of D6 for the front end of this module: a closed program whose constants' definitions
are closed has a finite term, and its readback is the program's δ, equal as de Bruijn terms. -/
theorem readbackThunkInstruction {program : Program} (closed : closedUnder 0 program = true)
    (definitions : definitionsClosed program = true) :
    ∃ finiteTerm, thunkInstruction program = some finiteTerm ∧
      readback finiteTerm = some (delta program) := by
  unfold thunkInstruction
  rw [if_pos closed]
  obtain ⟨finiteTerm, converts, readBack⟩ := (bodyCodeCorrect program).1 closed definitions
  exact ⟨folded finiteTerm, by rw [converts]; rfl, by rw [foldedReadback]; exact readBack⟩

/-! ## Where the front end is defined

The front end has a value only on closed programs whose constants' definitions are closed
(`thunkInstructionDefined`), as the Prolog's defines are: every closed subprogram is a slot whose
value is its conversion, every slot of an inner chain becomes a slot of the enclosing body, and the
fillings of the outermost chain are all those conversions, so a constant whose definition is not
closed, which has no conversion, leaves the whole program without one. So link (i) holds of every
finite term the front end gives (`readbackOfThunkInstruction`). -/

/-- Every closed slot holds the conversion of its subprogram, as `bodyCode` makes the slots. -/
def Canonical (slots : List Slot) : Prop :=
  ∀ (index : Nat) (slot : Slot) (program : Program), slots[index]? = some slot →
    slot.source = .closed program → slot.conversion = converted program

/-- `program` is the subprogram of a closed slot of `slots`. -/
def Present (slots : List Slot) (program : Program) : Prop :=
  ∃ (index : Nat) (slot : Slot), slots[index]? = some slot ∧ slot.source = .closed program

/-- The subprogram of every closed slot has a conversion. -/
def ConversionsDefined (slots : List Slot) : Prop :=
  ∀ program, Present slots program → (converted program).isSome = true

theorem Present.append {slots : List Slot} {program : Program} (extra : List Slot)
    (present : Present slots program) : Present (slots ++ extra) program := by
  obtain ⟨index, slot, found, isClosed⟩ := present
  exact ⟨index, slot, getElemAppendOfSome found, isClosed⟩

theorem Present.cons {head : Slot} {slots : List Slot} {program : Program}
    (present : Present (head :: slots) program) :
    head.source = .closed program ∨ Present slots program := by
  obtain ⟨index, slot, found, isClosed⟩ := present
  cases index with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact Or.inl isClosed
  | succ index => exact Or.inr ⟨index, slot, by simpa using found, isClosed⟩

theorem Canonical.tail {head : Slot} {slots : List Slot} (canonical : Canonical (head :: slots)) :
    Canonical slots :=
  fun index slot program found isClosed => canonical (index + 1) slot program (by simpa using found)
    isClosed

theorem ConversionsDefined.prefix {slots extra : List Slot}
    (defined : ConversionsDefined (slots ++ extra)) : ConversionsDefined slots :=
  fun program present => defined program (present.append extra)

theorem variableSourceNotClosed (count index : Nat) (program : Program) :
    variableSource count index ≠ .closed program := by
  unfold variableSource
  by_cases below : index < count <;> simp [below]

/-- `slotOf` keeps the slots before it and their canonical conversions, and returns a slot of the
source. -/
theorem slotOfCanonical {source : Source} {conversion : Option FiniteTerm}
    {slots slotsAfter : List Slot} {index : Nat} (canonical : Canonical slots)
    (canonicalConversion : ∀ program, source = .closed program → conversion = converted program)
    (result : slotOf source conversion slots = (index, slotsAfter)) :
    (∃ extra, slotsAfter = slots ++ extra) ∧ Canonical slotsAfter ∧
      ∃ slot, slotsAfter[index]? = some slot ∧ slot.source = source := by
  unfold slotOf at result
  cases found : slotPosition source slots with
  | some position =>
      rw [found] at result
      simp only [Prod.mk.injEq] at result
      obtain ⟨equalIndex, equalSlots⟩ := result
      subst equalIndex
      subst equalSlots
      exact ⟨⟨[], by simp⟩, canonical, slotPositionSome found⟩
  | none =>
      rw [found] at result
      simp only [Prod.mk.injEq] at result
      obtain ⟨equalIndex, equalSlots⟩ := result
      subst equalIndex
      subst equalSlots
      refine ⟨⟨_, rfl⟩, fun entryIndex entry program entryFound isClosed => ?_,
        ⟨⟨source, conversion⟩, by simp, rfl⟩⟩
      rcases Nat.lt_or_ge entryIndex slots.length with within | beyond
      · rw [List.getElem?_append_left within] at entryFound
        exact canonical entryIndex entry program entryFound isClosed
      · rw [List.getElem?_append_right beyond] at entryFound
        cases equal : entryIndex - slots.length with
        | zero =>
            simp only [equal, List.getElem?_cons_zero, Option.some.injEq] at entryFound
            subst entryFound
            exact canonicalConversion program isClosed
        | succ _ => simp [equal] at entryFound

/-- The slot of a closed subprogram whose conversion is its canonical one. -/
theorem closedSlotCanonical {program : Program} {slots slotsAfter : List Slot} {code : Code}
    (canonical : Canonical slots)
    (result : closedSlot program (converted program) slots = (code, slotsAfter)) :
    (∃ extra, slotsAfter = slots ++ extra) ∧ Canonical slotsAfter ∧ Present slotsAfter program := by
  unfold closedSlot at result
  cases slotResult : slotOf (.closed program) (converted program) slots with
  | mk index slotsMiddle =>
  rw [slotResult] at result
  simp only [Prod.mk.injEq] at result
  obtain ⟨_, equalSlots⟩ := result
  subst equalSlots
  obtain ⟨keepsPrefix, canonicalAfter, slot, found, isClosed⟩ :=
    slotOfCanonical canonical (fun other isClosed => by cases isClosed; rfl) slotResult
  exact ⟨keepsPrefix, canonicalAfter, index, slot, found, isClosed⟩

/-- The fillings of an inner chain keep the enclosing slots canonical, and every closed slot of the
inner chain is a closed slot of the enclosing body. -/
theorem innerFillingsPresent {count : Nat} : ∀ (innerSlots slots : List Slot)
    (fillings : List Code) (slotsAfter : List Slot),
    Canonical innerSlots → Canonical slots →
    innerFillings count innerSlots slots = (fillings, slotsAfter) →
    (∃ extra, slotsAfter = slots ++ extra) ∧ Canonical slotsAfter ∧
      ∀ program, Present innerSlots program → Present slotsAfter program
  | [], slots, fillings, slotsAfter, _, canonical, result => by
      simp only [innerFillings, Prod.mk.injEq] at result
      obtain ⟨_, equalSlots⟩ := result
      subst equalSlots
      refine ⟨⟨[], by simp⟩, canonical, fun program present => ?_⟩
      obtain ⟨_, _, found, _⟩ := present
      simp at found
  | ⟨.bound bound, conversion⟩ :: innerSlots, slots, fillings, slotsAfter, innerCanonical,
      canonical, result => by
      simp only [innerFillings] at result
      obtain ⟨keepsPrefix, canonicalAfter, presentAfter⟩ :=
        innerFillingsPresent innerSlots slots fillings slotsAfter innerCanonical.tail canonical
          result
      refine ⟨keepsPrefix, canonicalAfter, fun program present => ?_⟩
      rcases present.cons with isClosed | inRest
      · cases isClosed
      · exact presentAfter program inRest
  | ⟨.closed closed, conversion⟩ :: innerSlots, slots, fillings, slotsAfter, innerCanonical,
      canonical, result => by
      simp only [innerFillings] at result
      cases slotResult : slotOf (.closed closed) conversion slots with
      | mk index slotsMiddle =>
      cases restResult : innerFillings count innerSlots slotsMiddle with
      | mk restFillings restSlots =>
      rw [slotResult, restResult] at result
      simp only [Prod.mk.injEq] at result
      obtain ⟨_, equalSlots⟩ := result
      subst equalSlots
      have headConversion : conversion = converted closed :=
        innerCanonical 0 ⟨.closed closed, conversion⟩ closed rfl rfl
      obtain ⟨⟨middleExtra, middlePrefix⟩, middleCanonical, slot, slotFound, slotSource⟩ :=
        slotOfCanonical canonical
          (fun other isClosed => by cases isClosed; exact headConversion) slotResult
      obtain ⟨⟨restExtra, restPrefix⟩, restCanonical, presentAfter⟩ :=
        innerFillingsPresent innerSlots slotsMiddle restFillings restSlots innerCanonical.tail
          middleCanonical restResult
      refine ⟨⟨middleExtra ++ restExtra, by rw [restPrefix, middlePrefix, List.append_assoc]⟩,
        restCanonical, fun program present => ?_⟩
      rcases present.cons with isClosed | inRest
      · cases isClosed
        rw [restPrefix]
        exact Present.append restExtra ⟨index, slot, slotFound, slotSource⟩
      · exact presentAfter program inRest
  | ⟨.free free, conversion⟩ :: innerSlots, slots, fillings, slotsAfter, innerCanonical,
      canonical, result => by
      simp only [innerFillings] at result
      cases slotResult : slotOf (variableSource count free) none slots with
      | mk index slotsMiddle =>
      cases restResult : innerFillings count innerSlots slotsMiddle with
      | mk restFillings restSlots =>
      rw [slotResult, restResult] at result
      simp only [Prod.mk.injEq] at result
      obtain ⟨_, equalSlots⟩ := result
      subst equalSlots
      obtain ⟨⟨middleExtra, middlePrefix⟩, middleCanonical, _⟩ :=
        slotOfCanonical canonical
          (fun other isClosed => absurd isClosed (variableSourceNotClosed count free other))
          slotResult
      obtain ⟨⟨restExtra, restPrefix⟩, restCanonical, presentAfter⟩ :=
        innerFillingsPresent innerSlots slotsMiddle restFillings restSlots innerCanonical.tail
          middleCanonical restResult
      refine ⟨⟨middleExtra ++ restExtra, by rw [restPrefix, middlePrefix, List.append_assoc]⟩,
        restCanonical, fun program present => ?_⟩
      rcases present.cons with isClosed | inRest
      · cases isClosed
      · exact presentAfter program inRest

theorem convertedAbstraction {inner : Program} {code : Code} {slots : List Slot}
    (chainCode : bodyCode 1 [] true inner = (code, slots)) :
    converted (.abstraction inner) = thunkConversion (chainLength inner + 1) code slots := by
  simp only [converted, chainCode]

mutual
/-- `bodyCode` keeps the slots before it and makes canonical slots. -/
theorem bodyCodeCanonical : ∀ (program : Program) (count : Nat) (slots : List Slot)
    (continuesChain : Bool) (code : Code) (slotsAfter : List Slot),
    Canonical slots → bodyCode count slots continuesChain program = (code, slotsAfter) →
    (∃ extra, slotsAfter = slots ++ extra) ∧ Canonical slotsAfter
  | .boundVariable index, count, slots, continuesChain, code, slotsAfter, canonical, result => by
      simp only [bodyCode] at result
      cases slotResult : slotOf (variableSource count index) none slots with
      | mk slot slotsMiddle =>
      rw [slotResult] at result
      simp only [Prod.mk.injEq] at result
      obtain ⟨_, equalSlots⟩ := result
      subst equalSlots
      obtain ⟨keepsPrefix, canonicalAfter, _⟩ :=
        slotOfCanonical canonical
          (fun other isClosed => absurd isClosed (variableSourceNotClosed count index other))
          slotResult
      exact ⟨keepsPrefix, canonicalAfter⟩
  | .abstraction inner, count, slots, continuesChain, code, slotsAfter, canonical, result => by
      cases continuesChain with
      | true =>
          simp only [bodyCode, if_true] at result
          exact bodyCodeCanonical inner (count + 1) slots true code slotsAfter canonical result
      | false =>
          simp only [bodyCode, Bool.false_eq_true, if_false] at result
          cases chainCode : bodyCode 1 [] true inner with
          | mk innerCode innerSlots =>
          rw [chainCode] at result
          cases closedAbstraction : closedUnder 0 (.abstraction inner) with
          | true =>
              simp only [closedAbstraction, if_true] at result
              rw [← convertedAbstraction chainCode] at result
              obtain ⟨keepsPrefix, canonicalAfter, _⟩ := closedSlotCanonical canonical result
              exact ⟨keepsPrefix, canonicalAfter⟩
          | false =>
              simp only [closedAbstraction, Bool.false_eq_true, if_false] at result
              cases fillingsResult : innerFillings count innerSlots slots with
              | mk fillings slotsMiddle =>
              rw [fillingsResult] at result
              simp only [Prod.mk.injEq] at result
              obtain ⟨_, equalSlots⟩ := result
              subst equalSlots
              have innerCanonical :=
                (bodyCodeCanonical inner 1 [] true innerCode innerSlots
                  (fun _ _ _ found => by simp at found) chainCode).2
              obtain ⟨keepsPrefix, canonicalAfter, _⟩ :=
                innerFillingsPresent innerSlots slots fillings slotsMiddle innerCanonical canonical
                  fillingsResult
              exact ⟨keepsPrefix, canonicalAfter⟩
  | .application function argument, count, slots, continuesChain, code, slotsAfter, canonical,
      result => by
      simp only [bodyCode] at result
      cases closedApplication : closedUnder 0 (.application function argument) with
      | true =>
          simp only [closedApplication, if_true] at result
          obtain ⟨keepsPrefix, canonicalAfter, _⟩ := closedSlotCanonical canonical result
          exact ⟨keepsPrefix, canonicalAfter⟩
      | false =>
          simp only [closedApplication, Bool.false_eq_true, if_false] at result
          cases functionResult : bodyCode count slots false function with
          | mk functionCode slotsMiddle =>
          cases argumentResult : bodyCode count slotsMiddle false argument with
          | mk argumentCode slotsLast =>
          rw [functionResult, argumentResult] at result
          simp only [Prod.mk.injEq] at result
          obtain ⟨_, equalSlots⟩ := result
          subst equalSlots
          obtain ⟨⟨middleExtra, middlePrefix⟩, middleCanonical⟩ :=
            bodyCodeCanonical function count slots false functionCode slotsMiddle canonical
              functionResult
          obtain ⟨⟨lastExtra, lastPrefix⟩, lastCanonical⟩ :=
            bodyCodeCanonical argument count slotsMiddle false argumentCode slotsLast
              middleCanonical argumentResult
          exact ⟨⟨middleExtra ++ lastExtra, by rw [lastPrefix, middlePrefix, List.append_assoc]⟩,
            lastCanonical⟩
  | .choice left right, count, slots, continuesChain, code, slotsAfter, canonical, result => by
      simp only [bodyCode] at result
      cases closedChoice : closedUnder 0 (.choice left right) with
      | true =>
          simp only [closedChoice, if_true] at result
          obtain ⟨keepsPrefix, canonicalAfter, _⟩ := closedSlotCanonical canonical result
          exact ⟨keepsPrefix, canonicalAfter⟩
      | false =>
          simp only [closedChoice, Bool.false_eq_true, if_false] at result
          cases leftResult : bodyCode count slots false left with
          | mk leftCode slotsMiddle =>
          cases rightResult : bodyCode count slotsMiddle false right with
          | mk rightCode slotsLast =>
          rw [leftResult, rightResult] at result
          simp only [Prod.mk.injEq] at result
          obtain ⟨_, equalSlots⟩ := result
          subst equalSlots
          obtain ⟨⟨middleExtra, middlePrefix⟩, middleCanonical⟩ :=
            bodyCodeCanonical left count slots false leftCode slotsMiddle canonical leftResult
          obtain ⟨⟨lastExtra, lastPrefix⟩, lastCanonical⟩ :=
            bodyCodeCanonical right count slotsMiddle false rightCode slotsLast middleCanonical
              rightResult
          exact ⟨⟨middleExtra ++ lastExtra, by rw [lastPrefix, middlePrefix, List.append_assoc]⟩,
            lastCanonical⟩
  | .parallel left right, count, slots, continuesChain, code, slotsAfter, canonical, result => by
      simp only [bodyCode] at result
      cases closedParallel : closedUnder 0 (.parallel left right) with
      | true =>
          simp only [closedParallel, if_true] at result
          obtain ⟨keepsPrefix, canonicalAfter, _⟩ := closedSlotCanonical canonical result
          exact ⟨keepsPrefix, canonicalAfter⟩
      | false =>
          simp only [closedParallel, Bool.false_eq_true, if_false] at result
          cases leftResult : bodyCode count slots false left with
          | mk leftCode slotsMiddle =>
          cases rightResult : bodyCode count slotsMiddle false right with
          | mk rightCode slotsLast =>
          rw [leftResult, rightResult] at result
          simp only [Prod.mk.injEq] at result
          obtain ⟨_, equalSlots⟩ := result
          subst equalSlots
          obtain ⟨⟨middleExtra, middlePrefix⟩, middleCanonical⟩ :=
            bodyCodeCanonical left count slots false leftCode slotsMiddle canonical leftResult
          obtain ⟨⟨lastExtra, lastPrefix⟩, lastCanonical⟩ :=
            bodyCodeCanonical right count slotsMiddle false rightCode slotsLast middleCanonical
              rightResult
          exact ⟨⟨middleExtra ++ lastExtra, by rw [lastPrefix, middlePrefix, List.append_assoc]⟩,
            lastCanonical⟩
  | .constant definition, count, slots, continuesChain, code, slotsAfter, canonical, result => by
      simp only [bodyCode] at result
      obtain ⟨keepsPrefix, canonicalAfter, _⟩ := closedSlotCanonical canonical result
      exact ⟨keepsPrefix, canonicalAfter⟩

end

/-- The fillings of a chain outside any body exist only where every closed slot's subprogram has a
conversion. -/
theorem closedFillingsDefined : ∀ slots : List Slot, Canonical slots →
    (closedFillings slots).isSome = true → ConversionsDefined slots
  | [], _, _ => fun _ present => by
      obtain ⟨_, _, found, _⟩ := present
      simp at found
  | ⟨.bound bound, conversion⟩ :: slots, canonical, defined => by
      simp only [closedFillings] at defined
      have restDefined := closedFillingsDefined slots canonical.tail defined
      intro program present
      rcases present.cons with isClosed | inRest
      · cases isClosed
      · exact restDefined program inRest
  | ⟨.closed closed, conversion⟩ :: slots, canonical, defined => by
      have headConversion : conversion = converted closed :=
        canonical 0 ⟨.closed closed, conversion⟩ closed rfl rfl
      cases conversionIs : conversion with
      | none => simp [closedFillings, conversionIs, bind, Option.bind] at defined
      | some filling =>
          cases restIs : closedFillings slots with
          | none => simp [closedFillings, conversionIs, restIs, bind, Option.bind] at defined
          | some fillings =>
              have restDefined := closedFillingsDefined slots canonical.tail (by simp [restIs])
              intro program present
              rcases present.cons with isClosed | inRest
              · cases isClosed
                rw [← headConversion, conversionIs]
                rfl
              · exact restDefined program inRest
  | ⟨.free free, conversion⟩ :: slots, _, defined => by
      simp [closedFillings] at defined

mutual
/-- A program with a conversion has closed definitions, and so has a program whose code `bodyCode`
makes when every closed slot after it has a conversion. -/
theorem definitionsClosedOfConversions : ∀ program : Program,
    ((converted program).isSome = true → definitionsClosed program = true) ∧
    ∀ (count : Nat) (slots : List Slot) (continuesChain : Bool) (code : Code)
      (slotsAfter : List Slot),
      Canonical slots → bodyCode count slots continuesChain program = (code, slotsAfter) →
      ConversionsDefined slotsAfter → definitionsClosed program = true
  | .boundVariable _ => ⟨fun _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩
  | .abstraction inner => by
      have chainDefined : ∀ (code : Code) (innerSlots : List Slot),
          bodyCode 1 [] true inner = (code, innerSlots) →
          (closedFillings innerSlots).isSome = true → definitionsClosed inner = true := by
        intro code innerSlots chainCode fillingsDefined
        have emptyCanonical : Canonical [] := fun _ _ _ found => by simp at found
        have innerCanonical :=
          (bodyCodeCanonical inner 1 [] true code innerSlots emptyCanonical chainCode).2
        exact (definitionsClosedOfConversions inner).2 1 [] true code innerSlots emptyCanonical
          chainCode (closedFillingsDefined innerSlots innerCanonical fillingsDefined)
      have abstractionDefined : (converted (.abstraction inner)).isSome = true →
          definitionsClosed (.abstraction inner) = true := by
        intro converts
        cases chainCode : bodyCode 1 [] true inner with
        | mk code innerSlots =>
        rw [convertedAbstraction chainCode] at converts
        simp only [thunkConversion, Option.isSome_map] at converts
        simp only [definitionsClosed]
        exact chainDefined code innerSlots chainCode converts
      refine ⟨abstractionDefined, ?_⟩
      intro count slots continuesChain code slotsAfter canonical result defined
      cases continuesChain with
      | true =>
          simp only [bodyCode, if_true] at result
          simp only [definitionsClosed]
          exact (definitionsClosedOfConversions inner).2 (count + 1) slots true code slotsAfter
            canonical result defined
      | false =>
          simp only [bodyCode, Bool.false_eq_true, if_false] at result
          cases chainCode : bodyCode 1 [] true inner with
          | mk innerCode innerSlots =>
          rw [chainCode] at result
          cases closedAbstraction : closedUnder 0 (.abstraction inner) with
          | true =>
              simp only [closedAbstraction, if_true] at result
              rw [← convertedAbstraction chainCode] at result
              obtain ⟨_, _, present⟩ := closedSlotCanonical canonical result
              exact abstractionDefined (defined _ present)
          | false =>
              simp only [closedAbstraction, Bool.false_eq_true, if_false] at result
              cases fillingsResult : innerFillings count innerSlots slots with
              | mk fillings slotsMiddle =>
              rw [fillingsResult] at result
              simp only [Prod.mk.injEq] at result
              obtain ⟨_, equalSlots⟩ := result
              subst equalSlots
              have emptyCanonical : Canonical [] := fun _ _ _ found => by simp at found
              have innerCanonical :=
                (bodyCodeCanonical inner 1 [] true innerCode innerSlots emptyCanonical chainCode).2
              obtain ⟨_, _, presentAfter⟩ :=
                innerFillingsPresent innerSlots slots fillings slotsMiddle innerCanonical canonical
                  fillingsResult
              simp only [definitionsClosed]
              exact (definitionsClosedOfConversions inner).2 1 [] true innerCode innerSlots
                emptyCanonical chainCode
                (fun program present => defined program (presentAfter program present))
  | .application function argument => by
      have applicationDefined : (converted (.application function argument)).isSome = true →
          definitionsClosed (.application function argument) = true := by
        intro converts
        cases functionIs : converted function with
        | none => simp [converted, applicationConversion, functionIs, bind, Option.bind] at converts
        | some functionTerm =>
            cases argumentIs : converted argument with
            | none =>
                simp [converted, applicationConversion, functionIs, argumentIs, bind,
                  Option.bind] at converts
            | some argumentTerm =>
                simp only [definitionsClosed, Bool.and_eq_true]
                exact ⟨(definitionsClosedOfConversions function).1 (by simp [functionIs]),
                  (definitionsClosedOfConversions argument).1 (by simp [argumentIs])⟩
      refine ⟨applicationDefined, ?_⟩
      intro count slots continuesChain code slotsAfter canonical result defined
      simp only [bodyCode] at result
      cases closedApplication : closedUnder 0 (.application function argument) with
      | true =>
          simp only [closedApplication, if_true] at result
          obtain ⟨_, _, present⟩ := closedSlotCanonical canonical result
          exact applicationDefined (defined _ present)
      | false =>
          simp only [closedApplication, Bool.false_eq_true, if_false] at result
          cases functionResult : bodyCode count slots false function with
          | mk functionCode slotsMiddle =>
          cases argumentResult : bodyCode count slotsMiddle false argument with
          | mk argumentCode slotsLast =>
          rw [functionResult, argumentResult] at result
          simp only [Prod.mk.injEq] at result
          obtain ⟨_, equalSlots⟩ := result
          subst equalSlots
          obtain ⟨_, middleCanonical⟩ :=
            bodyCodeCanonical function count slots false functionCode slotsMiddle canonical
              functionResult
          obtain ⟨⟨lastExtra, lastPrefix⟩, _⟩ :=
            bodyCodeCanonical argument count slotsMiddle false argumentCode slotsLast
              middleCanonical argumentResult
          have middleDefined : ConversionsDefined slotsMiddle := by
            rw [lastPrefix] at defined
            exact defined.prefix
          simp only [definitionsClosed, Bool.and_eq_true]
          exact ⟨(definitionsClosedOfConversions function).2 count slots false functionCode
              slotsMiddle canonical functionResult middleDefined,
            (definitionsClosedOfConversions argument).2 count slotsMiddle false argumentCode
              slotsLast middleCanonical argumentResult defined⟩
  | .choice left right => by
      have choiceDefined : (converted (.choice left right)).isSome = true →
          definitionsClosed (.choice left right) = true := by
        intro converts
        cases leftIs : converted left with
        | none => simp [converted, choiceConversion, leftIs, bind, Option.bind] at converts
        | some leftTerm =>
            cases rightIs : converted right with
            | none =>
                simp [converted, choiceConversion, leftIs, rightIs, bind, Option.bind] at converts
            | some rightTerm =>
                simp only [definitionsClosed, Bool.and_eq_true]
                exact ⟨(definitionsClosedOfConversions left).1 (by simp [leftIs]),
                  (definitionsClosedOfConversions right).1 (by simp [rightIs])⟩
      refine ⟨choiceDefined, ?_⟩
      intro count slots continuesChain code slotsAfter canonical result defined
      simp only [bodyCode] at result
      cases closedChoice : closedUnder 0 (.choice left right) with
      | true =>
          simp only [closedChoice, if_true] at result
          obtain ⟨_, _, present⟩ := closedSlotCanonical canonical result
          exact choiceDefined (defined _ present)
      | false =>
          simp only [closedChoice, Bool.false_eq_true, if_false] at result
          cases leftResult : bodyCode count slots false left with
          | mk leftCode slotsMiddle =>
          cases rightResult : bodyCode count slotsMiddle false right with
          | mk rightCode slotsLast =>
          rw [leftResult, rightResult] at result
          simp only [Prod.mk.injEq] at result
          obtain ⟨_, equalSlots⟩ := result
          subst equalSlots
          obtain ⟨_, middleCanonical⟩ :=
            bodyCodeCanonical left count slots false leftCode slotsMiddle canonical leftResult
          obtain ⟨⟨lastExtra, lastPrefix⟩, _⟩ :=
            bodyCodeCanonical right count slotsMiddle false rightCode slotsLast middleCanonical
              rightResult
          have middleDefined : ConversionsDefined slotsMiddle := by
            rw [lastPrefix] at defined
            exact defined.prefix
          simp only [definitionsClosed, Bool.and_eq_true]
          exact ⟨(definitionsClosedOfConversions left).2 count slots false leftCode slotsMiddle
              canonical leftResult middleDefined,
            (definitionsClosedOfConversions right).2 count slotsMiddle false rightCode slotsLast
              middleCanonical rightResult defined⟩
  | .parallel left right => by
      have parallelDefined : (converted (.parallel left right)).isSome = true →
          definitionsClosed (.parallel left right) = true := by
        intro converts
        cases leftIs : converted left with
        | none => simp [converted, parallelConversion, leftIs, bind, Option.bind] at converts
        | some leftTerm =>
            cases rightIs : converted right with
            | none =>
                simp [converted, parallelConversion, leftIs, rightIs, bind, Option.bind] at converts
            | some rightTerm =>
                simp only [definitionsClosed, Bool.and_eq_true]
                exact ⟨(definitionsClosedOfConversions left).1 (by simp [leftIs]),
                  (definitionsClosedOfConversions right).1 (by simp [rightIs])⟩
      refine ⟨parallelDefined, ?_⟩
      intro count slots continuesChain code slotsAfter canonical result defined
      simp only [bodyCode] at result
      cases closedParallel : closedUnder 0 (.parallel left right) with
      | true =>
          simp only [closedParallel, if_true] at result
          obtain ⟨_, _, present⟩ := closedSlotCanonical canonical result
          exact parallelDefined (defined _ present)
      | false =>
          simp only [closedParallel, Bool.false_eq_true, if_false] at result
          cases leftResult : bodyCode count slots false left with
          | mk leftCode slotsMiddle =>
          cases rightResult : bodyCode count slotsMiddle false right with
          | mk rightCode slotsLast =>
          rw [leftResult, rightResult] at result
          simp only [Prod.mk.injEq] at result
          obtain ⟨_, equalSlots⟩ := result
          subst equalSlots
          obtain ⟨_, middleCanonical⟩ :=
            bodyCodeCanonical left count slots false leftCode slotsMiddle canonical leftResult
          obtain ⟨⟨lastExtra, lastPrefix⟩, _⟩ :=
            bodyCodeCanonical right count slotsMiddle false rightCode slotsLast middleCanonical
              rightResult
          have middleDefined : ConversionsDefined slotsMiddle := by
            rw [lastPrefix] at defined
            exact defined.prefix
          simp only [definitionsClosed, Bool.and_eq_true]
          exact ⟨(definitionsClosedOfConversions left).2 count slots false leftCode slotsMiddle
              canonical leftResult middleDefined,
            (definitionsClosedOfConversions right).2 count slotsMiddle false rightCode slotsLast
              middleCanonical rightResult defined⟩
  | .constant definition => by
      have constantDefined : (converted (.constant definition)).isSome = true →
          definitionsClosed (.constant definition) = true := by
        intro converts
        cases closedDefinition : closedUnder 0 definition with
        | false => simp [converted, closedDefinition] at converts
        | true =>
            simp only [converted, closedDefinition, if_true] at converts
            simp only [definitionsClosed, closedDefinition, Bool.true_and]
            exact (definitionsClosedOfConversions definition).1 converts
      refine ⟨constantDefined, ?_⟩
      intro count slots continuesChain code slotsAfter canonical result defined
      simp only [bodyCode] at result
      obtain ⟨_, _, present⟩ := closedSlotCanonical canonical result
      exact constantDefined (defined _ present)

end

/-- The front end has a value exactly on the closed programs whose constants' definitions are
closed. -/
theorem thunkInstructionDefined (program : Program) :
    (thunkInstruction program).isSome = true ↔
      closedUnder 0 program = true ∧ definitionsClosed program = true := by
  constructor
  · intro defined
    cases closedProgram : closedUnder 0 program with
    | false => simp [thunkInstruction, closedProgram] at defined
    | true =>
        simp only [thunkInstruction, closedProgram, if_true, Option.isSome_map] at defined
        exact ⟨rfl, (definitionsClosedOfConversions program).1 defined⟩
  · intro ⟨closed, definitions⟩
    obtain ⟨finiteTerm, converts, _⟩ := readbackThunkInstruction closed definitions
    simp [converts]

/-- Link (i) of D6 for the front end of this module, on every finite term it gives: the readback
is the program's δ. -/
theorem readbackOfThunkInstruction {program : Program} {finiteTerm : FiniteTerm}
    (converts : thunkInstruction program = some finiteTerm) :
    readback finiteTerm = some (delta program) := by
  obtain ⟨closed, definitions⟩ := (thunkInstructionDefined program).mp (by simp [converts])
  obtain ⟨other, otherConverts, otherReadback⟩ := readbackThunkInstruction closed definitions
  rw [converts, Option.some.injEq] at otherConverts
  rw [otherConverts]
  exact otherReadback

/-- D3's item 3: a closed term has a defunctionalization, and its readback is the term. -/
theorem readbackDefunctionalize {term : Term} (closed : Term.Closed term) :
    ∃ finiteTerm, defunctionalize term = some finiteTerm ∧ readback finiteTerm = some term := by
  have closedUnderZero : closedUnder 0 (Program.ofTerm term) = true := by
    rw [closedUnderOfTerm]
    exact (termClosedUnderZeroIff term).mpr closed
  have readBack := readbackThunkInstruction closedUnderZero (definitionsClosedOfTerm term)
  rw [deltaOfTerm] at readBack
  exact readBack

/-- Only a closed term has a defunctionalization, and its readback is the term. -/
theorem readbackOfDefunctionalize {term : Term} {finiteTerm : FiniteTerm}
    (defunctionalized : defunctionalize term = some finiteTerm) :
    Term.Closed term ∧ readback finiteTerm = some term := by
  unfold defunctionalize thunkInstruction at defunctionalized
  cases closedUnderZero : closedUnder 0 (Program.ofTerm term) with
  | false => simp [closedUnderZero] at defunctionalized
  | true =>
      have closed : Term.Closed term := by
        rw [closedUnderOfTerm] at closedUnderZero
        exact (termClosedUnderZeroIff term).mp closedUnderZero
      obtain ⟨other, otherDefunctionalized, readBack⟩ := readbackDefunctionalize closed
      unfold defunctionalize thunkInstruction at otherDefunctionalized
      rw [if_pos closedUnderZero] at defunctionalized otherDefunctionalized
      rw [defunctionalized, Option.some.injEq] at otherDefunctionalized
      subst otherDefunctionalized
      exact ⟨closed, readBack⟩

/-- A term has a defunctionalization exactly when it is closed, as `thunk_instruction/2` accepts
exactly the closed terms. -/
theorem defunctionalizeDefined (term : Term) :
    (defunctionalize term).isSome = true ↔ Term.Closed term := by
  constructor
  · intro defined
    cases defunctionalized : defunctionalize term with
    | none => simp [defunctionalized] at defined
    | some finiteTerm => exact (readbackOfDefunctionalize defunctionalized).1
  · intro closed
    obtain ⟨finiteTerm, defunctionalized, _⟩ := readbackDefunctionalize closed
    simp [defunctionalized]

/-- The converse of D3's item 2, from item 3: two terms with one defunctionalization are one
term, that is (de Bruijn terms being α-classes) α-equivalent. Item 2 itself holds by construction,
`defunctionalize` being a function of the term. -/
theorem defunctionalizeInjective {left right : Term} {finiteTerm : FiniteTerm}
    (leftDefunctionalized : defunctionalize left = some finiteTerm)
    (rightDefunctionalized : defunctionalize right = some finiteTerm) : left = right := by
  have leftReadback := (readbackOfDefunctionalize leftDefunctionalized).2
  have rightReadback := (readbackOfDefunctionalize rightDefunctionalized).2
  rw [leftReadback, Option.some.injEq] at rightReadback
  exact rightReadback

/-! ## Agreement with the Prolog

The finite terms of five closed terms, as `thunk_instruction/2` of
`gezi/prolog/gezi/defunctionalization.pl` printed them on 2026-10-07 (the Prolog's hole
`N` is `.slot N` here), checked by the kernel. They cover a chain of two binders reading a closed
subterm, a binder the body does not read, a closed subterm beside a binder read twice, an inner
chain that is not closed and reads both a variable of the enclosing chain and a closed subterm, and
two equal closed subterms sharing one slot. The terms that the witness of D3's item 5 below and
module `Adequacy` read are named here; K is `Semantics.first` and K* is `Semantics.second`. One
more program, as the reviewer measured it on 2026-10-07, covers a constant (`libraryNameFrontEnd`),
and is the witness that link (i) is stated on readbacks: the finite term of a program is in general
not the defunctionalization of its δ. `choiceFrontEnd` checks a right-nested chain of choices.

FIXME (2026-10-10, link (i) of D6 and D3 in https://github.com/Atry/private-overlay/issues/1561): what
is proved here of `thunkInstruction` (link (i), `readbackThunkInstruction`) and of
`defunctionalize` (D3's items 3 and 5, the injectivity) holds of the front end,
`Defunctionalization.thunkInstruction` of the Scala project `frontend`, its instructions replaced by
the finite terms of their layers, only where the two compute one finite term, and that they do is
not proved: the Scala is a separate implementation of the same clauses, not compiled from this
definition. The kernel checks the eight programs of this section against the output the Prolog
front end, which the Scala one replaced, printed on 2026-10-07. The test
`gezi/standardlibrary/src/test/scala/gezi/standardlibrary/DefunctionalizationAgreementTest.scala`
compares the Scala front end with this definition, the finite terms printed in one syntax byte for
byte, on 100 random source programs over the prelude's files drawn from a fixed seed, on the term
of every file of the prelude, and on 100 random closed terms of the calculus. Nothing is known
beyond the samples. Candidate fixes: this definition compiled and run as the front end in place of
the Scala one; or a check of each run, the run carrying its source program and the library's terms
into Lean and the kernel checking `thunkInstruction` of the source against the run's input. -/

namespace Agreement

/-! I is `Readback.Witness.identityTerm`; its defunctionalization is `Readback.Witness.identity`,
the Prolog's `thunk(slot(0),[0],[])`, and that of K, `Semantics.first`, is
`Readback.Witness.first`, the Prolog's `thunk(slot(0),[0,ignored],[])` (`unreadBinder`). -/

/-- The defunctionalization of K*, `Semantics.second`, the Prolog's
`thunk(slot(0),[ignored,0],[])`: the layer of the prelude's `false`. -/
def secondThunk : FiniteTerm := .thunk (.slot 0) [.ignored, .slot 0] []

/-- `λx2. x2 (x1 I)`, the body of `chainTerm`, with x1 free. -/
def chainBody : Term :=
  .abstraction (.application (.boundVariable 0)
    (.application (.boundVariable 1) Readback.Witness.identityTerm))

/-- `λx1.λx2. x2 (x1 I)`, a chain of two binders reading a closed subterm. -/
def chainTerm : Term := .abstraction chainBody

/-- The code of the body of `chainTerm`: slot 0 is x2, slot 1 is x1, slot 2 is I. -/
def chainCode : Code := .apply (.slot 0) (.apply (.slot 1) (.slot 2))

/-- The defunctionalization of `chainTerm`, the Prolog's
`thunk(apply(slot(0),apply(slot(1),slot(2))),[1,0],[thunk(slot(0),[0],[])])`. -/
def chainThunk : FiniteTerm := .thunk chainCode [.slot 1, .slot 0] [Readback.Witness.identity]

/-- `λx. x (I x)`: the binder is read twice, once as the argument of the closed subterm I, which
makes `I x` a β redex under the binder. -/
def binderRedex : Term :=
  .abstraction (.application (.boundVariable 0)
    (.application Readback.Witness.identityTerm (.boundVariable 0)))

/-- The defunctionalization of `binderRedex`, the Prolog's
`thunk(apply(slot(0),apply(slot(1),slot(0))),[0],[thunk(slot(0),[0],[])])`. -/
def binderRedexThunk : FiniteTerm :=
  .thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 0))) [.slot 0] [Readback.Witness.identity]

/-- A chain of two binders reading a closed subterm. -/
theorem chainOfTwo : defunctionalize chainTerm = some chainThunk := rfl

/-- K: a binder the body does not read is an `ignored` hole. -/
theorem unreadBinder : defunctionalize first = some Readback.Witness.first := rfl

/-- A closed subterm beside a binder read twice. -/
theorem binderReadTwice : defunctionalize binderRedex = some binderRedexThunk := rfl

/-- `λx.λy. y (λa. x (I a))`, `thunk(apply(slot(0),thunk(apply(slot(0),apply(slot(1),slot(2))),
[2],[slot(1),slot(2)])),[1,0],[thunk(slot(0),[0],[])])`: an inner chain that is not closed. -/
theorem innerChain :
    defunctionalize (.abstraction (.abstraction (.application (.boundVariable 0)
      (.abstraction (.application (.boundVariable 2)
        (.application Readback.Witness.identityTerm (.boundVariable 0))))))) =
    some (.thunk (.apply (.slot 0) (.thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 2)))
        [.slot 2] [.slot 1, .slot 2]))
      [.slot 1, .slot 0] [Readback.Witness.identity]) := rfl

/-- `λx. x I I`, `thunk(apply(apply(slot(0),slot(1)),slot(1)),[0],[thunk(slot(0),[0],[])])`: the
two occurrences of I share one slot. -/
theorem sharedClosedSubterm :
    defunctionalize (.abstraction
      (.application (.application (.boundVariable 0) Readback.Witness.identityTerm)
        Readback.Witness.identityTerm)) =
    some (.thunk (.apply (.apply (.slot 0) (.slot 1)) (.slot 1)) [.slot 0]
      [Readback.Witness.identity]) := rfl

/-- `thunk_instruction(lambda(constant(False)))`, False the handle of `false`, with the handle
unfolded to its layer, K*'s (`secondThunk`): `thunk(slot(0),[ignored],[False])` solved. -/
def namedFalseThunk : FiniteTerm := .thunk (.slot 0) [.ignored] [secondThunk]

/-- `λ_. false` with the name replaced by its body: `λ_.λx.λy. y`. -/
def falseInlined : Term := .abstraction second

/-- The defunctionalization of `falseInlined`, the Prolog's `thunk(slot(0),[ignored,ignored,0],[])`.
-/
def falseInlinedThunk : FiniteTerm := .thunk (.slot 0) [.ignored, .ignored, .slot 0] []

/-- The reviewer's measurement of 2026-10-07: `λ_. false` through `thunk_instruction/2` with its
handle solved, and the same program with the name replaced by the body of `false` through
`defunctionalize`, are two finite terms whose readback is that program. -/
theorem libraryNameReadback :
    defunctionalize second = some secondThunk ∧
      readback namedFalseThunk = some falseInlined ∧
        defunctionalize falseInlined = some falseInlinedThunk ∧
          readback falseInlinedThunk = some falseInlined :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `λ_. false` as a source program: an abstraction around the constant of `false`, whose
definition is K*. -/
def namedFalse : Program := .abstraction (.constant (Program.ofTerm second))

/-- The front end on `λ_. false`: the conversion makes the finite term the reviewer measured of
`thunk_instruction/2` on 2026-10-07 (`namedFalseThunk`), and `thunkInstruction` folds it into the
defunctionalization of δ of the program, `λ_.λx.λy. y` (`falseInlinedThunk`), so the name and the
term it names give one finite term. -/
theorem libraryNameFrontEnd :
    converted namedFalse = some namedFalseThunk ∧
      thunkInstruction namedFalse = some falseInlinedThunk ∧ delta namedFalse = falseInlined :=
  ⟨rfl, rfl, rfl⟩

/-- The front end on the right-nested chain `I + (I + K)`: the binary choice of the IR keeps the
nesting, and the readback is the chain itself. -/
theorem choiceFrontEnd :
    thunkInstruction (.choice (Program.ofTerm Readback.Witness.identityTerm)
        (.choice (Program.ofTerm Readback.Witness.identityTerm) (Program.ofTerm first))) =
        some (.choice Readback.Witness.identity
          (.choice Readback.Witness.identity Readback.Witness.first)) ∧
      readback (.choice Readback.Witness.identity
          (.choice Readback.Witness.identity Readback.Witness.first)) =
        some (.choice Readback.Witness.identityTerm (.choice Readback.Witness.identityTerm first)) :=
  ⟨rfl, rfl⟩

end Agreement

/-! ## The witness of D3's item 5: addresses are finer than α-equivalence

D3's example `λx1.λx2. x2 (x1 c)` with `c` = I is `Agreement.chainTerm`; its thunk is applied to
`a` = K. The first clause of the defunctionalized β rule fills the hole of `x1` and gives a thunk
whose readback is `λx2. x2 (a c)`; the defunctionalization of that readback hoists the closed
subterm `a c` into one slot, while the filled thunk keeps `a` and `c` in two, under a different
code. -/

namespace Witness

/-- `λx2. x2 (a c)` with `a` = K and `c` = I, the contractum of `(λx1.λx2. x2 (x1 c)) a`
(`contractumInstantiates`). -/
def contractumTerm : Term :=
  .abstraction (.application (.boundVariable 0) (.application first Readback.Witness.identityTerm))

/-- The thunk after its first hole, x1's slot 1, is filled with `a`. -/
def filled : FiniteTerm :=
  .thunk Agreement.chainCode [.slot 0] [Readback.Witness.first, Readback.Witness.identity]

/-- The defunctionalization of `λx2. x2 (a c)`: slot 1 is the closed subterm `a c`. -/
def canonical : FiniteTerm :=
  .thunk (.apply (.slot 0) (.slot 1)) [.slot 0]
    [.apply Readback.Witness.first Readback.Witness.identity]

theorem contractumDefunctionalized : defunctionalize contractumTerm = some canonical := rfl

/-- The application of the chain's thunk to `a` equals the filled thunk, by the first clause of
the defunctionalized β rule. -/
theorem applicationFilled : Equal (.apply Agreement.chainThunk Readback.Witness.first) filled :=
  Equal.betaFill (code := Agreement.chainCode) (hole := .slot 1) (holes := [.slot 0])
    (fillings := [Readback.Witness.identity]) (argument := Readback.Witness.first)

/-- `λx2. x2 (a c)` is the instance of the body of `λx1.λx2. x2 (x1 c)` at `a`, the contractum
of the β rule. -/
theorem contractumInstantiates :
    contractumTerm = Term.instantiate Agreement.chainBody first := by
  decide

/-- The β rule takes `(λx1.λx2. x2 (x1 c)) a` to `λx2. x2 (a c)`. -/
theorem applicationContracts {hypotheses : Term → Term → Prop} :
    DerivableLatticeEta hypotheses (.application Agreement.chainTerm first) contractumTerm := by
  rw [contractumInstantiates]
  exact DerivableLatticeEta.beta Agreement.chainBody first

theorem filledReadback : readback filled = some contractumTerm := by decide

theorem canonicalReadback : readback canonical = some contractumTerm := by decide

/-- The filled thunk and the defunctionalization of its readback are two finite terms: their
codes differ. -/
theorem filledNotCanonical : filled ≠ canonical := by
  intro equal
  simp [filled, canonical, Agreement.chainCode] at equal

/-- The filled thunk is the right side of the first clause of the defunctionalized β rule
(`Equal.betaFill`) for the application of the chain's thunk to `a`. -/
theorem filledByBetaFill :
    filled = .thunk Agreement.chainCode [.slot 0]
      (fill (.slot 1) [.slot 0] [Readback.Witness.identity] Readback.Witness.first) :=
  rfl

/-- D3's item 5: there are terms `M = λx. B` and `A`, closed since their defunctionalizations
are defined (`defunctionalizeDefined`), whose defunctionalizations are a thunk with a hole and a
finite term `a`, such that the first clause of the defunctionalized β rule (`Equal.betaFill`) takes
the application of the one to the other to a finite term that reads back to the contractum
`N = B[x := A]` of `M A`, and that is not the defunctionalization of `N`, whose readback is `N` as
well. So two different finite terms, two addresses, read back to one term. The witness is D3's
example above. -/
theorem addressesFinerThanAlpha :
    ∃ (chain body argument contractum : Term) (code : Code) (hole : Hole) (holes : List Hole)
      (fillings : List FiniteTerm) (argumentFinite canonicalFinite : FiniteTerm),
      chain = .abstraction body ∧ contractum = Term.instantiate body argument ∧
      defunctionalize chain = some (.thunk code (hole :: holes) fillings) ∧
        defunctionalize argument = some argumentFinite ∧
          Equal (.apply (.thunk code (hole :: holes) fillings) argumentFinite)
            (.thunk code holes (fill hole holes fillings argumentFinite)) ∧
            (∀ hypotheses, DerivableLatticeEta hypotheses (.application chain argument) contractum) ∧
              readback (.thunk code holes (fill hole holes fillings argumentFinite)) =
                some contractum ∧
                defunctionalize contractum = some canonicalFinite ∧
                  readback canonicalFinite = some contractum ∧
                    FiniteTerm.thunk code holes (fill hole holes fillings argumentFinite) ≠
                      canonicalFinite := by
  refine ⟨Agreement.chainTerm, Agreement.chainBody, first, contractumTerm, Agreement.chainCode,
    .slot 1, [.slot 0], [Readback.Witness.identity], Readback.Witness.first, canonical, rfl,
    contractumInstantiates, Agreement.chainOfTwo, Agreement.unreadBinder, .betaFill,
    fun _ => applicationContracts, ?_, contractumDefunctionalized, canonicalReadback, ?_⟩
  · rw [← filledByBetaFill]
    exact filledReadback
  · rw [← filledByBetaFill]
    exact filledNotCanonical

end Witness

end LambdaJit.Defunctionalization
