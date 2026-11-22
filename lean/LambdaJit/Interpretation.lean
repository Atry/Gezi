import LambdaJit.Article
import LambdaJit.Readback

/-!
# The interpretation of OpenTheory article terms in the calculus

The end-to-end theorem of design decision D6 (`lean/README.md`, "Design decisions") reads the terms of an article,
the first-order HOL terms of the encoding of D7, as terms of the calculus, the de Bruijn terms of
module `Terms`. The encoding is defined by the module documentation of the writer,
`gezi/prolog/gezi/opentheory_article.pl`: one type `LambdaJit.term`; the constants
`LambdaJit.apply`, `LambdaJit.choice` and `LambdaJit.parallel` of type `term → term → term`; and
for each pair of a code and a hole list a thunk
constant `LambdaJit.thunk.N`, applied by HOL application to the fillings in slot order, whose code
and holes are its defining term (D7.1), not its name.

This module holds four things.

- `Signature` and `signatureOf`: the code and the holes of each thunk constant by name, read
  structurally from the defining terms `LambdaJit.Code.thunkOf C H` of an article's definitions
  (`Article.Theory.definitions`); a statement carries its signature as a list. Every function below
  reads the constants of a term under a signature (`operatorOf`).
- `read`, the reading ⟦·⟧ of D10 on a closed article term in which every constant is applied to
  as many arguments as it takes: `apply`, `choice` and `parallel` literally, and a
  thunk constant applied to its fillings by the readback's thunk clause (module `Readback`, the
  clause of `readback` for a thunk), so that, for a thunk constant applied to exactly as many
  arguments as it takes (`thunkArity`, the precondition: `readLiteral` is undefined at any other
  argument count), it is defined exactly where the readback is.
- `interpret`, a total interpretation used by the proofs: it reads a HOL variable by a
  valuation, a HOL application as an application of the calculus, and a constant as a closed
  term, its curried form (`curried`): the constant's reading abstracted over its arguments. A
  partial application, such as `LambdaJit.apply X`, which the congruence of `Article.Derivable`
  relates as freely as any term, is so interpreted as a term too. Where `read` is defined, the
  two agree up to the β rule (`readDerivable`), and an instance of an article term under an
  instantiation of its variables is interpreted under the valuation that interprets the
  instantiation (`interpretInstantiate`). The type a constant carries plays no part; a variable
  is told apart by its name and its type, as `Article.Instantiation` tells it apart.
- `agree`: two terms under two signatures with one shape, the same variables and constants of the
  same operator, which are interpreted as one term (`interpretOfAgree`); it relates a statement to
  an article's import of it, the two numbering their thunk constants each from 0.

A name that is none of the three operators and no thunk constant of the signature (the constant
`=`, say) has no reading.

Link (ii) of D6 is that `read` of the article
term the writer writes for an IR term is `Readback.readback` of that IR term. Module `Encoding`
defines the writer's encoding as Lean states it (`Encoding.encode`) and proves that `read` of
`Encoding.encode t` is `Readback.readback t` (`Encoding.readEncode`); the rest of link (ii), that
the Prolog writer writes `Encoding.encode t`, is tested, not proved (FIXME at `key_term_written/2`
of `gezi/prolog/gezi/opentheory_article.pl`).
-/

namespace LambdaJit.Interpretation

open LambdaJit.Readback (thunkTerm interpretCode finalSlots abstractions readbackCode
  shiftIterate)

/-! ## The number of fillings of a thunk constant -/

mutual
/-- One more than the highest slot of the enclosing thunk that a code reads, 0 when it reads
none. A nested thunk's code numbers its own slots; its fillings read the enclosing thunk's. -/
def slotCount : Code → Nat
  | .slot index => index + 1
  | .apply function argument => max (slotCount function) (slotCount argument)
  | .thunk _ _ fillings => slotCountList fillings
  | .choice left right => max (slotCount left) (slotCount right)
  | .parallel left right => max (slotCount left) (slotCount right)

/-- The largest `slotCount` of a list of codes, 0 for the empty list. -/
def slotCountList : List Code → Nat
  | [] => 0
  | code :: codes => max (slotCount code) (slotCountList codes)
end

/-- The number of holes that are slots, not `ignored`. -/
def slotHoleCount (holes : List Hole) : Nat :=
  (holes.filter fun hole => hole != .ignored).length

/-- The number of fillings of a thunk of `code` with `holes`, the arity of its constant: the
code's slots that are no hole, as the writer's `thunk_arity/3` counts them. -/
def thunkArity (code : Code) (holes : List Hole) : Nat :=
  slotCount code - slotHoleCount holes

/-! ## The operators -/

/-- The name `LambdaJit.apply`. -/
def applyName : Article.Name := ⟨["LambdaJit"], "apply"⟩

/-- The name `LambdaJit.choice`. -/
def choiceName : Article.Name := ⟨["LambdaJit"], "choice"⟩

/-- The name `LambdaJit.parallel`. -/
def parallelName : Article.Name := ⟨["LambdaJit"], "parallel"⟩

/-- What a constant of the encoding stands for. -/
inductive Operator where
  /-- `LambdaJit.apply`, the application. -/
  | apply
  /-- `LambdaJit.choice`, the binary choice. -/
  | choice
  /-- `LambdaJit.parallel`, the parallel. -/
  | parallel
  /-- The thunk constant of `code` with `holes`. -/
  | thunk (code : Code) (holes : List Hole)
  /-- Any other constant. -/
  | unknown

/-! ## Signatures

A thunk constant's name says nothing of its code (design decision D7.1): the article defines the constant by `defineConst`, its
defining term `LambdaJit.Code.thunkOf C H` a first-order term of the code `C` and the holes `H`
over the constants below, and a statement carries the same pairs as a list. A signature is that
list, read structurally (`signatureOf`), and the operator of a name is looked up in it. -/

/-- The code and the holes of each thunk constant, by name: the first entry of a name counts. -/
abbrev Signature := List (Article.Name × Code × List Hole)

/-- The name `LambdaJit.Code.thunkOf`, the head of a thunk constant's defining term. -/
def thunkOfName : Article.Name := ⟨["LambdaJit", "Code"], "thunkOf"⟩

/-- The name `LambdaJit.Number.zero`. -/
def numberZeroName : Article.Name := ⟨["LambdaJit", "Number"], "zero"⟩

/-- The name `LambdaJit.Number.successor`. -/
def numberSuccessorName : Article.Name := ⟨["LambdaJit", "Number"], "successor"⟩

/-- The name `LambdaJit.Hole.slot`. -/
def holeSlotName : Article.Name := ⟨["LambdaJit", "Hole"], "slot"⟩

/-- The name `LambdaJit.Hole.ignored`. -/
def holeIgnoredName : Article.Name := ⟨["LambdaJit", "Hole"], "ignored"⟩

/-- The name `LambdaJit.Holes.nil`. -/
def holesNilName : Article.Name := ⟨["LambdaJit", "Holes"], "nil"⟩

/-- The name `LambdaJit.Holes.cons`. -/
def holesConsName : Article.Name := ⟨["LambdaJit", "Holes"], "cons"⟩

/-- The name `LambdaJit.Code.slot`. -/
def codeSlotName : Article.Name := ⟨["LambdaJit", "Code"], "slot"⟩

/-- The name `LambdaJit.Code.apply`. -/
def codeApplyName : Article.Name := ⟨["LambdaJit", "Code"], "apply"⟩

/-- The name `LambdaJit.Code.choice`. -/
def codeChoiceName : Article.Name := ⟨["LambdaJit", "Code"], "choice"⟩

/-- The name `LambdaJit.Code.parallel`. -/
def codeParallelName : Article.Name := ⟨["LambdaJit", "Code"], "parallel"⟩

/-- The name `LambdaJit.Code.thunk`. -/
def codeThunkName : Article.Name := ⟨["LambdaJit", "Code"], "thunk"⟩

/-- The name `LambdaJit.Codes.nil`. -/
def codesNilName : Article.Name := ⟨["LambdaJit", "Codes"], "nil"⟩

/-- The name `LambdaJit.Codes.cons`. -/
def codesConsName : Article.Name := ⟨["LambdaJit", "Codes"], "cons"⟩

/-- The number a term writes in unary: `LambdaJit.Number.zero` is 0 and
`LambdaJit.Number.successor n` one more than `n`; `none` for any other term. -/
def readNumber : Article.Term → Option Nat
  | .constant name _ => if name = numberZeroName then some 0 else none
  | .application (.constant name _) argument =>
      if name = numberSuccessorName then (readNumber argument).map (· + 1) else none
  | _ => none

/-- The hole a term writes: `LambdaJit.Hole.slot n` or `LambdaJit.Hole.ignored`. -/
def readHole : Article.Term → Option Hole
  | .constant name _ => if name = holeIgnoredName then some .ignored else none
  | .application (.constant name _) argument =>
      if name = holeSlotName then (readNumber argument).map .slot else none
  | _ => none

/-- The holes a term writes, a list of `LambdaJit.Holes.cons` ending in `LambdaJit.Holes.nil`. -/
def readHoles : Article.Term → Option (List Hole)
  | .constant name _ => if name = holesNilName then some [] else none
  | .application (.application (.constant name _) head) tail =>
      if name = holesConsName then
        match readHole head, readHoles tail with
        | some hole, some holes => some (hole :: holes)
        | _, _ => none
      else none
  | _ => none

mutual
/-- The code a term writes: `LambdaJit.Code.slot n`, `LambdaJit.Code.apply`, `LambdaJit.Code.choice`
or `LambdaJit.Code.parallel` of two codes, or `LambdaJit.Code.thunk` of a code, holes and a list
of codes. -/
def readCode : Article.Term → Option Code
  | .application (.constant name _) argument =>
      if name = codeSlotName then (readNumber argument).map .slot else none
  | .application (.application (.constant name _) left) right =>
      match readCode left, readCode right with
      | some left, some right =>
          if name = codeApplyName then some (.apply left right)
          else if name = codeChoiceName then some (.choice left right)
          else if name = codeParallelName then some (.parallel left right)
          else none
      | _, _ => none
  | .application (.application (.application (.constant name _) code) holes) fillings =>
      if name = codeThunkName then
        match readCode code, readHoles holes, readCodes fillings with
        | some code, some holes, some fillings => some (.thunk code holes fillings)
        | _, _, _ => none
      else none
  | _ => none

/-- The codes a term writes, a list of `LambdaJit.Codes.cons` ending in `LambdaJit.Codes.nil`. -/
def readCodes : Article.Term → Option (List Code)
  | .constant name _ => if name = codesNilName then some [] else none
  | .application (.application (.constant name _) head) tail =>
      if name = codesConsName then
        match readCode head, readCodes tail with
        | some code, some codes => some (code :: codes)
        | _, _ => none
      else none
  | _ => none
end

/-- The signature of an article's definitions: each name whose defining term is
`LambdaJit.Code.thunkOf C H`, with the code and the holes read from `C` and `H`. A definition of
any other form gives no entry. -/
def signatureOf (definitions : List (Article.Name × Article.Term)) : Signature :=
  definitions.filterMap fun (name, value) =>
    match value with
    | .application (.application (.constant head _) code) holes =>
        if head = thunkOfName then
          match readCode code, readHoles holes with
          | some code, some holes => some (name, code, holes)
          | _, _ => none
        else none
    | _ => none

/-- The operator a constant's name stands for under a signature: the three operators by their
fixed names, a thunk constant by the signature. -/
def operatorOf (signature : Signature) (name : Article.Name) : Operator :=
  if name = applyName then .apply
  else if name = choiceName then .choice
  else if name = parallelName then .parallel
  else
    match Article.lookupFirst name signature with
    | some (code, holes) => .thunk code holes
    | none => .unknown

/-- The number of arguments an operator takes. -/
def Operator.arity : Operator → Nat
  | .apply | .choice | .parallel => 2
  | .thunk code holes => thunkArity code holes
  | .unknown => 0

/-- λx. x, the term of an unknown operator: `Operator.literal` needs some term for it, and any
closed one serves, since `read` has no reading for an unknown constant and no proof reads this
one; it is closed, so substitution leaves it unchanged (`literalSubstitute`). -/
def unknownLiteral : Semantics.Term := .abstraction (.boundVariable 0)

/-- The term of an operator applied to the terms `values`: the application, choice or parallel
of the two values, or the thunk's interpretation `Readback.thunkTerm` under the values as its
fillings. An unknown operator gives `unknownLiteral`, and so does an operator of the first three
on other than two values, to which neither `curried` nor `read` applies it. -/
def Operator.literal : Operator → List Semantics.Term → Semantics.Term
  | .apply, [function, argument] => .application function argument
  | .choice, [left, right] => .choice left right
  | .parallel, [left, right] => .parallel left right
  | .thunk code holes, values => thunkTerm code holes values
  | _, _ => unknownLiteral

/-- The reading of an operator applied to the terms `values`, defined when the operator is known
and takes exactly that many arguments, and, for a thunk, where the readback's thunk clause is:
the readback of the code under the slot values that the fillings and the holes give
(`Readback.finalSlots`), under one abstraction per hole. -/
def Operator.readLiteral : Operator → List Semantics.Term → Option Semantics.Term
  | .apply, [function, argument] => some (.application function argument)
  | .choice, [left, right] => some (.choice left right)
  | .parallel, [left, right] => some (.parallel left right)
  | .thunk code holes, values =>
      if values.length = thunkArity code holes then
        (readbackCode (finalSlots holes values) code).map (abstractions holes.length)
      else none
  | _, _ => none

/-! ## The interpretation and the reading -/

/-- The bound variables of `count` enclosing abstractions, the outermost first: indices
`count - 1` down to 0. -/
def variablesBelow : Nat → List Semantics.Term
  | 0 => []
  | count + 1 => .boundVariable count :: variablesBelow count

/-- The curried form of an operator: its literal term over the bound variables of as many
abstractions as it takes arguments. `λx.λy. x y` for `apply`, the thunk's interpretation under
`arity` abstractions for a thunk constant. -/
def curried (operator : Operator) : Semantics.Term :=
  abstractions operator.arity (operator.literal (variablesBelow operator.arity))

/-- The terms of the calculus that HOL variables are read as, by name and type. -/
abbrev Valuation := Article.Name → Article.LogicType → Semantics.Term

/-- The total interpretation of an article term under a signature: a variable by the valuation, a
constant by the curried form of its operator, and a HOL application as an application. -/
def interpret (signature : Signature) (valuation : Valuation) : Article.Term → Semantics.Term
  | .termVariable name type => valuation name type
  | .constant name _ => curried (operatorOf signature name)
  | .application function argument =>
      .application (interpret signature valuation function)
        (interpret signature valuation argument)

/-- The reading of `term` applied to the readings `values` of further arguments: the arguments
are collected along the spine of HOL applications, and the head constant's operator reads them
(`Operator.readLiteral`). A variable has no reading. -/
def readApplied (signature : Signature) : Article.Term → List Semantics.Term → Option Semantics.Term
  | .termVariable _ _, _ => none
  | .constant name _, values => (operatorOf signature name).readLiteral values
  | .application function argument, values =>
      match readApplied signature argument [] with
      | some argumentTerm => readApplied signature function (argumentTerm :: values)
      | none => none

/-- The reading ⟦·⟧ of D10 of a closed article term in which every constant is applied to as
many arguments as it takes; `none` on any other term. -/
def read (signature : Signature) (term : Article.Term) : Option Semantics.Term :=
  readApplied signature term []

/-- `function` applied to `arguments` in order, the first innermost. -/
def applyAll : Semantics.Term → List Semantics.Term → Semantics.Term
  | function, [] => function
  | function, argument :: arguments => applyAll (.application function argument) arguments

/-- `head` applied by HOL application to `arguments` in order, the first innermost. -/
def applyArguments : Article.Term → List Article.Term → Article.Term
  | head, [] => head
  | head, argument :: arguments => applyArguments (.application head argument) arguments

/-- The head of a term's spine of HOL applications and the arguments along it, the first first. -/
def spine : Article.Term → Article.Term × List Article.Term
  | .application function argument =>
      match spine function with
      | (head, arguments) => (head, arguments ++ [argument])
  | term => (term, [])

/-! ## Facts about the interpretation -/

open Semantics (DerivableLatticeEta)

variable {hypotheses : Semantics.Term → Semantics.Term → Prop}

theorem applyAllCongruence : ∀ (arguments : List Semantics.Term) {left right : Semantics.Term},
    DerivableLatticeEta hypotheses left right →
      DerivableLatticeEta hypotheses (applyAll left arguments) (applyAll right arguments)
  | [], _, _, equal => equal
  | argument :: arguments, _, _, equal =>
      applyAllCongruence arguments (.congruenceFunction argument equal)

theorem interpretApplyArguments (signature : Signature) (valuation : Valuation) :
    ∀ (head : Article.Term) (arguments : List Article.Term),
      interpret signature valuation (applyArguments head arguments) =
        applyAll (interpret signature valuation head)
          (arguments.map (interpret signature valuation))
  | _, [] => rfl
  | head, argument :: arguments => by
      simp only [applyArguments, List.map_cons, applyAll]
      exact interpretApplyArguments signature valuation (.application head argument) arguments

theorem applyArgumentsAppend : ∀ (head : Article.Term) (arguments : List Article.Term)
    (argument : Article.Term),
    applyArguments head (arguments ++ [argument]) =
      .application (applyArguments head arguments) argument
  | _, [], _ => rfl
  | head, first :: arguments, argument =>
      applyArgumentsAppend (.application head first) arguments argument

/-- A term is its spine's head applied to its spine's arguments. -/
theorem applyArgumentsSpine : ∀ term : Article.Term,
    applyArguments (spine term).1 (spine term).2 = term
  | .application function argument => by
      have inner := applyArgumentsSpine function
      simp only [spine]
      rw [applyArgumentsAppend, inner]
  | .termVariable _ _ => rfl
  | .constant _ _ => rfl

/-- Raising every free index by one more than `count` times is raising those at or above `count`
after raising by `count`. -/
theorem shiftIterateSuccessor : ∀ (count : Nat) (term : Semantics.Term),
    shiftIterate (count + 1) term = Semantics.Term.shift (shiftIterate count term)
  | 0, _ => rfl
  | count + 1, term => shiftIterateSuccessor count (Semantics.Term.shift term)

theorem shiftIterateSuccessorFrom : ∀ (count : Nat) (term : Semantics.Term),
    shiftIterate (count + 1) term = Semantics.Term.shiftFrom count (shiftIterate count term)
  | 0, _ => rfl
  | count + 1, term =>
      calc shiftIterate (count + 1 + 1) term
          = Semantics.Term.shiftFrom 0 (shiftIterate (count + 1) term) :=
            shiftIterateSuccessor (count + 1) term
        _ = Semantics.Term.shiftFrom 0
              (Semantics.Term.shiftFrom count (shiftIterate count term)) := by
            rw [shiftIterateSuccessorFrom count term]
        _ = Semantics.Term.shiftFrom (count + 1)
              (Semantics.Term.shiftFrom 0 (shiftIterate count term)) :=
            Semantics.Term.shiftFromShiftFrom (shiftIterate count term) count 0 (Nat.zero_le count)
        _ = Semantics.Term.shiftFrom (count + 1) (shiftIterate (count + 1) term) := by
            rw [shiftIterateSuccessor count term]
            rfl

/-- Substituting at `count` into a term raised `count + 1` times removes one raise. -/
theorem substituteShiftIterate (count : Nat) (replacement term : Semantics.Term) :
    Semantics.Term.substitute count replacement (shiftIterate (count + 1) term) =
      shiftIterate count term := by
  rw [shiftIterateSuccessorFrom]
  exact Semantics.Term.substituteShiftFromCancel _ count replacement

theorem substituteVariablesBelow (depth : Nat) (replacement : Semantics.Term) :
    ∀ count, count ≤ depth →
      (variablesBelow count).map (Semantics.Term.substitute depth replacement) =
        variablesBelow count
  | 0, _ => rfl
  | count + 1, bounded => by
      have below : count < depth := by omega
      simp only [variablesBelow, List.map_cons, Semantics.Term.substitute, below, if_true,
        substituteVariablesBelow depth replacement count (by omega)]

/-- Substitution leaves `unknownLiteral` unchanged: it is closed. -/
theorem substituteUnknownLiteral (depth : Nat) (replacement : Semantics.Term) :
    Semantics.Term.substitute depth replacement unknownLiteral = unknownLiteral := by
  simp [unknownLiteral, Semantics.Term.substitute]

/-- Substitution passes into the literal term of every operator. -/
theorem literalSubstitute (depth : Nat) (replacement : Semantics.Term) :
    ∀ (operator : Operator) (values : List Semantics.Term),
      Semantics.Term.substitute depth replacement (operator.literal values) =
        operator.literal (values.map (Semantics.Term.substitute depth replacement))
  | .apply, [_, _] => rfl
  | .apply, [] => substituteUnknownLiteral depth replacement
  | .apply, [_] => substituteUnknownLiteral depth replacement
  | .apply, _ :: _ :: _ :: _ => substituteUnknownLiteral depth replacement
  | .choice, [_, _] => rfl
  | .choice, [] => substituteUnknownLiteral depth replacement
  | .choice, [_] => substituteUnknownLiteral depth replacement
  | .choice, _ :: _ :: _ :: _ => substituteUnknownLiteral depth replacement
  | .parallel, [_, _] => rfl
  | .parallel, [] => substituteUnknownLiteral depth replacement
  | .parallel, [_] => substituteUnknownLiteral depth replacement
  | .parallel, _ :: _ :: _ :: _ => substituteUnknownLiteral depth replacement
  | .unknown, _ => substituteUnknownLiteral depth replacement
  | .thunk code holes, values => Readback.thunkTermSubstitute code holes values depth replacement

/-- A term built from a list of values under as many abstractions as there are values, applied to
the values, generalised: when `build` commutes with substitution, and the values `before` are already
substituted for the outer abstractions, the remaining `count` values give `build` of all of them, by
one β step per value. The curried form of an operator (`curriedApplied`) and an article term with its
variables abstracted (module `StatementNormalisation`) are the two instances. -/
theorem abstractionsAppliedFrom (build : List Semantics.Term → Semantics.Term)
    (buildSubstitute : ∀ (depth : Nat) (replacement : Semantics.Term) (values : List Semantics.Term),
      Semantics.Term.substitute depth replacement (build values) =
        build (values.map (Semantics.Term.substitute depth replacement))) :
    ∀ (count : Nat) (before values : List Semantics.Term), values.length = count →
      DerivableLatticeEta hypotheses
        (applyAll (abstractions count
          (build (before.map (shiftIterate count) ++ variablesBelow count))) values)
        (build (before ++ values))
  | 0, before, [], _ => by
      have unshifted : before.map (shiftIterate 0) = before := by
        simp only [shiftIterate, List.map_id']
      simp only [abstractions, unshifted, variablesBelow, List.append_nil, applyAll]
      exact .reflexive _
  | count + 1, before, value :: values, length => by
      have remaining : values.length = count := by
        simp only [List.length_cons] at length
        omega
      have contracted :
          Semantics.Term.instantiate
              (abstractions count (build
                (before.map (shiftIterate (count + 1)) ++ variablesBelow (count + 1)))) value =
            abstractions count (build
              ((before ++ [value]).map (shiftIterate count) ++ variablesBelow count)) := by
        simp only [Semantics.Term.instantiate]
        rw [Readback.substituteAbstractions, Nat.zero_add, buildSubstitute, List.map_append,
          List.map_map]
        have shiftedBefore : before.map
            (Semantics.Term.substitute count (shiftIterate count value) ∘
              shiftIterate (count + 1)) = before.map (shiftIterate count) := by
          apply List.map_congr_left
          intro term _
          exact substituteShiftIterate count _ term
        have variables : (variablesBelow (count + 1)).map
            (Semantics.Term.substitute count (shiftIterate count value)) =
              shiftIterate count value :: variablesBelow count := by
          simp only [variablesBelow, List.map_cons, Semantics.Term.substitute, Nat.lt_irrefl,
            if_false, if_true, substituteVariablesBelow count _ count (Nat.le_refl count)]
        rw [shiftedBefore, variables, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.singleton_append]
      have step : DerivableLatticeEta hypotheses
          (.application (abstractions (count + 1) (build
            (before.map (shiftIterate (count + 1)) ++ variablesBelow (count + 1)))) value)
          (abstractions count (build
            ((before ++ [value]).map (shiftIterate count) ++ variablesBelow count))) := by
        rw [← contracted]
        exact .beta _ _
      have rest := abstractionsAppliedFrom build buildSubstitute count (before ++ [value]) values
        remaining
      rw [List.append_assoc, List.singleton_append] at rest
      exact .transitive (applyAllCongruence values step) rest

/-- The curried form of an operator applied to as many values as it takes arguments equals its
literal term on the values, by one β step per value. -/
theorem curriedApplied (operator : Operator) (values : List Semantics.Term)
    (length : values.length = operator.arity) :
    DerivableLatticeEta hypotheses (applyAll (curried operator) values) (operator.literal values) := by
  have general := abstractionsAppliedFrom (hypotheses := hypotheses) operator.literal
    (literalSubstitute · · operator) operator.arity [] values length
  simpa only [curried, List.map_nil, List.nil_append] using general

/-- The interpretation of an instance: interpreting the instance of `term` under an
instantiation is interpreting `term` under the valuation that interprets the instantiation's
images. A constant's type, which the instantiation changes, plays no part. -/
theorem interpretInstantiate (signature : Signature) (valuation : Valuation)
    (instantiation : Article.Instantiation) :
    ∀ term : Article.Term, interpret signature valuation (term.instantiate instantiation) =
      interpret signature
        (fun name type => interpret signature valuation (instantiation.termImage name type)) term
  | .termVariable _ _ => rfl
  | .constant _ _ => rfl
  | .application function argument => by
      simp only [Article.Term.instantiate, interpret,
        interpretInstantiate signature valuation instantiation function,
        interpretInstantiate signature valuation instantiation argument]

/-- A reading of an operator is its literal term, on as many values as it takes arguments. -/
theorem readLiteralSome : ∀ {operator : Operator} {values : List Semantics.Term}
    {term : Semantics.Term}, operator.readLiteral values = some term →
      values.length = operator.arity ∧ term = operator.literal values
  | .apply, [_, _], _, readBack => by
      simp only [Operator.readLiteral, Option.some.injEq] at readBack
      exact ⟨rfl, readBack.symm⟩
  | .choice, [_, _], _, readBack => by
      simp only [Operator.readLiteral, Option.some.injEq] at readBack
      exact ⟨rfl, readBack.symm⟩
  | .parallel, [_, _], _, readBack => by
      simp only [Operator.readLiteral, Option.some.injEq] at readBack
      exact ⟨rfl, readBack.symm⟩
  | .thunk code holes, values, term, readBack => by
      simp only [Operator.readLiteral] at readBack
      split at readBack
      · rename_i length
        cases bodyReadback : readbackCode (finalSlots holes values) code with
        | none => simp [bodyReadback] at readBack
        | some body =>
            simp only [bodyReadback, Option.map_some, Option.some.injEq] at readBack
            refine ⟨length, ?_⟩
            rw [← readBack]
            simp only [Operator.literal, thunkTerm,
              Readback.interpretCodeOfReadbackCode code _ body bodyReadback]
      · cases readBack
  | .apply, [], _, readBack | .apply, [_], _, readBack | .apply, _ :: _ :: _ :: _, _, readBack
  | .choice, [], _, readBack | .choice, [_], _, readBack | .choice, _ :: _ :: _ :: _, _, readBack
  | .parallel, [], _, readBack | .parallel, [_], _, readBack
  | .parallel, _ :: _ :: _ :: _, _, readBack
  | .unknown, _, _, readBack => by simp [Operator.readLiteral] at readBack

/-- Where the reading of `term` applied to `values` is defined, it equals the interpretation of
`term` applied to `values` by the β rule, under any hypotheses and any valuation. -/
theorem readAppliedDerivable (signature : Signature) (valuation : Valuation) :
    ∀ (term : Article.Term) (values : List Semantics.Term) (result : Semantics.Term),
      readApplied signature term values = some result →
        DerivableLatticeEta hypotheses (applyAll (interpret signature valuation term) values) result
  | .termVariable _ _, _, _, readBack => by simp [readApplied] at readBack
  | .constant name _, values, result, readBack => by
      simp only [readApplied] at readBack
      obtain ⟨length, equal⟩ := readLiteralSome readBack
      rw [equal]
      exact curriedApplied (operatorOf signature name) values length
  | .application function argument, values, result, readBack => by
      simp only [readApplied] at readBack
      split at readBack
      · rename_i argumentTerm argumentRead
        have argumentEqual :=
          readAppliedDerivable signature valuation argument [] argumentTerm argumentRead
        have functionEqual :=
          readAppliedDerivable signature valuation function (argumentTerm :: values) result
            readBack
        simp only [applyAll] at argumentEqual functionEqual
        exact .transitive
          (applyAllCongruence values (.congruenceArgument _ argumentEqual)) functionEqual
      · cases readBack

/-- Where the reading ⟦·⟧ of `term` is defined, it equals the interpretation of `term` by the β
rule, under any hypotheses and any valuation. -/
theorem readDerivable (signature : Signature) (valuation : Valuation) {term : Article.Term}
    {result : Semantics.Term} (readBack : read signature term = some result) :
    DerivableLatticeEta hypotheses (interpret signature valuation term) result :=
  readAppliedDerivable signature valuation term [] result readBack

/-- The interpretation of `term` applied to `values`, each constant applied to as many arguments as
it takes read by its operator (`Operator.readLiteral`), as `read` reads it, and any other constant
curried, a variable by the valuation: `interpret`'s term with the β redexes of its fully applied
constants contracted (`interpretReadingDerivable`). A decision that reads a statement this way
does not contract those redexes itself: measured 2026-11-19, the right side of the native route's
`even_scheme` is 34,064 nodes interpreted and 11,713 read this way, simplified both. -/
def interpretReading (signature : Signature) (valuation : Valuation) :
    Article.Term → List Semantics.Term → Semantics.Term
  | .termVariable name type, values => applyAll (valuation name type) values
  | .constant name _, values =>
      match (operatorOf signature name).readLiteral values with
      | some read => read
      | none => applyAll (curried (operatorOf signature name)) values
  | .application function argument, values =>
      interpretReading signature valuation function (interpretReading signature valuation argument [] :: values)

/-- `interpretReading` of `term` on `values` equals the interpretation of `term` applied to
`values` by the β rule, under any hypotheses and any valuation. -/
theorem interpretReadingDerivable (signature : Signature) (valuation : Valuation) :
    ∀ (term : Article.Term) (values : List Semantics.Term),
      DerivableLatticeEta hypotheses (applyAll (interpret signature valuation term) values)
        (interpretReading signature valuation term values)
  | .termVariable _ _, values => by
      simp only [interpret, interpretReading]
      exact .reflexive _
  | .constant name _, values => by
      simp only [interpret, interpretReading]
      split
      · rename_i read readBack
        obtain ⟨length, equal⟩ := readLiteralSome readBack
        rw [equal]
        exact curriedApplied (operatorOf signature name) values length
      · exact .reflexive _
  | .application function argument, values => by
      simp only [interpret, interpretReading]
      have argumentEqual := interpretReadingDerivable signature valuation argument []
      have functionEqual := interpretReadingDerivable signature valuation function
        (interpretReading signature valuation argument [] :: values)
      simp only [applyAll] at argumentEqual functionEqual
      exact .transitive (applyAllCongruence values (.congruenceArgument _ argumentEqual)) functionEqual

/-- The curried form of an operator is closed: substitution leaves it as it is, since it reads
only the variables of its own abstractions. -/
theorem substituteCurried (depth : Nat) (replacement : Semantics.Term) (operator : Operator) :
    Semantics.Term.substitute depth replacement (curried operator) = curried operator := by
  simp only [curried]
  rw [Readback.substituteAbstractions, literalSubstitute,
    substituteVariablesBelow _ _ operator.arity (Nat.le_add_left _ _)]

/-- Substitution passes into the interpretation: substituting into the interpretation of `term` is
interpreting `term` under the valuation substituted into. -/
theorem substituteInterpret (signature : Signature) (depth : Nat) (replacement : Semantics.Term)
    (valuation : Valuation) :
    ∀ term : Article.Term,
      Semantics.Term.substitute depth replacement (interpret signature valuation term) =
        interpret signature
          (fun name type => Semantics.Term.substitute depth replacement (valuation name type)) term
  | .termVariable _ _ => rfl
  | .constant name _ => substituteCurried depth replacement (operatorOf signature name)
  | .application function argument => by
      simp only [interpret, Semantics.Term.substitute,
        substituteInterpret signature depth replacement valuation function,
        substituteInterpret signature depth replacement valuation argument]

/-- The variables of an article term, by name and type, from left to right, with repetitions. -/
def termVariables : Article.Term → List (Article.Name × Article.LogicType)
  | .termVariable name type => [(name, type)]
  | .constant _ _ => []
  | .application function argument => termVariables function ++ termVariables argument

/-- The interpretation of a term depends only on the valuation of its variables: two valuations
that agree on every variable of `term` interpret it as one term. -/
theorem interpretAgree {signature : Signature} {first second : Valuation} :
    ∀ term : Article.Term,
      (∀ occurrence ∈ termVariables term,
        first occurrence.1 occurrence.2 = second occurrence.1 occurrence.2) →
        interpret signature first term = interpret signature second term
  | .termVariable name type, agree => agree (name, type) (List.mem_singleton_self _)
  | .constant _ _, _ => rfl
  | .application function argument, agree => by
      simp only [interpret]
      rw [interpretAgree function
          (fun occurrence member => agree occurrence (List.mem_append_left _ member)),
        interpretAgree argument
          (fun occurrence member => agree occurrence (List.mem_append_right _ member))]

/-! ## Terms that agree under two signatures

An article and a statement number their thunk constants each from 0 (D7.1), so the same thunk has
a name in one and another name in the other. Two terms agree under their two signatures when they
have one shape, the same variables, and constants with the same operator; agreeing terms are
interpreted as one term under every valuation (`interpretOfAgree`). The check walks the two terms
once, comparing a pair of thunk constants by `Code.equal` on their codes. -/

/-- Whether two operators are the same: the three fixed ones and `unknown` by their constructors,
two thunk operators by their codes (`Code.equal`) and their holes. -/
def Operator.same : Operator → Operator → Bool
  | .apply, .apply | .choice, .choice | .parallel, .parallel
  | .unknown, .unknown => true
  | .thunk code holes, .thunk otherCode otherHoles => code.equal otherCode && holes == otherHoles
  | _, _ => false

theorem Operator.equal_of_same : ∀ {first second : Operator}, first.same second = true →
    first = second
  | .apply, .apply, _ | .choice, .choice, _ | .parallel, .parallel, _
  | .unknown, .unknown, _ => rfl
  | .thunk code holes, .thunk otherCode otherHoles, same => by
      simp only [Operator.same, Bool.and_eq_true, beq_iff_eq] at same
      rw [Code.equality_of_equal same.1, same.2]
  | .apply, .choice, same | .apply, .parallel, same
  | .apply, .thunk _ _, same | .apply, .unknown, same
  | .choice, .apply, same | .choice, .parallel, same
  | .choice, .thunk _ _, same | .choice, .unknown, same
  | .parallel, .apply, same | .parallel, .choice, same
  | .parallel, .thunk _ _, same | .parallel, .unknown, same
  | .thunk _ _, .apply, same | .thunk _ _, .choice, same | .thunk _ _, .parallel, same
  | .thunk _ _, .unknown, same
  | .unknown, .apply, same | .unknown, .choice, same | .unknown, .parallel, same
  | .unknown, .thunk _ _, same => by
      simp [Operator.same] at same

/-- Whether `left` under the signature `first` and `right` under `second` agree: the same
variable, constants whose operators are the same (`Operator.same`), or applications whose
functions agree and whose arguments agree. A constant's type plays no part, as in `interpret`. -/
def agree (first second : Signature) : Article.Term → Article.Term → Bool
  | .termVariable name type, .termVariable otherName otherType =>
      name == otherName && type == otherType
  | .constant name _, .constant otherName _ =>
      (operatorOf first name).same (operatorOf second otherName)
  | .application function argument, .application otherFunction otherArgument =>
      agree first second function otherFunction && agree first second argument otherArgument
  | _, _ => false

/-- Terms that agree under two signatures are interpreted as one term under every valuation. -/
theorem interpretOfAgree {first second : Signature} (valuation : Valuation) :
    ∀ {left right : Article.Term}, agree first second left right = true →
      interpret first valuation left = interpret second valuation right
  | .termVariable name type, .termVariable otherName otherType, agreeing => by
      simp only [agree, Bool.and_eq_true, beq_iff_eq] at agreeing
      rw [agreeing.1, agreeing.2]
      rfl
  | .constant name _, .constant otherName _, agreeing => by
      simp only [agree] at agreeing
      simp only [interpret, Operator.equal_of_same agreeing]
  | .application function argument, .application otherFunction otherArgument, agreeing => by
      simp only [agree, Bool.and_eq_true] at agreeing
      simp only [interpret, interpretOfAgree valuation agreeing.1,
        interpretOfAgree valuation agreeing.2]
  | .termVariable _ _, .constant _ _, agreeing | .termVariable _ _, .application _ _, agreeing
  | .constant _ _, .termVariable _ _, agreeing | .constant _ _, .application _ _, agreeing
  | .application _ _, .termVariable _ _, agreeing | .application _ _, .constant _ _, agreeing => by
      simp [agree] at agreeing

end LambdaJit.Interpretation
