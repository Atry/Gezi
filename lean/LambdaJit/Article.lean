/-!
# The OpenTheory article reader

The trace of design decision D7 is an OpenTheory
article: a text of commands for a stack machine, format version 6
(https://www.gilith.com/opentheory/article.html, "the specification" below). Reading an article
yields an import set, the assumptions that its `axiom` commands add, and an export set, the
theorems that its `thm` commands add; the article is a proof that the exports follow from the
imports.

This module reads the fragment of the format that D7 uses and proves that what it accepts is
sound. The trusted part is the reader, the definitions up to `readArticle`, where each command's
meaning is written next to the specification's stack effect for it, and the definitions that the
statement of `readArticle_sound` uses: `Instantiation`, `Term.instantiate`, `importEquations`,
`Derivable`, `Object.Contains` and `MachineState.Holds`. The rest is proof, checked by Lean's
kernel.

The fragment:

- Types are type variables and type operators applied to argument types; terms are variables,
  constants at a type, and applications. There is no abstraction, so no variable is bound and the
  specification's α-equivalence of terms is equality.
- Every type operator is external (there is no `defineTypeOp`), and so is every constant but those
  `defineConst` defines (there is no `defineConstList`): each is its name, and no two different
  ones can share a name. `defineConst` records the name with its defining term in the theory's
  definitions (design decision D7.1: a thunk constant's
  code is its defining term), and the theorem `⊦ c = t` it pushes is an object that no inference
  reads (`Object.definition`): only `pop`, `def`, `ref` and `remove` move it. A name defined twice
  is a rejection.
- There is no `varType`, so no type variable arises in an accepted article: the type
  instantiation of `subst` is implemented as the specification says, and it is the identity on
  every type the reader builds.
- Equality is the constant `=` at a type `a → a → bool`; a theorem is an equation between two
  terms of the same type `a`.
- The reader runs exactly these commands: numbers, names, `version`, `typeOp`, `opType`, `const`,
  `constTerm`, `var`, `varTerm`, `appTerm`, `refl`, `sym`, `trans`, `appThm`, `subst`, `axiom`,
  `thm`, `defineConst`, `def`, `ref`, `remove`, `pop`, `nil` and `cons`. Any other command, a type error, a stack
  that does not hold what a command pops, a theorem with hypotheses and a theorem that is not an
  equation are rejections, each with its reason.

Choices where the specification leaves the reading open:

- `version`: the specification says it may only be the very first command, and it pops a number,
  so the article must begin with the command lines `6` and `version`; an article without them is
  of version 5 and rejected, and `version` anywhere else is rejected.
- `axiom` and `thm`: the hypothesis list must be empty. The specification lets `thm` claim more
  hypotheses than the theorem has; this reader exports only theorems without hypotheses.
- `subst`: each replacement term must have the type of its variable (HOL's instantiation rule;
  the specification states no constraint), and no type variable or term variable may be
  instantiated twice in one substitution (the specification does not say which entry wins).
- `opType`: `bool` takes no argument and `->` takes two (the arities the specification gives); an
  external type operator takes any number, the specification giving it no arity.
- `constTerm`: the constant `=` must be at a type `a → a → bool`, an instance of its principal
  type; the specification gives no constraint for `constTerm`.
- Lines: the text is split at newline characters, a final newline ends the last line, and every
  line that does not begin with `#` must be a command (an empty line is rejected). A line is taken
  apart as the characters that `characters` decodes from its UTF-8 bytes, which are its
  `String.toList` (`characters_eq_toList`), and a component of a name is built by `ofCharacters`,
  which is `String.ofList` (`ofCharacters_eq_ofList`): `String.toList` decodes by byte position and
  `String.ofList` pushes one byte at a time, which Lean's kernel evaluates in time quadratic in the
  length of the string, while `characters` walks the list of bytes once and `ofCharacters` holds its
  bytes as a list. The bytes of a string literal still come through `List.toByteArray`.

Soundness (`readArticle_sound`): when the reader accepts a text, every exported theorem has no
hypotheses and is an equation `left = right` with `Derivable imports left right`, where the
import set is the list of equations of the `axiom` commands read and `Derivable` is the least
relation that contains every instance of every import equation and is closed under reflexivity,
symmetry, transitivity and congruence of application; every assumption is an equation without
hypotheses; and every theorem the machine holds in any state it reaches has no hypotheses.
`Derivable` is untyped: the reader checks the types where the specification asks, and the theorem
does not restate them.
-/

namespace LambdaJit.Article

/-! ## Names, types and terms -/

/-- A name of the article format, the specification's `string list * string`: a namespace, the
list of its components from the outermost, and a local name. `bool` is `⟨[], "bool"⟩` and
`LambdaJit.term` is `⟨["LambdaJit"], "term"⟩`; a name whose namespace is empty is in the global
namespace. -/
structure Name where
  /-- The namespace, its components from the outermost. -/
  namespaceComponents : List String
  /-- The local name. -/
  localName : String
  deriving Repr

/-- Whether two names are equal, compared component by component with the Boolean equalities of
`List String` and `String`. -/
def Name.equal (first second : Name) : Bool :=
  first.namespaceComponents == second.namespaceComponents && first.localName == second.localName

theorem Name.equal_iff {first second : Name} : first.equal second = true ↔ first = second := by
  cases first
  cases second
  simp [Name.equal]

/-- The decision of the equality of names by `Name.equal`, which the kernel evaluates when it
decides an equality of names, as the reader and the checks of the articles do on every constant
and every definition. The decision that `deriving DecidableEq` writes cost far more in the kernel:
on the article of identity_zero_type_check (4162 lines), `Lean.Kernel.whnf` of `readLines` took
82,696,700 heartbeats with it, 23,211,766 without the reader's check that a name is not defined
twice, and 23,896,965 with that check written by the Boolean equalities of the components; on
successor_zero_type_check (8750 lines), 452,489,791 and 138,884,219 with and without the derived
decision in that check (measured 2026-11-21). -/
instance : DecidableEq Name := fun first second =>
  decidable_of_iff (first.equal second = true) Name.equal_iff

/-- The name of the primitive Boolean type operator, of arity 0. -/
def booleanName : Name := ⟨[], "bool"⟩

/-- The name of the primitive function space type operator, of arity 2. -/
def arrowName : Name := ⟨[], "->"⟩

/-- The name of the primitive equality constant, of principal type `a → a → bool`. -/
def equalityName : Name := ⟨[], "="⟩

/-- A type of higher order logic: a type variable, or a type operator applied to argument types,
the specification's `(ty1, ..., tyn) op`. A type operator is its name, every type operator being
external. -/
inductive LogicType where
  /-- The type variable named `name`. -/
  | typeVariable (name : Name)
  /-- The type operator named `name` applied to `arguments`. -/
  | operator (name : Name) (arguments : List LogicType)
  deriving Repr

mutual
/-- Decides the equality of two types. -/
def LogicType.decideEqual : (left right : LogicType) → Decidable (left = right)
  | .typeVariable leftName, .typeVariable rightName =>
      if equal : leftName = rightName then isTrue (equal ▸ rfl)
      else isFalse (fun same => by cases same; exact equal rfl)
  | .operator leftName leftArguments, .operator rightName rightArguments =>
      if equal : leftName = rightName then
        match LogicType.decideEqualList leftArguments rightArguments with
        | isTrue argumentsEqual => isTrue (equal ▸ argumentsEqual ▸ rfl)
        | isFalse argumentsDiffer =>
            isFalse (fun same => by cases same; exact argumentsDiffer rfl)
      else isFalse (fun same => by cases same; exact equal rfl)
  | .typeVariable _, .operator _ _ => isFalse (fun same => by cases same)
  | .operator _ _, .typeVariable _ => isFalse (fun same => by cases same)

/-- Decides the equality of two lists of types. -/
def LogicType.decideEqualList : (left right : List LogicType) → Decidable (left = right)
  | [], [] => isTrue rfl
  | leftHead :: leftTail, rightHead :: rightTail =>
      match LogicType.decideEqual leftHead rightHead,
          LogicType.decideEqualList leftTail rightTail with
      | isTrue headEqual, isTrue tailEqual => isTrue (headEqual ▸ tailEqual ▸ rfl)
      | isFalse headDiffers, _ => isFalse (fun same => by cases same; exact headDiffers rfl)
      | _, isFalse tailDiffers => isFalse (fun same => by cases same; exact tailDiffers rfl)
  | [], _ :: _ => isFalse (fun same => by cases same)
  | _ :: _, [] => isFalse (fun same => by cases same)
end

instance : DecidableEq LogicType := LogicType.decideEqual

/-- The type `bool`. -/
def LogicType.boolean : LogicType := .operator booleanName []

/-- The function type `domain → range`. -/
def LogicType.arrow (domain range : LogicType) : LogicType := .operator arrowName [domain, range]

/-- The type `sideType → sideType → bool` of the equality constant between terms of type
`sideType`. -/
def LogicType.equality (sideType : LogicType) : LogicType :=
  .arrow sideType (.arrow sideType .boolean)

/-- Whether `type` is `sideType → sideType → bool` for some `sideType`: an instance of the
principal type of `=`. -/
def LogicType.isEqualityType (type : LogicType) : Bool :=
  match type with
  | .operator _ (sideType :: _) => decide (type = .equality sideType)
  | _ => false

mutual
/-- `type.instantiate typeImage`: every type variable of `type`, named `name`, replaced by
`typeImage name`. -/
def LogicType.instantiate (typeImage : Name → LogicType) : LogicType → LogicType
  | .typeVariable name => typeImage name
  | .operator name arguments => .operator name (LogicType.instantiateList typeImage arguments)

/-- `LogicType.instantiate` on every type of a list. -/
def LogicType.instantiateList (typeImage : Name → LogicType) : List LogicType → List LogicType
  | [] => []
  | head :: tail => head.instantiate typeImage :: LogicType.instantiateList typeImage tail
end

/-- A term of the fragment: a term variable, a constant at a type, or an application. -/
inductive Term where
  /-- The term variable named `name` of type `type`; two variables with the same name and
  different types are different variables. -/
  | termVariable (name : Name) (type : LogicType)
  /-- The constant named `name` at the type `type`. -/
  | constant (name : Name) (type : LogicType)
  /-- The application of `function` to `argument`. -/
  | application (function argument : Term)
  deriving Repr

/-- Whether two terms are equal, compared node by node with `Name.equal` and the decision of the
equality of types. -/
def Term.equal : Term → Term → Bool
  | .termVariable firstName firstType, .termVariable secondName secondType =>
      firstName.equal secondName && decide (firstType = secondType)
  | .constant firstName firstType, .constant secondName secondType =>
      firstName.equal secondName && decide (firstType = secondType)
  | .application firstFunction firstArgument, .application secondFunction secondArgument =>
      firstFunction.equal secondFunction && firstArgument.equal secondArgument
  | .termVariable _ _, .constant _ _ => false
  | .termVariable _ _, .application _ _ => false
  | .constant _ _, .termVariable _ _ => false
  | .constant _ _, .application _ _ => false
  | .application _ _, .termVariable _ _ => false
  | .application _ _, .constant _ _ => false

theorem Term.equal_iff : ∀ {first second : Term}, first.equal second = true ↔ first = second
  | .termVariable _ _, .termVariable _ _ => by simp [Term.equal, Name.equal_iff]
  | .constant _ _, .constant _ _ => by simp [Term.equal, Name.equal_iff]
  | .application firstFunction firstArgument, .application secondFunction secondArgument => by
      simp [Term.equal, Term.equal_iff (first := firstFunction) (second := secondFunction),
        Term.equal_iff (first := firstArgument) (second := secondArgument)]
  | .termVariable _ _, .constant _ _ => by simp [Term.equal]
  | .termVariable _ _, .application _ _ => by simp [Term.equal]
  | .constant _ _, .termVariable _ _ => by simp [Term.equal]
  | .constant _ _, .application _ _ => by simp [Term.equal]
  | .application _ _, .termVariable _ _ => by simp [Term.equal]
  | .application _ _, .constant _ _ => by simp [Term.equal]

/-- The decision of the equality of terms by `Term.equal`, which the kernel evaluates on every
equation an article's proof commands compare, in place of the decision that `deriving DecidableEq`
writes: with the decision of names by `Name.equal` in both, `Lean.Kernel.whnf` of `readLines` took
23,704,798 heartbeats with the derived decision and 23,246,773 with this one on
identity_zero_type_check, and 121,045,304 and 100,177,279 on successor_zero_type_check, whose
article has the proof commands of 14 lemma instances; `lake build` of the package on 4 CPUs built
module `FixpointRunFixtures` in 246 s and 188 s (measured 2026-11-21, machine load 5 to 18). -/
instance : DecidableEq Term := fun first second =>
  decidable_of_iff (first.equal second = true) Term.equal_iff

/-- The type of a term, `none` when the term is ill-typed: a variable and a constant have the type
they carry, and `function argument` has type `τ` when `function` has type `σ → τ` and `argument`
has type `σ`, the constraint of `appTerm`. -/
def Term.typeOf : Term → Option LogicType
  | .termVariable _ type => some type
  | .constant _ type => some type
  | .application function argument =>
      match function.typeOf, argument.typeOf with
      | some (.operator name [domain, range]), some argumentType =>
          if name = arrowName ∧ domain = argumentType then some range else none
      | _, _ => none

/-- The equation `left = right` between terms of type `sideType`: the constant `=` at
`sideType → sideType → bool` applied to `left`, and the result applied to `right`. -/
def Term.equation (sideType : LogicType) (left right : Term) : Term :=
  .application (.application (.constant equalityName (.equality sideType)) left) right

/-- The sides of an equation: `some (sideType, left, right)` when `term` is
`Term.equation sideType left right`, and `none` when `term` is no equation. -/
def Term.equationSides? (term : Term) : Option (LogicType × Term × Term) :=
  match term with
  | .application (.application (.constant _ (.operator _ (sideType :: _))) left) right =>
      if term = .equation sideType left right then some (sideType, left, right) else none
  | _ => none

/-- A theorem `Γ ⊦ φ`, the specification's `thm`: the hypotheses `Γ`, a set written as a list,
and the conclusion `φ`. -/
structure Sequent where
  /-- The hypotheses. -/
  hypotheses : List Term
  /-- The conclusion. -/
  conclusion : Term
  deriving DecidableEq, Repr

/-! ## The virtual machine -/

/-- An object of the virtual machine, the specification's datatype `object`. -/
inductive Object where
  /-- `Num i`. -/
  | number (value : Int)
  /-- `Name n`. -/
  | name (value : Name)
  /-- `List l`. -/
  | list (elements : List Object)
  /-- `TypeOp op`, an external type operator, which is its name. -/
  | typeOperator (name : Name)
  /-- `Type ty`. -/
  | type (value : LogicType)
  /-- `Const c`, an external constant, which is its name. -/
  | constant (name : Name)
  /-- `Var v`, the term variable named `name` of type `type`. -/
  | termVariable (name : Name) (type : LogicType)
  /-- `Term t`. -/
  | term (value : Term)
  /-- `Thm th`. -/
  | sequent (value : Sequent)
  /-- The theorem `⊦ c = t` that `defineConst` pushes for the constant `name` and its defining
  term `value`: an object that no inference reads, so it contains no theorem. -/
  | definition (name : Name) (value : Term)
  deriving Repr

/-- A command of the fragment. The constructors spell out the specification's command names:
`typeOp` is `typeOperator`, `opType` is `operatorType`, `const` is `constant`, `constTerm` is
`constantTerm`, `var` is `termVariable`, `varTerm` is `variableTerm`, `appTerm` is
`applicationTerm`, `refl` is `reflexivity`, `sym` is `symmetry`, `trans` is `transitivity`,
`appThm` is `applicationTheorem`, `subst` is `substitution`, `axiom` is `importAxiom`, `thm` is
`exportTheorem`, `defineConst` is `defineConstant`, `def` is `define` and `ref` is `reference`. -/
inductive Command where
  /-- A number command `i`. -/
  | number (value : Int)
  /-- A name command `"s"`. -/
  | name (value : Name)
  | version
  | typeOperator
  | operatorType
  | constant
  | constantTerm
  | termVariable
  | variableTerm
  | applicationTerm
  | reflexivity
  | symmetry
  | transitivity
  | applicationTheorem
  | substitution
  | importAxiom
  | exportTheorem
  | defineConstant
  | define
  | reference
  | remove
  | pop
  | nil
  | cons
  deriving DecidableEq, Repr

/-- The state of the virtual machine: the stack, its top first; the dictionary, with at most one
entry per key; the assumptions, the theorems the `axiom` commands added, in order; and the
theorems the `thm` commands added, in order. The specification's assumptions and theorems are
sets; lists keep the article's order. The dictionary is a list, so a lookup takes time linear in
its size. -/
structure MachineState where
  /-- The stack, its top first. -/
  stack : List Object
  /-- The dictionary, at most one entry per key. -/
  dictionary : List (Int × Object)
  /-- The assumptions. -/
  assumptions : List Sequent
  /-- The theorems. -/
  theorems : List Sequent
  /-- The constants `defineConst` defined, each with its defining term, in order. -/
  definitions : List (Name × Term)

/-- The initial state: the stack, the dictionary, the assumptions, the theorems and the
definitions are empty. -/
def MachineState.initial : MachineState := ⟨[], [], [], [], []⟩

/-- The value of the first entry of `entries` whose key is `key`. -/
def lookupFirst {Key Value : Type} [DecidableEq Key] (key : Key) :
    List (Key × Value) → Option Value
  | [] => none
  | (entryKey, value) :: rest => if entryKey = key then some value else lookupFirst key rest

/-- The types of a list of objects that are all types; `none` when one of them is not a type. -/
def objectTypes : List Object → Option (List LogicType)
  | [] => some []
  | .type type :: rest => (objectTypes rest).map (type :: ·)
  | _ :: _ => none

/-- Whether the type operator named `name` may take `count` arguments: `bool` takes none and `->`
two; the specification gives no arity for an external type operator, so it takes any number. -/
def arityAccepted (name : Name) (count : Nat) : Bool :=
  if name = booleanName then count = 0 else if name = arrowName then count = 2 else true

/-- The type substitution `[ty1/α1, ..., tym/αm]` of a `subst` command, from its objects
`List [Name αi, Type tyi]`; rejected when an object has another shape or a name `αi` is not in the
global namespace. -/
def typeSubstitution : List Object → Except String (List (Name × LogicType))
  | [] => .ok []
  | .list [.name name, .type type] :: rest =>
      if name.namespaceComponents = [] then (typeSubstitution rest).map ((name, type) :: ·)
      else .error "subst: a type variable's name is not in the global namespace"
  | _ :: _ => .error "subst: a type entry is not a list of a name and a type"

/-- The term substitution `[t1/v1, ..., tn/vn]` of a `subst` command, from its objects
`List [Var vi, Term ti]`, each variable as its name and type; rejected when an object has another
shape or a term `ti` does not have the type of the variable `vi`. -/
def termSubstitution : List Object → Except String (List ((Name × LogicType) × Term))
  | [] => .ok []
  | .list [.termVariable name type, .term term] :: rest =>
      if term.typeOf = some type then (termSubstitution rest).map (((name, type), term) :: ·)
      else .error "subst: a replacement term does not have the type of its variable"
  | _ :: _ => .error "subst: a term entry is not a list of a variable and a term"

/-- The image of the type variable `name` under the type substitution `types`: `tyi` when `name`
is `αi`, the type variable itself otherwise. -/
def typeImageOf (types : List (Name × LogicType)) (name : Name) : LogicType :=
  (lookupFirst name types).getD (.typeVariable name)

/-- The type instantiation of a term: the type of every variable and every constant instantiated
by `typeImage`. -/
def Term.instantiateTypes (typeImage : Name → LogicType) : Term → Term
  | .termVariable name type => .termVariable name (type.instantiate typeImage)
  | .constant name type => .constant name (type.instantiate typeImage)
  | .application function argument =>
      .application (function.instantiateTypes typeImage) (argument.instantiateTypes typeImage)

/-- The term instantiation of a term: every occurrence of a variable `vi` replaced by `ti`. There
is no abstraction in the fragment, so every occurrence is free and nothing is renamed. -/
def Term.substituteVariables (terms : List ((Name × LogicType) × Term)) : Term → Term
  | .termVariable name type => (lookupFirst (name, type) terms).getD (.termVariable name type)
  | .constant name type => .constant name type
  | .application function argument =>
      .application (function.substituteVariables terms) (argument.substituteVariables terms)

/-- `(φ[ty1/α1, ..., tym/αm])[t1/v1, ..., tn/vn]`: the instance of a term under the substitution
of a `subst` command, its type variables first and its term variables second. -/
def Term.substitute (types : List (Name × LogicType)) (terms : List ((Name × LogicType) × Term))
    (term : Term) : Term :=
  (term.instantiateTypes (typeImageOf types)).substituteVariables terms

/-- Whether a term has no term variable: a closed term, the specification's constraint on the
defining term of `defineConst`. -/
def Term.closed : Term → Bool
  | .termVariable _ _ => false
  | .constant _ _ => true
  | .application function argument => function.closed && argument.closed

/-- One command on the machine state; `.error` with the reason when the command is rejected. Each
case quotes the specification's stack effect; a stack is written with its top first. -/
def step (state : MachineState) : Command → Except String MachineState
  -- Before: stack. After: Num i :: stack.
  | .number value => .ok { state with stack := .number value :: state.stack }
  -- Before: stack. After: Name n :: stack.
  | .name value => .ok { state with stack := .name value :: state.stack }
  -- `readArticle` reads the version command at the head of the article.
  | .version => .error "version may only occur as the very first command"
  -- Before: Name n :: stack. After: TypeOp op :: stack, op the external type operator named n.
  | .typeOperator =>
      match state.stack with
      | .name name :: rest => .ok { state with stack := .typeOperator name :: rest }
      | _ => .error "typeOp: the stack does not begin with a name"
  -- Before: List [Type ty1, ..., Type tyn] :: TypeOp op :: stack.
  -- After: Type ((ty1, ..., tyn) op) :: stack.
  | .operatorType =>
      match state.stack with
      | .list elements :: .typeOperator name :: rest =>
          match objectTypes elements with
          | some arguments =>
              if arityAccepted name arguments.length then
                .ok { state with stack := .type (.operator name arguments) :: rest }
              else .error "opType: bool takes no argument and -> takes two"
          | none => .error "opType: the list holds an object that is not a type"
      | _ => .error "opType: the stack does not begin with a list and a type operator"
  -- Before: Name n :: stack. After: Const c :: stack, c the external constant named n.
  | .constant =>
      match state.stack with
      | .name name :: rest => .ok { state with stack := .constant name :: rest }
      | _ => .error "const: the stack does not begin with a name"
  -- Before: Type ty :: Const c :: stack. After: Term t :: stack, t the constant c at type ty.
  | .constantTerm =>
      match state.stack with
      | .type type :: .constant name :: rest =>
          if name = equalityName ∧ type.isEqualityType = false then
            .error "constTerm: the constant = takes a type a -> a -> bool"
          else .ok { state with stack := .term (.constant name type) :: rest }
      | _ => .error "constTerm: the stack does not begin with a type and a constant"
  -- Before: Type ty :: Name n :: stack. After: Var v :: stack, v named n of type ty.
  -- Constraint: n is in the global namespace.
  | .termVariable =>
      match state.stack with
      | .type type :: .name name :: rest =>
          if name.namespaceComponents = [] then
            .ok { state with stack := .termVariable name type :: rest }
          else .error "var: the name is not in the global namespace"
      | _ => .error "var: the stack does not begin with a type and a name"
  -- Before: Var v :: stack. After: Term t :: stack, t the variable v.
  | .variableTerm =>
      match state.stack with
      | .termVariable name type :: rest =>
          .ok { state with stack := .term (.termVariable name type) :: rest }
      | _ => .error "varTerm: the stack does not begin with a variable"
  -- Before: Term x :: Term f :: stack. After: Term (f x) :: stack.
  -- Constraint: f has a type σ → τ and x has type σ.
  | .applicationTerm =>
      match state.stack with
      | .term argument :: .term function :: rest =>
          match (Term.application function argument).typeOf with
          | some _ => .ok { state with stack := .term (.application function argument) :: rest }
          | none => .error "appTerm: the function's type is not an arrow from the argument's type"
      | _ => .error "appTerm: the stack does not begin with two terms"
  -- Before: Term t :: stack. After: Thm (⊦ t = t) :: stack.
  | .reflexivity =>
      match state.stack with
      | .term term :: rest =>
          match term.typeOf with
          | some type => .ok { state with stack := .sequent ⟨[], .equation type term term⟩ :: rest }
          | none => .error "refl: the term is ill-typed"
      | _ => .error "refl: the stack does not begin with a term"
  -- Before: Thm (Γ ⊦ t = u) :: stack. After: Thm (Γ ⊦ u = t) :: stack.
  | .symmetry =>
      match state.stack with
      | .sequent sequent :: rest =>
          match sequent.conclusion.equationSides? with
          | some (type, left, right) =>
              .ok { state with
                stack := .sequent ⟨sequent.hypotheses, .equation type right left⟩ :: rest }
          | none => .error "sym: the theorem is not an equation"
      | _ => .error "sym: the stack does not begin with a theorem"
  -- Before: Thm (Δ ⊦ t2' = t3) :: Thm (Γ ⊦ t1 = t2) :: stack.
  -- After: Thm (Γ ∪ Δ ⊦ t1 = t3) :: stack. Constraint: t2 and t2' are α-equivalent, that is equal.
  | .transitivity =>
      match state.stack with
      | .sequent second :: .sequent first :: rest =>
          match first.conclusion.equationSides?, second.conclusion.equationSides? with
          | some (type, left, firstRight), some (_, secondLeft, right) =>
              if firstRight = secondLeft then
                .ok { state with
                  stack := .sequent ⟨first.hypotheses ++ second.hypotheses,
                    .equation type left right⟩ :: rest }
              else .error "trans: the middle terms differ"
          | _, _ => .error "trans: a theorem is not an equation"
      | _ => .error "trans: the stack does not begin with two theorems"
  -- Before: Thm (Δ ⊦ x = y) :: Thm (Γ ⊦ f = g) :: stack. After: Thm (Γ ∪ Δ ⊦ f x = g y) :: stack.
  -- Constraint: f has a type σ → τ and x has type σ.
  | .applicationTheorem =>
      match state.stack with
      | .sequent argumentSequent :: .sequent functionSequent :: rest =>
          match functionSequent.conclusion.equationSides?,
              argumentSequent.conclusion.equationSides? with
          | some (_, leftFunction, rightFunction), some (_, leftArgument, rightArgument) =>
              match (Term.application leftFunction leftArgument).typeOf with
              | some type =>
                  .ok { state with
                    stack := .sequent ⟨functionSequent.hypotheses ++ argumentSequent.hypotheses,
                      .equation type (.application leftFunction leftArgument)
                        (.application rightFunction rightArgument)⟩ :: rest }
              | none =>
                  .error "appThm: the function's type is not an arrow from the argument's type"
          | _, _ => .error "appThm: a theorem is not an equation"
      | _ => .error "appThm: the stack does not begin with two theorems"
  -- Before: Thm θ :: List [List [List [Name α1, Type ty1], ..., List [Name αm, Type tym]],
  --                        List [List [Var v1, Term t1], ..., List [Var vn, Term tn]]] :: stack.
  -- After: Thm ((θ[ty1/α1, ..., tym/αm])[t1/v1, ..., tn/vn]) :: stack; the hypotheses and the
  -- conclusion are instantiated. Constraint: the names αi are in the global namespace.
  | .substitution =>
      match state.stack with
      | .sequent sequent :: .list [.list typeEntries, .list termEntries] :: rest =>
          match typeSubstitution typeEntries, termSubstitution termEntries with
          | .ok types, .ok terms =>
              if (types.map Prod.fst).Nodup ∧ (terms.map Prod.fst).Nodup then
                .ok { state with
                  stack := .sequent ⟨sequent.hypotheses.map (Term.substitute types terms),
                    sequent.conclusion.substitute types terms⟩ :: rest }
              else .error "subst: a variable is instantiated twice"
          | .error message, _ => .error message
          | _, .error message => .error message
      | _ => .error "subst: the stack does not begin with a theorem and a substitution"
  -- Before: Term φ :: List [Term t1, ..., Term tn] :: stack. After: Thm ({t1, ..., tn} ⊦ φ) :: stack,
  -- and the theorem is added to the assumptions. Constraint: φ has type bool.
  -- This reader also requires the list to be empty and φ to be an equation.
  | .importAxiom =>
      match state.stack with
      | .term conclusion :: .list [] :: rest =>
          if conclusion.typeOf = some .boolean then
            match conclusion.equationSides? with
            | some _ =>
                .ok { state with
                  stack := .sequent ⟨[], conclusion⟩ :: rest,
                  assumptions := state.assumptions ++ [⟨[], conclusion⟩] }
            | none => .error "axiom: the conclusion is not an equation"
          else .error "axiom: the conclusion does not have type bool"
      | .term _ :: .list (_ :: _) :: _ =>
          .error "axiom: this reader accepts only an empty hypothesis list"
      | _ => .error "axiom: the stack does not begin with a term and a list"
  -- Before: Term φ :: List [Term t1, ..., Term tn] :: Thm (Γ ⊦ ψ) :: stack. After: stack, and
  -- {t1, ..., tn} ⊦ φ is added to the theorems. Constraints: φ and ψ are α-equivalent, that is
  -- equal; Γ is a subset of {t1, ..., tn}; the ti are distinct.
  -- This reader requires the list to be empty, so Γ must be empty too.
  | .exportTheorem =>
      match state.stack with
      | .term conclusion :: .list [] :: .sequent sequent :: rest =>
          if sequent.hypotheses = [] then
            if conclusion = sequent.conclusion then
              .ok { state with stack := rest, theorems := state.theorems ++ [⟨[], conclusion⟩] }
            else .error "thm: the claimed conclusion differs from the theorem's"
          else .error "thm: the theorem has hypotheses"
      | .term _ :: .list (_ :: _) :: .sequent _ :: _ =>
          .error "thm: this reader exports only theorems without hypotheses"
      | _ => .error "thm: the stack does not begin with a term, a list and a theorem"
  -- Before: Term t :: Name n :: stack. After: Thm (⊦ c = t) :: Const c :: stack, c a new constant
  -- named n with the type of t. Constraint: t has no free term variable (and no type variable,
  -- which no term of this reader has). This reader also requires t to be well typed and n to be
  -- defined once; the theorem is the object `definition n t`, and n with t joins the definitions.
  | .defineConstant =>
      match state.stack with
      | .term value :: .name name :: rest =>
          if value.closed = false then .error "defineConst: the defining term has a free variable"
          else if value.typeOf = none then .error "defineConst: the defining term is ill-typed"
          else if (state.definitions.map Prod.fst).contains name then
            .error "defineConst: the name is defined twice"
          else
            .ok { state with
              stack := .definition name value :: .constant name :: rest,
              definitions := state.definitions ++ [(name, value)] }
      | _ => .error "defineConst: the stack does not begin with a term and a name"
  -- Before: Num k :: x :: stack. After: x :: stack, and the dictionary maps k to x.
  | .define =>
      match state.stack with
      | .number key :: object :: rest =>
          .ok { state with
            stack := object :: rest,
            dictionary := (key, object) :: state.dictionary.filter (fun entry => entry.1 ≠ key) }
      | _ => .error "def: the stack does not begin with a number and an object"
  -- Before: Num k :: stack. After: dict[k] :: stack.
  -- Constraint: k is in the domain of the dictionary.
  | .reference =>
      match state.stack with
      | .number key :: rest =>
          match lookupFirst key state.dictionary with
          | some object => .ok { state with stack := object :: rest }
          | none => .error s!"ref: the key {key} is not in the dictionary"
      | _ => .error "ref: the stack does not begin with a number"
  -- Before: Num k :: stack. After: dict[k] :: stack, and the entry for k is deleted.
  -- Constraint: k is in the domain of the dictionary.
  | .remove =>
      match state.stack with
      | .number key :: rest =>
          match lookupFirst key state.dictionary with
          | some object =>
              .ok { state with
                stack := object :: rest,
                dictionary := state.dictionary.filter (fun entry => entry.1 ≠ key) }
          | none => .error s!"remove: the key {key} is not in the dictionary"
      | _ => .error "remove: the stack does not begin with a number"
  -- Before: x :: stack. After: stack.
  | .pop =>
      match state.stack with
      | _ :: rest => .ok { state with stack := rest }
      | [] => .error "pop: the stack is empty"
  -- Before: stack. After: List [] :: stack.
  | .nil => .ok { state with stack := .list [] :: state.stack }
  -- Before: List t :: h :: stack. After: List (h :: t) :: stack.
  | .cons =>
      match state.stack with
      | .list tail :: head :: rest => .ok { state with stack := .list (head :: tail) :: rest }
      | _ => .error "cons: the stack does not begin with a list and an object"

/-! ## Reading the text -/

/-- The characters whose UTF-8 encodings `bytes` holds one after another, the first first: a byte
below 128 is the character of its value, and any other first byte begins a character that
`ByteArray.utf8DecodeChar?` decodes from at most four bytes, which are then passed. `fuel` bounds
the number of characters; the reading stops at bytes that begin no character. -/
def decodeCharacters : Nat → List UInt8 → List Char
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, first :: rest =>
      if first < 128 then Char.ofNat first.toNat :: decodeCharacters fuel rest
      else
        match ByteArray.utf8DecodeChar? ((first :: rest).take 4).toByteArray 0 with
        | some character =>
            character :: decodeCharacters fuel ((first :: rest).drop character.utf8Size)
        | none => []

/-- The characters of a string, decoded from its UTF-8 bytes: its `String.toList`
(`characters_eq_toList`). -/
def characters (text : String) : List Char :=
  decodeCharacters text.toByteArray.size text.toByteArray.data.toList

/-- The string of a list of characters, its bytes the list of their UTF-8 encodings: the
`String.ofList` of the list (`ofCharacters_eq_ofList`). -/
def ofCharacters (characters : List Char) : String :=
  String.ofByteArray ⟨⟨characters.flatMap String.utf8EncodeChar⟩⟩ (by
    refine .intro characters ?_
    apply ByteArray.ext
    simp [List.utf8Encode, List.data_toByteArray])

/-- Whether a list of characters begins with `character`. -/
def beginsWith (character : Char) : List Char → Bool
  | first :: _ => first == character
  | [] => false

/-- The value of a list of decimal digits. -/
def digitsValue (digits : List Char) : Nat :=
  digits.foldl (fun accumulated digit => accumulated * 10 + (digit.toNat - '0'.toNat)) 0

/-- Whether a list of characters matches `[1-9][0-9]*`. -/
def isPositiveDigits : List Char → Bool
  | first :: rest => first.isDigit && first != '0' && rest.all Char.isDigit
  | [] => false

/-- The integer of a number command, a string matching `0|[-]?[1-9][0-9]*`; `none` for any other
string. -/
def parseNumber (line : String) : Option Int :=
  match characters line with
  | ['0'] => some 0
  | '-' :: digits =>
      if isPositiveDigits digits then some (-(digitsValue digits : Int)) else none
  | digits => if isPositiveDigits digits then some (digitsValue digits : Int) else none

/-- The components of the text between the quotes of a name command: COMPONENT strings separated
by unescaped dots, each processed by turning every `\c` into `c`. `current` holds the characters of
the component being read, last first, and `finished` the components before it, last first. `none`
when the text has an unescaped double quote, or a backslash that is not followed by a dot, a
double quote or a backslash: the strings the grammar's COMPONENT excludes. -/
def parseComponents : List Char → List Char → List String → Option (List String)
  | [], current, finished => some (ofCharacters current.reverse :: finished).reverse
  | '\\' :: escaped :: rest, current, finished =>
      if escaped = '.' ∨ escaped = '"' ∨ escaped = '\\' then
        parseComponents rest (escaped :: current) finished
      else none
  | ['\\'], _, _ => none
  | '.' :: rest, current, finished =>
      parseComponents rest [] (ofCharacters current.reverse :: finished)
  | '"' :: _, _, _ => none
  | character :: rest, current, finished => parseComponents rest (character :: current) finished

/-- The name of a name command, a string matching the grammar's NAME: a double quote, a NAMESPACE,
a COMPONENT and a double quote; `none` for any other string. The last component is the local name
and the ones before it are the namespace. -/
def parseName (line : String) : Option Name :=
  match characters line with
  | '"' :: afterQuote =>
      match afterQuote.reverse with
      | '"' :: insideReversed =>
          match parseComponents insideReversed.reverse [] [] with
          | some components =>
              match components.getLast? with
              | some localName => some ⟨components.dropLast, localName⟩
              | none => none
          | none => none
      | _ => none
  | _ => none

/-- The command of a command line: a name command when the line begins with a double quote, one
of the fragment's command names, or a number command. -/
def parseCommand (line : String) : Except String Command :=
  if beginsWith '"' (characters line) then
    match parseName line with
    | some name => .ok (.name name)
    | none => .error s!"malformed name command {line}"
  else
    match line with
    | "version" => .ok .version
    | "typeOp" => .ok .typeOperator
    | "opType" => .ok .operatorType
    | "const" => .ok .constant
    | "constTerm" => .ok .constantTerm
    | "var" => .ok .termVariable
    | "varTerm" => .ok .variableTerm
    | "appTerm" => .ok .applicationTerm
    | "refl" => .ok .reflexivity
    | "sym" => .ok .symmetry
    | "trans" => .ok .transitivity
    | "appThm" => .ok .applicationTheorem
    | "subst" => .ok .substitution
    | "axiom" => .ok .importAxiom
    | "thm" => .ok .exportTheorem
    | "defineConst" => .ok .defineConstant
    | "def" => .ok .define
    | "ref" => .ok .reference
    | "remove" => .ok .remove
    | "pop" => .ok .pop
    | "nil" => .ok .nil
    | "cons" => .ok .cons
    | _ =>
        match parseNumber line with
        | some value => .ok (.number value)
        | none => .error s!"unsupported command '{line}'"

/-- The lines of an article text: the text split at its newline characters, where a final newline
ends the last line and does not begin another. -/
def articleLines (text : String) : List String :=
  let pieces := text.splitOn "\n"
  if pieces.getLast? = some "" then pieces.dropLast else pieces

/-- A command with the number of its line, counted from 1 with the comment lines. -/
structure NumberedCommand where
  /-- The line number. -/
  line : Nat
  /-- The command. -/
  command : Command
  deriving Repr

/-- `parseLines` with the commands parsed so far, last first. Tail recursive, so that the kernel
evaluates an article at a depth that does not grow with its length: a recursion that returns to
wrap each command exceeded the kernel's depth (Lean 4.35) on articles of about 600 lines. -/
def parseLinesAfter (parsed : List NumberedCommand) :
    Nat → List String → Except String (List NumberedCommand)
  | _, [] => .ok parsed.reverse
  | lineNumber, line :: rest =>
      if beginsWith '#' (characters line) then parseLinesAfter parsed (lineNumber + 1) rest
      else
        match parseCommand line with
        | .ok command => parseLinesAfter (⟨lineNumber, command⟩ :: parsed) (lineNumber + 1) rest
        | .error message => .error s!"line {lineNumber}: {message}"

/-- The commands of the lines from line number `lineNumber` on: a line that begins with `#` is a
comment and is discarded, and every other line is parsed as a command. -/
def parseLines (lineNumber : Nat) (lines : List String) : Except String (List NumberedCommand) :=
  parseLinesAfter [] lineNumber lines

/-- The commands run in order from `state`; the first rejection rejects the run, with its line. -/
def runCommands (state : MachineState) : List NumberedCommand → Except String MachineState
  | [] => .ok state
  | numbered :: rest =>
      match step state numbered.command with
      | .ok next => runCommands next rest
      | .error message => .error s!"line {numbered.line}: {message}"

/-- The result of reading an article, the theory `Γ ⊳ Δ`: the assumptions `Γ` and the theorems
`Δ`, with the constants the article defined and their defining terms. -/
structure Theory where
  /-- The assumptions, the import set. -/
  assumptions : List Sequent
  /-- The theorems, the export set. -/
  theorems : List Sequent
  /-- The constants `defineConst` defined, each with its defining term, in order. -/
  definitions : List (Name × Term)

/-- Reads the lines of an article: every line is parsed before any command runs, the commands
must begin with `6` and `version`, and the remaining commands are run from the initial state; the
result is the final state's assumptions, theorems and definitions, the stack and the dictionary
being discarded. -/
def readLines (lines : List String) : Except String Theory :=
  match parseLines 1 lines with
  | .error message => .error message
  | .ok (⟨_, .number version⟩ :: ⟨versionLine, .version⟩ :: rest) =>
      if version = 6 then
        match runCommands .initial rest with
        | .ok final => .ok ⟨final.assumptions, final.theorems, final.definitions⟩
        | .error message => .error message
      else
        .error s!"line {versionLine}: this reader reads only version 6 of the format, not {version}"
  | .ok _ =>
      .error "the article does not begin with the commands 6 and version (it would be version 5)"

/-- Reads an article text: its lines (`articleLines`) read by `readLines`. -/
def readArticle (text : String) : Except String Theory :=
  readLines (articleLines text)

/-! ## The characters of a line

The reader takes a line apart with `characters`, tells a comment and a name command by
`beginsWith` on those characters, and builds the components of a name with `ofCharacters`. These
are `String.toList`, `String.startsWith` with a string of one character, and `String.ofList`
(`characters_eq_toList`, `beginsWith_characters`, `ofCharacters_eq_ofList`; the literals `"#"` and
`"\""` are `String.ofList ['#']` and `String.ofList ['"']` by `rfl`), so the reader reads every
line as it reads with those. -/

/-- The decoding of one character's UTF-8 encoding followed by any bytes is that character
followed by the decoding of the bytes. -/
theorem decodeCharacters_encoding_append (fuel : Nat) (character : Char) (rest : List UInt8) :
    decodeCharacters (fuel + 1) (String.utf8EncodeChar character ++ rest) =
      character :: decodeCharacters fuel rest := by
  by_cases ascii : character.toNat ≤ 127
  · have encoded : String.utf8EncodeChar character = [UInt8.ofNat character.toNat] := by
      simp only [String.utf8EncodeChar]
      exact if_pos ascii
    have value : (UInt8.ofNat character.toNat).toNat = character.toNat := by
      rw [UInt8.toNat_ofNat']
      omega
    have small : UInt8.ofNat character.toNat < 128 := by
      rw [UInt8.lt_iff_toNat_lt, value]
      simp only [UInt8.reduceToNat]
      omega
    rw [encoded, List.singleton_append]
    simp only [decodeCharacters, small, if_true, value, Char.ofNat_toNat]
  · obtain ⟨first, tail, encoded, large⟩ : ∃ first tail,
        String.utf8EncodeChar character = first :: tail ∧ ¬ first < 128 := by
      simp only [String.utf8EncodeChar]
      rw [if_neg (show ¬ character.val.toNat ≤ 127 from ascii)]
      split
      · refine ⟨_, _, rfl, ?_⟩
        rw [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat']
        simp only [UInt8.reduceToNat]
        omega
      · split
        · refine ⟨_, _, rfl, ?_⟩
          rw [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat']
          simp only [UInt8.reduceToNat]
          omega
        · refine ⟨_, _, rfl, ?_⟩
          rw [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat']
          simp only [UInt8.reduceToNat]
          omega
    have size := String.length_utf8EncodeChar character
    have bounded := Char.utf8Size_le_four character
    have taken : (String.utf8EncodeChar character ++ rest).take 4 =
        String.utf8EncodeChar character ++ rest.take (4 - character.utf8Size) := by
      rw [List.take_append, List.take_of_length_le (by omega), size]
    have dropped : (String.utf8EncodeChar character ++ rest).drop character.utf8Size = rest := by
      rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
        List.nil_append]
    rw [encoded, List.cons_append]
    simp only [decodeCharacters, large, if_false]
    rw [← List.cons_append, ← encoded, taken, List.toByteArray_append,
      ByteArray.utf8DecodeChar?_utf8EncodeChar_append]
    simp only [dropped]

/-- The decoding of the UTF-8 encodings of a list of characters, with at least as much fuel as
there are characters, is the list. -/
theorem decodeCharacters_flatMap : ∀ (characters : List Char) (fuel : Nat),
    characters.length ≤ fuel →
      decodeCharacters fuel (characters.flatMap String.utf8EncodeChar) = characters
  | [], fuel, _ => by cases fuel <;> rfl
  | character :: characters, fuel, bounded => by
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 :=
        ⟨fuel - 1, by simp only [List.length_cons] at bounded; omega⟩
      rw [List.flatMap_cons, decodeCharacters_encoding_append,
        decodeCharacters_flatMap characters fuel (by simp only [List.length_cons] at bounded; omega)]

/-- A list of characters has at most as many characters as its UTF-8 encodings have bytes. -/
theorem length_le_length_flatMap : ∀ characters : List Char,
    characters.length ≤ (characters.flatMap String.utf8EncodeChar).length
  | [] => Nat.le_refl 0
  | character :: characters => by
      have positive := Char.utf8Size_pos character
      have rest := length_le_length_flatMap characters
      simp only [List.flatMap_cons, List.length_append, String.length_utf8EncodeChar,
        List.length_cons]
      omega

/-- `characters` is `String.toList`. -/
theorem characters_eq_toList (text : String) : characters text = text.toList := by
  have bytes : text.toByteArray.data.toList = text.toList.flatMap String.utf8EncodeChar := by
    rw [← String.utf8Encode_toList, List.utf8Encode, List.toList_data_toByteArray]
  have size : text.toByteArray.size = (text.toList.flatMap String.utf8EncodeChar).length := by
    rw [← ByteArray.size_data, ← Array.length_toList, bytes]
  unfold characters
  rw [size, bytes]
  exact decodeCharacters_flatMap text.toList _ (length_le_length_flatMap text.toList)

/-- `ofCharacters` is `String.ofList`. -/
theorem ofCharacters_eq_ofList (characters : List Char) :
    ofCharacters characters = String.ofList characters := by
  apply String.toByteArray_inj.mp
  rw [String.toByteArray_ofList]
  apply ByteArray.ext
  simp [ofCharacters, List.utf8Encode, List.data_toByteArray]

/-- `beginsWith character` of a line's characters is whether the line starts with the string of
that character. -/
theorem beginsWith_characters (character : Char) (line : String) :
    beginsWith character (characters line) = line.startsWith (String.ofList [character]) := by
  rw [characters_eq_toList]
  apply Bool.eq_iff_iff.mpr
  rw [String.startsWith_string_iff, String.toList_ofList]
  cases line.toList with
  | nil => simp [beginsWith]
  | cons first rest =>
      simp only [beginsWith, beq_iff_eq, List.cons_prefix_cons, List.nil_prefix, and_true]
      exact eq_comm

/-! ## Soundness -/

/-- A simultaneous instantiation of type variables and term variables: `typeImage name` replaces
the type variable `name`, and `termImage name type` the term variable named `name` whose type,
before the instantiation, is `type`. The substitution of every `subst` command is one
(`Term.substitute_eq_instantiate`), and instantiations compose (`Term.instantiate_instantiate`),
which the substitutions of single `subst` commands do not: a type instantiation can make two
variables one. -/
structure Instantiation where
  /-- The image of each type variable. -/
  typeImage : Name → LogicType
  /-- The image of each term variable, by its name and its type before the instantiation. -/
  termImage : Name → LogicType → Term

/-- The instance of a term under an instantiation: every variable replaced by its image, every
constant kept at its instantiated type, and applications mapped componentwise. -/
def Term.instantiate (instantiation : Instantiation) : Term → Term
  | .termVariable name type => instantiation.termImage name type
  | .constant name type => .constant name (type.instantiate instantiation.typeImage)
  | .application function argument =>
      .application (function.instantiate instantiation) (argument.instantiate instantiation)

/-- The import set: the equations of the assumptions, each as the pair of its sides. -/
def importEquations (assumptions : List Sequent) : List (Term × Term) :=
  assumptions.filterMap fun sequent =>
    sequent.conclusion.equationSides?.map fun (_, left, right) => (left, right)

/-- `Derivable imports left right`: the equation `left = right` is in the least relation that
contains every instance of every import equation and is closed under reflexivity, symmetry,
transitivity and congruence of application. Types play no part in it. -/
inductive Derivable (imports : List (Term × Term)) : Term → Term → Prop where
  /-- Every instance of every import equation. -/
  | importInstance {left right : Term} (instantiation : Instantiation)
      (member : (left, right) ∈ imports) :
      Derivable imports (left.instantiate instantiation) (right.instantiate instantiation)
  /-- Reflexivity. -/
  | reflexivity (term : Term) : Derivable imports term term
  /-- Symmetry. -/
  | symmetry {left right : Term} : Derivable imports left right → Derivable imports right left
  /-- Transitivity. -/
  | transitivity {first second third : Term} :
      Derivable imports first second → Derivable imports second third →
        Derivable imports first third
  /-- Congruence of application: `f = g` and `x = y` give `f x = g y`. -/
  | congruence {leftFunction rightFunction leftArgument rightArgument : Term} :
      Derivable imports leftFunction rightFunction →
        Derivable imports leftArgument rightArgument →
          Derivable imports (.application leftFunction leftArgument)
            (.application rightFunction rightArgument)

/-- `object.Contains sequent`: the object is the theorem `sequent`, or a list with an element
that contains it. -/
inductive Object.Contains : Object → Sequent → Prop where
  /-- A theorem contains itself. -/
  | sequent (sequent : Sequent) : Object.Contains (.sequent sequent) sequent
  /-- A list contains what its elements contain. -/
  | list {elements : List Object} {element : Object} {sequent : Sequent} :
      element ∈ elements → element.Contains sequent → Object.Contains (.list elements) sequent

/-- The machine holds the theorem `sequent`: an object of its stack or a value of its dictionary
contains it, or it is one of its assumptions or of its theorems. -/
def MachineState.Holds (state : MachineState) (sequent : Sequent) : Prop :=
  (∃ object ∈ state.stack, object.Contains sequent) ∨
    (∃ entry ∈ state.dictionary, entry.2.Contains sequent) ∨
      sequent ∈ state.assumptions ∨ sequent ∈ state.theorems

/-- A theorem without hypotheses whose conclusion is an equation derivable from `imports`. -/
def SequentSound (imports : List (Term × Term)) (sequent : Sequent) : Prop :=
  sequent.hypotheses = [] ∧ ∃ sideType left right,
    sequent.conclusion = .equation sideType left right ∧ Derivable imports left right

/-- Every theorem the object contains is sound. -/
def ObjectSound (imports : List (Term × Term)) (object : Object) : Prop :=
  ∀ sequent, object.Contains sequent → SequentSound imports sequent

/-- The invariant of the machine: every theorem it holds is sound for its own import set. -/
def StateSound (state : MachineState) : Prop :=
  (∀ object ∈ state.stack, ObjectSound (importEquations state.assumptions) object) ∧
    (∀ entry ∈ state.dictionary, ObjectSound (importEquations state.assumptions) entry.2) ∧
      (∀ sequent ∈ state.assumptions, SequentSound (importEquations state.assumptions) sequent) ∧
        (∀ sequent ∈ state.theorems, SequentSound (importEquations state.assumptions) sequent)

/-! ### Instantiation -/

/-- The instantiation `first` followed by `second`. -/
def Instantiation.andThen (first second : Instantiation) : Instantiation where
  typeImage name := (first.typeImage name).instantiate second.typeImage
  termImage name type := (first.termImage name type).instantiate second

/-- The instantiation that keeps every variable. -/
def Instantiation.identity : Instantiation where
  typeImage := .typeVariable
  termImage := .termVariable

mutual
theorem LogicType.instantiate_instantiate (first second : Name → LogicType) :
    (type : LogicType) → (type.instantiate first).instantiate second =
      type.instantiate (fun name => (first name).instantiate second)
  | .typeVariable _ => rfl
  | .operator name arguments => by
      simp only [LogicType.instantiate]
      rw [LogicType.instantiateList_instantiateList first second arguments]

theorem LogicType.instantiateList_instantiateList (first second : Name → LogicType) :
    (types : List LogicType) →
      LogicType.instantiateList second (LogicType.instantiateList first types) =
        LogicType.instantiateList (fun name => (first name).instantiate second) types
  | [] => rfl
  | head :: tail => by
      simp only [LogicType.instantiateList]
      rw [LogicType.instantiate_instantiate first second head,
        LogicType.instantiateList_instantiateList first second tail]
end

mutual
theorem LogicType.instantiate_typeVariable :
    (type : LogicType) → type.instantiate .typeVariable = type
  | .typeVariable _ => rfl
  | .operator name arguments => by
      simp only [LogicType.instantiate]
      rw [LogicType.instantiateList_typeVariable arguments]

theorem LogicType.instantiateList_typeVariable :
    (types : List LogicType) → LogicType.instantiateList .typeVariable types = types
  | [] => rfl
  | head :: tail => by
      simp only [LogicType.instantiateList]
      rw [LogicType.instantiate_typeVariable head, LogicType.instantiateList_typeVariable tail]
end

theorem Term.instantiate_instantiate (first second : Instantiation) :
    (term : Term) → (term.instantiate first).instantiate second =
      term.instantiate (first.andThen second)
  | .termVariable _ _ => rfl
  | .constant name type => by
      simp only [Term.instantiate, Instantiation.andThen]
      rw [LogicType.instantiate_instantiate]
  | .application function argument => by
      simp only [Term.instantiate]
      rw [Term.instantiate_instantiate first second function,
        Term.instantiate_instantiate first second argument]

theorem Term.instantiate_identity : (term : Term) → term.instantiate .identity = term
  | .termVariable _ _ => rfl
  | .constant name type => by
      simp only [Term.instantiate, Instantiation.identity]
      rw [LogicType.instantiate_typeVariable]
  | .application function argument => by
      simp only [Term.instantiate]
      rw [Term.instantiate_identity function, Term.instantiate_identity argument]

/-- The instantiation of the substitution of a `subst` command. -/
def substitutionInstantiation (types : List (Name × LogicType))
    (terms : List ((Name × LogicType) × Term)) : Instantiation where
  typeImage := typeImageOf types
  termImage name type :=
    (lookupFirst (name, type.instantiate (typeImageOf types)) terms).getD
      (.termVariable name (type.instantiate (typeImageOf types)))

theorem Term.substitute_eq_instantiate (types : List (Name × LogicType))
    (terms : List ((Name × LogicType) × Term)) :
    (term : Term) → term.substitute types terms =
      term.instantiate (substitutionInstantiation types terms)
  | .termVariable _ _ => rfl
  | .constant _ _ => rfl
  | .application function argument => by
      show Term.application (function.substitute types terms) (argument.substitute types terms) = _
      rw [Term.substitute_eq_instantiate types terms function,
        Term.substitute_eq_instantiate types terms argument]
      rfl

theorem Derivable.instantiate {imports : List (Term × Term)} (instantiation : Instantiation)
    {left right : Term} (derivable : Derivable imports left right) :
    Derivable imports (left.instantiate instantiation) (right.instantiate instantiation) := by
  induction derivable with
  | importInstance inner member =>
      rw [Term.instantiate_instantiate, Term.instantiate_instantiate]
      exact .importInstance _ member
  | reflexivity term => exact .reflexivity _
  | symmetry _ symmetric => exact .symmetry symmetric
  | transitivity _ _ firstStep secondStep => exact .transitivity firstStep secondStep
  | congruence _ _ functions arguments => exact .congruence functions arguments

theorem Derivable.monotone {imports larger : List (Term × Term)}
    (included : ∀ equation ∈ imports, equation ∈ larger) {left right : Term}
    (derivable : Derivable imports left right) : Derivable larger left right := by
  induction derivable with
  | importInstance instantiation member => exact .importInstance instantiation (included _ member)
  | reflexivity term => exact .reflexivity term
  | symmetry _ symmetric => exact .symmetry symmetric
  | transitivity _ _ firstStep secondStep => exact .transitivity firstStep secondStep
  | congruence _ _ functions arguments => exact .congruence functions arguments

/-! ### Equations -/

theorem Term.equationSides?_equation (sideType : LogicType) (left right : Term) :
    (Term.equation sideType left right).equationSides? = some (sideType, left, right) := by
  simp [Term.equationSides?, Term.equation, LogicType.equality, LogicType.arrow]

theorem Term.equationSides?_eq_some {term : Term} {sideType : LogicType} {left right : Term}
    (sides : term.equationSides? = some (sideType, left, right)) :
    term = .equation sideType left right := by
  unfold Term.equationSides? at sides
  split at sides
  · split at sides
    · rename_i isEquation
      cases sides
      exact isEquation
    · cases sides
  · cases sides

theorem Term.equation_instantiate (instantiation : Instantiation) (sideType : LogicType)
    (left right : Term) :
    (Term.equation sideType left right).instantiate instantiation =
      .equation (sideType.instantiate instantiation.typeImage) (left.instantiate instantiation)
        (right.instantiate instantiation) := by
  simp [Term.equation, Term.instantiate, LogicType.equality, LogicType.arrow, LogicType.boolean,
    LogicType.instantiate, LogicType.instantiateList]

/-! ### The invariant -/

theorem SequentSound.monotone {imports larger : List (Term × Term)}
    (included : ∀ equation ∈ imports, equation ∈ larger) {sequent : Sequent}
    (sound : SequentSound imports sequent) : SequentSound larger sequent := by
  obtain ⟨noHypotheses, sideType, left, right, isEquation, derivable⟩ := sound
  exact ⟨noHypotheses, sideType, left, right, isEquation, derivable.monotone included⟩

theorem ObjectSound.monotone {imports larger : List (Term × Term)}
    (included : ∀ equation ∈ imports, equation ∈ larger) {object : Object}
    (sound : ObjectSound imports object) : ObjectSound larger object :=
  fun sequent contains => (sound sequent contains).monotone included

theorem ObjectSound.ofSequent {imports : List (Term × Term)} {sequent : Sequent}
    (sound : SequentSound imports sequent) : ObjectSound imports (.sequent sequent) := by
  intro contained contains
  cases contains
  exact sound

theorem ObjectSound.toSequent {imports : List (Term × Term)} {sequent : Sequent}
    (sound : ObjectSound imports (.sequent sequent)) : SequentSound imports sequent :=
  sound sequent (.sequent sequent)

theorem lookupFirst_mem {Key Value : Type} [DecidableEq Key] {key : Key} {value : Value} :
    {entries : List (Key × Value)} → lookupFirst key entries = some value →
      (key, value) ∈ entries
  | [], found => by cases found
  | (entryKey, entryValue) :: rest, found => by
      simp only [lookupFirst] at found
      split at found
      · rename_i sameKey
        cases found
        rw [sameKey]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (lookupFirst_mem found)

theorem StateSound.initial : StateSound MachineState.initial := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro _ member <;> cases member

/-- The objects a command pops from a sound state are sound. -/
theorem StateSound.popped {state : MachineState} (sound : StateSound state)
    {popped rest : List Object} (stackEquation : state.stack = popped ++ rest) :
    ∀ object ∈ popped, ObjectSound (importEquations state.assumptions) object := by
  intro object member
  exact sound.1 object (by rw [stackEquation]; exact List.mem_append_left rest member)

/-- A command that replaces the objects `popped` at the top of the stack by sound objects
`pushed`, and changes nothing else, keeps the state sound. -/
theorem StateSound.replaceTop {state : MachineState} (sound : StateSound state)
    {popped pushed rest : List Object} (stackEquation : state.stack = popped ++ rest)
    (pushedSound : ∀ object ∈ pushed, ObjectSound (importEquations state.assumptions) object) :
    StateSound { state with stack := pushed ++ rest } := by
  obtain ⟨stackSound, dictionarySound, assumptionsSound, theoremsSound⟩ := sound
  refine ⟨?_, dictionarySound, assumptionsSound, theoremsSound⟩
  intro object member
  rcases List.mem_append.mp member with pushedMember | restMember
  · exact pushedSound object pushedMember
  · exact stackSound object (by rw [stackEquation]; exact List.mem_append_right popped restMember)

/-- An object that contains no theorem is sound. -/
theorem ObjectSound.ofNoSequent {imports : List (Term × Term)} {object : Object}
    (noSequent : ∀ sequent, ¬ object.Contains sequent) : ObjectSound imports object :=
  fun sequent contains => absurd contains (noSequent sequent)

/-- The objects below the popped ones in a sound state are sound. -/
theorem StateSound.rest {state : MachineState} (sound : StateSound state)
    {popped rest : List Object} (stackEquation : state.stack = popped ++ rest) :
    ∀ object ∈ rest, ObjectSound (importEquations state.assumptions) object := by
  intro object member
  exact sound.1 object (by rw [stackEquation]; exact List.mem_append_right popped member)

/-- A command that replaces the objects `popped` at the top of the stack by one sound object, and
changes nothing else, keeps the state sound. -/
theorem StateSound.pushSound {state : MachineState} (sound : StateSound state)
    {popped rest : List Object} (stackEquation : state.stack = popped ++ rest) {object : Object}
    (objectSound : ObjectSound (importEquations state.assumptions) object) :
    StateSound { state with stack := object :: rest } :=
  sound.replaceTop (pushed := [object]) stackEquation (by
    intro pushedObject member
    rw [List.mem_singleton.mp member]
    exact objectSound)

theorem step_sound {state next : MachineState} {command : Command} (sound : StateSound state)
    (stepped : step state command = .ok next) : StateSound next := by
  cases command with
  | number value =>
      cases stepped
      exact sound.pushSound (popped := []) rfl
        (.ofNoSequent fun _ contains => nomatch contains)
  | name value =>
      cases stepped
      exact sound.pushSound (popped := []) rfl
        (.ofNoSequent fun _ contains => nomatch contains)
  | version => cases stepped
  | typeOperator =>
      simp only [step] at stepped
      split at stepped
      · rename_i name rest stackEquation
        cases stepped
        exact sound.pushSound (popped := [.name name]) stackEquation
          (.ofNoSequent fun _ contains => nomatch contains)
      · cases stepped
  | operatorType =>
      simp only [step] at stepped
      split at stepped
      · rename_i elements name rest stackEquation
        split at stepped
        · split at stepped
          · cases stepped
            exact sound.pushSound (popped := [.list elements, .typeOperator name]) stackEquation
              (.ofNoSequent fun _ contains => nomatch contains)
          · cases stepped
        · cases stepped
      · cases stepped
  | constant =>
      simp only [step] at stepped
      split at stepped
      · rename_i name rest stackEquation
        cases stepped
        exact sound.pushSound (popped := [.name name]) stackEquation
          (.ofNoSequent fun _ contains => nomatch contains)
      · cases stepped
  | constantTerm =>
      simp only [step] at stepped
      split at stepped
      · rename_i type name rest stackEquation
        split at stepped
        · cases stepped
        · cases stepped
          exact sound.pushSound (popped := [.type type, .constant name]) stackEquation
            (.ofNoSequent fun _ contains => nomatch contains)
      · cases stepped
  | termVariable =>
      simp only [step] at stepped
      split at stepped
      · rename_i type name rest stackEquation
        split at stepped
        · cases stepped
          exact sound.pushSound (popped := [.type type, .name name]) stackEquation
            (.ofNoSequent fun _ contains => nomatch contains)
        · cases stepped
      · cases stepped
  | variableTerm =>
      simp only [step] at stepped
      split at stepped
      · rename_i name type rest stackEquation
        cases stepped
        exact sound.pushSound (popped := [.termVariable name type]) stackEquation
          (.ofNoSequent fun _ contains => nomatch contains)
      · cases stepped
  | applicationTerm =>
      simp only [step] at stepped
      split at stepped
      · rename_i argument function rest stackEquation
        split at stepped
        · cases stepped
          exact sound.pushSound (popped := [.term argument, .term function]) stackEquation
            (.ofNoSequent fun _ contains => nomatch contains)
        · cases stepped
      · cases stepped
  | reflexivity =>
      simp only [step] at stepped
      split at stepped
      · rename_i term rest stackEquation
        split at stepped
        · rename_i type _
          cases stepped
          exact sound.pushSound (popped := [.term term]) stackEquation
            (.ofSequent ⟨rfl, type, term, term, rfl, .reflexivity term⟩)
        · cases stepped
      · cases stepped
  | symmetry =>
      simp only [step] at stepped
      split at stepped
      · rename_i sequent rest stackEquation
        split at stepped
        · rename_i type left right sides
          cases stepped
          obtain ⟨noHypotheses, sideType, soundLeft, soundRight, isEquation, derivable⟩ :=
            (sound.popped (popped := [.sequent sequent]) stackEquation _
              List.mem_cons_self).toSequent
          rw [isEquation, Term.equationSides?_equation] at sides
          cases sides
          exact sound.pushSound (popped := [.sequent sequent]) stackEquation
            (.ofSequent ⟨noHypotheses, type, right, left, rfl, derivable.symmetry⟩)
        · cases stepped
      · cases stepped
  | transitivity =>
      simp only [step] at stepped
      split at stepped
      · rename_i second first rest stackEquation
        split at stepped
        · rename_i type left firstRight secondType secondLeft right firstSides secondSides
          split at stepped
          · rename_i middleEqual
            cases stepped
            have poppedSound := sound.popped (popped := [.sequent second, .sequent first])
              stackEquation
            obtain ⟨secondNoHypotheses, _, secondSoundLeft, secondSoundRight, secondIsEquation,
              secondDerivable⟩ := (poppedSound _ List.mem_cons_self).toSequent
            obtain ⟨firstNoHypotheses, _, firstSoundLeft, firstSoundRight, firstIsEquation,
              firstDerivable⟩ :=
              (poppedSound _ (List.mem_cons_of_mem _ List.mem_cons_self)).toSequent
            rw [firstIsEquation, Term.equationSides?_equation] at firstSides
            rw [secondIsEquation, Term.equationSides?_equation] at secondSides
            cases firstSides
            cases secondSides
            subst middleEqual
            exact sound.pushSound (popped := [.sequent second, .sequent first]) stackEquation
              (.ofSequent ⟨by rw [firstNoHypotheses, secondNoHypotheses]; rfl, type, left, right,
                rfl, firstDerivable.transitivity secondDerivable⟩)
          · cases stepped
        · cases stepped
      · cases stepped
  | applicationTheorem =>
      simp only [step] at stepped
      split at stepped
      · rename_i argumentSequent functionSequent rest stackEquation
        split at stepped
        · rename_i functionType leftFunction rightFunction argumentType leftArgument
            rightArgument functionSides argumentSides
          split at stepped
          · rename_i type _
            cases stepped
            have poppedSound := sound.popped
              (popped := [.sequent argumentSequent, .sequent functionSequent]) stackEquation
            obtain ⟨argumentNoHypotheses, _, argumentSoundLeft, argumentSoundRight,
              argumentIsEquation, argumentDerivable⟩ :=
              (poppedSound _ List.mem_cons_self).toSequent
            obtain ⟨functionNoHypotheses, _, functionSoundLeft, functionSoundRight,
              functionIsEquation, functionDerivable⟩ :=
              (poppedSound _ (List.mem_cons_of_mem _ List.mem_cons_self)).toSequent
            rw [functionIsEquation, Term.equationSides?_equation] at functionSides
            rw [argumentIsEquation, Term.equationSides?_equation] at argumentSides
            cases functionSides
            cases argumentSides
            exact sound.pushSound
              (popped := [.sequent argumentSequent, .sequent functionSequent]) stackEquation
              (.ofSequent ⟨by rw [functionNoHypotheses, argumentNoHypotheses]; rfl, type, _, _,
                rfl, functionDerivable.congruence argumentDerivable⟩)
          · cases stepped
        · cases stepped
      · cases stepped
  | substitution =>
      simp only [step] at stepped
      split at stepped
      · rename_i sequent typeEntries termEntries rest stackEquation
        split at stepped
        · rename_i types terms _ _
          split at stepped
          · cases stepped
            obtain ⟨noHypotheses, sideType, left, right, isEquation, derivable⟩ :=
              (sound.popped (popped := [.sequent sequent, .list [.list typeEntries,
                .list termEntries]]) stackEquation _ List.mem_cons_self).toSequent
            have instanceEquation : sequent.conclusion.substitute types terms =
                .equation (sideType.instantiate (substitutionInstantiation types terms).typeImage)
                  (left.instantiate (substitutionInstantiation types terms))
                  (right.instantiate (substitutionInstantiation types terms)) := by
              rw [Term.substitute_eq_instantiate, isEquation, Term.equation_instantiate]
            exact sound.pushSound
              (popped := [.sequent sequent, .list [.list typeEntries, .list termEntries]])
              stackEquation
              (.ofSequent ⟨by rw [noHypotheses]; rfl, _, _, _, instanceEquation,
                derivable.instantiate _⟩)
          · cases stepped
        · cases stepped
        · cases stepped
      · cases stepped
  | importAxiom =>
      simp only [step] at stepped
      split at stepped
      · rename_i conclusion rest stackEquation
        split at stepped
        · split at stepped
          · rename_i sides sidesEquation
            obtain ⟨sideType, left, right⟩ := sides
            cases stepped
            have isEquation := Term.equationSides?_eq_some sidesEquation
            have grown : ∀ equation ∈ importEquations state.assumptions,
                equation ∈ importEquations (state.assumptions ++ [⟨[], conclusion⟩]) := by
              intro equation member
              simp only [importEquations, List.filterMap_append]
              exact List.mem_append_left _ member
            have imported : (left, right) ∈
                importEquations (state.assumptions ++ [⟨[], conclusion⟩]) := by
              simp only [importEquations, List.filterMap_append]
              apply List.mem_append_right
              simp [sidesEquation]
            have importedInstance :=
              Derivable.importInstance Instantiation.identity imported
            rw [Term.instantiate_identity, Term.instantiate_identity] at importedInstance
            have newSound : SequentSound
                (importEquations (state.assumptions ++ [⟨[], conclusion⟩])) ⟨[], conclusion⟩ :=
              ⟨rfl, sideType, left, right, isEquation, importedInstance⟩
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro object member
              rcases List.mem_cons.mp member with isNew | inRest
              · rw [isNew]
                exact ObjectSound.ofSequent newSound
              · exact (sound.rest (popped := [.term conclusion, .list []]) stackEquation object
                  inRest).monotone grown
            · intro entry member
              exact (sound.2.1 entry member).monotone grown
            · intro sequent member
              rcases List.mem_append.mp member with old | isNew
              · exact (sound.2.2.1 sequent old).monotone grown
              · rw [List.mem_singleton.mp isNew]
                exact newSound
            · intro sequent member
              exact (sound.2.2.2 sequent member).monotone grown
          · cases stepped
        · cases stepped
      · cases stepped
      · cases stepped
  | exportTheorem =>
      simp only [step] at stepped
      split at stepped
      · rename_i conclusion sequent rest stackEquation
        split at stepped
        · split at stepped
          · rename_i sameConclusion
            cases stepped
            obtain ⟨_, sideType, left, right, isEquation, derivable⟩ :=
              (sound.popped (popped := [.term conclusion, .list [], .sequent sequent])
                stackEquation _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))).toSequent
            refine ⟨sound.rest (popped := [.term conclusion, .list [], .sequent sequent])
              stackEquation, sound.2.1, sound.2.2.1, ?_⟩
            intro exported member
            rcases List.mem_append.mp member with old | isNew
            · exact sound.2.2.2 exported old
            · rw [List.mem_singleton.mp isNew]
              exact ⟨rfl, sideType, left, right, by rw [sameConclusion, isEquation], derivable⟩
          · cases stepped
        · cases stepped
      · cases stepped
      · cases stepped
  | defineConstant =>
      simp only [step] at stepped
      split at stepped
      · rename_i value name rest stackEquation
        split at stepped
        · cases stepped
        · split at stepped
          · cases stepped
          · split at stepped
            · cases stepped
            · cases stepped
              exact sound.replaceTop (popped := [.term value, .name name])
                (pushed := [.definition name value, .constant name]) stackEquation
                (fun object member => .ofNoSequent fun _ contains => by
                  rcases List.mem_cons.mp member with isDefinition | inRest
                  · rw [isDefinition] at contains
                    nomatch contains
                  · rw [List.mem_singleton.mp inRest] at contains
                    nomatch contains)
      · cases stepped
  | define =>
      simp only [step] at stepped
      split at stepped
      · rename_i key object rest stackEquation
        cases stepped
        have objectSound := sound.popped (popped := [.number key, object]) stackEquation _
          (List.mem_cons_of_mem _ List.mem_cons_self)
        refine ⟨?_, ?_, sound.2.2.1, sound.2.2.2⟩
        · intro member memberOf
          rcases List.mem_cons.mp memberOf with isObject | inRest
          · rw [isObject]
            exact objectSound
          · exact sound.rest (popped := [.number key, object]) stackEquation member inRest
        · intro entry member
          rcases List.mem_cons.mp member with isNew | inRest
          · rw [isNew]
            exact objectSound
          · exact sound.2.1 entry (List.mem_filter.mp inRest).1
      · cases stepped
  | reference =>
      simp only [step] at stepped
      split at stepped
      · rename_i key rest stackEquation
        split at stepped
        · rename_i object found
          cases stepped
          exact sound.pushSound (popped := [.number key]) stackEquation
            (sound.2.1 (key, object) (lookupFirst_mem found))
        · cases stepped
      · cases stepped
  | remove =>
      simp only [step] at stepped
      split at stepped
      · rename_i key rest stackEquation
        split at stepped
        · rename_i object found
          cases stepped
          refine ⟨?_, ?_, sound.2.2.1, sound.2.2.2⟩
          · intro member memberOf
            rcases List.mem_cons.mp memberOf with isObject | inRest
            · rw [isObject]
              exact sound.2.1 (key, object) (lookupFirst_mem found)
            · exact sound.rest (popped := [.number key]) stackEquation member inRest
          · intro entry member
            exact sound.2.1 entry (List.mem_filter.mp member).1
        · cases stepped
      · cases stepped
  | pop =>
      simp only [step] at stepped
      split at stepped
      · rename_i top rest stackEquation
        cases stepped
        exact sound.replaceTop (popped := [top]) (pushed := []) stackEquation
          (fun _ member => nomatch member)
      · cases stepped
  | nil =>
      cases stepped
      exact sound.pushSound (popped := []) rfl
        (.ofNoSequent fun _ contains => by
          cases contains with
          | list member _ => cases member)
  | cons =>
      simp only [step] at stepped
      split at stepped
      · rename_i tail head rest stackEquation
        cases stepped
        have poppedSound := sound.popped (popped := [.list tail, head]) stackEquation
        have tailSound := poppedSound _ List.mem_cons_self
        have headSound := poppedSound _ (List.mem_cons_of_mem _ List.mem_cons_self)
        refine sound.pushSound (popped := [.list tail, head]) stackEquation ?_
        intro sequent contains
        cases contains with
        | list member elementContains =>
            rcases List.mem_cons.mp member with isHead | inTail
            · rw [isHead] at elementContains
              exact headSound sequent elementContains
            · exact tailSound sequent (.list inTail elementContains)
      · cases stepped

theorem runCommands_sound :
    {state final : MachineState} → {commands : List NumberedCommand} → StateSound state →
      runCommands state commands = .ok final → StateSound final
  | state, final, [], sound, ran => by
      simp only [runCommands] at ran
      cases ran
      exact sound
  | state, final, numbered :: rest, sound, ran => by
      simp only [runCommands] at ran
      split at ran
      · rename_i next stepped
        exact runCommands_sound (step_sound sound stepped) ran
      · cases ran

/-- Soundness of the reader. When it accepts `text` with the result `theory`:

1. every exported theorem has no hypotheses and is an equation `left = right` with
   `Derivable imports left right`, the import set being the equations of `theory.assumptions`;
2. every assumption has no hypotheses and is an equation, so the import set has one equation for
   each assumption;
3. every theorem the machine holds in any state it reaches from the initial state has no
   hypotheses. The states reached while reading `text` are among them: they are
   `runCommands MachineState.initial` of the prefixes of the commands after the version header. -/
theorem readArticle_sound {text : String} {theory : Theory}
    (accepted : readArticle text = .ok theory) :
    (∀ exported ∈ theory.theorems, exported.hypotheses = [] ∧
      ∃ sideType left right, exported.conclusion = .equation sideType left right ∧
        Derivable (importEquations theory.assumptions) left right) ∧
    (∀ assumption ∈ theory.assumptions, assumption.hypotheses = [] ∧
      ∃ sideType left right, assumption.conclusion = .equation sideType left right) ∧
    (∀ commands state, runCommands .initial commands = .ok state →
      ∀ sequent, state.Holds sequent → sequent.hypotheses = []) := by
  have everyState : ∀ commands state, runCommands .initial commands = .ok state →
      StateSound state := fun _ _ ran => runCommands_sound StateSound.initial ran
  refine ⟨?_, ?_, ?_⟩
  · unfold readArticle readLines at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · split at accepted
        · rename_i final ran
          cases accepted
          exact (everyState _ _ ran).2.2.2
        · cases accepted
      · cases accepted
    · cases accepted
  · unfold readArticle readLines at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · split at accepted
        · rename_i final ran
          cases accepted
          intro assumption member
          obtain ⟨noHypotheses, sideType, left, right, isEquation, _⟩ :=
            (everyState _ _ ran).2.2.1 assumption member
          exact ⟨noHypotheses, sideType, left, right, isEquation⟩
        · cases accepted
      · cases accepted
    · cases accepted
  · intro commands state ran sequent holds
    obtain ⟨stackSound, dictionarySound, assumptionsSound, theoremsSound⟩ :=
      everyState commands state ran
    rcases holds with ⟨object, member, contains⟩ | ⟨entry, member, contains⟩ | member | member
    · exact (stackSound object member sequent contains).1
    · exact (dictionarySound entry member sequent contains).1
    · exact (assumptionsSound sequent member).1
    · exact (theoremsSound sequent member).1

end LambdaJit.Article
