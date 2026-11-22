import LambdaJit.Ir

/-!
# λ-lattice-η on defunctionalized terms, ⊢^{defunctionalized}_{λ-lattice-η}

This module holds ⊢^{defunctionalized}_{λ-lattice-η}, the equational theory over the IR of
design decision D2, as an inductive relation on
finite terms,
the solutions of stores (module `Ir`), and its reading on the addresses of a store
(`Store.Equal`). The rules:

- reflexivity, symmetry, transitivity;
- congruence for every constructor: a thunk's fillings, each rule replacing one filling, so that
  replacing every filling is a chain of them (`Equal.congruenceFillings`), and an application's
  function and argument, a choice's sides and a parallel's sides;
- the defunctionalized β rule, D2's two clauses: an application of a thunk with a hole fills
  its first hole, and a thunk with no hole left equals the instance of its code under its
  fillings;
- the defunctionalized η rule: a thunk with one hole whose code is `apply (slot function) (slot hole)`, with
  `function` another slot than `hole`, equals the filling of slot `function`.

There is no delta: a library name is a label on an address, not a layer (D1).

FIXME (2026-10-04, D2): the axioms of λ-lattice-η are the numbered equations (1), (3), (5) and https://github.com/Atry/private-overlay/issues/2016
(10), the other λ-lattice laws being theorems of them (module `LatticeEtaDerivability`), and none
of them is a rule here: their IR form is not settled, and neither is which of them the IR needs as
rules. Until it is, choices and parallels have congruence only, and a lemma that needs a
numbered equation (D5's second tier, and `parallel_types`, whose lemmas are theorems of
λ-lattice-η) is not a theorem of this relation. The derivations of the others from the four
axioms (module `FourEquations`) take β steps, and whether this relation follows them is not shown
(the second witness of module `Adequacy` is a β step it does not follow); those of (8) and (9)
also take steps under a binder, which it has no rule for (the next FIXME). https://github.com/Atry/private-overlay/issues/2017

FIXME (2026-10-04, D2 against D3): no rule rewrites inside a code (there is no rule under https://github.com/Atry/private-overlay/issues/2017
a binder), so `\x. x ((\y. y) x)` and `\x. x x`, whose equation ⊢_{λ-lattice-η} derives
by the β rule under the binder, are two thunks with different codes that this relation does not
relate; D3's item 4, which asks every step of ⊢_{λ-lattice-η} on a readback to have a step
here, needs such a rule.
-/

namespace LambdaJit

/-- Equality in λ-lattice-η on defunctionalized terms between two finite terms (D2). -/
inductive Equal : FiniteTerm → FiniteTerm → Prop where
  | reflexive (term : FiniteTerm) : Equal term term
  | symmetric {left right : FiniteTerm} : Equal left right → Equal right left
  | transitive {left middle right : FiniteTerm} :
      Equal left middle → Equal middle right → Equal left right
  /-- Two thunks of one code and one hole list are equal when one filling is replaced by
  an equal one. -/
  | congruenceThunk {code : Code} {holes : List Hole}
      {before after : List FiniteTerm} {left right : FiniteTerm} :
      Equal left right →
      Equal (.thunk code holes (before ++ left :: after))
        (.thunk code holes (before ++ right :: after))
  /-- Two applications are equal when their functions and their arguments are. -/
  | congruenceApply {leftFunction leftArgument rightFunction rightArgument : FiniteTerm} :
      Equal leftFunction rightFunction →
      Equal leftArgument rightArgument →
      Equal (.apply leftFunction leftArgument) (.apply rightFunction rightArgument)
  /-- Two choices are equal when their left sides and their right sides are. -/
  | congruenceChoice {leftLeft leftRight rightLeft rightRight : FiniteTerm} :
      Equal leftLeft rightLeft →
      Equal leftRight rightRight →
      Equal (.choice leftLeft leftRight) (.choice rightLeft rightRight)
  /-- Two parallels are equal when their left sides and their right sides are. -/
  | congruenceParallel {leftLeft leftRight rightLeft rightRight : FiniteTerm} :
      Equal leftLeft rightLeft →
      Equal leftRight rightRight →
      Equal (.parallel leftLeft leftRight) (.parallel rightLeft rightRight)
  /-- The defunctionalized β rule, first clause: applying a thunk fills its first hole (D1, D2). -/
  | betaFill {code : Code} {hole : Hole} {holes : List Hole}
      {fillings : List FiniteTerm} {argument : FiniteTerm} :
      Equal (.apply (.thunk code (hole :: holes) fillings) argument)
        (.thunk code holes (fill hole holes fillings argument))
  /-- The defunctionalized β rule, second clause: a thunk with no hole left equals the instance of its code
  under its fillings, which are then the values of all its slots in slot order (D2). -/
  | betaInstance {code : Code} {fillings : List FiniteTerm} {instantiated : FiniteTerm} :
      code.instantiate fillings = some instantiated →
      Equal (.thunk code [] fillings) instantiated
  /-- The defunctionalized η rule: a thunk with the one hole `hole` whose code applies slot `function` to slot
  `hole`, `function` another slot than `hole`, equals the filling of slot `function` (D2). -/
  | eta {function hole : Nat} {fillings : List FiniteTerm} {filling : FiniteTerm} :
      function ≠ hole →
      fillings[fillingPosition [.slot hole] function]? = some filling →
      Equal (.thunk (.apply (.slot function) (.slot hole)) [.slot hole] fillings) filling

/-- Two lists of terms, equal element by element. -/
def Pointwise {α β : Type} (relation : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | left :: lefts, right :: rights => relation left right ∧ Pointwise relation lefts rights
  | _, _ => False

namespace Equal

/-- Every filling of a thunk replaced by an equal one: a chain of `congruenceThunk`. -/
theorem congruenceFillings {code : Code} {holes : List Hole} :
    ∀ (before lefts rights : List FiniteTerm), Pointwise Equal lefts rights →
      Equal (.thunk code holes (before ++ lefts)) (.thunk code holes (before ++ rights))
  | before, [], [], _ => reflexive _
  | before, left :: lefts, right :: rights, ⟨headEqual, tailEqual⟩ => by
      have step := congruenceFillings (code := code) (holes := holes)
        (before ++ [right]) lefts rights tailEqual
      simp only [List.append_assoc, List.singleton_append] at step
      exact transitive (congruenceThunk headEqual) step
  | _, [], _ :: _, holds => holds.elim
  | _, _ :: _, [], holds => holds.elim

end Equal

/-- Two addresses of a store are equal in λ-lattice-η on defunctionalized terms when they
have solutions within one fuel
and the solutions are equal (D1, D2). An address without a solution is equal to nothing,
itself included. -/
def Store.Equal (store : Store) (left right : Address) : Prop :=
  ∃ fuel leftTerm rightTerm,
    store.solution fuel left = some leftTerm ∧
    store.solution fuel right = some rightTerm ∧
    LambdaJit.Equal leftTerm rightTerm

end LambdaJit
