import LambdaJit.Readback

/-!
# Confluence of the oriented rules of ⊢^{defunctionalized}_{λ-lattice-η}

This module proves that two finite terms equal in λ-lattice-η on defunctionalized terms
(module `Theory`, the relation `Equal`) reduce to a common term, for a reduction that orients the
rules of `Equal` from left to right (`equalJoinable`), and draws the consequence used by D3's item 4: a thunk with holes that is not shaped as the left
side of the defunctionalized η rule keeps its code and its holes under reduction, so two such
thunks with different codes or different holes are never equal (`notEqualThunks`), and neither
are two choices whose left sides are such thunks (`notEqualChoices`).

## The reduction

`Reduces` contracts, at once, any set of redexes of a finite term: the parallel reduction of Tait and
Martin-Löf, called simultaneous here because the calculus already has an operator named parallel.
Its redexes are the left sides of the three rules of `Equal` that are no congruence: an application
of a thunk with holes (the first clause of the defunctionalized β rule), a thunk without holes
(its second clause) and a thunk shaped as the left side of the defunctionalized η rule. Inside a
thunk, only the fillings reduce: no rule of `Equal` rewrites inside a code.

A thunk without holes reduces to the instance of its code under a slot reading that is total
(`Readback.readClamped`, which `Readback.readSlot` instantiates on terms): a slot beyond the
fillings reads the last filling, and a default when there is none. `Equal`'s second β clause
takes the instance only where every slot read has a filling, and there the two agree
(`instantiateClampedOfInstantiate`); with the strict instance the reduction would not be
confluent. The witness: the code `apply (slot 0) (slot 5)` with the holes `[slot 5]` and one
filling `F` is the left side of an η rule, so applied to `a` it reduces to `apply F a`; by the
first β clause it also reduces to the thunk without holes whose fillings are `[F, a]`, whose
strict instance is undefined, slot 5 lying beyond them, while its clamped instance is `apply F a`
again.

## The proof

Takahashi's method: `develop` contracts every redex of a term at once (choosing the η rule where an
application's function is an η redex), every one-step reduct of a term reduces in one step to its
development (`reducesDevelop`), so the reduction has the diamond property, and its reflexive
transitive closure is confluent (`confluent`). Every rule of `Equal` is a reduction step or a
congruence of reductions, so `Equal` relates only terms that reduce to a common term.
-/

namespace LambdaJit.Confluence

open LambdaJit.Readback

/-! ## Total instantiation -/

/-- The thunk of λx. x, the value of a slot read beyond an empty list of fillings:
`instantiateClamped` needs some finite term there, and any closed one serves, since where every
slot read has a filling the clamped instance is the strict one (`instantiateClampedOfInstantiate`)
and no proof reads this one. -/
def defaultFilling : FiniteTerm := .thunk (.slot 0) [.slot 0] []

mutual
/-- The instance of a code under its fillings, every slot read by `readClamped` with
`defaultFilling` as the default. -/
def instantiateClamped (fillings : List FiniteTerm) : Code → FiniteTerm
  | .slot index => readClamped defaultFilling fillings index
  | .apply function argument =>
      .apply (instantiateClamped fillings function) (instantiateClamped fillings argument)
  | .thunk code holes codes => .thunk code holes (instantiateClampedList fillings codes)
  | .choice left right =>
      .choice (instantiateClamped fillings left) (instantiateClamped fillings right)
  | .parallel left right =>
      .parallel (instantiateClamped fillings left) (instantiateClamped fillings right)

/-- `instantiateClamped` on each code of a list. -/
def instantiateClampedList (fillings : List FiniteTerm) : List Code → List FiniteTerm
  | [] => []
  | code :: codes => instantiateClamped fillings code :: instantiateClampedList fillings codes
end

mutual
/-- Where `Code.instantiate` is defined, `instantiateClamped` is the same instance. -/
theorem instantiateClampedOfInstantiate (fillings : List FiniteTerm) :
    ∀ (code : Code) (term : FiniteTerm), code.instantiate fillings = some term →
      instantiateClamped fillings code = term
  | .slot index, term, instantiated => by
      simp only [Code.instantiate] at instantiated
      simp only [instantiateClamped, readClamped, instantiated]
  | .apply function argument, term, instantiated => by
      cases functionInstance : function.instantiate fillings with
      | none => simp [Code.instantiate, functionInstance, bind, Option.bind] at instantiated
      | some functionTerm =>
        cases argumentInstance : argument.instantiate fillings with
        | none =>
            simp [Code.instantiate, functionInstance, argumentInstance, bind, Option.bind]
              at instantiated
        | some argumentTerm =>
            simp only [Code.instantiate, functionInstance, argumentInstance, bind, Option.bind,
              pure, Option.some.injEq] at instantiated
            subst instantiated
            simp only [instantiateClamped,
              instantiateClampedOfInstantiate fillings function functionTerm functionInstance,
              instantiateClampedOfInstantiate fillings argument argumentTerm argumentInstance]
  | .thunk code holes codes, term, instantiated => by
      cases codesInstance : Code.instantiateList fillings codes with
      | none => simp [Code.instantiate, codesInstance, bind, Option.bind] at instantiated
      | some terms =>
          simp only [Code.instantiate, codesInstance, bind, Option.bind, pure,
            Option.some.injEq] at instantiated
          subst instantiated
          simp only [instantiateClamped,
            instantiateClampedListOfInstantiateList fillings codes terms codesInstance]
  | .choice left right, term, instantiated => by
      cases leftInstance : left.instantiate fillings with
      | none => simp [Code.instantiate, leftInstance, bind, Option.bind] at instantiated
      | some leftTerm =>
        cases rightInstance : right.instantiate fillings with
        | none =>
            simp [Code.instantiate, leftInstance, rightInstance, bind, Option.bind] at instantiated
        | some rightTerm =>
            simp only [Code.instantiate, leftInstance, rightInstance, bind, Option.bind, pure,
              Option.some.injEq] at instantiated
            subst instantiated
            simp only [instantiateClamped,
              instantiateClampedOfInstantiate fillings left leftTerm leftInstance,
              instantiateClampedOfInstantiate fillings right rightTerm rightInstance]
  | .parallel left right, term, instantiated => by
      cases leftInstance : left.instantiate fillings with
      | none => simp [Code.instantiate, leftInstance, bind, Option.bind] at instantiated
      | some leftTerm =>
        cases rightInstance : right.instantiate fillings with
        | none =>
            simp [Code.instantiate, leftInstance, rightInstance, bind, Option.bind] at instantiated
        | some rightTerm =>
            simp only [Code.instantiate, leftInstance, rightInstance, bind, Option.bind, pure,
              Option.some.injEq] at instantiated
            subst instantiated
            simp only [instantiateClamped,
              instantiateClampedOfInstantiate fillings left leftTerm leftInstance,
              instantiateClampedOfInstantiate fillings right rightTerm rightInstance]

/-- `instantiateClampedOfInstantiate` on each code of a list. -/
theorem instantiateClampedListOfInstantiateList (fillings : List FiniteTerm) :
    ∀ (codes : List Code) (terms : List FiniteTerm),
      Code.instantiateList fillings codes = some terms →
        instantiateClampedList fillings codes = terms
  | [], terms, instantiated => by
      simp only [Code.instantiateList, Option.some.injEq] at instantiated
      subst instantiated
      rfl
  | code :: codes, terms, instantiated => by
      cases headInstance : code.instantiate fillings with
      | none => simp [Code.instantiateList, headInstance, bind, Option.bind] at instantiated
      | some head =>
        cases tailInstance : Code.instantiateList fillings codes with
        | none =>
            simp [Code.instantiateList, headInstance, tailInstance, bind, Option.bind]
              at instantiated
        | some tail =>
            simp only [Code.instantiateList, headInstance, tailInstance, bind, Option.bind, pure,
              Option.some.injEq] at instantiated
            subst instantiated
            simp only [instantiateClampedList,
              instantiateClampedOfInstantiate fillings code head headInstance,
              instantiateClampedListOfInstantiateList fillings codes tail tailInstance]
end

/-! ## The reduction -/

/-- The position of the filling that a thunk shaped as the left side of the defunctionalized η
rule equals: its code is `apply (slot function) (slot hole)`, its holes are `[slot hole]`, and
`function` is another slot than `hole`. -/
def etaPosition : Code → List Hole → Option Nat
  | .apply (.slot function) (.slot hole), [.slot holeSlot] =>
      if hole = holeSlot ∧ function ≠ hole then some (fillingPosition [.slot hole] function)
      else none
  | _, _ => none

theorem etaPositionSome {code : Code} {holes : List Hole} {position : Nat}
    (found : etaPosition code holes = some position) :
    ∃ function hole, code = .apply (.slot function) (.slot hole) ∧ holes = [.slot hole] ∧
      function ≠ hole ∧ position = fillingPosition [.slot hole] function := by
  unfold etaPosition at found
  split at found
  · rename_i function hole holeSlot
    by_cases shaped : hole = holeSlot ∧ function ≠ hole
    · rw [if_pos shaped, Option.some.injEq] at found
      obtain ⟨sameHole, distinct⟩ := shaped
      subst sameHole
      exact ⟨function, hole, rfl, rfl, distinct, found.symm⟩
    · rw [if_neg shaped] at found
      cases found
  · cases found

theorem etaPositionOfShape {function hole : Nat} (distinct : function ≠ hole) :
    etaPosition (.apply (.slot function) (.slot hole)) [.slot hole] =
      some (fillingPosition [.slot hole] function) := by
  simp [etaPosition, distinct]

theorem etaPositionNil (code : Code) : etaPosition code [] = none := by
  unfold etaPosition
  split
  · rename_i holes _ equal
    cases equal
  · rfl

mutual
/-- One step of simultaneous reduction: any set of redexes contracted at once, every operand
reducing in the same step. -/
def Reduces : FiniteTerm → FiniteTerm → Prop
  | .thunk code holes fillings, result =>
      (∃ results, ReducesList fillings results ∧ result = .thunk code holes results) ∨
      (holes = [] ∧ ∃ results, ReducesList fillings results ∧
        result = instantiateClamped results code) ∨
      (∃ position, etaPosition code holes = some position ∧
        ∃ results, ReducesList fillings results ∧ results[position]? = some result)
  | .apply function argument, result =>
      (∃ functionResult argumentResult, Reduces function functionResult ∧
        Reduces argument argumentResult ∧ result = .apply functionResult argumentResult) ∨
      (match function with
        | .thunk code (hole :: holes) fillings =>
            ∃ results argumentResult, ReducesList fillings results ∧
              Reduces argument argumentResult ∧
                result = .thunk code holes (fill hole holes results argumentResult)
        | _ => False)
  | .choice left right, result =>
      ∃ leftResult rightResult, Reduces left leftResult ∧ Reduces right rightResult ∧
        result = .choice leftResult rightResult
  | .parallel left right, result =>
      ∃ leftResult rightResult, Reduces left leftResult ∧ Reduces right rightResult ∧
        result = .parallel leftResult rightResult

/-- Simultaneous reduction of two lists, element by element. -/
def ReducesList : List FiniteTerm → List FiniteTerm → Prop
  | [], [] => True
  | term :: terms, result :: results => Reduces term result ∧ ReducesList terms results
  | _, _ => False
end

/-! ## Reflexivity and lists -/

mutual
theorem reducesReflexive : ∀ term : FiniteTerm, Reduces term term
  | .thunk code holes fillings => by
      unfold Reduces
      exact Or.inl ⟨fillings, reducesListReflexive fillings, rfl⟩
  | .apply function argument => by
      unfold Reduces
      exact Or.inl ⟨function, argument, reducesReflexive function, reducesReflexive argument, rfl⟩
  | .choice left right => by
      unfold Reduces
      exact ⟨left, right, reducesReflexive left, reducesReflexive right, rfl⟩
  | .parallel left right => by
      unfold Reduces
      exact ⟨left, right, reducesReflexive left, reducesReflexive right, rfl⟩

theorem reducesListReflexive : ∀ terms : List FiniteTerm, ReducesList terms terms
  | [] => by unfold ReducesList; trivial
  | term :: terms => by
      unfold ReducesList
      exact ⟨reducesReflexive term, reducesListReflexive terms⟩
end

theorem reducesListCons {term result : FiniteTerm} {terms results : List FiniteTerm} :
    ReducesList (term :: terms) (result :: results) ↔
      Reduces term result ∧ ReducesList terms results :=
  Iff.rfl

theorem reducesListLength : ∀ (terms results : List FiniteTerm), ReducesList terms results →
    terms.length = results.length
  | [], [], _ => rfl
  | _ :: terms, _ :: results, reduces => by
      have tail := (reducesListCons.mp reduces).2
      simp [reducesListLength terms results tail]
  | [], _ :: _, reduces => by unfold ReducesList at reduces; exact reduces.elim
  | _ :: _, [], reduces => by unfold ReducesList at reduces; exact reduces.elim

theorem reducesListGet : ∀ (terms results : List FiniteTerm), ReducesList terms results →
    ∀ (index : Nat) (term : FiniteTerm), terms[index]? = some term →
      ∃ result, results[index]? = some result ∧ Reduces term result
  | [], _, _, _, _, found => by simp at found
  | _ :: _, [], reduces, _, _, _ => by unfold ReducesList at reduces; exact reduces.elim
  | head :: terms, result :: results, reduces, 0, term, found => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact ⟨result, rfl, (reducesListCons.mp reduces).1⟩
  | _ :: terms, _ :: results, reduces, index + 1, term, found => by
      simp only [List.getElem?_cons_succ] at found ⊢
      exact reducesListGet terms results (reducesListCons.mp reduces).2 index term found

theorem reducesListGetRight : ∀ (terms results : List FiniteTerm), ReducesList terms results →
    ∀ (index : Nat) (result : FiniteTerm), results[index]? = some result →
      ∃ term, terms[index]? = some term ∧ Reduces term result
  | _, [], _, _, _, found => by simp at found
  | [], _ :: _, reduces, _, _, _ => by unfold ReducesList at reduces; exact reduces.elim
  | term :: terms, head :: results, reduces, 0, result, found => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact ⟨term, rfl, (reducesListCons.mp reduces).1⟩
  | _ :: terms, _ :: results, reduces, index + 1, result, found => by
      simp only [List.getElem?_cons_succ] at found ⊢
      exact reducesListGetRight terms results (reducesListCons.mp reduces).2 index result found

theorem reducesListAppend : ∀ (terms results more moreResults : List FiniteTerm),
    ReducesList terms results → ReducesList more moreResults →
      ReducesList (terms ++ more) (results ++ moreResults)
  | [], [], _, _, _, moreReduce => moreReduce
  | _ :: terms, _ :: results, more, moreResults, reduces, moreReduce => by
      simp only [List.cons_append]
      exact reducesListCons.mpr ⟨(reducesListCons.mp reduces).1,
        reducesListAppend terms results more moreResults (reducesListCons.mp reduces).2 moreReduce⟩
  | [], _ :: _, _, _, reduces, _ => by unfold ReducesList at reduces; exact reduces.elim
  | _ :: _, [], _, _, reduces, _ => by unfold ReducesList at reduces; exact reduces.elim

theorem reducesListTake : ∀ (count : Nat) (terms results : List FiniteTerm),
    ReducesList terms results → ReducesList (terms.take count) (results.take count)
  | 0, _, _, _ => by simp only [List.take_zero]; unfold ReducesList; trivial
  | _ + 1, [], [], _ => by simp only [List.take_nil]; unfold ReducesList; trivial
  | count + 1, _ :: terms, _ :: results, reduces => by
      simp only [List.take_succ_cons]
      exact reducesListCons.mpr ⟨(reducesListCons.mp reduces).1,
        reducesListTake count terms results (reducesListCons.mp reduces).2⟩
  | _ + 1, [], _ :: _, reduces => by unfold ReducesList at reduces; exact reduces.elim
  | _ + 1, _ :: _, [], reduces => by unfold ReducesList at reduces; exact reduces.elim

theorem reducesListDrop : ∀ (count : Nat) (terms results : List FiniteTerm),
    ReducesList terms results → ReducesList (terms.drop count) (results.drop count)
  | 0, _, _, reduces => by simpa using reduces
  | _ + 1, [], [], _ => by simp only [List.drop_nil]; unfold ReducesList; trivial
  | count + 1, _ :: terms, _ :: results, reduces => by
      simp only [List.drop_succ_cons]
      exact reducesListDrop count terms results (reducesListCons.mp reduces).2
  | _ + 1, [], _ :: _, reduces => by unfold ReducesList at reduces; exact reduces.elim
  | _ + 1, _ :: _, [], reduces => by unfold ReducesList at reduces; exact reduces.elim

/-- Filling a hole is compatible with reduction. -/
theorem reducesListFill (hole : Hole) (holes : List Hole) {fillings results : List FiniteTerm}
    {argument argumentResult : FiniteTerm} (fillingsReduce : ReducesList fillings results)
    (argumentReduces : Reduces argument argumentResult) :
    ReducesList (fill hole holes fillings argument) (fill hole holes results argumentResult) := by
  cases hole with
  | ignored => exact fillingsReduce
  | slot index =>
      simp only [fill]
      exact reducesListAppend _ _ _ _
        (reducesListTake _ fillings results fillingsReduce)
        (reducesListCons.mpr ⟨argumentReduces,
          reducesListDrop _ fillings results fillingsReduce⟩)

/-- Replacing one element of a list by a reduct is a reduction of the list. -/
theorem reducesListAt (before after : List FiniteTerm) {term result : FiniteTerm}
    (reduces : Reduces term result) :
    ReducesList (before ++ term :: after) (before ++ result :: after) :=
  reducesListAppend _ _ _ _ (reducesListReflexive before)
    (reducesListCons.mpr ⟨reduces, reducesListReflexive after⟩)

theorem reducesReadClamped {fillings results : List FiniteTerm}
    (reduces : ReducesList fillings results) (index : Nat) :
    Reduces (readClamped defaultFilling fillings index) (readClamped defaultFilling results index) := by
  have sameLength := reducesListLength fillings results reduces
  unfold readClamped
  cases found : fillings[index]? with
  | some term =>
      obtain ⟨result, resultFound, termReduces⟩ :=
        reducesListGet fillings results reduces index term found
      simp only [resultFound]
      exact termReduces
  | none =>
      have resultAbsent : results[index]? = none := by
        rw [List.getElem?_eq_none_iff] at found ⊢
        omega
      simp only [resultAbsent, List.getLast?_eq_getElem?]
      cases lastFound : fillings[fillings.length - 1]? with
      | some term =>
          obtain ⟨result, resultFound, termReduces⟩ :=
            reducesListGet fillings results reduces _ term lastFound
          rw [← sameLength, resultFound]
          exact termReduces
      | none =>
          have lastAbsent : results[results.length - 1]? = none := by
            rw [List.getElem?_eq_none_iff] at lastFound ⊢
            omega
          simp only [lastAbsent, Option.getD_none]
          exact reducesReflexive _

mutual
/-- Instantiating one code under fillings and under their reducts is a reduction. -/
theorem reducesInstantiate : ∀ (fillings results : List FiniteTerm) (code : Code),
    ReducesList fillings results →
      Reduces (instantiateClamped fillings code) (instantiateClamped results code)
  | fillings, results, .slot index, reduces => by
      simp only [instantiateClamped]
      exact reducesReadClamped reduces index
  | fillings, results, .apply function argument, reduces => by
      simp only [instantiateClamped]
      unfold Reduces
      exact Or.inl ⟨_, _, reducesInstantiate fillings results function reduces,
        reducesInstantiate fillings results argument reduces, rfl⟩
  | fillings, results, .thunk code holes codes, reduces => by
      simp only [instantiateClamped]
      unfold Reduces
      exact Or.inl ⟨_, reducesInstantiateList fillings results codes reduces, rfl⟩
  | fillings, results, .choice left right, reduces => by
      simp only [instantiateClamped]
      unfold Reduces
      exact ⟨_, _, reducesInstantiate fillings results left reduces,
        reducesInstantiate fillings results right reduces, rfl⟩
  | fillings, results, .parallel left right, reduces => by
      simp only [instantiateClamped]
      unfold Reduces
      exact ⟨_, _, reducesInstantiate fillings results left reduces,
        reducesInstantiate fillings results right reduces, rfl⟩

/-- `reducesInstantiate` on each code of a list. -/
theorem reducesInstantiateList : ∀ (fillings results : List FiniteTerm) (codes : List Code),
    ReducesList fillings results →
      ReducesList (instantiateClampedList fillings codes) (instantiateClampedList results codes)
  | _, _, [], _ => by simp only [instantiateClampedList]; unfold ReducesList; trivial
  | fillings, results, code :: codes, reduces => by
      simp only [instantiateClampedList]
      exact reducesListCons.mpr ⟨reducesInstantiate fillings results code reduces,
        reducesInstantiateList fillings results codes reduces⟩
end

/-! ## The development -/

/-- Whether a thunk of code `code`, holes `holes` and `count` fillings is the left side of a
defunctionalized η rule, the filling it equals being present. -/
def etaRedex (code : Code) (holes : List Hole) (count : Nat) : Bool :=
  match etaPosition code holes with
  | some position => decide (position < count)
  | none => false

/-- The development of a thunk whose fillings are developed: the instance of its code when it has
no hole, the filling an η redex equals, or the thunk. -/
def developThunk (code : Code) (holes : List Hole) (developed : List FiniteTerm) : FiniteTerm :=
  match holes, etaPosition code holes with
  | [], _ => instantiateClamped developed code
  | _ :: _, some position => (developed[position]?).getD (.thunk code holes developed)
  | _ :: _, none => .thunk code holes developed

mutual
/-- Takahashi's complete development: every redex of the term contracted at once. An application
of a thunk with holes fills its first hole, unless the thunk is an η redex, which is contracted
instead. -/
def develop : FiniteTerm → FiniteTerm
  | .thunk code holes fillings => developThunk code holes (developList fillings)
  | .apply (function@(.thunk code (hole :: holes) fillings)) argument =>
      if etaRedex code (hole :: holes) fillings.length then
        .apply (develop function) (develop argument)
      else .thunk code holes (fill hole holes (developList fillings) (develop argument))
  | .apply function argument => .apply (develop function) (develop argument)
  | .choice left right => .choice (develop left) (develop right)
  | .parallel left right => .parallel (develop left) (develop right)

/-- `develop` on each term of a list. -/
def developList : List FiniteTerm → List FiniteTerm
  | [] => []
  | term :: terms => develop term :: developList terms
end

theorem developListMap : ∀ terms : List FiniteTerm, developList terms = terms.map develop
  | [] => by unfold developList; rfl
  | term :: terms => by
      unfold developList
      rw [developListMap terms, List.map_cons]

/-- A thunk whose fillings reduce to the developed fillings reduces to the development. -/
theorem reducesDevelopThunk (code : Code) (holes : List Hole) {results developed : List FiniteTerm}
    (reduces : ReducesList results developed) :
    Reduces (.thunk code holes results) (developThunk code holes developed) := by
  cases holes with
  | nil =>
      show Reduces (.thunk code [] results) (instantiateClamped developed code)
      unfold Reduces
      exact Or.inr (Or.inl ⟨rfl, developed, reduces, rfl⟩)
  | cons hole holes =>
      cases eta : etaPosition code (hole :: holes) with
      | none =>
          have developedIs : developThunk code (hole :: holes) developed =
              .thunk code (hole :: holes) developed := by
            simp only [developThunk, eta]
          rw [developedIs]
          unfold Reduces
          exact Or.inl ⟨developed, reduces, rfl⟩
      | some position =>
          cases found : developed[position]? with
          | none =>
              have developedIs : developThunk code (hole :: holes) developed =
                  .thunk code (hole :: holes) developed := by
                simp only [developThunk, eta, found, Option.getD_none]
              rw [developedIs]
              unfold Reduces
              exact Or.inl ⟨developed, reduces, rfl⟩
          | some term =>
              have developedIs : developThunk code (hole :: holes) developed = term := by
                simp only [developThunk, eta, found, Option.getD_some]
              rw [developedIs]
              unfold Reduces
              exact Or.inr (Or.inr ⟨position, eta, developed, reduces, found⟩)

/-- An application whose function is no thunk with holes reduces only by congruence, and its
development is the application of the developments. -/
theorem reducesDevelopCongruence {function argument result : FiniteTerm}
    (notFill : ∀ (code : Code) (hole : Hole) (holes : List Hole) (fillings : List FiniteTerm),
      function = .thunk code (hole :: holes) fillings → False)
    (functionDevelops : ∀ functionResult, Reduces function functionResult →
      Reduces functionResult (develop function))
    (argumentDevelops : ∀ argumentResult, Reduces argument argumentResult →
      Reduces argumentResult (develop argument))
    (reduces : Reduces (.apply function argument) result) :
    Reduces result (develop (.apply function argument)) := by
  rw [develop.eq_3 function argument notFill]
  have congruence : ∃ functionResult argumentResult, Reduces function functionResult ∧
      Reduces argument argumentResult ∧ result = .apply functionResult argumentResult := by
    unfold Reduces at reduces
    rcases reduces with congruence | filled
    · exact congruence
    · cases function with
      | thunk code holes fillings =>
          cases holes with
          | nil => exact filled.elim
          | cons hole holes => exact (notFill code hole holes fillings rfl).elim
      | apply _ _ => exact filled.elim
      | choice _ _ => exact filled.elim
      | parallel _ _ => exact filled.elim
  obtain ⟨functionResult, argumentResult, functionReduces, argumentReduces, resultIs⟩ := congruence
  subst resultIs
  unfold Reduces
  exact Or.inl ⟨_, _, functionDevelops _ functionReduces, argumentDevelops _ argumentReduces, rfl⟩

mutual
/-- Takahashi's lemma: every one-step reduct of a term reduces in one step to the term's
development. -/
theorem reducesDevelop : ∀ (term result : FiniteTerm), Reduces term result →
    Reduces result (develop term)
  | .thunk code holes fillings, result, reduces => by
      rw [develop.eq_1]
      unfold Reduces at reduces
      rcases reduces with ⟨results, fillingsReduce, resultIs⟩ |
        ⟨holesNil, results, fillingsReduce, resultIs⟩ |
        ⟨position, eta, results, fillingsReduce, found⟩
      · subst resultIs
        exact reducesDevelopThunk code holes (reducesListDevelop fillings results fillingsReduce)
      · subst resultIs
        subst holesNil
        exact reducesInstantiate results (developList fillings) code
          (reducesListDevelop fillings results fillingsReduce)
      · obtain ⟨developed, developedFound, resultReduces⟩ :=
          reducesListGet results (developList fillings)
            (reducesListDevelop fillings results fillingsReduce) position result found
        obtain ⟨_, hole, _, holesIs, _, _⟩ := etaPositionSome eta
        subst holesIs
        have developedIs : developThunk code [.slot hole] (developList fillings) = developed := by
          simp only [developThunk, eta, developedFound, Option.getD_some]
        rw [developedIs]
        exact resultReduces
  | .apply (.thunk code (hole :: holes) fillings) argument, result, reduces => by
      have fillingsDevelop := fun results (fillingsReduce : ReducesList fillings results) =>
        reducesListDevelop fillings results fillingsReduce
      have argumentDevelops := fun argumentResult (argumentReduces : Reduces argument argumentResult) =>
        reducesDevelop argument argumentResult argumentReduces
      have functionDevelops := fun functionResult
          (functionReduces : Reduces (.thunk code (hole :: holes) fillings) functionResult) =>
        reducesDevelop (.thunk code (hole :: holes) fillings) functionResult functionReduces
      rw [develop.eq_2]
      unfold Reduces at reduces
      by_cases redex : etaRedex code (hole :: holes) fillings.length = true
      · rw [if_pos redex]
        obtain ⟨position, eta, below⟩ : ∃ position,
            etaPosition code (hole :: holes) = some position ∧ position < fillings.length := by
          unfold etaRedex at redex
          cases eta : etaPosition code (hole :: holes) with
          | none =>
              rw [eta] at redex
              cases redex
          | some position =>
              rw [eta] at redex
              exact ⟨position, rfl, of_decide_eq_true redex⟩
        obtain ⟨functionIndex, holeIndex, codeIs, holesIs, distinct, positionIs⟩ :=
          etaPositionSome eta
        rcases reduces with
          ⟨functionResult, argumentResult, functionReduces, argumentReduces, resultIs⟩ |
          ⟨results, argumentResult, fillingsReduce, argumentReduces, resultIs⟩
        · subst resultIs
          unfold Reduces
          exact Or.inl ⟨_, _, functionDevelops _ functionReduces,
            argumentDevelops _ argumentReduces, rfl⟩
        · -- The critical pair of the first β clause and the η rule.
          subst resultIs
          injection holesIs with holeIs holesNil
          subst holeIs
          subst holesNil
          subst codeIs
          have developedLength : (developList fillings).length = fillings.length := by
            rw [developListMap, List.length_map]
          obtain ⟨developed, developedFound⟩ :
              ∃ developed, (developList fillings)[position]? = some developed :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          have functionDeveloped :
              develop (.thunk (.apply (.slot functionIndex) (.slot holeIndex)) [.slot holeIndex]
                fillings) = developed := by
            rw [develop.eq_1]
            simp only [developThunk, eta, developedFound, Option.getD_some]
          rw [functionDeveloped]
          have besideFound : (developList fillings)[if functionIndex < holeIndex then functionIndex
              else functionIndex - 1]? = some developed := by
            rw [← fillingPositionSingleton distinct, ← positionIs]
            exact developedFound
          have instantiated : instantiateClamped
              (fill (.slot holeIndex) [] (developList fillings) (develop argument))
              (.apply (.slot functionIndex) (.slot holeIndex)) =
                .apply developed (develop argument) := by
            simp only [instantiateClamped, fill, fillingPositionNil]
            rw [readClampedInserted,
              readClampedBesideInserted _ _ _ _ _ developed distinct besideFound]
          unfold Reduces
          exact Or.inr (Or.inl ⟨rfl, _,
            reducesListFill _ _ (fillingsDevelop results fillingsReduce)
              (argumentDevelops _ argumentReduces), instantiated.symm⟩)
      · rw [if_neg redex]
        rcases reduces with
          ⟨functionResult, argumentResult, functionReduces, argumentReduces, resultIs⟩ |
          ⟨results, argumentResult, fillingsReduce, argumentReduces, resultIs⟩
        · subst resultIs
          unfold Reduces at functionReduces
          rcases functionReduces with ⟨results, fillingsReduce, functionIs⟩ | ⟨holesNil, _⟩ |
            ⟨position, eta, results, fillingsReduce, found⟩
          · subst functionIs
            unfold Reduces
            exact Or.inr ⟨developList fillings, develop argument,
              fillingsDevelop results fillingsReduce, argumentDevelops _ argumentReduces, rfl⟩
          · cases holesNil
          · exfalso
            apply redex
            have sameLength := reducesListLength _ _ fillingsReduce
            have within := (List.getElem?_eq_some_iff.mp found).1
            unfold etaRedex
            rw [eta]
            exact decide_eq_true (by omega)
        · subst resultIs
          unfold Reduces
          exact Or.inl ⟨_, reducesListFill hole holes (fillingsDevelop results fillingsReduce)
            (argumentDevelops _ argumentReduces), rfl⟩
  | .apply (.thunk code [] fillings) argument, result, reduces =>
      reducesDevelopCongruence (fun _ _ _ _ equal => by cases equal)
        (fun functionResult functionReduces =>
          reducesDevelop (.thunk code [] fillings) functionResult functionReduces)
        (fun argumentResult argumentReduces => reducesDevelop argument argumentResult argumentReduces)
        reduces
  | .apply (.apply innerFunction innerArgument) argument, result, reduces =>
      reducesDevelopCongruence (fun _ _ _ _ equal => by cases equal)
        (fun functionResult functionReduces =>
          reducesDevelop (.apply innerFunction innerArgument) functionResult functionReduces)
        (fun argumentResult argumentReduces => reducesDevelop argument argumentResult argumentReduces)
        reduces
  | .apply (.choice left right) argument, result, reduces =>
      reducesDevelopCongruence (fun _ _ _ _ equal => by cases equal)
        (fun functionResult functionReduces =>
          reducesDevelop (.choice left right) functionResult functionReduces)
        (fun argumentResult argumentReduces => reducesDevelop argument argumentResult argumentReduces)
        reduces
  | .apply (.parallel left right) argument, result, reduces =>
      reducesDevelopCongruence (fun _ _ _ _ equal => by cases equal)
        (fun functionResult functionReduces =>
          reducesDevelop (.parallel left right) functionResult functionReduces)
        (fun argumentResult argumentReduces => reducesDevelop argument argumentResult argumentReduces)
        reduces
  | .choice left right, result, reduces => by
      rw [develop.eq_4]
      unfold Reduces at reduces
      obtain ⟨leftResult, rightResult, leftReduces, rightReduces, resultIs⟩ := reduces
      subst resultIs
      unfold Reduces
      exact ⟨_, _, reducesDevelop left leftResult leftReduces,
        reducesDevelop right rightResult rightReduces, rfl⟩
  | .parallel left right, result, reduces => by
      rw [develop.eq_5]
      unfold Reduces at reduces
      obtain ⟨leftResult, rightResult, leftReduces, rightReduces, resultIs⟩ := reduces
      subst resultIs
      unfold Reduces
      exact ⟨_, _, reducesDevelop left leftResult leftReduces,
        reducesDevelop right rightResult rightReduces, rfl⟩

/-- `reducesDevelop` on each term of a list. -/
theorem reducesListDevelop : ∀ (terms results : List FiniteTerm), ReducesList terms results →
    ReducesList results (developList terms)
  | [], [], _ => by
      unfold developList
      unfold ReducesList
      trivial
  | term :: terms, result :: results, reduces => by
      unfold developList
      exact reducesListCons.mpr ⟨reducesDevelop term result (reducesListCons.mp reduces).1,
        reducesListDevelop terms results (reducesListCons.mp reduces).2⟩
  | [], _ :: _, reduces => by unfold ReducesList at reduces; exact reduces.elim
  | _ :: _, [], reduces => by unfold ReducesList at reduces; exact reduces.elim
end

/-! ## Confluence -/

/-- The reflexive transitive closure of `Reduces`. -/
inductive ReducesMany : FiniteTerm → FiniteTerm → Prop where
  | reflexive (term : FiniteTerm) : ReducesMany term term
  | step {first middle last : FiniteTerm} :
      Reduces first middle → ReducesMany middle last → ReducesMany first last

theorem ReducesMany.single {first second : FiniteTerm} (reduces : Reduces first second) :
    ReducesMany first second :=
  .step reduces (.reflexive second)

theorem ReducesMany.transitive {first middle last : FiniteTerm}
    (firstPart : ReducesMany first middle) (secondPart : ReducesMany middle last) :
    ReducesMany first last := by
  induction firstPart with
  | reflexive _ => exact secondPart
  | step reduces _ inner => exact .step reduces (inner secondPart)

/-- A context compatible with one step is compatible with many. -/
theorem ReducesMany.lift (context : FiniteTerm → FiniteTerm)
    (compatible : ∀ first second, Reduces first second → Reduces (context first) (context second))
    {first second : FiniteTerm} (reduces : ReducesMany first second) :
    ReducesMany (context first) (context second) := by
  induction reduces with
  | reflexive _ => exact .reflexive _
  | step reduces _ inner => exact .step (compatible _ _ reduces) inner

/-- The strip lemma: one step and many steps from one term reduce to a common term. -/
theorem strip {term first second : FiniteTerm} (reduces : Reduces term first)
    (many : ReducesMany term second) :
    ∃ common, ReducesMany first common ∧ Reduces second common := by
  induction many generalizing first with
  | reflexive _ => exact ⟨first, .reflexive first, reduces⟩
  | step stepReduces _ inner =>
      obtain ⟨common, commonMany, secondReduces⟩ := inner (reducesDevelop _ _ stepReduces)
      exact ⟨common, .step (reducesDevelop _ _ reduces) commonMany, secondReduces⟩

/-- Confluence: two reduction sequences from one term reduce to a common term. -/
theorem confluent {term first second : FiniteTerm} (firstMany : ReducesMany term first)
    (secondMany : ReducesMany term second) :
    ∃ common, ReducesMany first common ∧ ReducesMany second common := by
  induction firstMany generalizing second with
  | reflexive _ => exact ⟨second, secondMany, .reflexive second⟩
  | step reduces _ inner =>
      obtain ⟨middleCommon, middleMany, secondReduces⟩ := strip reduces secondMany
      obtain ⟨common, firstToCommon, middleToCommon⟩ := inner middleMany
      exact ⟨common, firstToCommon, .step secondReduces middleToCommon⟩

/-! ## Every equation of the IR theory is joinable -/

/-- Two terms that reduce to a common term. -/
def Joinable (left right : FiniteTerm) : Prop :=
  ∃ common, ReducesMany left common ∧ ReducesMany right common

theorem reducesThunkAt (code : Code) (holes : List Hole) (before after : List FiniteTerm)
    (first second : FiniteTerm) (reduces : Reduces first second) :
    Reduces (.thunk code holes (before ++ first :: after))
      (.thunk code holes (before ++ second :: after)) := by
  unfold Reduces
  exact Or.inl ⟨_, reducesListAt before after reduces, rfl⟩

theorem reducesChoiceLeft (right first second : FiniteTerm)
    (reduces : Reduces first second) :
    Reduces (.choice first right) (.choice second right) := by
  unfold Reduces
  exact ⟨_, _, reduces, reducesReflexive right, rfl⟩

theorem reducesChoiceRight (left first second : FiniteTerm)
    (reduces : Reduces first second) :
    Reduces (.choice left first) (.choice left second) := by
  unfold Reduces
  exact ⟨_, _, reducesReflexive left, reduces, rfl⟩

theorem reducesApplyFunction (argument first second : FiniteTerm)
    (reduces : Reduces first second) : Reduces (.apply first argument) (.apply second argument) := by
  unfold Reduces
  exact Or.inl ⟨_, _, reduces, reducesReflexive argument, rfl⟩

theorem reducesApplyArgument (function first second : FiniteTerm)
    (reduces : Reduces first second) : Reduces (.apply function first) (.apply function second) := by
  unfold Reduces
  exact Or.inl ⟨_, _, reducesReflexive function, reduces, rfl⟩

theorem reducesParallelLeft (right first second : FiniteTerm)
    (reduces : Reduces first second) :
    Reduces (.parallel first right) (.parallel second right) := by
  unfold Reduces
  exact ⟨_, _, reduces, reducesReflexive right, rfl⟩

theorem reducesParallelRight (left first second : FiniteTerm)
    (reduces : Reduces first second) :
    Reduces (.parallel left first) (.parallel left second) := by
  unfold Reduces
  exact ⟨_, _, reducesReflexive left, reduces, rfl⟩

/-- Two terms equal in λ-lattice-η on defunctionalized terms reduce to a common term: each
rule of `Equal` that is no congruence is one reduction step, each congruence lifts the common
reducts of its premises, and transitivity is confluence. -/
theorem equalJoinable {left right : FiniteTerm} (equal : Equal left right) :
    Joinable left right := by
  induction equal with
  | reflexive term => exact ⟨term, .reflexive _, .reflexive _⟩
  | symmetric _ inner =>
      obtain ⟨common, leftMany, rightMany⟩ := inner
      exact ⟨common, rightMany, leftMany⟩
  | transitive _ _ leftInner rightInner =>
      obtain ⟨leftCommon, leftMany, middleLeftMany⟩ := leftInner
      obtain ⟨rightCommon, middleRightMany, rightMany⟩ := rightInner
      obtain ⟨common, leftToCommon, rightToCommon⟩ := confluent middleLeftMany middleRightMany
      exact ⟨common, leftMany.transitive leftToCommon, rightMany.transitive rightToCommon⟩
  | @congruenceThunk code holes before after _ _ _ inner =>
      obtain ⟨common, leftMany, rightMany⟩ := inner
      exact ⟨_, leftMany.lift (fun term => .thunk code holes (before ++ term :: after))
          (reducesThunkAt code holes before after),
        rightMany.lift (fun term => .thunk code holes (before ++ term :: after))
          (reducesThunkAt code holes before after)⟩
  | @congruenceApply leftFunction leftArgument rightFunction rightArgument _ _ functionInner
      argumentInner =>
      obtain ⟨functionCommon, leftFunctionMany, rightFunctionMany⟩ := functionInner
      obtain ⟨argumentCommon, leftArgumentMany, rightArgumentMany⟩ := argumentInner
      exact ⟨.apply functionCommon argumentCommon,
        (leftFunctionMany.lift (fun term => .apply term leftArgument)
          (reducesApplyFunction leftArgument)).transitive
          (leftArgumentMany.lift (fun term => .apply functionCommon term)
            (reducesApplyArgument functionCommon)),
        (rightFunctionMany.lift (fun term => .apply term rightArgument)
          (reducesApplyFunction rightArgument)).transitive
          (rightArgumentMany.lift (fun term => .apply functionCommon term)
            (reducesApplyArgument functionCommon))⟩
  | @congruenceChoice leftLeft leftRight rightLeft rightRight _ _ leftInner rightInner =>
      obtain ⟨leftCommon, leftLeftMany, rightLeftMany⟩ := leftInner
      obtain ⟨rightCommon, leftRightMany, rightRightMany⟩ := rightInner
      exact ⟨.choice leftCommon rightCommon,
        (leftLeftMany.lift (fun term => .choice term leftRight)
          (reducesChoiceLeft leftRight)).transitive
          (leftRightMany.lift (fun term => .choice leftCommon term)
            (reducesChoiceRight leftCommon)),
        (rightLeftMany.lift (fun term => .choice term rightRight)
          (reducesChoiceLeft rightRight)).transitive
          (rightRightMany.lift (fun term => .choice leftCommon term)
            (reducesChoiceRight leftCommon))⟩
  | @congruenceParallel leftLeft leftRight rightLeft rightRight _ _ leftInner rightInner =>
      obtain ⟨leftCommon, leftLeftMany, rightLeftMany⟩ := leftInner
      obtain ⟨rightCommon, leftRightMany, rightRightMany⟩ := rightInner
      exact ⟨.parallel leftCommon rightCommon,
        (leftLeftMany.lift (fun term => .parallel term leftRight)
          (reducesParallelLeft leftRight)).transitive
          (leftRightMany.lift (fun term => .parallel leftCommon term)
            (reducesParallelRight leftCommon)),
        (rightLeftMany.lift (fun term => .parallel term rightRight)
          (reducesParallelLeft rightRight)).transitive
          (rightRightMany.lift (fun term => .parallel leftCommon term)
            (reducesParallelRight leftCommon))⟩
  | @betaFill code hole holes fillings argument =>
      have step : Reduces (.apply (.thunk code (hole :: holes) fillings) argument)
          (.thunk code holes (fill hole holes fillings argument)) := by
        unfold Reduces
        exact Or.inr ⟨fillings, argument, reducesListReflexive fillings,
          reducesReflexive argument, rfl⟩
      exact ⟨_, .single step, .reflexive _⟩
  | @betaInstance code fillings instantiated instantiation =>
      have step : Reduces (.thunk code [] fillings) instantiated := by
        unfold Reduces
        exact Or.inr (Or.inl ⟨rfl, fillings, reducesListReflexive fillings,
          (instantiateClampedOfInstantiate fillings code instantiated instantiation).symm⟩)
      exact ⟨_, .single step, .reflexive _⟩
  | @eta function hole fillings filling distinct found =>
      have step : Reduces (.thunk (.apply (.slot function) (.slot hole)) [.slot hole] fillings)
          filling := by
        unfold Reduces
        exact Or.inr (Or.inr ⟨_, etaPositionOfShape distinct, fillings,
          reducesListReflexive fillings, found⟩)
      exact ⟨_, .single step, .reflexive _⟩

/-! ## What reduction keeps -/

/-- A thunk with holes that is no η redex reduces only to a thunk of the same code and holes:
no rule rewrites inside a code. -/
theorem reducesThunkKeeps {code : Code} {holes : List Hole} {fillings : List FiniteTerm}
    {result : FiniteTerm} (nonempty : holes ≠ []) (notEta : etaPosition code holes = none)
    (reduces : Reduces (.thunk code holes fillings) result) :
    ∃ results, result = .thunk code holes results := by
  unfold Reduces at reduces
  rcases reduces with ⟨results, _, resultIs⟩ | ⟨holesNil, _⟩ | ⟨_, eta, _⟩
  · exact ⟨results, resultIs⟩
  · exact absurd holesNil nonempty
  · rw [notEta] at eta
    cases eta

theorem reducesManyThunkKeeps {code : Code} {holes : List Hole} {fillings : List FiniteTerm}
    {result : FiniteTerm} (nonempty : holes ≠ []) (notEta : etaPosition code holes = none)
    (reduces : ReducesMany (.thunk code holes fillings) result) :
    ∃ results, result = .thunk code holes results := by
  generalize start : FiniteTerm.thunk code holes fillings = term at reduces
  induction reduces generalizing fillings with
  | reflexive _ => exact ⟨fillings, start.symm⟩
  | step reduces _ inner =>
      subst start
      obtain ⟨results, middleIs⟩ := reducesThunkKeeps nonempty notEta reduces
      exact inner middleIs.symm

/-- Many steps of reduction, element by element. -/
def ReducesManyList : List FiniteTerm → List FiniteTerm → Prop
  | [], [] => True
  | term :: terms, result :: results => ReducesMany term result ∧ ReducesManyList terms results
  | _, _ => False

theorem reducesManyListReflexive : ∀ terms : List FiniteTerm, ReducesManyList terms terms
  | [] => trivial
  | term :: terms => ⟨.reflexive term, reducesManyListReflexive terms⟩

theorem reducesManyListStep : ∀ (terms middles results : List FiniteTerm),
    ReducesList terms middles → ReducesManyList middles results → ReducesManyList terms results
  | [], [], [], _, _ => trivial
  | _ :: terms, _ :: middles, _ :: results, first, rest =>
      ⟨.step (reducesListCons.mp first).1 rest.1,
        reducesManyListStep terms middles results (reducesListCons.mp first).2 rest.2⟩
  | [], _ :: _, _, first, _ => by unfold ReducesList at first; exact first.elim
  | _ :: _, [], _, first, _ => by unfold ReducesList at first; exact first.elim
  | [], [], _ :: _, _, rest => rest.elim
  | _ :: _, _ :: _, [], _, rest => rest.elim

theorem reducesManyListGet : ∀ (terms results : List FiniteTerm), ReducesManyList terms results →
    ∀ (index : Nat) (term : FiniteTerm), terms[index]? = some term →
      ∃ result, results[index]? = some result ∧ ReducesMany term result
  | [], _, _, _, _, found => by simp at found
  | _ :: _, [], many, _, _, _ => many.elim
  | head :: terms, result :: results, many, 0, term, found => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact ⟨result, rfl, many.1⟩
  | _ :: terms, _ :: results, many, index + 1, term, found => by
      simp only [List.getElem?_cons_succ] at found ⊢
      exact reducesManyListGet terms results many.2 index term found

/-- A choice reduces only to a choice of the reducts of its two sides. -/
theorem reducesManyChoiceKeeps {left right result : FiniteTerm}
    (reduces : ReducesMany (.choice left right) result) :
    ∃ leftResult rightResult, ReducesMany left leftResult ∧ ReducesMany right rightResult ∧
      result = .choice leftResult rightResult := by
  generalize start : FiniteTerm.choice left right = term at reduces
  induction reduces generalizing left right with
  | reflexive _ => exact ⟨left, right, .reflexive left, .reflexive right, start.symm⟩
  | step reduces _ inner =>
      subst start
      unfold Reduces at reduces
      obtain ⟨leftMiddle, rightMiddle, leftReduces, rightReduces, middleIs⟩ := reduces
      obtain ⟨leftResult, rightResult, leftMany, rightMany, resultIs⟩ := inner middleIs.symm
      exact ⟨leftResult, rightResult, .step leftReduces leftMany, .step rightReduces rightMany,
        resultIs⟩

/-! ## What the IR theory separates -/

/-- Two thunks with holes that are no η redexes and differ in their codes or their holes are not
equal in λ-lattice-η on defunctionalized terms. -/
theorem notEqualThunks {code otherCode : Code} {holes otherHoles : List Hole}
    {fillings otherFillings : List FiniteTerm}
    (nonempty : holes ≠ []) (notEta : etaPosition code holes = none)
    (otherNonempty : otherHoles ≠ []) (otherNotEta : etaPosition otherCode otherHoles = none)
    (differ : code ≠ otherCode ∨ holes ≠ otherHoles) :
    ¬ Equal (.thunk code holes fillings) (.thunk otherCode otherHoles otherFillings) := by
  intro equal
  obtain ⟨common, leftMany, rightMany⟩ := equalJoinable equal
  obtain ⟨leftResults, leftIs⟩ := reducesManyThunkKeeps nonempty notEta leftMany
  obtain ⟨rightResults, rightIs⟩ := reducesManyThunkKeeps otherNonempty otherNotEta rightMany
  rw [leftIs] at rightIs
  injection rightIs with codeEqual holesEqual _
  rcases differ with codeDiffer | holesDiffer
  · exact codeDiffer codeEqual
  · exact holesDiffer holesEqual

/-- Two choices are not equal in λ-lattice-η on defunctionalized terms when their left sides
are thunks as in `notEqualThunks`: a choice reduces only side by side, and no rule of the theory
swaps, merges or drops sides. -/
theorem notEqualChoices {right otherRight : FiniteTerm}
    {code otherCode : Code} {holes otherHoles : List Hole}
    {fillings otherFillings : List FiniteTerm}
    (nonempty : holes ≠ []) (notEta : etaPosition code holes = none)
    (otherNonempty : otherHoles ≠ []) (otherNotEta : etaPosition otherCode otherHoles = none)
    (differ : code ≠ otherCode ∨ holes ≠ otherHoles) :
    ¬ Equal (.choice (.thunk code holes fillings) right)
      (.choice (.thunk otherCode otherHoles otherFillings) otherRight) := by
  intro equal
  obtain ⟨common, leftMany, rightMany⟩ := equalJoinable equal
  obtain ⟨leftResult, _, leftResultMany, _, leftIs⟩ := reducesManyChoiceKeeps leftMany
  obtain ⟨rightResult, _, rightResultMany, _, rightIs⟩ := reducesManyChoiceKeeps rightMany
  rw [leftIs] at rightIs
  injection rightIs with resultsEqual _
  subst resultsEqual
  obtain ⟨_, leftThunk⟩ := reducesManyThunkKeeps nonempty notEta leftResultMany
  obtain ⟨_, rightThunk⟩ := reducesManyThunkKeeps otherNonempty otherNotEta rightResultMany
  rw [leftThunk] at rightThunk
  injection rightThunk with codeEqual holesEqual _
  rcases differ with codeDiffer | holesDiffer
  · exact codeDiffer codeEqual
  · exact holesDiffer holesEqual

end LambdaJit.Confluence
