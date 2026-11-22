import LambdaJit.SyntacticConsistency

/-!
# DdLP96's contextual preorder ⊑_O on Λ_{+∥}: head reduction, solvability, (S0) to (S4)

This module formalises the syntactic part of the contextual preorder record
(the record below): sections 2 and 3, and the definition of ⊑_O of its section 1. It needs no model.

- `HeadStep` is DdLP96's →hsa (M. Dezani-Ciancaglini, U. de'Liguoro, A. Piperno, Filter models for
  conjunctive-disjunctive λ-calculi, TCS 170, 1996; Definition 5): the rules (β), (ξ), (+a),
  (+app), (∥s), (∥app) and (ν_sa), on the terms of module `Terms`.
- `HeadReductionsAtMost steps term` says that no →hsa reduction sequence from `term` has more than
  `steps` steps, and `Solvable` is DdLP96's SOL_sa (Definition 6, written as Definition 4):
  some bound exists. `solvableIffAccessible` proves it equal to the accessibility of `term` under
  the converse of →hsa, the record's "the reduction tree is finite" (by König's lemma there; here
  by the finite list of successors `headSuccessors`).
- `ContextualPreorder` is DdLP96's ⊑_O (Definition 14), with contexts ranging over Λ_{+∥}
  (module `Terms`' `Context`); `ContextualEquivalence` is ≃_O. `ContextualNormalForm` is the set
  { N ∈ NF_βη | T ⊑_O N }: that set is OUR definition, built on DdLP96's Definition 14, which
  defines only the preorder.
- The record's (S0) to (S4): `headStepNoneIffHeadNormalForm` and `solvableOfHeadNormalForm` (S0);
  `solvableChoice` and `solvableParallel` with their step-count forms (S1);
  `solvableOfUniqueSuccessor` (S2); `solvableBetaSpine`, `solvableChoiceSpine` and
  `solvableParallelSpine` (S3); `solvableOfSolvableApplication`, lemma X (S4).

Lemma X is proved in a more general form than the record states: M N ∈ SOL gives M ∈ SOL for
every term N, not only for a variable x ∉ FV(M). The record's proof uses x only in the case
M = λy. M₀, through renaming; here that case uses that every →hsa step of M₀ is a step of
M₀[y := N] (`HeadStep.substitute`), which holds for every N.
-/

namespace LambdaJit.ContextualPreorder

open LambdaJit.Semantics
open LambdaJit.Semantics.Term

/-! ## Head reduction →hsa -/

/-- DdLP96's M ∉ Abst ∪ Par ∪ Sum, the side condition of (ν_sa): the term is not an abstraction,
a parallel or a choice. -/
def NotAbstractionParallelChoice : Term → Prop
  | .boundVariable _ => True
  | .abstraction _ => False
  | .application _ _ => True
  | .choice _ _ => False
  | .parallel _ _ => False

/-- DdLP96's head reduction →hsa (Definition 5). -/
inductive HeadStep : Term → Term → Prop where
  /-- (β): (λx. M) N → M[x := N]. -/
  | beta (body argument : Term) :
      HeadStep (.application (.abstraction body) argument) (instantiate body argument)
  /-- (ξ): λx. M → λx. M′ from M → M′. -/
  | abstraction {body result : Term} :
      HeadStep body result → HeadStep (.abstraction body) (.abstraction result)
  /-- (+a), on the left: M + N → M′ + N from M → M′. -/
  | choiceLeft {left result : Term} (right : Term) :
      HeadStep left result → HeadStep (.choice left right) (.choice result right)
  /-- (+a), on the right: N + M → N + M′ from M → M′. -/
  | choiceRight (left : Term) {right result : Term} :
      HeadStep right result → HeadStep (.choice left right) (.choice left result)
  /-- (+app): (M + N) L → M L + N L. -/
  | choiceApplication (left right argument : Term) :
      HeadStep (.application (.choice left right) argument)
        (.choice (.application left argument) (.application right argument))
  /-- (∥s): M ∥ N → M′ ∥ N′ from M → M′ and N → N′. -/
  | parallel {left leftResult right rightResult : Term} :
      HeadStep left leftResult → HeadStep right rightResult →
        HeadStep (.parallel left right) (.parallel leftResult rightResult)
  /-- (∥app): (M ∥ N) L → M L ∥ N L. -/
  | parallelApplication (left right argument : Term) :
      HeadStep (.application (.parallel left right) argument)
        (.parallel (.application left argument) (.application right argument))
  /-- (ν_sa): M N → M′ N from M → M′, when M ∉ Abst ∪ Par ∪ Sum. -/
  | function {function result : Term} (argument : Term) :
      NotAbstractionParallelChoice function → HeadStep function result →
        HeadStep (.application function argument) (.application result argument)

/-- The successors of an application whose function is `function`, given the successors of
`function`: the contractum of (β), (+app) or (∥app) when the function is an abstraction, a choice
or a parallel, and otherwise the successors of the function applied to the argument (ν_sa). -/
def applicationSuccessors : Term → Term → List Term → List Term
  | .boundVariable _, argument, functionSuccessors =>
      functionSuccessors.map (fun result => .application result argument)
  | .abstraction body, argument, _ => [instantiate body argument]
  | .application _ _, argument, functionSuccessors =>
      functionSuccessors.map (fun result => .application result argument)
  | .choice left right, argument, _ =>
      [.choice (.application left argument) (.application right argument)]
  | .parallel left right, argument, _ =>
      [.parallel (.application left argument) (.application right argument)]

/-- The list of the →hsa successors of a term: →hsa is finitely branching. -/
def headSuccessors : Term → List Term
  | .boundVariable _ => []
  | .abstraction body => (headSuccessors body).map .abstraction
  | .application function argument =>
      applicationSuccessors function argument (headSuccessors function)
  | .choice left right =>
      (headSuccessors left).map (fun result => .choice result right) ++
        (headSuccessors right).map (fun result => .choice left result)
  | .parallel left right =>
      (headSuccessors left).flatMap (fun leftResult =>
        (headSuccessors right).map (fun rightResult => .parallel leftResult rightResult))

/-- Every listed successor is a →hsa step. -/
theorem headStepOfMem : ∀ {term result : Term}, result ∈ headSuccessors term → HeadStep term result
  | .boundVariable _, _, member => by simp [headSuccessors] at member
  | .abstraction body, _, member => by
      simp only [headSuccessors, List.mem_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      exact .abstraction (headStepOfMem innerMember)
  | .choice left right, _, member => by
      simp only [headSuccessors, List.mem_append, List.mem_map] at member
      rcases member with ⟨inner, innerMember, rfl⟩ | ⟨inner, innerMember, rfl⟩
      · exact .choiceLeft right (headStepOfMem innerMember)
      · exact .choiceRight left (headStepOfMem innerMember)
  | .parallel left right, _, member => by
      simp only [headSuccessors, List.mem_flatMap, List.mem_map] at member
      obtain ⟨leftResult, leftMember, rightResult, rightMember, rfl⟩ := member
      exact .parallel (headStepOfMem leftMember) (headStepOfMem rightMember)
  | .application (.boundVariable index) argument, _, member => by
      simp [headSuccessors, applicationSuccessors] at member
  | .application (.abstraction body) argument, _, member => by
      simp only [headSuccessors, applicationSuccessors, List.mem_singleton] at member
      subst member
      exact .beta body argument
  | .application (.choice left right) argument, _, member => by
      simp only [headSuccessors, applicationSuccessors, List.mem_singleton] at member
      subst member
      exact .choiceApplication left right argument
  | .application (.parallel left right) argument, _, member => by
      simp only [headSuccessors, applicationSuccessors, List.mem_singleton] at member
      subst member
      exact .parallelApplication left right argument
  | .application (.application function inner) argument, _, member => by
      simp only [headSuccessors, applicationSuccessors, List.mem_map] at member
      obtain ⟨result, resultMember, rfl⟩ := member
      exact .function argument trivial (headStepOfMem resultMember)

/-- Every →hsa step is listed. -/
theorem memOfHeadStep {term result : Term} (step : HeadStep term result) :
    result ∈ headSuccessors term := by
  induction step with
  | beta body argument => simp [headSuccessors, applicationSuccessors]
  | abstraction _ inner => exact List.mem_map.mpr ⟨_, inner, rfl⟩
  | choiceLeft right _ inner =>
      exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨_, inner, rfl⟩))
  | choiceRight left _ inner =>
      exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨_, inner, rfl⟩))
  | choiceApplication left right argument => simp [headSuccessors, applicationSuccessors]
  | parallel _ _ leftInner rightInner =>
      exact List.mem_flatMap.mpr ⟨_, leftInner, List.mem_map.mpr ⟨_, rightInner, rfl⟩⟩
  | parallelApplication left right argument => simp [headSuccessors, applicationSuccessors]
  | @function function result argument notOther _ inner =>
      cases function with
      | boundVariable index => exact List.mem_map.mpr ⟨_, inner, rfl⟩
      | abstraction body => exact absurd notOther id
      | application inner argumentInner => exact List.mem_map.mpr ⟨_, inner, rfl⟩
      | choice left right => exact absurd notOther id
      | parallel left right => exact absurd notOther id

/-- →hsa is finitely branching: its successors are the members of `headSuccessors`. -/
theorem headStepIffMem {term result : Term} : HeadStep term result ↔ result ∈ headSuccessors term :=
  ⟨memOfHeadStep, headStepOfMem⟩

/-- A function that takes a →hsa step under (ν_sa) is an application: a variable has no
step, and an abstraction, a parallel and a choice are excluded by the side condition. -/
theorem applicationOfStepNotOther {function result : Term} (step : HeadStep function result)
    (notOther : NotAbstractionParallelChoice function) :
    ∃ inner argument, function = .application inner argument := by
  cases step with
  | beta body argument => exact ⟨_, _, rfl⟩
  | choiceApplication left right argument => exact ⟨_, _, rfl⟩
  | parallelApplication left right argument => exact ⟨_, _, rfl⟩
  | function argument _ _ => exact ⟨_, _, rfl⟩
  | abstraction _ => exact absurd notOther id
  | choiceLeft _ _ => exact absurd notOther id
  | choiceRight _ _ => exact absurd notOther id
  | parallel _ _ => exact absurd notOther id

/-- →hsa commutes with substitution: a step of M is a step of M[x := N], for every N. -/
theorem HeadStep.substitute {term result : Term} (step : HeadStep term result) :
    ∀ (depth : Nat) (replacement : Term),
      HeadStep (Term.substitute depth replacement term) (Term.substitute depth replacement result) := by
  induction step with
  | beta body argument =>
      intro depth replacement
      rw [BetaEtaConfluence.substituteInstantiate]
      exact .beta _ _
  | abstraction _ inner =>
      intro depth replacement
      exact .abstraction (inner (depth + 1) (shift replacement))
  | choiceLeft right _ inner =>
      intro depth replacement
      exact .choiceLeft _ (inner depth replacement)
  | choiceRight left _ inner =>
      intro depth replacement
      exact .choiceRight _ (inner depth replacement)
  | choiceApplication left right argument =>
      intro depth replacement
      exact .choiceApplication _ _ _
  | parallel _ _ leftInner rightInner =>
      intro depth replacement
      exact .parallel (leftInner depth replacement) (rightInner depth replacement)
  | parallelApplication left right argument =>
      intro depth replacement
      exact .parallelApplication _ _ _
  | @function function result argument notOther functionStep inner =>
      intro depth replacement
      obtain ⟨innerFunction, innerArgument, rfl⟩ := applicationOfStepNotOther functionStep notOther
      exact .function _ trivial (inner depth replacement)

/-! ## Solvability SOL -/

/-- `HeadReductionsAtMost steps term`: no →hsa reduction sequence from `term` has more than
`steps` steps. With 0 steps, `term` is a →hsa normal form. -/
def HeadReductionsAtMost : Nat → Term → Prop
  | 0, term => ∀ result, ¬ HeadStep term result
  | steps + 1, term => ∀ result, HeadStep term result → HeadReductionsAtMost steps result

/-- DdLP96's SOL_sa (Definition 6, written as their Definition 4: there is an n such that no
→hsa reduction sequence has length m ≥ n): some bound on the length of the →hsa reduction sequences from `term` exists. The record
calls such a term solvable (可解). -/
def Solvable (term : Term) : Prop := ∃ steps, HeadReductionsAtMost steps term

namespace HeadReductionsAtMost

/-- A bound may be raised by one. -/
theorem succ : ∀ {steps : Nat} {term : Term},
    HeadReductionsAtMost steps term → HeadReductionsAtMost (steps + 1) term
  | 0, _, normal => fun result step => absurd step (normal result)
  | _ + 1, _, bounded => fun result step => succ (bounded result step)

/-- A bound may be raised. -/
theorem raise {steps more : Nat} {term : Term} (bounded : HeadReductionsAtMost steps term)
    (atMost : steps ≤ more) : HeadReductionsAtMost more term := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le atMost
  induction extra with
  | zero => exact bounded
  | succ extra inner => exact succ (inner (Nat.le_add_right steps extra))

/-- A successor of a term bounded by `steps + 1` is bounded by `steps`. -/
theorem step {steps : Nat} {term result : Term} (bounded : HeadReductionsAtMost (steps + 1) term)
    (headStep : HeadStep term result) : HeadReductionsAtMost steps result :=
  bounded result headStep

/-- A term with a →hsa step is not bounded by 0. -/
theorem notZero {term result : Term} (bounded : HeadReductionsAtMost 0 term)
    (headStep : HeadStep term result) : False :=
  bounded result headStep

/-- A substitution instance bounds the term it is an instance of: every reduction sequence of M
is one of M[x := N] (`HeadStep.substitute`). -/
theorem ofSubstitute : ∀ {steps : Nat} {term : Term} {depth : Nat} {replacement : Term},
    HeadReductionsAtMost steps (Term.substitute depth replacement term) →
      HeadReductionsAtMost steps term
  | 0, _, _, _, normal => fun _ step => normal _ (step.substitute _ _)
  | _ + 1, _, _, _, bounded => fun _ step => ofSubstitute (bounded _ (step.substitute _ _))

/-- λx. M has the reduction sequences of M under (ξ), and no other. -/
theorem abstraction : ∀ {steps : Nat} {body : Term},
    HeadReductionsAtMost steps body → HeadReductionsAtMost steps (.abstraction body)
  | 0, _, normal => fun result step => by
      cases step with
      | abstraction inner => exact normal _ inner
  | _ + 1, _, bounded => fun result step => by
      cases step with
      | abstraction inner => exact abstraction (bounded _ inner)

end HeadReductionsAtMost

/-- A bound common to every member of a list of solvable terms. -/
theorem commonBound : ∀ (terms : List Term), (∀ term ∈ terms, Solvable term) →
    ∃ steps, ∀ term ∈ terms, HeadReductionsAtMost steps term
  | [], _ => ⟨0, fun _ member => absurd member (List.not_mem_nil)⟩
  | first :: rest, solvable => by
      obtain ⟨firstSteps, firstBounded⟩ := solvable first List.mem_cons_self
      obtain ⟨restSteps, restBounded⟩ :=
        commonBound rest (fun term member => solvable term (List.mem_cons_of_mem first member))
      refine ⟨firstSteps + restSteps, fun term member => ?_⟩
      rcases List.mem_cons.mp member with equal | inRest
      · subst equal
        exact firstBounded.raise (Nat.le_add_right firstSteps restSteps)
      · exact (restBounded term inRest).raise (Nat.le_add_left restSteps firstSteps)

/-- A term whose successors are all solvable is solvable: →hsa is finitely branching, so their
bounds have a maximum. -/
theorem solvableOfSuccessors {term : Term}
    (successors : ∀ result, HeadStep term result → Solvable result) : Solvable term := by
  obtain ⟨steps, bounded⟩ := commonBound (headSuccessors term)
    (fun result member => successors result (headStepOfMem member))
  exact ⟨steps + 1, fun result step => bounded result (memOfHeadStep step)⟩

/-- A successor of a solvable term is solvable. -/
theorem Solvable.step {term result : Term} (solvable : Solvable term)
    (headStep : HeadStep term result) : Solvable result := by
  obtain ⟨steps, bounded⟩ := solvable
  cases steps with
  | zero => exact absurd headStep (bounded result)
  | succ steps => exact ⟨steps, bounded result headStep⟩

/-- SOL is the set of terms from which every →hsa reduction sequence is finite, that is the
terms accessible under the converse of →hsa (the record, section 3: "由 König 引理，M ∈ SOL 当且仅当
归约树有限"). -/
theorem solvableIffAccessible {term : Term} :
    Solvable term ↔ Acc (fun later earlier => HeadStep earlier later) term := by
  constructor
  · intro ⟨steps, bounded⟩
    induction steps generalizing term with
    | zero => exact Acc.intro term (fun result step => absurd step (bounded result))
    | succ steps inner =>
        exact Acc.intro term (fun result step => inner (bounded result step))
  · intro accessible
    induction accessible with
    | intro term _ inner => exact solvableOfSuccessors inner

/-- A substitution instance of M is solvable only if M is. -/
theorem Solvable.ofSubstitute {term : Term} {depth : Nat} {replacement : Term}
    (solvable : Solvable (Term.substitute depth replacement term)) : Solvable term :=
  let ⟨steps, bounded⟩ := solvable
  ⟨steps, HeadReductionsAtMost.ofSubstitute bounded⟩

/-! ## (S0) Normal forms are solvable -/

/-- x M₁ … Mₖ (k ≥ 0): an application spine whose head is a variable. -/
inductive StuckSpine : Term → Prop where
  /-- x. -/
  | boundVariable (index : Nat) : StuckSpine (.boundVariable index)
  /-- A stuck spine applied to one more argument. -/
  | application {function : Term} (argument : Term) :
      StuckSpine function → StuckSpine (.application function argument)

/-- DdLP96's set ℋ of →h normal forms (their Proposition 16): the least set containing x M⃗ and
closed under λx. H, H₁ + H₂, H ∥ M and M ∥ H. -/
inductive HeadNormalForm : Term → Prop where
  /-- (a): x M⃗. -/
  | stuck {term : Term} : StuckSpine term → HeadNormalForm term
  /-- (b): λx. H. -/
  | abstraction {body : Term} : HeadNormalForm body → HeadNormalForm (.abstraction body)
  /-- (c): H₁ + H₂. -/
  | choice {left right : Term} :
      HeadNormalForm left → HeadNormalForm right → HeadNormalForm (.choice left right)
  /-- (d): H ∥ M. -/
  | parallelLeft {left : Term} (right : Term) :
      HeadNormalForm left → HeadNormalForm (.parallel left right)
  /-- (d): M ∥ H. -/
  | parallelRight (left : Term) {right : Term} :
      HeadNormalForm right → HeadNormalForm (.parallel left right)

/-- A stuck spine has no →hsa step. -/
theorem StuckSpine.noStep {term : Term} (stuck : StuckSpine term) : ∀ result, ¬ HeadStep term result := by
  induction stuck with
  | boundVariable index => intro result step; cases step
  | application argument functionStuck inner =>
      intro result step
      cases step with
      | function _ _ functionStep => exact inner _ functionStep
      | beta body argument => cases functionStuck
      | choiceApplication left right argument => cases functionStuck
      | parallelApplication left right argument => cases functionStuck

/-- A head normal form that is not an abstraction, a parallel or a choice is a stuck spine. -/
theorem HeadNormalForm.stuckOfNotOther {term : Term} (normal : HeadNormalForm term)
    (notOther : NotAbstractionParallelChoice term) : StuckSpine term := by
  cases normal with
  | stuck stuck => exact stuck
  | abstraction _ => exact absurd notOther id
  | choice _ _ => exact absurd notOther id
  | parallelLeft _ _ => exact absurd notOther id
  | parallelRight _ _ => exact absurd notOther id

/-- The record's (S0): the →hsa normal forms are exactly the members of ℋ. -/
theorem headStepNoneIffHeadNormalForm :
    ∀ {term : Term}, (∀ result, ¬ HeadStep term result) ↔ HeadNormalForm term
  | .boundVariable index => ⟨fun _ => .stuck (.boundVariable index), fun _ result step => by cases step⟩
  | .abstraction body => by
      constructor
      · intro normal
        exact .abstraction (headStepNoneIffHeadNormalForm.mp
          (fun result step => normal _ (.abstraction step)))
      · intro normal result step
        cases normal with
        | stuck stuck => cases stuck
        | abstraction bodyNormal =>
            cases step with
            | abstraction inner => exact headStepNoneIffHeadNormalForm.mpr bodyNormal _ inner
  | .choice left right => by
      constructor
      · intro normal
        exact .choice
          (headStepNoneIffHeadNormalForm.mp (fun result step => normal _ (.choiceLeft right step)))
          (headStepNoneIffHeadNormalForm.mp (fun result step => normal _ (.choiceRight left step)))
      · intro normal result step
        cases normal with
        | stuck stuck => cases stuck
        | choice leftNormal rightNormal =>
            cases step with
            | choiceLeft _ inner => exact headStepNoneIffHeadNormalForm.mpr leftNormal _ inner
            | choiceRight _ inner => exact headStepNoneIffHeadNormalForm.mpr rightNormal _ inner
  | .parallel left right => by
      constructor
      · intro normal
        rcases Classical.em (∀ result, ¬ HeadStep left result) with leftNone | leftSome
        · exact .parallelLeft right (headStepNoneIffHeadNormalForm.mp leftNone)
        · rcases Classical.em (∀ result, ¬ HeadStep right result) with rightNone | rightSome
          · exact .parallelRight left (headStepNoneIffHeadNormalForm.mp rightNone)
          · obtain ⟨leftResult, leftStep⟩ := Classical.not_forall_not.mp leftSome
            obtain ⟨rightResult, rightStep⟩ := Classical.not_forall_not.mp rightSome
            exact absurd (HeadStep.parallel leftStep rightStep) (normal _)
      · intro normal result step
        cases step with
        | parallel leftStep rightStep =>
            cases normal with
            | stuck stuck => cases stuck
            | parallelLeft _ leftNormal =>
                exact headStepNoneIffHeadNormalForm.mpr leftNormal _ leftStep
            | parallelRight _ rightNormal =>
                exact headStepNoneIffHeadNormalForm.mpr rightNormal _ rightStep
  | .application function argument => by
      constructor
      · intro normal
        have notOther : NotAbstractionParallelChoice function := by
          cases function with
          | boundVariable index => trivial
          | abstraction body => exact normal _ (.beta body argument)
          | application inner innerArgument => trivial
          | choice left right => exact normal _ (.choiceApplication left right argument)
          | parallel left right => exact normal _ (.parallelApplication left right argument)
        have functionNormal : HeadNormalForm function :=
          headStepNoneIffHeadNormalForm.mp
            (fun result step => normal _ (.function argument notOther step))
        exact .stuck (.application argument (functionNormal.stuckOfNotOther notOther))
      · intro normal
        cases normal with
        | stuck stuck => exact stuck.noStep

/-- The record's (S0): a head normal form is solvable, with no step at all. -/
theorem solvableOfHeadNormalForm {term : Term} (normal : HeadNormalForm term) : Solvable term :=
  ⟨0, headStepNoneIffHeadNormalForm.mpr normal⟩

/-- The record's (S0): x M⃗ is solvable. -/
theorem solvableOfStuckSpine {term : Term} (stuck : StuckSpine term) : Solvable term :=
  ⟨0, stuck.noStep⟩

/-! ## (S1) Choice and parallel -/

namespace HeadReductionsAtMost

/-- A bound of M + N bounds M: every step of M is one of M + N by (+a). -/
theorem choiceLeft : ∀ {steps : Nat} {left right : Term},
    HeadReductionsAtMost steps (.choice left right) → HeadReductionsAtMost steps left
  | 0, _, _, normal => fun _ step => normal _ (.choiceLeft _ step)
  | _ + 1, _, _, bounded => fun _ step => choiceLeft (bounded _ (.choiceLeft _ step))

/-- A bound of M + N bounds N. -/
theorem choiceRight : ∀ {steps : Nat} {left right : Term},
    HeadReductionsAtMost steps (.choice left right) → HeadReductionsAtMost steps right
  | 0, _, _, normal => fun _ step => normal _ (.choiceRight _ step)
  | _ + 1, _, _, bounded => fun _ step => choiceRight (bounded _ (.choiceRight _ step))

/-- len(M + N) ≤ len(M) + len(N), len being the record's length of the longest →hsa reduction
sequence (section 3), here a bound `HeadReductionsAtMost`: the steps of M + N are those of M and
those of N, interleaved by (+a). -/
theorem choice : ∀ (total : Nat) {leftSteps rightSteps : Nat} {left right : Term},
    leftSteps + rightSteps = total →
      HeadReductionsAtMost leftSteps left → HeadReductionsAtMost rightSteps right →
        HeadReductionsAtMost total (.choice left right)
  | 0, leftSteps, rightSteps, _, _, sum, leftBounded, rightBounded => by
      have leftZero : leftSteps = 0 := by omega
      have rightZero : rightSteps = 0 := by omega
      subst leftZero rightZero
      intro result step
      cases step with
      | choiceLeft _ inner => exact leftBounded _ inner
      | choiceRight _ inner => exact rightBounded _ inner
  | total + 1, leftSteps, rightSteps, _, _, sum, leftBounded, rightBounded => by
      intro result step
      cases step with
      | choiceLeft _ inner =>
          cases leftSteps with
          | zero => exact absurd inner (leftBounded _)
          | succ leftSteps =>
              exact choice total (by omega) (leftBounded _ inner) rightBounded
      | choiceRight _ inner =>
          cases rightSteps with
          | zero => exact absurd inner (rightBounded _)
          | succ rightSteps =>
              exact choice total (by omega) leftBounded (rightBounded _ inner)

/-- len(M ∥ N) ≤ len(M): the steps of M ∥ N are pairs of steps by (∥s). -/
theorem parallelLeft : ∀ {steps : Nat} {left : Term} (right : Term),
    HeadReductionsAtMost steps left → HeadReductionsAtMost steps (.parallel left right)
  | 0, _, _, normal => fun result step => by
      cases step with
      | parallel leftStep _ => exact normal _ leftStep
  | _ + 1, _, _, bounded => fun result step => by
      cases step with
      | parallel leftStep _ => exact parallelLeft _ (bounded _ leftStep)

/-- len(M ∥ N) ≤ len(N). -/
theorem parallelRight : ∀ {steps : Nat} (left : Term) {right : Term},
    HeadReductionsAtMost steps right → HeadReductionsAtMost steps (.parallel left right)
  | 0, _, _, normal => fun result step => by
      cases step with
      | parallel _ rightStep => exact normal _ rightStep
  | _ + 1, _, _, bounded => fun result step => by
      cases step with
      | parallel _ rightStep => exact parallelRight _ (bounded _ rightStep)

/-- A bound of M ∥ N bounds M or N: were there a sequence longer than the bound from each, they
would pair into one from M ∥ N by (∥s). -/
theorem parallel : ∀ {steps : Nat} {left right : Term},
    HeadReductionsAtMost steps (.parallel left right) →
      HeadReductionsAtMost steps left ∨ HeadReductionsAtMost steps right
  | 0, left, right, normal => by
      rcases Classical.em (∀ result, ¬ HeadStep left result) with leftNone | leftSome
      · exact .inl leftNone
      · rcases Classical.em (∀ result, ¬ HeadStep right result) with rightNone | rightSome
        · exact .inr rightNone
        · obtain ⟨leftResult, leftStep⟩ := Classical.not_forall_not.mp leftSome
          obtain ⟨rightResult, rightStep⟩ := Classical.not_forall_not.mp rightSome
          exact absurd (HeadStep.parallel leftStep rightStep) (normal _)
  | steps + 1, left, right, bounded => by
      refine Classical.byContradiction fun neither => ?_
      have leftUnbounded : ¬ HeadReductionsAtMost (steps + 1) left := fun leftBounded =>
        neither (.inl leftBounded)
      have rightUnbounded : ¬ HeadReductionsAtMost (steps + 1) right := fun rightBounded =>
        neither (.inr rightBounded)
      obtain ⟨leftResult, leftLong⟩ := Classical.not_forall.mp leftUnbounded
      obtain ⟨rightResult, rightLong⟩ := Classical.not_forall.mp rightUnbounded
      have leftStep : HeadStep left leftResult :=
        Classical.byContradiction fun noStep => leftLong (fun step => absurd step noStep)
      have rightStep : HeadStep right rightResult :=
        Classical.byContradiction fun noStep => rightLong (fun step => absurd step noStep)
      rcases parallel (bounded _ (.parallel leftStep rightStep)) with leftShort | rightShort
      · exact leftLong (fun _ => leftShort)
      · exact rightLong (fun _ => rightShort)

end HeadReductionsAtMost

/-- The record's (S1): M₁ + M₂ ∈ SOL iff both are. -/
theorem solvableChoice {left right : Term} :
    Solvable (.choice left right) ↔ Solvable left ∧ Solvable right :=
  ⟨fun ⟨steps, bounded⟩ => ⟨⟨steps, bounded.choiceLeft⟩, ⟨steps, bounded.choiceRight⟩⟩,
    fun ⟨⟨leftSteps, leftBounded⟩, ⟨rightSteps, rightBounded⟩⟩ =>
      ⟨leftSteps + rightSteps, HeadReductionsAtMost.choice _ rfl leftBounded rightBounded⟩⟩

/-- The record's (S1): M₁ ∥ M₂ ∈ SOL iff at least one is. -/
theorem solvableParallel {left right : Term} :
    Solvable (.parallel left right) ↔ Solvable left ∨ Solvable right :=
  ⟨fun ⟨steps, bounded⟩ => bounded.parallel.elim (fun leftBounded => .inl ⟨steps, leftBounded⟩)
      (fun rightBounded => .inr ⟨steps, rightBounded⟩),
    fun solvable => solvable.elim
      (fun ⟨steps, leftBounded⟩ => ⟨steps, HeadReductionsAtMost.parallelLeft right leftBounded⟩)
      (fun ⟨steps, rightBounded⟩ => ⟨steps, HeadReductionsAtMost.parallelRight left rightBounded⟩)⟩

/-! ## (S2) The unique successor -/

/-- The record's (S2), with lengths: when M has exactly one successor M′, len(M) = 1 + len(M′). -/
theorem headReductionsAtMostOfUniqueSuccessor {term successor : Term}
    (unique : ∀ result, HeadStep term result ↔ result = successor) (steps : Nat) :
    HeadReductionsAtMost (steps + 1) term ↔ HeadReductionsAtMost steps successor :=
  ⟨fun bounded => bounded successor ((unique successor).mpr rfl),
    fun bounded result step => ((unique result).mp step) ▸ bounded⟩

/-- The record's (S2): when M has exactly one successor M′, M ∈ SOL iff M′ ∈ SOL. -/
theorem solvableOfUniqueSuccessor {term successor : Term}
    (unique : ∀ result, HeadStep term result ↔ result = successor) :
    Solvable term ↔ Solvable successor :=
  ⟨fun solvable => solvable.step ((unique successor).mpr rfl),
    fun ⟨steps, bounded⟩ => ⟨steps + 1, (headReductionsAtMostOfUniqueSuccessor unique steps).mpr bounded⟩⟩

/-! ## (S3) Expansion at the head -/

/-- M P₁ … Pₖ: `head` applied to the arguments in order. -/
def applyAll : Term → List Term → Term
  | head, [] => head
  | head, argument :: rest => applyAll (.application head argument) rest

/-- The steps of an application whose function is an application are (ν_sa) steps. -/
theorem headStepApplicationOfApplication {function inner argument result : Term} :
    HeadStep (.application (.application function inner) argument) result ↔
      ∃ functionResult, HeadStep (.application function inner) functionResult ∧
        result = .application functionResult argument := by
  constructor
  · intro step
    cases step with
    | function _ _ functionStep => exact ⟨_, functionStep, rfl⟩
  · intro ⟨functionResult, functionStep, equal⟩
    subst equal
    exact .function argument trivial functionStep

/-- The steps of an application spine whose head is an application are the steps of the head,
applied to the same arguments. -/
theorem headStepApplyAll : ∀ (arguments : List Term) {function inner result : Term},
    HeadStep (applyAll (.application function inner) arguments) result ↔
      ∃ headResult, HeadStep (.application function inner) headResult ∧
        result = applyAll headResult arguments
  | [], _, _, result => ⟨fun step => ⟨result, step, rfl⟩, fun ⟨_, step, equal⟩ => equal ▸ step⟩
  | argument :: rest, function, inner, result => by
      show HeadStep (applyAll (.application (.application function inner) argument) rest) result ↔ _
      rw [headStepApplyAll rest]
      constructor
      · intro ⟨headResult, headStep, equal⟩
        obtain ⟨functionResult, functionStep, headEqual⟩ :=
          headStepApplicationOfApplication.mp headStep
        subst headEqual
        exact ⟨functionResult, functionStep, equal⟩
      · intro ⟨functionResult, functionStep, equal⟩
        exact ⟨_, headStepApplicationOfApplication.mpr ⟨functionResult, functionStep, rfl⟩, equal⟩

/-- An application spine whose head is a redex with one contractum has one successor: the
contractum applied to the same arguments. -/
theorem uniqueSuccessorApplyAll {function inner contractum : Term} (arguments : List Term)
    (unique : ∀ result, HeadStep (.application function inner) result ↔ result = contractum) :
    ∀ result, HeadStep (applyAll (.application function inner) arguments) result ↔
      result = applyAll contractum arguments := by
  intro result
  rw [headStepApplyAll]
  constructor
  · intro ⟨headResult, headStep, equal⟩
    rw [(unique headResult).mp headStep] at equal
    exact equal
  · intro equal
    exact ⟨contractum, (unique contractum).mpr rfl, equal⟩

/-- The record's (S3): (λx. M) N P⃗ ∈ SOL iff M[x := N] P⃗ ∈ SOL. -/
theorem solvableBetaSpine (body argument : Term) (arguments : List Term) :
    Solvable (applyAll (.application (.abstraction body) argument) arguments) ↔
      Solvable (applyAll (instantiate body argument) arguments) :=
  solvableOfUniqueSuccessor (uniqueSuccessorApplyAll arguments fun result =>
    ⟨fun step => by cases step with
      | beta => rfl
      | function _ notOther _ => exact absurd notOther id,
     fun equal => equal ▸ .beta body argument⟩)

/-- The one successor of (M + N) P is M P + N P. -/
theorem uniqueSuccessorChoiceApplication (left right argument : Term) :
    ∀ result, HeadStep (.application (.choice left right) argument) result ↔
      result = .choice (.application left argument) (.application right argument) :=
  fun result => ⟨fun step => by cases step with
      | choiceApplication => rfl
      | function _ notOther _ => exact absurd notOther id,
    fun equal => equal ▸ .choiceApplication left right argument⟩

/-- The one successor of (M ∥ N) P is M P ∥ N P. -/
theorem uniqueSuccessorParallelApplication (left right argument : Term) :
    ∀ result, HeadStep (.application (.parallel left right) argument) result ↔
      result = .parallel (.application left argument) (.application right argument) :=
  fun result => ⟨fun step => by cases step with
      | parallelApplication => rfl
      | function _ notOther _ => exact absurd notOther id,
    fun equal => equal ▸ .parallelApplication left right argument⟩

/-- The record's (S3): (M₁ + M₂) P⃗ ∈ SOL iff M₁ P⃗ ∈ SOL and M₂ P⃗ ∈ SOL, for every k ≥ 0. -/
theorem solvableChoiceSpine : ∀ (arguments : List Term) (left right : Term),
    Solvable (applyAll (.choice left right) arguments) ↔
      Solvable (applyAll left arguments) ∧ Solvable (applyAll right arguments)
  | [], _, _ => solvableChoice
  | argument :: rest, left, right =>
      (solvableOfUniqueSuccessor (uniqueSuccessorApplyAll rest
        (uniqueSuccessorChoiceApplication left right argument))).trans
        (solvableChoiceSpine rest (.application left argument) (.application right argument))

/-- The record's (S3): (M₁ ∥ M₂) P⃗ ∈ SOL iff M₁ P⃗ ∈ SOL or M₂ P⃗ ∈ SOL, for every k ≥ 0. -/
theorem solvableParallelSpine : ∀ (arguments : List Term) (left right : Term),
    Solvable (applyAll (.parallel left right) arguments) ↔
      Solvable (applyAll left arguments) ∨ Solvable (applyAll right arguments)
  | [], _, _ => solvableParallel
  | argument :: rest, left, right =>
      (solvableOfUniqueSuccessor (uniqueSuccessorApplyAll rest
        (uniqueSuccessorParallelApplication left right argument))).trans
        (solvableParallelSpine rest (.application left argument) (.application right argument))

/-! ## (S4) Lemma X -/

/-- The record's lemma X, by induction on the bound of M N, as the record's proof inducts on
len(M x): M N bounded by `steps` gives M ∈ SOL. -/
theorem solvableOfBoundedApplication : ∀ (steps : Nat) {function argument : Term},
    HeadReductionsAtMost steps (.application function argument) → Solvable function
  | _, .boundVariable index, _, _ => solvableOfStuckSpine (.boundVariable index)
  | 0, .abstraction body, argument, normal => absurd (.beta body argument) (normal _)
  | 0, .choice left right, argument, normal =>
      absurd (.choiceApplication left right argument) (normal _)
  | 0, .parallel left right, argument, normal =>
      absurd (.parallelApplication left right argument) (normal _)
  | 0, .application _ _, argument, normal =>
      ⟨0, fun _ step => normal _ (.function argument trivial step)⟩
  | steps + 1, .abstraction body, argument, bounded =>
      -- M x has the one successor M₀[y := x], whose solvability gives that of M₀ and of λy. M₀.
      let ⟨bodySteps, bodyBounded⟩ :=
        Solvable.ofSubstitute (term := body) (depth := 0) (replacement := argument)
          ⟨steps, bounded _ (.beta body argument)⟩
      ⟨bodySteps, HeadReductionsAtMost.abstraction bodyBounded⟩
  | steps + 1, .choice left right, argument, bounded =>
      -- the one successor is M₁ x + M₂ x; both sides are bounded by `steps`.
      have successorBounded := bounded _ (.choiceApplication left right argument)
      solvableChoice.mpr ⟨solvableOfBoundedApplication steps successorBounded.choiceLeft,
        solvableOfBoundedApplication steps successorBounded.choiceRight⟩
  | steps + 1, .parallel left right, argument, bounded =>
      -- the one successor is M₁ x ∥ M₂ x; one side is bounded by `steps`.
      have successorBounded := bounded _ (.parallelApplication left right argument)
      successorBounded.parallel.elim
        (fun leftBounded => solvableParallel.mpr (.inl (solvableOfBoundedApplication steps leftBounded)))
        (fun rightBounded =>
          solvableParallel.mpr (.inr (solvableOfBoundedApplication steps rightBounded)))
  | steps + 1, .application _ _, argument, bounded =>
      -- the successors of M x are M″ x for the successors M″ of M, each bounded by `steps`.
      solvableOfSuccessors fun _ step =>
        solvableOfBoundedApplication steps (bounded _ (.function argument trivial step))

/-- The record's (S4), lemma X, in a more general form: M N ∈ SOL gives M ∈ SOL for every term N
(the record states it for a variable x ∉ FV(M)). -/
theorem solvableOfSolvableApplication {function argument : Term}
    (solvable : Solvable (.application function argument)) : Solvable function :=
  let ⟨steps, bounded⟩ := solvable
  solvableOfBoundedApplication steps bounded

/-! ## The contextual preorder ⊑_O -/

/-- DdLP96's M ⊑_O N (Definition 14): for every context C of Λ_{+∥}, C[M] ∈ SOL gives
C[N] ∈ SOL. -/
def ContextualPreorder (lower upper : Term) : Prop :=
  ∀ context : Context, Solvable (context.fill lower) → Solvable (context.fill upper)

/-- DdLP96's ≃_O: the symmetric part of ⊑_O. -/
def ContextualEquivalence (left right : Term) : Prop :=
  ContextualPreorder left right ∧ ContextualPreorder right left

/-- { N ∈ NF_βη | T ⊑_O N }: `candidate` is a closed βη normal form and `term` ⊑_O `candidate`.
This set is OUR definition, built on DdLP96's Definition 14: DdLP96 define only the preorder ⊑_O,
and the sets they attach to a term are other ones (head normal forms, capabilities, approximants,
types). For a closed T it is NF◇_{λ-lattice-η}(T)
(`consistentNormalFormLatticeEtaIffContextualNormalForm`, module `LatticeEtaBridge`). -/
def ContextualNormalForm (term candidate : Term) : Prop :=
  NormalForm candidate ∧ ContextualPreorder term candidate

namespace ContextualPreorder

/-- ⊑_O is reflexive. -/
theorem reflexive (term : Term) : ContextualPreorder term term := fun _ solvable => solvable

/-- ⊑_O is transitive. -/
theorem transitive {lower middle upper : Term} (lowerMiddle : ContextualPreorder lower middle)
    (middleUpper : ContextualPreorder middle upper) : ContextualPreorder lower upper :=
  fun context solvable => middleUpper context (lowerMiddle context solvable)

/-- ⊑_O is a precongruence (DdLP96, after Definition 14: "Clearly, the relation ⊑_O is a
precongruence"): M ⊑_O N gives C[M] ⊑_O C[N] for every context C, since a context of C[ ] is a
context composed with C. -/
theorem fill {lower upper : Term} (preorder : ContextualPreorder lower upper) (inner : Context) :
    ContextualPreorder (inner.fill lower) (inner.fill upper) := by
  intro outer solvable
  rw [← SyntacticConsistency.composeContextsFill] at solvable ⊢
  exact preorder _ solvable

end ContextualPreorder

namespace ContextualEquivalence

/-- ≃_O is reflexive. -/
theorem reflexive (term : Term) : ContextualEquivalence term term :=
  ⟨ContextualPreorder.reflexive term, ContextualPreorder.reflexive term⟩

/-- ≃_O is symmetric. -/
theorem symmetric {left right : Term} (equivalence : ContextualEquivalence left right) :
    ContextualEquivalence right left :=
  ⟨equivalence.2, equivalence.1⟩

/-- ≃_O is transitive. -/
theorem transitive {left middle right : Term} (first : ContextualEquivalence left middle)
    (second : ContextualEquivalence middle right) : ContextualEquivalence left right :=
  ⟨first.1.transitive second.1, second.2.transitive first.2⟩

/-- ≃_O is a congruence. -/
theorem fill {left right : Term} (equivalence : ContextualEquivalence left right)
    (context : Context) : ContextualEquivalence (context.fill left) (context.fill right) :=
  ⟨equivalence.1.fill context, equivalence.2.fill context⟩

/-- Application is a congruence for ≃_O: F X ≃_O G Y when F ≃_O G and X ≃_O Y. -/
theorem application {leftFunction rightFunction leftArgument rightArgument : Term}
    (functions : ContextualEquivalence leftFunction rightFunction)
    (arguments : ContextualEquivalence leftArgument rightArgument) :
    ContextualEquivalence (.application leftFunction leftArgument)
      (.application rightFunction rightArgument) :=
  (functions.fill (.applicationFunction .hole leftArgument)).transitive
    (arguments.fill (.applicationArgument rightFunction .hole))

end ContextualEquivalence

end LambdaJit.ContextualPreorder
