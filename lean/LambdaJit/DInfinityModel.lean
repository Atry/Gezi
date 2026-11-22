import LambdaJit.DInfinityApplication
import LambdaJit.DdLP96Model

/-!
# DdLP96's reading of Λ_{+∥} in Wadsworth's D∞: an instance of `DdLP96Model`

The reading [[M]]ρ of the proofs file, section 4 (+ as the meet
⊓, ∥ as the join ⊔), in the D∞ of modules `DInfinity` and `DInfinityApplication`, is
defined by recursion on the term together with the two facts the abstraction case needs: the
reading is monotone in the environment, and continuous in it, in the sense that every projection
Pₖ([[M]]ρ) is below [[M]] in the environment of the projections Pₙ ∘ ρ for some n (`Reading`).
The case of the abstraction proves continuity from the finiteness of Dₖ: Pₖ₊₁([[λx. M]]ρ) is
determined by the finitely many values [[M]]ρ[x ↦ φ_{k∞}(a)] for a ∈ Dₖ.

`wadsworthModel` is the instance of `DdLP96Model`: every field is proved, with no hypothesis.
-/

namespace LambdaJit.DInfinity

namespace Limit

open LambdaJit.Semantics
open LambdaJit.ContextualPreorder (extendEnvironment)

/-- The pointwise order of environments. -/
def EnvironmentBelow (lower upper : Nat → Limit) : Prop :=
  ∀ index, Limit.below (lower index) (upper index)

/-- Pₙ ∘ ρ. -/
noncomputable def projectEnvironment (approximation : Nat) (environment : Nat → Limit) : Nat → Limit :=
  fun index => project approximation (environment index)

theorem extendBelow {lowerEnvironment upperEnvironment : Nat → Limit} {lower upper : Limit}
    (environmentBelow : EnvironmentBelow lowerEnvironment upperEnvironment)
    (below : Limit.below lower upper) :
    EnvironmentBelow (extendEnvironment lower lowerEnvironment) (extendEnvironment upper upperEnvironment)
  | 0 => below
  | index + 1 => environmentBelow index

theorem projectEnvironmentBelow (approximation : Nat) (environment : Nat → Limit) :
    EnvironmentBelow (projectEnvironment approximation environment) environment :=
  fun index => projectBelow approximation (environment index)

theorem projectEnvironmentIndexMonotone {lower upper : Nat} (bound : lower ≤ upper)
    (environment : Nat → Limit) :
    EnvironmentBelow (projectEnvironment lower environment) (projectEnvironment upper environment) :=
  fun index => projectIndexMonotone bound (environment index)

theorem topGreatest (value : Limit) : Limit.below value top :=
  fun index => (level index).topGreatest _

/-- A reading of a term: a function of environments, monotone, and continuous in the sense that
every projection of its value is below its value in a projected environment. -/
structure Reading where
  /-- The value in an environment. -/
  value : (Nat → Limit) → Limit
  monotone : ∀ {lower upper}, EnvironmentBelow lower upper → Limit.below (value lower) (value upper)
  continuous : ∀ environment projection, ∃ approximation,
    Limit.below (project projection (value environment))
      (value (projectEnvironment approximation environment))

/-- The reading of a variable. -/
noncomputable def variableReading (index : Nat) : Reading where
  value environment := environment index
  monotone below := below index
  continuous _ projection := ⟨projection, orderReflexive _⟩

/-- The reading of a binary operation that is monotone and continuous in both arguments. -/
noncomputable def binaryReading (operation : Limit → Limit → Limit)
    (operationMonotone : ∀ {leftLower leftUpper rightLower rightUpper},
      Limit.below leftLower leftUpper → Limit.below rightLower rightUpper →
        Limit.below (operation leftLower rightLower) (operation leftUpper rightUpper))
    (operationContinuous : ∀ left right projection, ∃ approximation,
      Limit.below (project projection (operation left right))
        (operation (project approximation left) (project approximation right)))
    (left right : Reading) : Reading where
  value environment := operation (left.value environment) (right.value environment)
  monotone below := operationMonotone (left.monotone below) (right.monotone below)
  continuous environment projection := by
    obtain ⟨middle, operationBelow⟩ :=
      operationContinuous (left.value environment) (right.value environment) projection
    obtain ⟨leftApproximation, leftBelow⟩ := left.continuous environment middle
    obtain ⟨rightApproximation, rightBelow⟩ := right.continuous environment middle
    refine ⟨max leftApproximation rightApproximation, orderTransitive operationBelow
      (operationMonotone (orderTransitive leftBelow ?_) (orderTransitive rightBelow ?_))⟩
    · exact left.monotone (projectEnvironmentIndexMonotone (Nat.le_max_left _ _) environment)
    · exact right.monotone (projectEnvironmentIndexMonotone (Nat.le_max_right _ _) environment)

/-- For each element of a list some number satisfies a property; then one bound has, for each
element, a number at or below it that satisfies the property. -/
theorem boundOverList {Element : Type} (property : Element → Nat → Prop)
    (witnesses : ∀ element, ∃ number, property element number) :
    ∀ elements : List Element, ∃ bound, ∀ element ∈ elements,
      ∃ number, number ≤ bound ∧ property element number
  | [] => ⟨0, fun _ absent => nomatch absent⟩
  | first :: rest => by
      obtain ⟨firstNumber, firstHolds⟩ := witnesses first
      obtain ⟨restBound, restHolds⟩ := boundOverList property witnesses rest
      refine ⟨max firstNumber restBound, fun element member => ?_⟩
      cases List.mem_cons.mp member with
      | inl isFirst =>
          subst isFirst
          exact ⟨firstNumber, Nat.le_max_left _ _, firstHolds⟩
      | inr inRest =>
          obtain ⟨number, bound, holds⟩ := restHolds element inRest
          exact ⟨number, Nat.le_trans bound (Nat.le_max_right _ _), holds⟩

/-- The function d ↦ [[M]]ρ[x ↦ d] of a body's reading. -/
noncomputable def bodyFunction (body : Reading) (environment : Nat → Limit) : Limit → Limit :=
  fun value => body.value (extendEnvironment value environment)

theorem bodyFunctionMonotone (body : Reading) (environment : Nat → Limit) :
    Monotone (bodyFunction body environment) :=
  fun below => body.monotone (extendBelow (fun _ => orderReflexive _) below)

theorem bodyFunctionContinuous (body : Reading) (environment : Nat → Limit) :
    Continuous (bodyFunction body environment) := fun value projection => by
  obtain ⟨approximation, below⟩ := body.continuous (extendEnvironment value environment) projection
  refine ⟨approximation, orderTransitive below (body.monotone ?_)⟩
  intro index
  cases index with
  | zero => exact orderReflexive _
  | succ index => exact projectBelow approximation (environment index)

/-- The reading of an abstraction. -/
noncomputable def abstractionReading (body : Reading) : Reading where
  value environment := abstraction (bodyFunction body environment) (bodyFunctionMonotone body environment)
  monotone below := abstractionMonotone fun _ =>
    body.monotone (extendBelow below (orderReflexive _))
  continuous environment projection := by
    obtain ⟨bound, each⟩ := boundOverList
      (fun (argument : (level projection).Carrier) approximation =>
        Limit.below (project projection (body.value (extendEnvironment (embed projection argument) environment)))
          (body.value (projectEnvironment approximation
            (extendEnvironment (embed projection argument) environment))))
      (fun argument => body.continuous _ projection) (level projection).elements
    refine ⟨bound, orderTransitive (projectIncreasing projection _) ?_⟩
    apply extensionalBelow.mpr
    intro argument
    rw [applyProjectFunction]
    refine orderTransitive ?_ (supremumAbove _ projection)
    obtain ⟨approximation, atMost, below⟩ :=
      each (argument.1 projection) ((level projection).memberElements _)
    show Limit.below (project projection (body.value
        (extendEnvironment (embed projection (argument.1 projection)) environment)))
      (project projection (body.value
        (extendEnvironment (embed projection (argument.1 projection)) (projectEnvironment bound environment))))
    rw [← projectIdempotent]
    refine projectMonotone projection (orderTransitive below (body.monotone ?_))
    intro index
    cases index with
    | zero => exact projectBelow approximation _
    | succ index => exact projectIndexMonotone atMost (environment index)

/-- The reading of application. -/
noncomputable def applicationReading : Reading → Reading → Reading :=
  binaryReading apply
    (fun functionBelow argumentBelow => orderTransitive (applyMonotoneFunction functionBelow _)
      (applyMonotoneArgument _ argumentBelow))
    applyContinuous

/-- The reading of a choice, the meet. -/
noncomputable def choiceReading : Reading → Reading → Reading :=
  binaryReading meet
    (fun leftBelow rightBelow => meetGreatest (orderTransitive (meetBelowLeft _ _) leftBelow)
      (orderTransitive (meetBelowRight _ _) rightBelow))
    (fun _ _ projection => ⟨projection, by rw [projectMeet]; exact orderReflexive _⟩)

/-- The reading of a parallel, the join. -/
noncomputable def parallelReading : Reading → Reading → Reading :=
  binaryReading join
    (fun leftBelow rightBelow => joinLeast (orderTransitive leftBelow (joinAboveLeft _ _))
      (orderTransitive rightBelow (joinAboveRight _ _)))
    (fun _ _ projection => ⟨projection, by rw [projectJoin]; exact orderReflexive _⟩)

/-- DdLP96's reading of a term, with its monotonicity and continuity in the environment. -/
noncomputable def interpretReading : Term → Reading
  | .boundVariable index => variableReading index
  | .abstraction body => abstractionReading (interpretReading body)
  | .application function argument =>
      applicationReading (interpretReading function) (interpretReading argument)
  | .choice left right => choiceReading (interpretReading left) (interpretReading right)
  | .parallel left right => parallelReading (interpretReading left) (interpretReading right)

/-- DdLP96's reading [[M]]ρ in D∞. -/
noncomputable def interpret (term : Term) (environment : Nat → Limit) : Limit :=
  (interpretReading term).value environment

theorem interpretAbstraction (body : Term) (environment : Nat → Limit) (value : Limit) :
    apply (interpret (.abstraction body) environment) value =
      interpret body (extendEnvironment value environment) :=
  applyAbstraction _ (bodyFunctionMonotone (interpretReading body) environment)
    (bodyFunctionContinuous (interpretReading body) environment) value

theorem distributive (value left right : Limit) :
    Limit.below (meet value (join left right)) (join (meet value left) (meet value right)) :=
  fun index => (level index).distributive _ _ _

end Limit

open LambdaJit.ContextualPreorder (DdLP96Model)

/-- Wadsworth's D∞ with the two-point D₀ and DdLP96's reading in it: an instance of
`DdLP96Model`, every field proved. -/
noncomputable def wadsworthModel : DdLP96Model where
  Value := Limit
  below := Limit.below
  apply := Limit.apply
  meet := Limit.meet
  join := Limit.join
  top := Limit.top
  bottom := Limit.bottom
  project := Limit.project
  interpret := Limit.interpret
  orderReflexive := Limit.orderReflexive
  orderTransitive := Limit.orderTransitive
  orderAntisymmetric := Limit.orderAntisymmetric
  meetBelowLeft := Limit.meetBelowLeft
  meetBelowRight := Limit.meetBelowRight
  meetGreatest := Limit.meetGreatest
  joinAboveLeft := Limit.joinAboveLeft
  joinAboveRight := Limit.joinAboveRight
  joinLeast := Limit.joinLeast
  topGreatest := Limit.topGreatest
  bottomLeast _ := fun index => (level index).bottomLeast _
  topNotBottom := Limit.topNotBottom
  distributive := Limit.distributive
  extensional := Limit.extensionalBelow
  applyMonotoneArgument function _ _ below := Limit.applyMonotoneArgument function below
  applyBottom := Limit.applyBottom
  applyTop := Limit.applyTop
  applyMeet := Limit.applyMeet
  applyJoin := Limit.applyJoin
  projectBelow := Limit.projectBelow
  projectIncreasing := Limit.projectIncreasing
  projectProject := Limit.projectProject
  projectLeast := Limit.projectLeast
  projectMeet := Limit.projectMeet
  projectJoin := Limit.projectJoin
  projectTop := Limit.projectTop
  projectZeroTwoPoint := Limit.projectZeroTwoPoint
  applyLeast := Limit.applyLeast
  applyProjectArgument := Limit.applyProjectArgument
  applyProjectResult := Limit.applyProjectResult
  compact level compactValue chain limit fixed increasing least below :=
    Limit.compact level compactValue chain limit fixed increasing least below
  topOfApplyBottom := Limit.topOfApplyBottom
  compactList := Limit.compactList
  memCompactList := Limit.memberCompactList
  richEnvironment := Limit.richEnvironment
  richEnvironmentRich := Limit.richEnvironmentRich
  interpretVariable _ _ := rfl
  interpretApplication _ _ _ := rfl
  interpretAbstraction := Limit.interpretAbstraction
  interpretChoice _ _ _ := rfl
  interpretParallel _ _ _ := rfl

end LambdaJit.DInfinity
