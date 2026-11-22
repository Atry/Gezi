import LambdaJit.ContextualPreorder

/-!
# DdLP96's reading of Λ_{+∥} in Scott's D∞, as a structure passed as an argument

The structure `DdLP96Model` lists the facts about Wadsworth's D∞ (with the two-point D₀) and about
DdLP96's reading of the terms in it (+ read as the meet ⊓, ∥ as the join ⊔) that
the proofs of the contextual preorder record,
sections 4 to 7, and of the proofs file, section 20, use. It is
passed as an explicit argument to every theorem that uses it, not an axiom
(D10, `lean/README.md`, "Design decisions"). The structure has an instance,
`wadsworthModel` of module `DInfinityModel`, Wadsworth's construction with every field proved, and
module `ContextualPreorderUnconditional` states the theorems that take a model with no model
argument.

The paper statements the fields stand for are those of
the proofs file, section 20.1:
Wadsworth's laws (P1), (P3), (P4), (P6), (P7), (P8), (P11) and (P12) (C. P. Wadsworth, The relation
between computational and denotational properties for Scott's D∞-models of the lambda-calculus,
SIAM J. Comput. 5(3), 1976, pp. 497 and 498, read by an agent from scanned images; not reread
here), and the facts (E1) to (E5) the proofs file derives from them, among them that every 𝔻ₙ is
finite, so that the compact elements are countable and the rich environment ρ₀ of section 20.2
exists; and the proofs file's section 4, "DdLP96's reading is a model of ⊢", for the compositional
reading, from which weakening and the substitution lemma are derived here. Writing xₙ for Pₙ(x), the
compact elements of level n, 𝔻ₙ, are here the fixed points of `project n` (by (P4), the image of
Pₙ).

The theorems of this module, given a model: the interpretation is invariant under →hsa
(`interpretHeadStep`; its invariance under ⊢_{λ-lattice-η} is `interpretDerivableLatticeEta` of
module `LatticeEtaConsistency`); and a solvable term does not read as ⊥ in the environment that maps every
variable to ⊤ (`interpretNotBottomOfSolvable`, the record's theorem 4.1, direction ⇒).
-/

namespace LambdaJit.ContextualPreorder

open LambdaJit.Semantics
open LambdaJit.Semantics.Term

/-- The environment ρ[0 ↦ value] of de Bruijn indices: index 0 is `value`, index i + 1 is index i
of `environment`. It is the environment under one more abstraction. -/
def extendEnvironment {Value : Type} (value : Value) (environment : Nat → Value) : Nat → Value
  | 0 => value
  | index + 1 => environment index

/-- Wadsworth's D∞ with the two-point D₀ and DdLP96's reading of Λ_{+∥} in it, as the facts the
record's proofs use (D10). Its instance is
`wadsworthModel` (module `DInfinityModel`). -/
structure DdLP96Model where
  /-- The carrier D∞. -/
  Value : Type
  /-- The order ⊑ of D∞. -/
  below : Value → Value → Prop
  /-- Application x(y) of D∞. -/
  apply : Value → Value → Value
  /-- The binary meet ⊓ of D∞, DdLP96's reading of +. -/
  meet : Value → Value → Value
  /-- The binary join ⊔ of D∞, DdLP96's reading of ∥. -/
  join : Value → Value → Value
  /-- The top ⊤ of D∞. -/
  top : Value
  /-- The bottom ⊥ of D∞. -/
  bottom : Value
  /-- The projection Pₙ = φ_{n∞} ∘ ψ_{∞n}; xₙ = Pₙ(x). -/
  project : Nat → Value → Value
  /-- DdLP96's reading [[M]]ρ of a term in an environment of de Bruijn indices. -/
  interpret : Term → (Nat → Value) → Value
  /-- ⊑ is reflexive. -/
  orderReflexive : ∀ value, below value value
  /-- ⊑ is transitive. -/
  orderTransitive : ∀ {lower middle upper}, below lower middle → below middle upper →
    below lower upper
  /-- ⊑ is antisymmetric. -/
  orderAntisymmetric : ∀ {left right}, below left right → below right left → left = right
  /-- (E1) x ⊓ y ⊑ x. -/
  meetBelowLeft : ∀ left right, below (meet left right) left
  /-- (E1) x ⊓ y ⊑ y. -/
  meetBelowRight : ∀ left right, below (meet left right) right
  /-- (E1) the meet is the greatest lower bound. -/
  meetGreatest : ∀ {left right lower}, below lower left → below lower right →
    below lower (meet left right)
  /-- (E1) x ⊑ x ⊔ y. -/
  joinAboveLeft : ∀ left right, below left (join left right)
  /-- (E1) y ⊑ x ⊔ y. -/
  joinAboveRight : ∀ left right, below right (join left right)
  /-- (E1) the join is the least upper bound. -/
  joinLeast : ∀ {left right upper}, below left upper → below right upper →
    below (join left right) upper
  /-- ⊤ is the greatest element. -/
  topGreatest : ∀ value, below value top
  /-- ⊥ is the least element. -/
  bottomLeast : ∀ value, below bottom value
  /-- D∞ has more than one element: ⊤ ≠ ⊥ (D₀ is the two-point lattice). -/
  topNotBottom : top ≠ bottom
  /-- (E1) distributivity, x ⊓ (y ⊔ z) ⊑ (x ⊓ y) ⊔ (x ⊓ z): the meets and joins of D∞ are taken
  componentwise, and every Dₙ is a finite distributive lattice. -/
  distributive : ∀ value left right,
    below (meet value (join left right)) (join (meet value left) (meet value right))
  /-- (P6) extensionality: x ⊑ y if and only if x(z) ⊑ y(z) for every z. -/
  extensional : ∀ {left right}, below left right ↔ ∀ argument, below (apply left argument)
    (apply right argument)
  /-- (E5) application is monotone in its argument. -/
  applyMonotoneArgument : ∀ function {lower upper}, below lower upper →
    below (apply function lower) (apply function upper)
  /-- (P8) ⊥(y) = ⊥. -/
  applyBottom : ∀ argument, apply bottom argument = bottom
  /-- (E5) ⊤ y = ⊤. -/
  applyTop : ∀ argument, apply top argument = top
  /-- (E5) the meet is pointwise in the function position: (x ⊓ x′)(y) = x(y) ⊓ x′(y). -/
  applyMeet : ∀ left right argument,
    apply (meet left right) argument = meet (apply left argument) (apply right argument)
  /-- (E5) the join is pointwise in the function position: (x ⊔ x′)(y) = x(y) ⊔ x′(y). -/
  applyJoin : ∀ left right argument,
    apply (join left right) argument = join (apply left argument) (apply right argument)
  /-- (P1) xₙ ⊑ x. -/
  projectBelow : ∀ level value, below (project level value) value
  /-- (P1) xₙ ⊑ x_{n+1}. -/
  projectIncreasing : ∀ level value, below (project level value) (project (level + 1) value)
  /-- (P4) (xₙ)ₘ = x_{min(n, m)}. -/
  projectProject : ∀ inner outer value,
    project outer (project inner value) = project (min inner outer) value
  /-- (P3) x = ⊔ₙ xₙ, the half that (P1) does not give: every upper bound of the xₙ is above x. -/
  projectLeast : ∀ value upper, (∀ level, below (project level value) upper) → below value upper
  /-- (E1) Pₙ preserves binary meets. -/
  projectMeet : ∀ level left right,
    project level (meet left right) = meet (project level left) (project level right)
  /-- (E1) Pₙ preserves binary joins. -/
  projectJoin : ∀ level left right,
    project level (join left right) = join (project level left) (project level right)
  /-- (E1) P₀ preserves ⊤ (the proofs file's (E4): φ_{0∞}(⊤₀) = ⊤). -/
  projectTop : project 0 top = top
  /-- (E4) 𝔻₀ = {⊥, ⊤}: D₀ is the two-point lattice and φ_{0∞} maps its two points to ⊥ and ⊤. -/
  projectZeroTwoPoint : ∀ value, project 0 value = bottom ∨ project 0 value = top
  /-- (P7) x(y) = ⊔ₙ x_{n+1}(yₙ), the half that (P1) and monotonicity do not give: every upper bound
  of the x_{n+1}(yₙ) is above x(y). -/
  applyLeast : ∀ function argument upper,
    (∀ level, below (apply (project (level + 1) function) (project level argument)) upper) →
      below (apply function argument) upper
  /-- (P12) with m = n: x_{n+1}(y) = x_{n+1}(yₙ). -/
  applyProjectArgument : ∀ level function argument,
    apply (project (level + 1) function) argument =
      apply (project (level + 1) function) (project level argument)
  /-- (P11) with m = n: x_{n+1}(y) = (x_{n+1}(y))ₙ. -/
  applyProjectResult : ∀ level function argument,
    project level (apply (project (level + 1) function) argument) =
      apply (project (level + 1) function) argument
  /-- (E2) the elements of 𝔻ₙ are compact: d ∈ 𝔻ₙ below an element x that is below every upper
  bound of an increasing chain is below some member of the chain. -/
  compact : ∀ (level : Nat) (compactValue : Value) (chain : Nat → Value) (limit : Value),
    project level compactValue = compactValue → (∀ index, below (chain index) (chain (index + 1))) →
      (∀ upper, (∀ index, below (chain index) upper) → below limit upper) →
        below compactValue limit → ∃ index, below compactValue (chain index)
  /-- (E4), the direction the proofs file's (L) uses at level 0 (section 20.2): x(⊥) = ⊤ gives
  x = ⊤. -/
  topOfApplyBottom : ∀ value, apply value bottom = top → value = top
  /-- (E1): 𝔻ₙ is finite; the list of its elements. -/
  compactList : Nat → List Value
  /-- (E1): the members of `compactList n` are the elements of 𝔻ₙ, the fixed points of Pₙ. -/
  memCompactList : ∀ level value, value ∈ compactList level ↔ project level value = value
  /-- The proofs file's rich environment ρ₀ (section 20.2, 丰富的环境): every 𝔻ₙ is finite, so the
  compact elements are countable, and an environment can give each of them to infinitely many
  variables. -/
  richEnvironment : Nat → Value
  /-- Every compact element is the value in ρ₀ of a variable at or beyond every bound. -/
  richEnvironmentRich : ∀ level value, project level value = value → ∀ bound,
    ∃ index, bound ≤ index ∧ richEnvironment index = value
  /-- The reading of a variable: [[x]]ρ = ρ(x). -/
  interpretVariable : ∀ index environment,
    interpret (.boundVariable index) environment = environment index
  /-- The reading of an application: [[M N]]ρ = [[M]]ρ([[N]]ρ). -/
  interpretApplication : ∀ function argument environment,
    interpret (.application function argument) environment =
      apply (interpret function environment) (interpret argument environment)
  /-- The reading of an abstraction, through its applications: [[λx. M]]ρ(d) = [[M]]ρ[x ↦ d]. -/
  interpretAbstraction : ∀ body environment value,
    apply (interpret (.abstraction body) environment) value =
      interpret body (extendEnvironment value environment)
  /-- DdLP96's reading of the choice: [[M + N]]ρ = [[M]]ρ ⊓ [[N]]ρ. -/
  interpretChoice : ∀ left right environment,
    interpret (.choice left right) environment =
      meet (interpret left environment) (interpret right environment)
  /-- DdLP96's reading of the parallel: [[M ∥ N]]ρ = [[M]]ρ ⊔ [[N]]ρ. -/
  interpretParallel : ∀ left right environment,
    interpret (.parallel left right) environment =
      join (interpret left environment) (interpret right environment)

namespace DdLP96Model

variable (model : DdLP96Model)

/-! ## Lattice and application lemmas -/

/-- Two elements with the same applications are equal: (P6) and antisymmetry. -/
theorem equalOfApply {left right : model.Value}
    (same : ∀ argument, model.apply left argument = model.apply right argument) : left = right :=
  model.orderAntisymmetric
    (model.extensional.mpr fun argument => same argument ▸ model.orderReflexive _)
    (model.extensional.mpr fun argument => same argument ▸ model.orderReflexive _)

/-- ρ with `value` inserted at index `cutoff`: the environment of a term placed under one more
binder outside the `cutoff` innermost ones. -/
def insertEnvironment {Value : Type} (cutoff : Nat) (value : Value) (environment : Nat → Value) :
    Nat → Value :=
  fun index => if index < cutoff then environment index
    else if index = cutoff then value else environment (index - 1)

theorem insertEnvironmentZero {Value : Type} (value : Value) (environment : Nat → Value) :
    insertEnvironment 0 value environment = extendEnvironment value environment := by
  funext index
  cases index <;> simp [insertEnvironment, extendEnvironment]

theorem extendInsertEnvironment {Value : Type} (cutoff : Nat) (value inner : Value)
    (environment : Nat → Value) :
    extendEnvironment inner (insertEnvironment cutoff value environment) =
      insertEnvironment (cutoff + 1) value (extendEnvironment inner environment) := by
  funext index
  cases index with
  | zero => simp [extendEnvironment, insertEnvironment]
  | succ index =>
      by_cases below : index < cutoff
      · simp [extendEnvironment, insertEnvironment, below]
      · by_cases equal : index = cutoff
        · subst equal
          simp [extendEnvironment, insertEnvironment]
        · obtain ⟨previous, rfl⟩ : ∃ previous, index = previous + 1 := ⟨index - 1, by omega⟩
          have notBelow : ¬ previous + 1 + 1 < cutoff + 1 := by omega
          simp [extendEnvironment, insertEnvironment, below, equal, notBelow]

/-- Weakening: a term shifted past a new binder reads in the environment with that binder inserted
as the term reads in the environment without it. -/
theorem interpretShiftFrom : ∀ (term : Term) (cutoff : Nat) (environment : Nat → model.Value)
    (value : model.Value),
    model.interpret (shiftFrom cutoff term) (insertEnvironment cutoff value environment) =
      model.interpret term environment
  | .boundVariable index, cutoff, environment, value => by
      unfold shiftFrom
      split
      · rw [model.interpretVariable, model.interpretVariable]
        simp [insertEnvironment, *]
      · rw [model.interpretVariable, model.interpretVariable]
        have notBelow : ¬ index + 1 < cutoff := by omega
        have notEqual : ¬ index + 1 = cutoff := by omega
        simp [insertEnvironment, notBelow, notEqual]
  | .abstraction body, cutoff, environment, value => model.equalOfApply fun inner => by
      show model.apply (model.interpret (.abstraction (shiftFrom (cutoff + 1) body)) _) inner = _
      rw [model.interpretAbstraction, model.interpretAbstraction, extendInsertEnvironment]
      exact interpretShiftFrom body (cutoff + 1) _ value
  | .application function argument, cutoff, environment, value => by
      show model.interpret (.application (shiftFrom cutoff function) (shiftFrom cutoff argument)) _ = _
      rw [model.interpretApplication, model.interpretApplication,
        interpretShiftFrom function, interpretShiftFrom argument]
  | .choice left right, cutoff, environment, value => by
      show model.interpret (.choice (shiftFrom cutoff left) (shiftFrom cutoff right)) _ = _
      rw [model.interpretChoice, model.interpretChoice, interpretShiftFrom left,
        interpretShiftFrom right]
  | .parallel left right, cutoff, environment, value => by
      show model.interpret (.parallel (shiftFrom cutoff left) (shiftFrom cutoff right)) _ = _
      rw [model.interpretParallel, model.interpretParallel, interpretShiftFrom left,
        interpretShiftFrom right]

/-- Weakening at index 0: a variable that does not occur does not change the reading. -/
theorem interpretShift (term : Term) (environment : Nat → model.Value) (value : model.Value) :
    model.interpret (shift term) (extendEnvironment value environment) =
      model.interpret term environment := by
  rw [← insertEnvironmentZero]
  exact model.interpretShiftFrom term 0 environment value

/-- The substitution lemma at any depth: substituting N for index d reads as the term in the
environment with [[N]]ρ inserted at d. -/
theorem interpretSubstitute : ∀ (term : Term) (depth : Nat) (replacement : Term)
    (environment : Nat → model.Value),
    model.interpret (substitute depth replacement term) environment =
      model.interpret term
        (insertEnvironment depth (model.interpret replacement environment) environment)
  | .boundVariable index, depth, replacement, environment => by
      unfold substitute
      split
      · rw [model.interpretVariable, model.interpretVariable]
        simp [insertEnvironment, *]
      · split
        · rw [model.interpretVariable]
          simp [insertEnvironment, *]
        · rw [model.interpretVariable, model.interpretVariable]
          simp [insertEnvironment, *]
  | .abstraction body, depth, replacement, environment => model.equalOfApply fun inner => by
      show model.apply (model.interpret
        (.abstraction (substitute (depth + 1) (shift replacement) body)) _) inner = _
      rw [model.interpretAbstraction, model.interpretAbstraction, interpretSubstitute body,
        model.interpretShift, extendInsertEnvironment]
  | .application function argument, depth, replacement, environment => by
      show model.interpret (.application (substitute depth replacement function)
        (substitute depth replacement argument)) _ = _
      rw [model.interpretApplication, model.interpretApplication, interpretSubstitute function,
        interpretSubstitute argument]
  | .choice left right, depth, replacement, environment => by
      show model.interpret (.choice (substitute depth replacement left)
        (substitute depth replacement right)) _ = _
      rw [model.interpretChoice, model.interpretChoice, interpretSubstitute left,
        interpretSubstitute right]
  | .parallel left right, depth, replacement, environment => by
      show model.interpret (.parallel (substitute depth replacement left)
        (substitute depth replacement right)) _ = _
      rw [model.interpretParallel, model.interpretParallel, interpretSubstitute left,
        interpretSubstitute right]

/-- The substitution lemma, [[M[x := N]]]ρ = [[M]]ρ[x ↦ [[N]]ρ], which the proofs file's section 4
cites for the β rule. -/
theorem interpretInstantiate (body argument : Term) (environment : Nat → model.Value) :
    model.interpret (instantiate body argument) environment =
      model.interpret body (extendEnvironment (model.interpret argument environment) environment) := by
  unfold instantiate
  rw [model.interpretSubstitute, insertEnvironmentZero]

/-- Application is monotone in its function: (P6) from left to right. -/
theorem applyMonotoneFunction {lower upper : model.Value} (below : model.below lower upper)
    (argument : model.Value) : model.below (model.apply lower argument) (model.apply upper argument) :=
  model.extensional.mp below argument

/-- x ⊓ y = x when x ⊑ y. -/
theorem meetOfBelow {lower upper : model.Value} (below : model.below lower upper) :
    model.meet lower upper = lower :=
  model.orderAntisymmetric (model.meetBelowLeft _ _)
    (model.meetGreatest (model.orderReflexive _) below)

/-- x ⊓ y = y ⊓ x. -/
theorem meetCommutative (left right : model.Value) : model.meet left right = model.meet right left :=
  model.orderAntisymmetric (model.meetGreatest (model.meetBelowRight _ _) (model.meetBelowLeft _ _))
    (model.meetGreatest (model.meetBelowRight _ _) (model.meetBelowLeft _ _))

/-- x ⊔ y = y ⊔ x. -/
theorem joinCommutative (left right : model.Value) : model.join left right = model.join right left :=
  model.orderAntisymmetric (model.joinLeast (model.joinAboveRight _ _) (model.joinAboveLeft _ _))
    (model.joinLeast (model.joinAboveRight _ _) (model.joinAboveLeft _ _))

/-- x ⊔ (x ⊓ y) = x. -/
theorem joinAbsorption (kept other : model.Value) : model.join kept (model.meet kept other) = kept :=
  model.orderAntisymmetric (model.joinLeast (model.orderReflexive _) (model.meetBelowLeft _ _))
    (model.joinAboveLeft _ _)

/-- ⊤ ⊓ x = x. -/
theorem meetTopLeft (value : model.Value) : model.meet model.top value = value := by
  rw [meetCommutative]
  exact model.meetOfBelow (model.topGreatest value)

/-- The meet is monotone in both sides. -/
theorem meetMonotone {left left' right right' : model.Value} (leftBelow : model.below left left')
    (rightBelow : model.below right right') :
    model.below (model.meet left right) (model.meet left' right') :=
  model.meetGreatest (model.orderTransitive (model.meetBelowLeft _ _) leftBelow)
    (model.orderTransitive (model.meetBelowRight _ _) rightBelow)

/-- The join is monotone in both sides. -/
theorem joinMonotone {left left' right right' : model.Value} (leftBelow : model.below left left')
    (rightBelow : model.below right right') :
    model.below (model.join left right) (model.join left' right') :=
  model.joinLeast (model.orderTransitive leftBelow (model.joinAboveLeft _ _))
    (model.orderTransitive rightBelow (model.joinAboveRight _ _))

/-- An element below ⊥ is ⊥. -/
theorem bottomOfBelowBottom {value : model.Value} (below : model.below value model.bottom) :
    value = model.bottom :=
  model.orderAntisymmetric below (model.bottomLeast value)

/-- An element above ⊤ is ⊤. -/
theorem topOfTopBelow {value : model.Value} (below : model.below model.top value) :
    value = model.top :=
  model.orderAntisymmetric (model.topGreatest value) below

/-! ## The interpretation respects ⊢ and →hsa -/

/-- The η rule holds in the reading: [[λx. M x]]ρ = [[M]]ρ when x ∉ FV(M), by (P6) and
weakening. -/
theorem interpretEta (function : Term) (environment : Nat → model.Value) :
    model.interpret (.abstraction (.application (shift function) (.boundVariable 0))) environment =
      model.interpret function environment :=
  model.equalOfApply fun value => by
    rw [model.interpretAbstraction, model.interpretApplication, model.interpretVariable,
      model.interpretShift]
    rfl

/-- The congruence under λ holds in the reading: equal bodies in every environment give equal
abstractions, by (P6). -/
theorem interpretAbstractionCongruence {left right : Term}
    (equal : ∀ environment, model.interpret left environment = model.interpret right environment)
    (environment : Nat → model.Value) :
    model.interpret (.abstraction left) environment = model.interpret (.abstraction right) environment :=
  model.equalOfApply fun value => by
    rw [model.interpretAbstraction, model.interpretAbstraction, equal]

/-- Given a model satisfying the fields of `DdLP96Model`, every →hsa step is an equation of the
reading, in every environment (the record, section 4.1):
(β) by the substitution lemma, (+app) and (∥app) by (E5), the others by compositionality. -/
theorem interpretHeadStep {term result : Term} (step : HeadStep term result) :
    ∀ environment, model.interpret term environment = model.interpret result environment := by
  induction step with
  | beta body argument =>
      intro environment
      rw [model.interpretApplication, model.interpretAbstraction, model.interpretInstantiate]
  | abstraction _ inner => exact model.interpretAbstractionCongruence inner
  | choiceLeft right _ inner =>
      intro environment
      rw [model.interpretChoice, model.interpretChoice, inner]
  | choiceRight left _ inner =>
      intro environment
      rw [model.interpretChoice, model.interpretChoice, inner]
  | choiceApplication left right argument =>
      intro environment
      simp only [model.interpretApplication, model.interpretChoice, model.applyMeet]
  | parallel _ _ leftInner rightInner =>
      intro environment
      rw [model.interpretParallel, model.interpretParallel, leftInner, rightInner]
  | parallelApplication left right argument =>
      intro environment
      simp only [model.interpretApplication, model.interpretParallel, model.applyJoin]
  | function argument _ _ inner =>
      intro environment
      rw [model.interpretApplication, model.interpretApplication, inner]

/-! ## The record's theorem 4.1, direction ⇒ -/

/-- ρ_⊤, the environment that maps every variable to ⊤. -/
def topEnvironment : Nat → model.Value := fun _ => model.top

/-- d ⊤ … ⊤ with `count` arguments ⊤. -/
def applyTops : Nat → model.Value → model.Value
  | 0, value => value
  | count + 1, value => applyTops count (model.apply value model.top)

/-- ⊤ ⊤ … ⊤ = ⊤, by (E5). -/
theorem applyTopsTop : ∀ count, model.applyTops count model.top = model.top
  | 0 => rfl
  | count + 1 => by
      show model.applyTops count (model.apply model.top model.top) = model.top
      rw [model.applyTop]
      exact applyTopsTop count

/-- ⊥ ⊤ … ⊤ = ⊥, by (P8). -/
theorem applyTopsBottom : ∀ count, model.applyTops count model.bottom = model.bottom
  | 0 => rfl
  | count + 1 => by
      show model.applyTops count (model.apply model.bottom model.top) = model.bottom
      rw [model.applyBottom]
      exact applyTopsBottom count

/-- Applying more arguments ⊤ to a value that has become ⊤ keeps it ⊤. -/
theorem applyTopsAdd : ∀ (count extra : Nat) (value : model.Value),
    model.applyTops (count + extra) value = model.applyTops extra (model.applyTops count value)
  | 0, extra, value => by simp [applyTops]
  | count + 1, extra, value => by
      rw [Nat.add_right_comm]
      exact applyTopsAdd count extra (model.apply value model.top)

/-- (E5): ⊤ arguments distribute over a meet in the function position. -/
theorem applyTopsMeet : ∀ (count : Nat) (left right : model.Value),
    model.applyTops count (model.meet left right) =
      model.meet (model.applyTops count left) (model.applyTops count right)
  | 0, _, _ => rfl
  | count + 1, left, right => by
      show model.applyTops count (model.apply (model.meet left right) model.top) = _
      rw [model.applyMeet]
      exact applyTopsMeet count _ _

/-- (E5): ⊤ arguments distribute over a join in the function position. -/
theorem applyTopsJoin : ∀ (count : Nat) (left right : model.Value),
    model.applyTops count (model.join left right) =
      model.join (model.applyTops count left) (model.applyTops count right)
  | 0, _, _ => rfl
  | count + 1, left, right => by
      show model.applyTops count (model.apply (model.join left right) model.top) = _
      rw [model.applyJoin]
      exact applyTopsJoin count _ _

/-- A stuck spine x M⃗ reads as ⊤ in ρ_⊤: its head reads as ⊤, and ⊤ y = ⊤ (E5). -/
theorem interpretStuckSpine {term : Term} (stuck : StuckSpine term) :
    model.interpret term model.topEnvironment = model.top := by
  induction stuck with
  | boundVariable index => rw [model.interpretVariable]; rfl
  | application argument _ inner => rw [model.interpretApplication, inner, model.applyTop]

/-- The record, section 4.1: a head normal form H reads in ρ_⊤ as a value d with d ⊤ … ⊤ = ⊤ for
enough arguments ⊤. -/
theorem applyTopsHeadNormalForm {term : Term} (normal : HeadNormalForm term) :
    ∃ count, model.applyTops count (model.interpret term model.topEnvironment) = model.top := by
  induction normal with
  | stuck stuck => exact ⟨0, model.interpretStuckSpine stuck⟩
  | @abstraction body _ inner =>
      obtain ⟨count, tops⟩ := inner
      refine ⟨count + 1, ?_⟩
      show model.applyTops count
        (model.apply (model.interpret (.abstraction body) model.topEnvironment) model.top) = model.top
      rw [model.interpretAbstraction]
      have sameEnvironment : extendEnvironment model.top model.topEnvironment = model.topEnvironment := by
        funext index
        cases index <;> rfl
      rw [sameEnvironment]
      exact tops
  | choice _ _ leftInner rightInner =>
      obtain ⟨leftCount, leftTops⟩ := leftInner
      obtain ⟨rightCount, rightTops⟩ := rightInner
      refine ⟨leftCount + rightCount, ?_⟩
      rw [model.interpretChoice, model.applyTopsMeet, model.applyTopsAdd leftCount rightCount,
        Nat.add_comm leftCount rightCount, model.applyTopsAdd rightCount leftCount, leftTops,
        rightTops, model.applyTopsTop, model.applyTopsTop, model.meetTopLeft]
  | parallelLeft right _ inner =>
      obtain ⟨count, tops⟩ := inner
      refine ⟨count, ?_⟩
      rw [model.interpretParallel, model.applyTopsJoin, tops]
      exact model.topOfTopBelow (model.joinAboveLeft _ _)
  | parallelRight left _ inner =>
      obtain ⟨count, tops⟩ := inner
      refine ⟨count, ?_⟩
      rw [model.interpretParallel, model.applyTopsJoin, tops]
      exact model.topOfTopBelow (model.joinAboveRight _ _)

/-- A solvable term reduces by →hsa to a head normal form: follow any step while there is one;
the bound on the length of the reduction sequences ends the walk. -/
theorem reducesToHeadNormalForm : ∀ (steps : Nat) {term : Term},
    HeadReductionsAtMost steps term →
      ∃ normal, HeadNormalForm normal ∧
        ∀ environment, model.interpret term environment = model.interpret normal environment
  | 0, term, normalForm =>
      ⟨term, headStepNoneIffHeadNormalForm.mp normalForm, fun _ => rfl⟩
  | steps + 1, term, bounded => by
      rcases Classical.em (∀ result, ¬ HeadStep term result) with none | some
      · exact ⟨term, headStepNoneIffHeadNormalForm.mp none, fun _ => rfl⟩
      · obtain ⟨result, step⟩ := Classical.not_forall_not.mp some
        obtain ⟨normal, isNormal, same⟩ := reducesToHeadNormalForm steps (bounded result step)
        exact ⟨normal, isNormal, fun environment =>
          (model.interpretHeadStep step environment).trans (same environment)⟩

/-- The record's theorem 4.1, direction ⇒, given a model satisfying the fields of `DdLP96Model`:
a solvable term does not read as ⊥ in ρ_⊤. It reduces to a head normal form H with the same
reading, H ⊤ … ⊤ reads as ⊤, and ⊥ ⊤ … ⊤ = ⊥ ≠ ⊤. -/
theorem interpretNotBottomOfSolvable {term : Term} (solvable : Solvable term) :
    model.interpret term model.topEnvironment ≠ model.bottom := by
  intro isBottom
  obtain ⟨steps, bounded⟩ := solvable
  obtain ⟨normal, isNormal, same⟩ := model.reducesToHeadNormalForm steps bounded
  obtain ⟨count, tops⟩ := model.applyTopsHeadNormalForm isNormal
  rw [← same, isBottom, model.applyTopsBottom] at tops
  exact model.topNotBottom tops.symm

end DdLP96Model

end LambdaJit.ContextualPreorder
