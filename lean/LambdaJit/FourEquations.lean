import LambdaJit.Terms

/-!
# Derivations of numbered equations from others, under any set of laws

`DerivableFrom laws` is the least congruence that contains the β rule, the η rule and the
equations `laws`. Its rules are `laws`, symmetry, transitivity, the congruence in the argument of
an application and in the body of an abstraction, the β rule and the η rule. Reflexivity and the
congruences in the function of an application and in each side of a choice and of a parallel are
theorems of them (`reflexive`, `congruenceFunction`, `congruenceChoiceLeft`,
`congruenceChoiceRight`, `congruenceParallelLeft`, `congruenceParallelRight`).

Each theorem names, as hypotheses on `laws`, the numbered equations of
the proofs file (section 1) it uses. Module `LatticeEtaDerivability`
reads them with ⊢_{λ-lattice-η}, whose axioms are (1), (3), (5) and (10), as `laws`, and derives
there the other λ-lattice laws with no unit law. One theorem is about another set of equations:
`choiceFunctionDistributiveFromEquationsOneThreeSixTen`, equation (8), (M + N) P = M P + N P, is
derivable from (1), (3), (6) and (10) with β, η and the congruence, without (7), (8) and (9).

The proofs follow section 6 of the proofs file; each docstring below names the step of that
section it checks. "A refines B" stands for the equation A + B = B.
-/

namespace LambdaJit.FourEquations

open LambdaJit.Semantics
open LambdaJit.Semantics.Term

/-- The least congruence that contains the β rule, the η rule and the equations `laws`. The
constructors are the rules of `Semantics.DerivableLatticeEta` that are not numbered equations,
`laws` in the place of the hypotheses. -/
inductive DerivableFrom (laws : Term → Term → Prop) : Term → Term → Prop where
  /-- Every equation of `laws`. -/
  | law {left right : Term} : laws left right → DerivableFrom laws left right
  /-- Symmetry: N = M from M = N. -/
  | symmetric {left right : Term} : DerivableFrom laws left right → DerivableFrom laws right left
  /-- Transitivity: M = P from M = N and N = P. -/
  | transitive {left middle right : Term} :
      DerivableFrom laws left middle → DerivableFrom laws middle right →
        DerivableFrom laws left right
  /-- The congruence in the argument of an application: Z M = Z N from M = N. -/
  | congruenceArgument (function : Term) {left right : Term} :
      DerivableFrom laws left right →
        DerivableFrom laws (application function left) (application function right)
  /-- The congruence in the body of an abstraction, ξ: λx. M = λx. N from M = N. -/
  | congruenceAbstraction {left right : Term} :
      DerivableFrom laws left right → DerivableFrom laws (abstraction left) (abstraction right)
  /-- The β rule: (λx. M) N = M[x := N]. -/
  | beta (body argument : Term) :
      DerivableFrom laws (application (abstraction body) argument) (instantiate body argument)
  /-- The η rule: λx. M x = M with x ∉ FV(M). -/
  | eta (function : Term) :
      DerivableFrom laws (abstraction (application (shift function) (boundVariable 0))) function

/-- `laws` contains every instance of equation (1), M + N = N + M. -/
def EquationOne (laws : Term → Term → Prop) : Prop :=
  ∀ left right, laws (choice left right) (choice right left)

/-- `laws` contains every instance of equation (3), M ∥ N = N ∥ M. -/
def EquationThree (laws : Term → Term → Prop) : Prop :=
  ∀ left right, laws (parallel left right) (parallel right left)

/-- `laws` contains every instance of equation (5), M ∥ (M + N) = M. -/
def EquationFive (laws : Term → Term → Prop) : Prop :=
  ∀ kept other, laws (parallel kept (choice kept other)) kept

/-- `laws` contains every instance of equation (6), M + (M ∥ N) = M. -/
def EquationSix (laws : Term → Term → Prop) : Prop :=
  ∀ kept other, laws (choice kept (parallel kept other)) kept

/-- `laws` contains every instance of equation (10), M A + M (A + B) = M (A + B). -/
def EquationTen (laws : Term → Term → Prop) : Prop :=
  ∀ function argument addition,
    laws (choice (application function argument) (application function (choice argument addition)))
      (application function (choice argument addition))

/-- The instance of equation (8) at `left`, `right` and `argument`:
(left + right) argument = left argument + right argument is derivable from `laws`. -/
def ChoiceFunctionDistributive (laws : Term → Term → Prop) (left right argument : Term) : Prop :=
  DerivableFrom laws (application (choice left right) argument)
    (choice (application left argument) (application right argument))

namespace DerivableFrom

variable {laws : Term → Term → Prop}

/-- Rewriting both sides of a derived equation by derived equations. -/
theorem rewrite {left right rewrittenLeft rewrittenRight : Term}
    (equal : DerivableFrom laws left right)
    (leftEqual : DerivableFrom laws left rewrittenLeft)
    (rightEqual : DerivableFrom laws right rewrittenRight) :
    DerivableFrom laws rewrittenLeft rewrittenRight :=
  .transitive (.symmetric leftEqual) (.transitive equal rightEqual)

/-! ## The functions the derivations give to (10), each with its β step -/

/-- λw. value -/
def constant (value : Term) : Term := abstraction (shift value)

/-- λw. w + value -/
def addRight (value : Term) : Term := abstraction (choice (boundVariable 0) (shift value))

/-- λw. value + w -/
def addLeft (value : Term) : Term := abstraction (choice (shift value) (boundVariable 0))

/-- λw. value ∥ w -/
def parallelWith (value : Term) : Term := abstraction (parallel (shift value) (boundVariable 0))

/-- λw. w ∥ value -/
def parallelOn (value : Term) : Term := abstraction (parallel (boundVariable 0) (shift value))

/-- λg. g argument -/
def applyTo (argument : Term) : Term :=
  abstraction (application (boundVariable 0) (shift argument))

/-- W = λz. left z + right z -/
def pointwiseChoice (left right : Term) : Term :=
  abstraction (choice (application (shift left) (boundVariable 0))
    (application (shift right) (boundVariable 0)))

/-- V = λz. left z ∥ right z -/
def pointwiseParallel (left right : Term) : Term :=
  abstraction (parallel (application (shift left) (boundVariable 0))
    (application (shift right) (boundVariable 0)))

/-- λw. λz. left z + w z -/
def withLeft (left : Term) : Term :=
  abstraction (abstraction (choice (application (shiftFrom 1 (shift left)) (boundVariable 0))
    (application (boundVariable 1) (boundVariable 0))))

/-- λw. λz. w z + right z -/
def withRight (right : Term) : Term :=
  abstraction (abstraction (choice (application (boundVariable 1) (boundVariable 0))
    (application (shiftFrom 1 (shift right)) (boundVariable 0))))

/-- (λw. value) argument = value, by β. -/
theorem betaConstant (value argument : Term) :
    DerivableFrom laws (application (constant value) argument) value := by
  have step := DerivableFrom.beta (laws := laws) (shift value) argument
  simp only [instantiate, substituteShift] at step
  exact step

/-- (λw. w + value) argument = argument + value, by β. -/
theorem betaAddRight (value argument : Term) :
    DerivableFrom laws (application (addRight value) argument) (choice argument value) := by
  have step := DerivableFrom.beta (laws := laws) (choice (boundVariable 0) (shift value)) argument
  simp [instantiate, substitute, substituteShift] at step
  exact step

/-- (λw. value + w) argument = value + argument, by β. -/
theorem betaAddLeft (value argument : Term) :
    DerivableFrom laws (application (addLeft value) argument) (choice value argument) := by
  have step := DerivableFrom.beta (laws := laws) (choice (shift value) (boundVariable 0)) argument
  simp [instantiate, substitute, substituteShift] at step
  exact step

/-- (λw. value ∥ w) argument = value ∥ argument, by β. -/
theorem betaParallelWith (value argument : Term) :
    DerivableFrom laws (application (parallelWith value) argument) (parallel value argument) := by
  have step := DerivableFrom.beta (laws := laws) (parallel (shift value) (boundVariable 0)) argument
  simp [instantiate, substitute, substituteShift] at step
  exact step

/-- (λw. w ∥ value) argument = argument ∥ value, by β. -/
theorem betaParallelOn (value argument : Term) :
    DerivableFrom laws (application (parallelOn value) argument) (parallel argument value) := by
  have step := DerivableFrom.beta (laws := laws) (parallel (boundVariable 0) (shift value)) argument
  simp [instantiate, substitute, substituteShift] at step
  exact step

/-- (λg. g argument) function = function argument, by β. -/
theorem betaApplyTo (argument function : Term) :
    DerivableFrom laws (application (applyTo argument) function)
      (application function argument) := by
  have step := DerivableFrom.beta (laws := laws)
    (application (boundVariable 0) (shift argument)) function
  simp [instantiate, substitute, substituteShift] at step
  exact step

/-- W argument = left argument + right argument, by β. -/
theorem betaPointwiseChoice (left right argument : Term) :
    DerivableFrom laws (application (pointwiseChoice left right) argument)
      (choice (application left argument) (application right argument)) := by
  have step := DerivableFrom.beta (laws := laws)
    (choice (application (shift left) (boundVariable 0))
      (application (shift right) (boundVariable 0))) argument
  simp [instantiate, substitute, substituteShift] at step
  exact step

/-- V argument = left argument ∥ right argument, by β. -/
theorem betaPointwiseParallel (left right argument : Term) :
    DerivableFrom laws (application (pointwiseParallel left right) argument)
      (parallel (application left argument) (application right argument)) := by
  have step := DerivableFrom.beta (laws := laws)
    (parallel (application (shift left) (boundVariable 0))
      (application (shift right) (boundVariable 0))) argument
  simp [instantiate, substitute, substituteShift] at step
  exact step

/-- (λw. λz. left z + w z) argument = λz. left z + argument z, by β. -/
theorem betaWithLeft (left argument : Term) :
    DerivableFrom laws (application (withLeft left) argument)
      (abstraction (choice (application (shift left) (boundVariable 0))
        (application (shift argument) (boundVariable 0)))) := by
  have step := DerivableFrom.beta (laws := laws)
    (abstraction (choice (application (shiftFrom 1 (shift left)) (boundVariable 0))
      (application (boundVariable 1) (boundVariable 0)))) argument
  simp [instantiate, substitute, substituteShiftFromCancel] at step
  exact step

/-- (λw. λz. w z + right z) argument = λz. argument z + right z, by β. -/
theorem betaWithRight (right argument : Term) :
    DerivableFrom laws (application (withRight right) argument)
      (abstraction (choice (application (shift argument) (boundVariable 0))
        (application (shift right) (boundVariable 0)))) := by
  have step := DerivableFrom.beta (laws := laws)
    (abstraction (choice (application (boundVariable 1) (boundVariable 0))
      (application (shiftFrom 1 (shift right)) (boundVariable 0)))) argument
  simp [instantiate, substitute, substituteShiftFromCancel] at step
  exact step

/-! ## Reflexivity and the congruences that are theorems -/

/-- Reflexivity, M = M, a theorem: (λx. x) M = M by the β rule, so M = (λx. x) M = M by symmetry
and transitivity. -/
theorem reflexive (term : Term) : DerivableFrom laws term term := by
  have step := DerivableFrom.beta (laws := laws) (boundVariable 0) term
  simp [instantiate, substitute] at step
  exact .transitive (.symmetric step) step

/-- From M = N, `leftImage` = `rightImage` when F M contracts to `leftImage` and F N to
`rightImage`: the congruence in the argument of F, read through the two contractions. -/
theorem congruenceThroughContraction {function left right leftImage rightImage : Term}
    (equal : DerivableFrom laws left right)
    (leftContraction : DerivableFrom laws (application function left) leftImage)
    (rightContraction : DerivableFrom laws (application function right) rightImage) :
    DerivableFrom laws leftImage rightImage :=
  rewrite (.congruenceArgument function equal) leftContraction rightContraction

/-- The congruence in the function of an application, M Z = N Z from M = N, a theorem: the
congruence in the argument of λg. g Z, and the β rule. -/
theorem congruenceFunction {left right : Term} (argument : Term)
    (equal : DerivableFrom laws left right) :
    DerivableFrom laws (application left argument) (application right argument) :=
  congruenceThroughContraction equal (betaApplyTo argument left) (betaApplyTo argument right)

/-- The congruence in the left side of a choice, M + P = N + P from M = N, a theorem: the
congruence in the argument of λw. w + P, and the β rule. -/
theorem congruenceChoiceLeft {left right : Term} (other : Term)
    (equal : DerivableFrom laws left right) :
    DerivableFrom laws (choice left other) (choice right other) :=
  congruenceThroughContraction equal (betaAddRight other left) (betaAddRight other right)

/-- The congruence in the right side of a choice, P + M = P + N from M = N, a theorem: the
congruence in the argument of λw. P + w, and the β rule. -/
theorem congruenceChoiceRight (other : Term) {left right : Term}
    (equal : DerivableFrom laws left right) :
    DerivableFrom laws (choice other left) (choice other right) :=
  congruenceThroughContraction equal (betaAddLeft other left) (betaAddLeft other right)

/-- The congruence in the left side of a parallel, M ∥ P = N ∥ P from M = N, a theorem: the
congruence in the argument of λw. w ∥ P, and the β rule. -/
theorem congruenceParallelLeft {left right : Term} (other : Term)
    (equal : DerivableFrom laws left right) :
    DerivableFrom laws (parallel left other) (parallel right other) :=
  congruenceThroughContraction equal (betaParallelOn other left) (betaParallelOn other right)

/-- The congruence in the right side of a parallel, P ∥ M = P ∥ N from M = N, a theorem: the
congruence in the argument of λw. P ∥ w, and the β rule. -/
theorem congruenceParallelRight (other : Term) {left right : Term}
    (equal : DerivableFrom laws left right) :
    DerivableFrom laws (parallel other left) (parallel other right) :=
  congruenceThroughContraction equal (betaParallelWith other left) (betaParallelWith other right)

/-- A derivation whose laws are themselves derivable from `laws` is a derivation from `laws`. -/
theorem ofDerivableLaws {left right : Term}
    (derivation : DerivableFrom (DerivableFrom laws) left right) :
    DerivableFrom laws left right := by
  induction derivation with
  | law derivable => exact derivable
  | symmetric _ inner => exact .symmetric inner
  | transitive _ _ firstStep secondStep => exact .transitive firstStep secondStep
  | congruenceArgument function _ inner => exact .congruenceArgument function inner
  | congruenceAbstraction _ inner => exact .congruenceAbstraction inner
  | beta body argument => exact .beta body argument
  | eta function => exact .eta function

/-- The congruence in both sides of a choice at once. -/
theorem choiceBoth {left rewrittenLeft right rewrittenRight : Term}
    (leftEqual : DerivableFrom laws left rewrittenLeft)
    (rightEqual : DerivableFrom laws right rewrittenRight) :
    DerivableFrom laws (choice left right) (choice rewrittenLeft rewrittenRight) :=
  .transitive (.congruenceChoiceLeft right leftEqual)
    (.congruenceChoiceRight rewrittenLeft rightEqual)

/-- Equation (10) read through contractions: from M A = `image` and M (A + B) = `imageOfSum`,
`image` + `imageOfSum` = `imageOfSum`. -/
theorem monotoneThroughContraction (equationTen : EquationTen laws)
    {function argument addition image imageOfSum : Term}
    (atArgument : DerivableFrom laws (application function argument) image)
    (atSum : DerivableFrom laws (application function (choice argument addition)) imageOfSum) :
    DerivableFrom laws (choice image imageOfSum) imageOfSum :=
  rewrite (.law (equationTen function argument addition)) (choiceBoth atArgument atSum) atSum

/-- (λz. B) shifted and applied to index 0 is B: the β step under a binder. -/
theorem betaShiftedAtZero (body : Term) :
    DerivableFrom laws (application (shift (abstraction body)) (boundVariable 0)) body := by
  have step := DerivableFrom.beta (laws := laws) (shiftFrom 1 body) (boundVariable 0)
  rw [instantiateShiftFrom] at step
  exact step

/-- ξ and η: F = G from F z = G z at a fresh z. -/
theorem extensional {function other : Term}
    (pointwise : DerivableFrom laws (application (shift function) (boundVariable 0))
      (application (shift other) (boundVariable 0))) :
    DerivableFrom laws function other :=
  .transitive (.symmetric (.eta function))
    (.transitive (.congruenceAbstraction pointwise) (.eta other))

/-- Monotonicity in the function position, from (10) and β: from A + B = B, A P + B P = B P.
(10) with M := λg. g P (section 2 of the proofs file, the last item). -/
theorem functionMonotone (equationTen : EquationTen laws) {smaller larger : Term}
    (argument : Term) (refines : DerivableFrom laws (choice smaller larger) larger) :
    DerivableFrom laws (choice (application smaller argument) (application larger argument))
      (application larger argument) :=
  monotoneThroughContraction equationTen (betaApplyTo argument smaller)
    (.transitive (.congruenceArgument _ refines) (betaApplyTo argument larger))

/-! ## Equation (8) from (1) and (10), given that X and Y refine W = λz. X z + Y z -/

section Distributivity

variable (commutative : ∀ left right, DerivableFrom laws (choice left right) (choice right left))
variable (equationTen : EquationTen laws)

include commutative in
/-- Section 6's lemma (v), by (1): from a + b = b and b + a = a, a = b. -/
theorem antisymmetricByCommutative {first second : Term}
    (firstRefines : DerivableFrom laws (choice first second) second)
    (secondRefines : DerivableFrom laws (choice second first) first) :
    DerivableFrom laws first second :=
  .transitive (.symmetric secondRefines) (.transitive (commutative second first) firstRefines)

include commutative equationTen in
/-- Section 6's lemma (iii), by (1), (10) and β: from a + c = c and b + c = c,
(a + b) + c = c. -/
theorem choiceRefinesByCommutative {first second upper : Term}
    (firstRefines : DerivableFrom laws (choice first upper) upper)
    (secondRefines : DerivableFrom laws (choice second upper) upper) :
    DerivableFrom laws (choice (choice first second) upper) upper := by
  have step := monotoneThroughContraction equationTen (betaAddRight second first)
    (betaAddRight second (choice first upper))
  have chain : DerivableFrom laws (choice (choice first upper) second) upper :=
    .transitive (.congruenceChoiceLeft second firstRefines)
      (.transitive (commutative upper second) secondRefines)
  exact rewrite step (.congruenceChoiceRight _ chain) chain

include commutative equationTen in
/-- The end of section 6's derivation of (8), from lemma (iii) on: (8) at X, Y and P from
X + W = W and Y + W = W, where W = λz. X z + Y z, by (1), (10) and β. -/
theorem choiceFunctionDistributiveOfRefines (left right argument : Term)
    (leftRefines : DerivableFrom laws (choice left (pointwiseChoice left right))
      (pointwiseChoice left right))
    (rightRefines : DerivableFrom laws (choice right (pointwiseChoice left right))
      (pointwiseChoice left right)) :
    ChoiceFunctionDistributive laws left right argument := by
  have sumRefines := choiceRefinesByCommutative commutative equationTen leftRefines rightRefines
  -- (X + Y) P + (X P + Y P) = X P + Y P
  have upward : DerivableFrom laws
      (choice (application (choice left right) argument)
        (choice (application left argument) (application right argument)))
      (choice (application left argument) (application right argument)) := by
    have step := functionMonotone equationTen argument sumRefines
    exact rewrite step (.congruenceChoiceRight _ (betaPointwiseChoice left right argument))
      (betaPointwiseChoice left right argument)
  -- (X P + Y P) + (X + Y) P = (X + Y) P
  have downward : DerivableFrom laws
      (choice (choice (application left argument) (application right argument))
        (application (choice left right) argument))
      (application (choice left right) argument) := by
    have leftStep : DerivableFrom laws
        (choice (application left argument) (application (choice left right) argument))
        (application (choice left right) argument) :=
      monotoneThroughContraction equationTen (betaApplyTo argument left)
        (betaApplyTo argument (choice left right))
    have rightStepSwapped := monotoneThroughContraction equationTen (addition := left)
      (betaApplyTo argument right) (betaApplyTo argument (choice right left))
    have swap : DerivableFrom laws (application (choice right left) argument)
        (application (choice left right) argument) :=
      .congruenceFunction argument (commutative right left)
    have rightStep : DerivableFrom laws
        (choice (application right argument) (application (choice left right) argument))
        (application (choice left right) argument) :=
      rewrite rightStepSwapped (.congruenceChoiceRight _ swap) swap
    exact choiceRefinesByCommutative commutative equationTen leftStep rightStep
  exact antisymmetricByCommutative commutative upward downward

end Distributivity

/-! ## Equation (8) from (1), (3), (6), (10), β and η -/

/-- Equation (8) from (1), (3), (6), (10), β, η and the congruence, without (7), (8) and (9):
section 6's derivation of (8) with X ∥ Y, which (1), (3) and (6) make refine both X and Y. With W = λz. X z + Y z and F = λw. λz. X z + w z, (10) at F with A := X ∥ Y and
B := Y gives F (X ∥ Y) + F Y = F Y, where F Y = W by β and F (X ∥ Y) = X by β, ξ, (10) and η; so
X refines W, and Y likewise; then `choiceFunctionDistributiveOfRefines`. -/
theorem choiceFunctionDistributiveOfEquationsOneThreeSixTen (equationOne : EquationOne laws)
    (equationThree : EquationThree laws) (equationSix : EquationSix laws)
    (equationTen : EquationTen laws) (left right argument : Term) :
    ChoiceFunctionDistributive laws left right argument := by
  have commutative : ∀ first second, DerivableFrom laws (choice first second)
      (choice second first) :=
    fun first second => .law (equationOne first second)
  -- (a ∥ b) + a = a and (a ∥ b) + b = b
  have parallelRefinesLeft : ∀ first second,
      DerivableFrom laws (choice (parallel first second) first) first := fun first second =>
    .transitive (commutative _ _) (.law (equationSix first second))
  have parallelRefinesRight : ∀ first second,
      DerivableFrom laws (choice (parallel first second) second) second := fun first second =>
    .transitive (commutative _ _)
      (.transitive (.congruenceChoiceRight second (.law (equationThree first second)))
        (.law (equationSix second first)))
  have leftRefines : DerivableFrom laws (choice left (pointwiseChoice left right))
      (pointwiseChoice left right) := by
    have atParallel : DerivableFrom laws
        (application (withLeft left) (parallel left right)) left :=
      .transitive (betaWithLeft left (parallel left right))
        (.transitive (.congruenceAbstraction
          (.transitive (commutative _ _)
            (functionMonotone equationTen (boundVariable 0)
              (parallelRefinesLeft (shift left) (shift right)))))
          (.eta left))
    have atSum : DerivableFrom laws
        (application (withLeft left) (choice (parallel left right) right))
        (pointwiseChoice left right) :=
      .transitive (.congruenceArgument _ (parallelRefinesRight left right))
        (betaWithLeft left right)
    exact monotoneThroughContraction equationTen atParallel atSum
  have rightRefines : DerivableFrom laws (choice right (pointwiseChoice left right))
      (pointwiseChoice left right) := by
    have atParallel : DerivableFrom laws
        (application (withRight right) (parallel left right)) right :=
      .transitive (betaWithRight right (parallel left right))
        (.transitive (.congruenceAbstraction
          (functionMonotone equationTen (boundVariable 0)
            (parallelRefinesRight (shift left) (shift right))))
          (.eta right))
    have atSum : DerivableFrom laws
        (application (withRight right) (choice (parallel left right) left))
        (pointwiseChoice left right) :=
      .transitive (.congruenceArgument _ (parallelRefinesLeft left right))
        (betaWithRight right left)
    exact monotoneThroughContraction equationTen atParallel atSum
  exact choiceFunctionDistributiveOfRefines commutative equationTen left right argument
    leftRefines rightRefines

/-! ## T1, T9 from left to right, step 丙 and lemma (vii), from (3), (5), (10) and β -/

section FromFourEquations

variable (equationThree : EquationThree laws) (equationFive : EquationFive laws)
  (equationTen : EquationTen laws)

include equationTen in
/-- Section 6's step 甲, T1: N + N = N, by (10) with M := λw. N, A := B := N, and β. -/
theorem choiceIdempotent (term : Term) : DerivableFrom laws (choice term term) term :=
  monotoneThroughContraction equationTen (addition := term) (betaConstant term term)
    (betaConstant term (choice term term))

include equationFive in
/-- T9 from left to right, by (5): N ∥ A = N from N + A = A, since N ∥ A = N ∥ (N + A) = N. -/
theorem parallelOfRefines {lower upper : Term}
    (refines : DerivableFrom laws (choice lower upper) upper) :
    DerivableFrom laws (parallel lower upper) lower :=
  .transitive (.congruenceParallelRight lower (.symmetric refines))
    (.law (equationFive lower upper))

include equationThree equationFive in
/-- Section 6's step 丙: from P + Q = Q and Q + P = P, P = Q, by (3) and (5). -/
theorem antisymmetric {first second : Term}
    (firstRefines : DerivableFrom laws (choice first second) second)
    (secondRefines : DerivableFrom laws (choice second first) first) :
    DerivableFrom laws first second := by
  have firstParallel : DerivableFrom laws (parallel first second) first :=
    parallelOfRefines equationFive firstRefines
  have secondParallel : DerivableFrom laws (parallel second first) second :=
    parallelOfRefines equationFive secondRefines
  exact .transitive (.symmetric firstParallel)
    (.transitive (.law (equationThree first second)) secondParallel)

include equationFive equationTen in
/-- Section 6's lemma (vii), by (5), (10) and β: from c + a = a and c + b = b,
c + (a ∥ b) = a ∥ b. -/
theorem refinesParallel {lower first second : Term}
    (firstRefined : DerivableFrom laws (choice lower first) first)
    (secondRefined : DerivableFrom laws (choice lower second) second) :
    DerivableFrom laws (choice lower (parallel first second)) (parallel first second) := by
  have step := monotoneThroughContraction equationTen (betaParallelOn second lower)
    (betaParallelOn second (choice lower first))
  have lowerParallel : DerivableFrom laws (parallel lower second) lower :=
    parallelOfRefines equationFive secondRefined
  exact rewrite step (choiceBoth lowerParallel (.congruenceParallelLeft second firstRefined))
    (.congruenceParallelLeft second firstRefined)

end FromFourEquations

end DerivableFrom

/-- The equations (1), (3), (6) and (10), every instance of each. -/
inductive EquationsOneThreeSixTen : Term → Term → Prop where
  /-- (1): M + N = N + M. -/
  | choiceCommutative (left right : Term) :
      EquationsOneThreeSixTen (choice left right) (choice right left)
  /-- (3): M ∥ N = N ∥ M. -/
  | parallelCommutative (left right : Term) :
      EquationsOneThreeSixTen (parallel left right) (parallel right left)
  /-- (6): M + (M ∥ N) = M. -/
  | choiceAbsorption (kept other : Term) :
      EquationsOneThreeSixTen (choice kept (parallel kept other)) kept
  /-- (10): M A + M (A + B) = M (A + B). -/
  | argumentMonotone (function argument addition : Term) :
      EquationsOneThreeSixTen (choice (application function argument)
        (application function (choice argument addition)))
        (application function (choice argument addition))

/-- Equation (8), (M + N) P = M P + N P, is derivable from (1), (3), (6) and (10) with β, η and
the congruence, without (7), (8) and (9). -/
theorem choiceFunctionDistributiveFromEquationsOneThreeSixTen (left right argument : Term) :
    ChoiceFunctionDistributive EquationsOneThreeSixTen left right argument :=
  DerivableFrom.choiceFunctionDistributiveOfEquationsOneThreeSixTen
    EquationsOneThreeSixTen.choiceCommutative EquationsOneThreeSixTen.parallelCommutative
    EquationsOneThreeSixTen.choiceAbsorption EquationsOneThreeSixTen.argumentMonotone
    left right argument

end LambdaJit.FourEquations
