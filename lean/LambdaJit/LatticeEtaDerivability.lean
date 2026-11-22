import LambdaJit.Semantics

/-!
# ⊢_{λ-lattice-η}: the derivability of the calculus

The derivability relation of the calculus: DdLP96's λ-lattice laws
(their Definition 51 written as equations) with the η rule, and no unit law, since DdLP96 have no unit
axiom. The proofs file writes it ⊢_{λ-lattice-η} in section 3 and ⊢_B in section 21.

`DerivableLatticeEta hypotheses left right` has one constructor per rule, so that a checker can
read its rules from the constructor list: the hypotheses; symmetry, transitivity, the congruence
in the argument of an application and the congruence under λ (four closure rules of a
congruence); the β rule and the η rule; and the axioms (1) M + N = N + M,
(3) M ∥ N = N ∥ M, (5) M ∥ (M + N) = M and (10) M A + M (A + B) = M (A + B). The other λ-lattice
laws are theorems, each derived from its axioms through `FourEquations.DerivableFrom`:

- (6) M + (M ∥ N) = M from (1), (5), (10) and β (`DerivableLatticeEta.choiceAbsorption`);
- (2) and (4) from (1), (3), (5), (6), (10) and β (`choiceAssociative`, `parallelAssociative`);
- (8) from (1), (3), (6), (10), β and η, the proofs file's second derivation of (8), section 6
  (`choiceFunctionDistributive`);
- (9) from (1), (3), (5), (6), (8), (10), β and η (`parallelFunctionDistributive`).

Reflexivity and the congruences in the function of an application and in each side of a choice
and of a parallel are theorems of the closure rules and β.

This module imports only module `Semantics`, so that the modules on the IR side can state their
results in ⊢_{λ-lattice-η}. Module `LatticeEtaConsistency` proves, without the unit law, that
⊢_{λ-lattice-η} with no hypothesis is consistent
(`consistentLatticeEtaWithoutHypotheses`) and that every equation it derives is a contextual
equivalence (`contextualEquivalenceOfDerivableLatticeEta`).
-/

namespace LambdaJit.FourEquations.DerivableFrom

open LambdaJit.Semantics
open LambdaJit.Semantics.Term

variable {laws : Term → Term → Prop}

/-! ## The λ-lattice laws from (1), (3), (5), (10), β and η, with no unit law -/

section WithoutUnitLaw

variable (equationOne : EquationOne laws) (equationThree : EquationThree laws)
  (equationFive : EquationFive laws) (equationTen : EquationTen laws)

include equationOne equationFive equationTen in
/-- (6), M + (M ∥ N) = M, from (1), (5), (10) and β: the proofs file's section 6. (10) with
M := λw. x ∥ w, A := y, B := x gives (x ∥ y) + (x ∥ (y + x)) = x ∥ (y + x), and
x ∥ (y + x) = x by (1) and (5). -/
theorem choiceAbsorptionWithoutUnitLaw (kept other : Term) :
    DerivableFrom laws (choice kept (parallel kept other)) kept := by
  have step := monotoneThroughContraction equationTen (betaParallelWith kept other)
    (betaParallelWith kept (choice other kept))
  have chain : DerivableFrom laws (parallel kept (choice other kept)) kept :=
    .transitive (.congruenceParallelRight kept (.law (equationOne other kept)))
      (.law (equationFive kept other))
  have refines : DerivableFrom laws (choice (parallel kept other) kept) kept :=
    rewrite step (.congruenceChoiceRight _ chain) chain
  exact .transitive (.law (equationOne _ _)) refines

include equationOne equationFive equationTen in
/-- The first half of section 6's lemma (vi), (a ∥ b) + a = a, by (1) and (6). -/
theorem parallelRefinesLeftWithoutUnitLaw (first second : Term) :
    DerivableFrom laws (choice (parallel first second) first) first :=
  .transitive (.law (equationOne _ _))
    (choiceAbsorptionWithoutUnitLaw equationOne equationFive equationTen first second)

include equationOne equationThree equationFive equationTen in
/-- The second half of section 6's lemma (vi), (a ∥ b) + b = b, by (1), (3) and (6). -/
theorem parallelRefinesRightWithoutUnitLaw (first second : Term) :
    DerivableFrom laws (choice (parallel first second) second) second :=
  .transitive (.law (equationOne _ _))
    (.transitive (.congruenceChoiceRight second (.law (equationThree first second)))
      (choiceAbsorptionWithoutUnitLaw equationOne equationFive equationTen second first))

include equationOne equationThree equationFive equationTen in
/-- T9 from right to left, section 6's lemma (i): from a ∥ b = a, a + b = b, by
a + b = (a ∥ b) + b = b. -/
theorem refinesOfParallelWithoutUnitLaw {lower upper : Term}
    (parallelEqual : DerivableFrom laws (parallel lower upper) lower) :
    DerivableFrom laws (choice lower upper) upper :=
  .transitive (.congruenceChoiceLeft upper (.symmetric parallelEqual))
    (parallelRefinesRightWithoutUnitLaw equationOne equationThree equationFive equationTen lower upper)

include equationOne equationThree equationFive equationTen in
/-- The first half of section 6's lemma (ii), a + (a + b) = a + b: a ∥ (a + b) = a by (5), then
lemma (i). -/
theorem leftRefinesChoiceWithoutUnitLaw (first second : Term) :
    DerivableFrom laws (choice first (choice first second)) (choice first second) :=
  refinesOfParallelWithoutUnitLaw equationOne equationThree equationFive equationTen
    (.law (equationFive first second))

include equationOne equationThree equationFive equationTen in
/-- The second half of section 6's lemma (ii), b + (a + b) = a + b: b ∥ (a + b) = b ∥ (b + a) = b by
(1) and (5), then lemma (i). -/
theorem rightRefinesChoiceWithoutUnitLaw (kept other : Term) :
    DerivableFrom laws (choice kept (choice other kept)) (choice other kept) :=
  refinesOfParallelWithoutUnitLaw equationOne equationThree equationFive equationTen
    (.transitive (.congruenceParallelRight kept (.law (equationOne other kept)))
      (.law (equationFive kept other)))

include equationOne equationThree equationFive equationTen in
/-- Section 6's lemma (iv), by (1), (3), (5), (10) and β: from a + b = b and b + c = c, a + c = c.
(10) with M := λw. w + c, A := a, B := b gives (a + c) + ((a + b) + c) = (a + b) + c, that is
(a + c) + c = c; then lemma (ii) and step 丙. -/
theorem refinesTransitiveWithoutUnitLaw {lower middle upper : Term}
    (lowerRefines : DerivableFrom laws (choice lower middle) middle)
    (middleRefines : DerivableFrom laws (choice middle upper) upper) :
    DerivableFrom laws (choice lower upper) upper := by
  have step := monotoneThroughContraction equationTen (betaAddRight upper lower)
    (betaAddRight upper (choice lower middle))
  have chain : DerivableFrom laws (choice (choice lower middle) upper) upper :=
    .transitive (.congruenceChoiceLeft upper lowerRefines) middleRefines
  have sumRefines : DerivableFrom laws (choice (choice lower upper) upper) upper :=
    rewrite step (.congruenceChoiceRight _ chain) chain
  exact antisymmetric equationThree equationFive sumRefines
    (rightRefinesChoiceWithoutUnitLaw equationOne equationThree equationFive equationTen upper lower)

include equationOne equationThree equationFive equationTen in
/-- (2) from (1), (3), (5), (6), (10) and β: section 6's derivation of (2), with L = (x + y) + z
and R = x + (y + z), its lemmas (ii) to (v) taken in the forms above, (iii) being
`choiceRefinesByCommutative` and (v) `antisymmetric`. -/
theorem choiceAssociativeWithoutUnitLaw (first second third : Term) :
    DerivableFrom laws (choice (choice first second) third)
      (choice first (choice second third)) := by
  have commutative : ∀ left right, DerivableFrom laws (choice left right) (choice right left) :=
    fun left right => .law (equationOne left right)
  have leftRefines := leftRefinesChoiceWithoutUnitLaw equationOne equationThree equationFive
    equationTen
  have rightRefines := rightRefinesChoiceWithoutUnitLaw equationOne equationThree equationFive
    equationTen
  have transitive : ∀ {lower middle upper : Term},
      DerivableFrom laws (choice lower middle) middle →
      DerivableFrom laws (choice middle upper) upper →
      DerivableFrom laws (choice lower upper) upper :=
    refinesTransitiveWithoutUnitLaw equationOne equationThree equationFive equationTen
  have firstRefinesRight := leftRefines first (choice second third)
  have secondThirdRefinesRight := rightRefines (choice second third) first
  have secondRefinesRight := transitive (leftRefines second third) secondThirdRefinesRight
  have firstSecondRefinesRight := choiceRefinesByCommutative commutative equationTen
    firstRefinesRight secondRefinesRight
  have thirdRefinesRight := transitive (rightRefines third second) secondThirdRefinesRight
  have leftSideRefinesRight := choiceRefinesByCommutative commutative equationTen
    firstSecondRefinesRight thirdRefinesRight
  have firstSecondRefinesLeft := leftRefines (choice first second) third
  have thirdRefinesLeft := rightRefines third (choice first second)
  have firstRefinesLeft := transitive (leftRefines first second) firstSecondRefinesLeft
  have secondRefinesLeft := transitive (rightRefines second first) firstSecondRefinesLeft
  have secondThirdRefinesLeft := choiceRefinesByCommutative commutative equationTen
    secondRefinesLeft thirdRefinesLeft
  have rightSideRefinesLeft := choiceRefinesByCommutative commutative equationTen
    firstRefinesLeft secondThirdRefinesLeft
  exact antisymmetric equationThree equationFive leftSideRefinesRight rightSideRefinesLeft

include equationOne equationThree equationFive equationTen in
/-- (4) from (1), (3), (5), (6), (10) and β: section 6's derivation of (4), with L = (x ∥ y) ∥ z
and R = x ∥ (y ∥ z), by lemmas (iv), (v), (vi) and (vii) (`refinesParallel`). -/
theorem parallelAssociativeWithoutUnitLaw (first second third : Term) :
    DerivableFrom laws (parallel (parallel first second) third)
      (parallel first (parallel second third)) := by
  have refinesLeft := parallelRefinesLeftWithoutUnitLaw equationOne equationFive equationTen
  have refinesRight := parallelRefinesRightWithoutUnitLaw equationOne equationThree equationFive
    equationTen
  have transitive : ∀ {lower middle upper : Term},
      DerivableFrom laws (choice lower middle) middle →
      DerivableFrom laws (choice middle upper) upper →
      DerivableFrom laws (choice lower upper) upper :=
    refinesTransitiveWithoutUnitLaw equationOne equationThree equationFive equationTen
  have rightRefinesFirst := refinesLeft first (parallel second third)
  have rightRefinesSecondThird := refinesRight first (parallel second third)
  have rightRefinesSecond := transitive rightRefinesSecondThird (refinesLeft second third)
  have rightRefinesThird := transitive rightRefinesSecondThird (refinesRight second third)
  have rightRefinesFirstSecond :=
    refinesParallel equationFive equationTen rightRefinesFirst rightRefinesSecond
  have rightRefinesLeft :=
    refinesParallel equationFive equationTen rightRefinesFirstSecond rightRefinesThird
  have leftRefinesFirstSecond := refinesLeft (parallel first second) third
  have leftRefinesThird := refinesRight (parallel first second) third
  have leftRefinesFirst := transitive leftRefinesFirstSecond (refinesLeft first second)
  have leftRefinesSecond := transitive leftRefinesFirstSecond (refinesRight first second)
  have leftRefinesSecondThird :=
    refinesParallel equationFive equationTen leftRefinesSecond leftRefinesThird
  have leftRefinesRight :=
    refinesParallel equationFive equationTen leftRefinesFirst leftRefinesSecondThird
  exact antisymmetric equationThree equationFive leftRefinesRight rightRefinesLeft

include equationOne equationThree equationFive equationTen in
/-- (8) from (1), (3), (6), (10), β and η: the proofs file's second derivation of (8), section 6,
`choiceFunctionDistributiveOfEquationsOneThreeSixTen`, with (6) derived above. -/
theorem choiceFunctionDistributiveWithoutUnitLaw (left right argument : Term) :
    ChoiceFunctionDistributive laws left right argument :=
  ofDerivableLaws (choiceFunctionDistributiveOfEquationsOneThreeSixTen (laws := DerivableFrom laws)
    (fun first second => .law (equationOne first second))
    (fun first second => .law (equationThree first second))
    (fun kept other => choiceAbsorptionWithoutUnitLaw equationOne equationFive equationTen kept other)
    (fun function point addition => .law (equationTen function point addition))
    left right argument)

include equationOne equationThree equationFive equationTen in
/-- (9) from (1), (3), (5), (6), (8), (10), β and η: section 6's derivation of (9), with
V = λz. X z ∥ Y z, with the lemmas above in the place of the proofs file's steps that use (7). -/
theorem parallelFunctionDistributiveWithoutUnitLaw (left right argument : Term) :
    DerivableFrom laws (application (parallel left right) argument)
      (parallel (application left argument) (application right argument)) := by
  have distributes := choiceFunctionDistributiveWithoutUnitLaw equationOne equationThree
    equationFive equationTen
  have refinesLeft := parallelRefinesLeftWithoutUnitLaw equationOne equationFive equationTen
  have refinesRight := parallelRefinesRightWithoutUnitLaw equationOne equationThree equationFive
    equationTen
  have pointwiseRefinesLeft : DerivableFrom laws
      (choice (pointwiseParallel left right) left) left :=
    extensional
      (.transitive
        (distributes (shift (pointwiseParallel left right)) (shift left) (boundVariable 0))
        (.transitive (.congruenceChoiceLeft _ (betaShiftedAtZero _)) (refinesLeft _ _)))
  have pointwiseRefinesRight : DerivableFrom laws
      (choice (pointwiseParallel left right) right) right :=
    extensional
      (.transitive
        (distributes (shift (pointwiseParallel left right)) (shift right) (boundVariable 0))
        (.transitive (.congruenceChoiceLeft _ (betaShiftedAtZero _)) (refinesRight _ _)))
  have pointwiseRefinesParallel :=
    refinesParallel equationFive equationTen pointwiseRefinesLeft pointwiseRefinesRight
  have appliedParallelRefinesLeft := functionMonotone equationTen (boundVariable 0)
    (refinesLeft (shift left) (shift right))
  have appliedParallelRefinesRight := functionMonotone equationTen (boundVariable 0)
    (refinesRight (shift left) (shift right))
  have parallelRefinesPointwise : DerivableFrom laws
      (choice (parallel left right) (pointwiseParallel left right))
      (pointwiseParallel left right) :=
    extensional
      (.transitive
        (distributes (parallel (shift left) (shift right))
          (shift (pointwiseParallel left right)) (boundVariable 0))
        (.transitive (.congruenceChoiceRight _ (betaShiftedAtZero _))
          (.transitive
            (refinesParallel equationFive equationTen appliedParallelRefinesLeft
              appliedParallelRefinesRight)
            (.symmetric (betaShiftedAtZero _)))))
  have parallelEqualsPointwise := antisymmetric equationThree equationFive
    parallelRefinesPointwise pointwiseRefinesParallel
  exact .transitive (.congruenceFunction argument parallelEqualsPointwise)
    (betaPointwiseParallel left right argument)

end WithoutUnitLaw

end LambdaJit.FourEquations.DerivableFrom

namespace LambdaJit.Semantics

open Term

/-- E ⊢_{λ-lattice-η} M = N, the proofs file's ⊢_B (section 21): the least congruence that contains
the hypotheses E, the β rule, the η rule and the axioms (1), (3), (5) and (10); DdLP96's λ-lattice
laws with the η rule, and no unit law. One
constructor per rule: the four closure rules of a congruence (symmetry, transitivity, the congruence
in the argument of an application and the congruence under λ), the β rule, the η rule and the four
axioms. -/
inductive DerivableLatticeEta (hypotheses : Term → Term → Prop) : Term → Term → Prop where
  /-- E: every hypothesis. -/
  | hypothesis {left right : Term} : hypotheses left right → DerivableLatticeEta hypotheses left right
  /-- Symmetry: N = M from M = N. -/
  | symmetric {left right : Term} :
      DerivableLatticeEta hypotheses left right → DerivableLatticeEta hypotheses right left
  /-- Transitivity: M = P from M = N and N = P. -/
  | transitive {left middle right : Term} :
      DerivableLatticeEta hypotheses left middle → DerivableLatticeEta hypotheses middle right →
        DerivableLatticeEta hypotheses left right
  /-- The congruence in the argument of an application: Z M = Z N from M = N. -/
  | congruenceArgument (function : Term) {left right : Term} :
      DerivableLatticeEta hypotheses left right →
        DerivableLatticeEta hypotheses (application function left) (application function right)
  /-- The congruence in the body of an abstraction, ξ: λx. M = λx. N from M = N. -/
  | congruenceAbstraction {left right : Term} :
      DerivableLatticeEta hypotheses left right →
        DerivableLatticeEta hypotheses (abstraction left) (abstraction right)
  /-- The β rule: (λx. M) N = M[x := N]. -/
  | beta (body argument : Term) :
      DerivableLatticeEta hypotheses (application (abstraction body) argument)
        (instantiate body argument)
  /-- The η rule: λx. M x = M with x ∉ FV(M). -/
  | eta (function : Term) :
      DerivableLatticeEta hypotheses (abstraction (application (shift function) (boundVariable 0)))
        function
  /-- (1), an axiom: M + N = N + M. -/
  | choiceCommutative (left right : Term) :
      DerivableLatticeEta hypotheses (choice left right) (choice right left)
  /-- (3), an axiom: M ∥ N = N ∥ M. -/
  | parallelCommutative (left right : Term) :
      DerivableLatticeEta hypotheses (parallel left right) (parallel right left)
  /-- (5), an axiom: M ∥ (M + N) = M. -/
  | parallelAbsorption (kept other : Term) :
      DerivableLatticeEta hypotheses (parallel kept (choice kept other)) kept
  /-- (10), an axiom: M A + M (A + B) = M (A + B). -/
  | argumentMonotone (function argument addition : Term) :
      DerivableLatticeEta hypotheses
        (choice (application function argument) (application function (choice argument addition)))
        (application function (choice argument addition))

namespace DerivableLatticeEta

variable {hypotheses : Term → Term → Prop}

/-- A derivation whose laws are equations derivable in ⊢_{λ-lattice-η} is a derivation in it. -/
theorem ofDerivableFrom {left right : Term}
    (derivation : FourEquations.DerivableFrom (DerivableLatticeEta hypotheses) left right) :
    DerivableLatticeEta hypotheses left right := by
  induction derivation with
  | law derivable => exact derivable
  | symmetric _ inner => exact .symmetric inner
  | transitive _ _ leftStep rightStep => exact .transitive leftStep rightStep
  | congruenceArgument function _ inner => exact .congruenceArgument function inner
  | congruenceAbstraction _ inner => exact .congruenceAbstraction inner
  | beta body argument => exact .beta body argument
  | eta function => exact .eta function

/-- A derivation from weaker hypotheses is a derivation from stronger ones. -/
theorem weaken {weaker stronger : Term → Term → Prop}
    (included : ∀ left right, weaker left right → stronger left right) {left right : Term}
    (derivation : DerivableLatticeEta weaker left right) :
    DerivableLatticeEta stronger left right := by
  induction derivation with
  | hypothesis isHypothesis => exact .hypothesis (included _ _ isHypothesis)
  | symmetric _ inner => exact .symmetric inner
  | transitive _ _ leftStep rightStep => exact .transitive leftStep rightStep
  | congruenceArgument function _ inner => exact .congruenceArgument function inner
  | congruenceAbstraction _ inner => exact .congruenceAbstraction inner
  | beta body argument => exact .beta body argument
  | eta function => exact .eta function
  | choiceCommutative left right => exact .choiceCommutative left right
  | parallelCommutative left right => exact .parallelCommutative left right
  | parallelAbsorption kept other => exact .parallelAbsorption kept other
  | argumentMonotone function argument addition => exact .argumentMonotone function argument addition

/-! ## Reflexivity and the congruences that are theorems -/

/-- Reflexivity, M = M (`FourEquations.DerivableFrom.reflexive`). -/
theorem reflexive (term : Term) : DerivableLatticeEta hypotheses term term :=
  ofDerivableFrom (FourEquations.DerivableFrom.reflexive term)

/-- The congruence in the function of an application, M Z = N Z from M = N. -/
theorem congruenceFunction {left right : Term} (argument : Term)
    (equal : DerivableLatticeEta hypotheses left right) :
    DerivableLatticeEta hypotheses (application left argument) (application right argument) :=
  ofDerivableFrom (FourEquations.DerivableFrom.congruenceFunction argument (.law equal))

/-- Extensionality, M = N from M x = N x with x ∉ FV(M) ∪ FV(N): the congruence under λ, then the η
rule on each side. -/
theorem extensional {left right : Term}
    (applied : DerivableLatticeEta hypotheses (application (shift left) (boundVariable 0))
      (application (shift right) (boundVariable 0))) :
    DerivableLatticeEta hypotheses left right :=
  .transitive (.symmetric (.eta left)) (.transitive (.congruenceAbstraction applied) (.eta right))

/-- The congruence in the left side of a choice. -/
theorem congruenceChoiceLeft {left right : Term} (other : Term)
    (equal : DerivableLatticeEta hypotheses left right) :
    DerivableLatticeEta hypotheses (choice left other) (choice right other) :=
  ofDerivableFrom (FourEquations.DerivableFrom.congruenceChoiceLeft other (.law equal))

/-- The congruence in the right side of a choice. -/
theorem congruenceChoiceRight (other : Term) {left right : Term}
    (equal : DerivableLatticeEta hypotheses left right) :
    DerivableLatticeEta hypotheses (choice other left) (choice other right) :=
  ofDerivableFrom (FourEquations.DerivableFrom.congruenceChoiceRight other (.law equal))

/-- Both sides of a choice replaced by equal ones. -/
theorem congruenceChoice {leftBefore leftAfter rightBefore rightAfter : Term}
    (leftEqual : DerivableLatticeEta hypotheses leftBefore leftAfter)
    (rightEqual : DerivableLatticeEta hypotheses rightBefore rightAfter) :
    DerivableLatticeEta hypotheses (choice leftBefore rightBefore) (choice leftAfter rightAfter) :=
  ofDerivableFrom (FourEquations.DerivableFrom.choiceBoth (.law leftEqual) (.law rightEqual))

/-- The congruence in the left side of a parallel. -/
theorem congruenceParallelLeft {left right : Term} (other : Term)
    (equal : DerivableLatticeEta hypotheses left right) :
    DerivableLatticeEta hypotheses (parallel left other) (parallel right other) :=
  ofDerivableFrom (FourEquations.DerivableFrom.congruenceParallelLeft other (.law equal))

/-- The congruence in the right side of a parallel. -/
theorem congruenceParallelRight (other : Term) {left right : Term}
    (equal : DerivableLatticeEta hypotheses left right) :
    DerivableLatticeEta hypotheses (parallel other left) (parallel other right) :=
  ofDerivableFrom (FourEquations.DerivableFrom.congruenceParallelRight other (.law equal))

/-! ## The λ-lattice laws that are theorems -/

/-- The axioms of ⊢_{λ-lattice-η} as hypotheses of the derivations of `FourEquations`. -/
theorem equationOne : FourEquations.EquationOne (DerivableLatticeEta hypotheses) :=
  choiceCommutative

theorem equationThree : FourEquations.EquationThree (DerivableLatticeEta hypotheses) :=
  parallelCommutative

theorem equationFive : FourEquations.EquationFive (DerivableLatticeEta hypotheses) :=
  parallelAbsorption

theorem equationTen : FourEquations.EquationTen (DerivableLatticeEta hypotheses) :=
  argumentMonotone

/-- T1: M + M = M, from (10) and β. -/
theorem choiceIdempotent (term : Term) : DerivableLatticeEta hypotheses (choice term term) term :=
  ofDerivableFrom (FourEquations.DerivableFrom.choiceIdempotent equationTen term)

/-- (6): M + (M ∥ N) = M, from (1), (5), (10) and β. -/
theorem choiceAbsorption (kept other : Term) :
    DerivableLatticeEta hypotheses (choice kept (parallel kept other)) kept :=
  ofDerivableFrom (FourEquations.DerivableFrom.choiceAbsorptionWithoutUnitLaw equationOne
    equationFive equationTen kept other)

/-- (2): (M + N) + P = M + (N + P), from (1), (3), (5), (6), (10) and β. -/
theorem choiceAssociative (left middle right : Term) :
    DerivableLatticeEta hypotheses (choice (choice left middle) right)
      (choice left (choice middle right)) :=
  ofDerivableFrom (FourEquations.DerivableFrom.choiceAssociativeWithoutUnitLaw equationOne
    equationThree equationFive equationTen left middle right)

/-- (4): (M ∥ N) ∥ P = M ∥ (N ∥ P), from (1), (3), (5), (6), (10) and β. -/
theorem parallelAssociative (left middle right : Term) :
    DerivableLatticeEta hypotheses (parallel (parallel left middle) right)
      (parallel left (parallel middle right)) :=
  ofDerivableFrom (FourEquations.DerivableFrom.parallelAssociativeWithoutUnitLaw equationOne
    equationThree equationFive equationTen left middle right)

/-- (8): (M + N) P = M P + N P, from (1), (3), (6), (10), β and η, the proofs file's second
derivation of (8). -/
theorem choiceFunctionDistributive (left right argument : Term) :
    DerivableLatticeEta hypotheses (application (choice left right) argument)
      (choice (application left argument) (application right argument)) :=
  ofDerivableFrom (FourEquations.DerivableFrom.choiceFunctionDistributiveWithoutUnitLaw equationOne
    equationThree equationFive equationTen left right argument)

/-- (9): (M ∥ N) P = M P ∥ N P, from (1), (3), (5), (6), (8), (10), β and η. -/
theorem parallelFunctionDistributive (left right argument : Term) :
    DerivableLatticeEta hypotheses (application (parallel left right) argument)
      (parallel (application left argument) (application right argument)) :=
  ofDerivableFrom (FourEquations.DerivableFrom.parallelFunctionDistributiveWithoutUnitLaw
    equationOne equationThree equationFive equationTen left right argument)

/-- T2: M ∥ M = M, by (6) and (5). -/
theorem parallelIdempotent (term : Term) :
    DerivableLatticeEta hypotheses (parallel term term) term :=
  .transitive (.congruenceParallelRight term (.symmetric (choiceAbsorption term term)))
    (.parallelAbsorption term (parallel term term))

/-- T9, from left to right: N ∥ A = N from N + A = A, by (5). -/
theorem parallelOfRefines {lower upper : Term}
    (refines : DerivableLatticeEta hypotheses (choice lower upper) upper) :
    DerivableLatticeEta hypotheses (parallel lower upper) lower :=
  .transitive (.congruenceParallelRight lower (.symmetric refines)) (.parallelAbsorption lower upper)

/-- T9, from right to left: N + A = A from N ∥ A = N, by (1), (3) and (6). -/
theorem refinesOfParallel {lower upper : Term}
    (refines : DerivableLatticeEta hypotheses (parallel lower upper) lower) :
    DerivableLatticeEta hypotheses (choice lower upper) upper :=
  ofDerivableFrom (FourEquations.DerivableFrom.refinesOfParallelWithoutUnitLaw equationOne
    equationThree equationFive equationTen (.law refines))

/-- A parallel refines its left side, (M ∥ N) + M = M, by (1) and (6). -/
theorem parallelRefinesLeft (left right : Term) :
    DerivableLatticeEta hypotheses (choice (parallel left right) left) left :=
  ofDerivableFrom (FourEquations.DerivableFrom.parallelRefinesLeftWithoutUnitLaw equationOne
    equationFive equationTen left right)

/-- A parallel refines its right side, (M ∥ N) + N = N, by (1), (3) and (6). -/
theorem parallelRefinesRight (left right : Term) :
    DerivableLatticeEta hypotheses (choice (parallel left right) right) right :=
  ofDerivableFrom (FourEquations.DerivableFrom.parallelRefinesRightWithoutUnitLaw equationOne
    equationThree equationFive equationTen left right)

/-- Section 6's lemma (iv): from a + b = b and b + c = c, a + c = c. -/
theorem refinesTransitive {lower middle upper : Term}
    (lowerRefines : DerivableLatticeEta hypotheses (choice lower middle) middle)
    (middleRefines : DerivableLatticeEta hypotheses (choice middle upper) upper) :
    DerivableLatticeEta hypotheses (choice lower upper) upper :=
  ofDerivableFrom (FourEquations.DerivableFrom.refinesTransitiveWithoutUnitLaw equationOne
    equationThree equationFive equationTen (.law lowerRefines) (.law middleRefines))

/-- Section 6's step 丙: from a + b = b and b + a = a, a = b, by (3) and (5). -/
theorem antisymmetric {first second : Term}
    (firstRefines : DerivableLatticeEta hypotheses (choice first second) second)
    (secondRefines : DerivableLatticeEta hypotheses (choice second first) first) :
    DerivableLatticeEta hypotheses first second :=
  ofDerivableFrom (FourEquations.DerivableFrom.antisymmetric equationThree equationFive
    (.law firstRefines) (.law secondRefines))

/-- T7: λx. (M + N) = λx. M + λx. N, by β, (8) and η. -/
theorem abstractionChoice (left right : Term) :
    DerivableLatticeEta hypotheses (abstraction (choice left right))
      (choice (abstraction left) (abstraction right)) := by
  have expandedLeft : DerivableLatticeEta hypotheses left
      (application (abstraction (shiftFrom 1 left)) (boundVariable 0)) :=
    .symmetric (ofDerivableFrom (FourEquations.DerivableFrom.betaShiftedAtZero left))
  have expandedRight : DerivableLatticeEta hypotheses right
      (application (abstraction (shiftFrom 1 right)) (boundVariable 0)) :=
    .symmetric (ofDerivableFrom (FourEquations.DerivableFrom.betaShiftedAtZero right))
  have distributed : DerivableLatticeEta hypotheses (choice left right)
      (application (shift (choice (abstraction left) (abstraction right))) (boundVariable 0)) :=
    .transitive (congruenceChoice expandedLeft expandedRight)
      (.symmetric (choiceFunctionDistributive _ _ _))
  exact .transitive (.congruenceAbstraction distributed) (.eta _)

/-- T8: λx. (M ∥ N) = λx. M ∥ λx. N, as T7 with (9) for (8). -/
theorem abstractionParallel (left right : Term) :
    DerivableLatticeEta hypotheses (abstraction (parallel left right))
      (parallel (abstraction left) (abstraction right)) := by
  have expandedLeft : DerivableLatticeEta hypotheses left
      (application (abstraction (shiftFrom 1 left)) (boundVariable 0)) :=
    .symmetric (ofDerivableFrom (FourEquations.DerivableFrom.betaShiftedAtZero left))
  have expandedRight : DerivableLatticeEta hypotheses right
      (application (abstraction (shiftFrom 1 right)) (boundVariable 0)) :=
    .symmetric (ofDerivableFrom (FourEquations.DerivableFrom.betaShiftedAtZero right))
  have distributed : DerivableLatticeEta hypotheses (parallel left right)
      (application (shift (parallel (abstraction left) (abstraction right))) (boundVariable 0)) :=
    .transitive (.transitive (congruenceParallelLeft _ expandedLeft)
        (congruenceParallelRight _ expandedRight))
      (.symmetric (parallelFunctionDistributive _ _ _))
  exact .transitive (.congruenceAbstraction distributed) (.eta _)

/-- The congruence under a context: C[M] = C[N] from M = N. -/
theorem congruenceFill {left right : Term} (equal : DerivableLatticeEta hypotheses left right) :
    ∀ context : Context, DerivableLatticeEta hypotheses (context.fill left) (context.fill right)
  | .hole => equal
  | .abstraction body => .congruenceAbstraction (congruenceFill equal body)
  | .applicationFunction function argument =>
      congruenceFunction argument (congruenceFill equal function)
  | .applicationArgument function argument =>
      .congruenceArgument function (congruenceFill equal argument)
  | .choiceLeft left right => congruenceChoiceLeft right (congruenceFill equal left)
  | .choiceRight left right => congruenceChoiceRight left (congruenceFill equal right)
  | .parallelLeft left right => congruenceParallelLeft right (congruenceFill equal left)
  | .parallelRight left right => congruenceParallelRight left (congruenceFill equal right)

/-- Weakening by derivations: when every hypothesis of `weaker` is derivable from `stronger`, so is
every equation derivable from `weaker`. -/
theorem weakenByDerivations {weaker stronger : Term → Term → Prop}
    (included : ∀ left right, weaker left right → DerivableLatticeEta stronger left right)
    {left right : Term} (derivation : DerivableLatticeEta weaker left right) :
    DerivableLatticeEta stronger left right := by
  induction derivation with
  | hypothesis isHypothesis => exact included _ _ isHypothesis
  | symmetric _ inner => exact .symmetric inner
  | transitive _ _ leftStep rightStep => exact .transitive leftStep rightStep
  | congruenceArgument function _ inner => exact .congruenceArgument function inner
  | congruenceAbstraction _ inner => exact .congruenceAbstraction inner
  | beta body argument => exact .beta body argument
  | eta function => exact .eta function
  | choiceCommutative left right => exact .choiceCommutative left right
  | parallelCommutative left right => exact .parallelCommutative left right
  | parallelAbsorption kept other => exact .parallelAbsorption kept other
  | argumentMonotone function argument addition => exact .argumentMonotone function argument addition

/-- The choice case of T10 with the hole on the left: (X + P) + (Y + P) = Y + P from X + Y = Y, by
(1), (2) and T1. -/
theorem choiceLeftMonotone {smaller larger : Term} (other : Term)
    (refines : DerivableLatticeEta hypotheses (choice smaller larger) larger) :
    DerivableLatticeEta hypotheses (choice (choice smaller other) (choice larger other))
      (choice larger other) :=
  .transitive (choiceAssociative smaller other (choice larger other))
    (.transitive (congruenceChoiceRight smaller (.choiceCommutative other (choice larger other)))
      (.transitive (congruenceChoiceRight smaller (choiceAssociative larger other other))
        (.transitive
          (congruenceChoiceRight smaller (congruenceChoiceRight larger (choiceIdempotent other)))
          (.transitive (.symmetric (choiceAssociative smaller larger other))
            (congruenceChoiceLeft other refines)))))

/-- The choice case of T10 with the hole on the right: (P + X) + (P + Y) = P + Y from X + Y = Y, by
(1) and the case on the left. -/
theorem choiceRightMonotone {smaller larger : Term} (other : Term)
    (refines : DerivableLatticeEta hypotheses (choice smaller larger) larger) :
    DerivableLatticeEta hypotheses (choice (choice other smaller) (choice other larger))
      (choice other larger) :=
  .transitive
    (congruenceChoice (.choiceCommutative other smaller) (.choiceCommutative other larger))
    (.transitive (choiceLeftMonotone other refines) (.choiceCommutative larger other))

/-- The parallel case of T10 with the hole on the left: (X ∥ P) + (Y ∥ P) = Y ∥ P from X + Y = Y.
By T9, X ∥ Y = X; then (X ∥ P) ∥ (Y ∥ P) = X ∥ P by (3), (4) and T2; and T9 again. -/
theorem parallelLeftMonotone {smaller larger : Term} (other : Term)
    (refines : DerivableLatticeEta hypotheses (choice smaller larger) larger) :
    DerivableLatticeEta hypotheses (choice (parallel smaller other) (parallel larger other))
      (parallel larger other) := by
  have parallelRefines : DerivableLatticeEta hypotheses (parallel smaller larger) smaller :=
    parallelOfRefines refines
  have parallelsRefines : DerivableLatticeEta hypotheses
      (parallel (parallel smaller other) (parallel larger other)) (parallel smaller other) :=
    .transitive (parallelAssociative smaller other (parallel larger other))
      (.transitive (congruenceParallelRight smaller (.parallelCommutative other (parallel larger other)))
        (.transitive (congruenceParallelRight smaller (parallelAssociative larger other other))
          (.transitive
            (congruenceParallelRight smaller (congruenceParallelRight larger (parallelIdempotent other)))
            (.transitive (.symmetric (parallelAssociative smaller larger other))
              (congruenceParallelLeft other parallelRefines)))))
  exact refinesOfParallel parallelsRefines

/-- The parallel case of T10 with the hole on the right: (P ∥ X) + (P ∥ Y) = P ∥ Y from X + Y = Y,
by (3) and the case on the left. -/
theorem parallelRightMonotone {smaller larger : Term} (other : Term)
    (refines : DerivableLatticeEta hypotheses (choice smaller larger) larger) :
    DerivableLatticeEta hypotheses (choice (parallel other smaller) (parallel other larger))
      (parallel other larger) :=
  .transitive
    (congruenceChoice (.parallelCommutative other smaller) (.parallelCommutative other larger))
    (.transitive (parallelLeftMonotone other refines) (.parallelCommutative larger other))

/-- T10, context monotonicity: if A + B = B, then C[A] + C[B] = C[B] for every context C, by
induction on C: the function position by (8), the argument position
by (10), the abstraction by T7, and choices and parallels by the four cases above. -/
theorem contextMonotone {smaller larger : Term}
    (refines : DerivableLatticeEta hypotheses (choice smaller larger) larger) :
    ∀ context : Context,
      DerivableLatticeEta hypotheses (choice (context.fill smaller) (context.fill larger))
        (context.fill larger)
  | .hole => refines
  | .abstraction body =>
      .transitive (.symmetric (abstractionChoice _ _))
        (.congruenceAbstraction (contextMonotone refines body))
  | .applicationFunction function argument =>
      .transitive (.symmetric (choiceFunctionDistributive _ _ argument))
        (congruenceFunction argument (contextMonotone refines function))
  | .applicationArgument function argument =>
      .transitive
        (congruenceChoiceRight _
          (.congruenceArgument function (.symmetric (contextMonotone refines argument))))
        (.transitive (.argumentMonotone function _ _)
          (.congruenceArgument function (contextMonotone refines argument)))
  | .choiceLeft left right => choiceLeftMonotone right (contextMonotone refines left)
  | .choiceRight left right => choiceRightMonotone left (contextMonotone refines right)
  | .parallelLeft left right => parallelLeftMonotone right (contextMonotone refines left)
  | .parallelRight left right => parallelRightMonotone left (contextMonotone refines right)

end DerivableLatticeEta

/-! ## Consistency, ◇ and NF◇ in ⊢_{λ-lattice-η} -/

/-- A set of equations E is consistent in ⊢_{λ-lattice-η} when E ⊬_{λ-lattice-η} K = K*. -/
def ConsistentLatticeEta (hypotheses : Term → Term → Prop) : Prop :=
  ¬ DerivableLatticeEta hypotheses first second

/-- Weakening read on consistency in ⊢_{λ-lattice-η}: when every hypothesis of `weaker` is derivable
from `stronger`, the consistency of `stronger` gives that of `weaker`. -/
theorem ConsistentLatticeEta.weaken {weaker stronger : Term → Term → Prop}
    (included : ∀ left right, weaker left right → DerivableLatticeEta stronger left right)
    (consistent : ConsistentLatticeEta stronger) : ConsistentLatticeEta weaker :=
  fun derivation => consistent (DerivableLatticeEta.weakenByDerivations included derivation)

/-- ◇_{λ-lattice-η}(left = right): the equation is consistent in ⊢_{λ-lattice-η}. -/
def ConsistentEquationLatticeEta (left right : Term) : Prop :=
  ConsistentLatticeEta (listed [(left, right)])

/-- N ∈ NF◇_{λ-lattice-η}(T): `candidate` is a closed βη normal form and
◇_{λ-lattice-η}(candidate + term = term). -/
def ConsistentNormalFormLatticeEta (term candidate : Term) : Prop :=
  NormalForm candidate ∧ ConsistentEquationLatticeEta (choice candidate term) term

end LambdaJit.Semantics
