import LambdaJit.ParallelTypesTheorems
import LambdaJit.LatticeEtaBridge

/-!
# The filters of non-member binary numerals are incompatible

the binary naturals record, sections 8.1 to 8.4: for every binary numeral n and
boolean p with member(n, p) false, the one equation ñ + `binary_set p` = `binary_set p` derives
λx.λy. x = λx.λy. y by ⊢_{λ-lattice-η}, the relation `DerivableLatticeEta` of module
`LatticeEtaDerivability`, which has no unit law (`nonMemberIncompatible`, by induction on the
numeral, over every numeral (`Numeral`) and both booleans). So `binary_set p` ⊑_O ñ is false, by
Definition 14 (`nonMemberNotContextualPreorder`): ñ ∉ NF◇(`binary_set p`). The step from the
derivation to Definition 14 is `ContextualPreorder.consistentEquationLatticeEtaOfContextualPreorder`.

What is trusted is how each library function is written as a term: the definitions below, each
with its file's text quoted, as module `ParallelTypesTheorems` writes its terms. The library's
`binary` directory takes `fixpoint`, `true` and `false` from `native_types`, whose files put the
markers `generic` and `constructor` around a term; the markers are written out as their own file's
terms, and the theorem's hypothesis is about `binary_set p` as the library has it, markers included.
The markers are identities by the β rule alone (`constructorApply`, `nativeFixpointIsFixpoint`),
and `binarySetUnfold` unfolds them so. Where `binary_set` has no answer it writes `top`, the library's
file `top`, which is `ContextualPreorder.top`. The file writes a chain `T3 + T2 + T1`, which the
front end reads as the right-nested binary choice `T1 + (T2 + T3)`, as the IR's choice is.

The proofs apply both sides of an equation to three closed terms (`applyCases`), which gives the
paper's equations by the β rule and needs no substitution lemma for derivations. Without the unit
law no member vanishes from a choice, so the three terms are chosen for each step to make every
member the step does not want refine a member it keeps, and the choice then equals what it keeps
(`DerivableLatticeEta.antisymmetric`): (K, λ_. K*, λ_. K*) and (K*, λ_. K, λ_. K) for lemma 8.3,
(`top`, I, `binary_odd`) for the case of `binary_even`, (Z, λ_. Z, I) for the case of `binary_odd`. `top`
applied to arguments is a parallel that `top` and each argument refine (`applyCasesTop`), which is what
the false side's zero case contributes.
-/

namespace LambdaJit.BinaryNaturalsNonMember

open LambdaJit.Semantics
open LambdaJit.Semantics.Term
open LambdaJit.ParallelTypesTheorems
open LambdaJit.ContextualPreorder (functionalOfTop selfApplicationFixedPoint)

/-! ## The library's terms -/

/-- The library function `binary_zero`. Its field, the field 0 of
`gezi/corpora/library/binary/natural.lambdalattice`, reads:

    λz. λ_. λ_. z
-/
def binaryZero : Term := abstraction (abstraction (abstraction (boundVariable 2)))

/-- The library function `binary_even`. Its field, the field 1 of
`gezi/corpora/library/binary/natural.lambdalattice`, reads:

    λh. λ_. λe. λ_. e h
-/
def binaryEven : Term :=
  abstraction (abstraction (abstraction (abstraction
    (application (boundVariable 1) (boundVariable 3)))))

/-- The library function `binary_odd`. Its field, the field 2 of
`gezi/corpora/library/binary/natural.lambdalattice`, reads:

    λh. λ_. λ_. λo. o h
-/
def binaryOdd : Term :=
  abstraction (abstraction (abstraction (abstraction
    (application (boundVariable 0) (boundVariable 3)))))

/-- The library function `generic` of `native_types`. Its field, the field 0 of
`gezi/corpora/library/native_types/markers.lambdalattice`, reads:

    λx. (λy. λz. z) x x
-/
def generic : Term :=
  abstraction
    (application (application (abstraction (abstraction (boundVariable 0))) (boundVariable 0))
      (boundVariable 0))

/-- The library function `constructor` of `native_types`. Its field, the field 1 of
`gezi/corpora/library/native_types/markers.lambdalattice`, reads:

    λx. (λy. λz. y) x x
-/
def constructor : Term :=
  abstraction
    (application (application (abstraction (abstraction (boundVariable 1))) (boundVariable 0))
      (boundVariable 0))

/-- The library function `fixpoint` of `native_types`, with `generic` replaced by its term. Its
field, the field 0 of `gezi/corpora/library/native_types/fixpoint.lambdalattice`, reads:

    generic ((λx. λf. f (x x f)) λx. λf. f (x x f))

The argument of `generic` is module `ParallelTypesTheorems`' `fixpoint`, Turing's fixed point
combinator. -/
def nativeFixpoint : Term := application generic fixpoint

/-- The library function `true` of `native_types`. Its field, the field 0 of
`gezi/corpora/library/native_types/boolean.lambdalattice`, reads:

    constructor λt. λf. t
-/
def nativeTrue : Term := application constructor (abstraction (abstraction (boundVariable 1)))

/-- The library function `false` of `native_types`. Its field, the field 1 of
`gezi/corpora/library/native_types/boolean.lambdalattice`, reads:

    constructor λt. λf. f
-/
def nativeFalse : Term := application constructor (abstraction (abstraction (boundVariable 0)))

/-- `top`, the library's file `gezi/corpora/library/top.lambdalattice`, whose field reads

    (λf. (λx. f (x x)) λx. f (x x)) λz. λx. (z ∥ x)

that is `ContextualPreorder.top`, Y applied to λz. λx. z ∥ x. -/
abbrev top : Term := ContextualPreorder.top

/-- The function `binary_set` takes the fixed point of: the body of its field below `fixpoint`,
with `false` and `true` replaced by their terms; the three shapes the field writes are the terms of
`binaryZero`, `binaryEven` and `binaryOdd`. -/
def binarySetStep : Term :=
  abstraction (abstraction
    (choice (application (application (boundVariable 0) binaryZero) top)
      (choice (application binaryEven (application (boundVariable 1) nativeFalse))
        (application binaryOdd (application (boundVariable 1) nativeTrue)))))

/-- The library function `binary_set`, with `fixpoint` replaced by its term. Its field, the
field 4 of `gezi/corpora/library/binary/natural.lambdalattice`, reads:

    fixpoint λself. λp. (p (λz. λe. λo. z) top + (λh. λz. λe. λo. e h) (self false) + (λh. λz. λe. λo. o h) (self true))
-/
def binarySet : Term := application nativeFixpoint binarySetStep

/-- The boolean term for a Lean boolean: `nativeTrue` or `nativeFalse`. -/
def booleanTerm : Bool → Term
  | true => nativeTrue
  | false => nativeFalse

/-- `binary_set p`, the paper's S_p: S_t at true, S_f at false. -/
def binarySetAt (parameter : Bool) : Term := application binarySet (booleanTerm parameter)

/-! ## The numerals -/

/-- A binary numeral as written with the three constructors, canonical or not. -/
inductive Numeral where
  /-- `binary_zero`. -/
  | zero
  /-- `binary_even half`, 2 · half. -/
  | even (half : Numeral)
  /-- `binary_odd half`, 2 · half + 1. -/
  | odd (half : Numeral)

/-- λz.λe.λo. e h, the contractum of `binary_even h` by the β rule. -/
def evenNormal (half : Term) : Term :=
  abstraction (abstraction (abstraction
    (application (boundVariable 1) (shift (shift (shift half))))))

/-- λz.λe.λo. o h, the contractum of `binary_odd h` by the β rule. -/
def oddNormal (half : Term) : Term :=
  abstraction (abstraction (abstraction
    (application (boundVariable 0) (shift (shift (shift half))))))

/-- The paper's ñ: the numeral's βη normal form, built from `binaryZero`, `evenNormal` and
`oddNormal` (the shifts leave the closed numeral under them unchanged). -/
def Numeral.term : Numeral → Term
  | .zero => binaryZero
  | .even half => evenNormal half.term
  | .odd half => oddNormal half.term

/-- The shifts vanish on a closed numeral: the term of `binary_even binary_zero` is
λz.λe.λo. e (λz.λe.λo. z), checked by evaluation. -/
theorem evenZeroTerm :
    (Numeral.even .zero).term =
      abstraction (abstraction (abstraction (application (boundVariable 1) binaryZero))) :=
  rfl

/-- member(n, p) of the paper's section 8.1: member(zero, p) = p,
member(even h, p) = member(h, false), member(odd h, p) = member(h, true). -/
def Numeral.member : Numeral → Bool → Bool
  | .zero, parameter => parameter
  | .even half, _ => half.member false
  | .odd half, _ => half.member true

/-! ## Equations by the β rule and the λ-lattice laws -/

section Equations

variable {hypotheses : Term → Term → Prop}

/-- A term applied to three arguments, the case arguments of a binary numeral. -/
def applyCases (function zeroCase evenCase oddCase : Term) : Term :=
  application (application (application function zeroCase) evenCase) oddCase

theorem applyCasesCongruence {left right : Term} (zeroCase evenCase oddCase : Term)
    (equal : DerivableLatticeEta hypotheses left right) :
    DerivableLatticeEta hypotheses (applyCases left zeroCase evenCase oddCase)
      (applyCases right zeroCase evenCase oddCase) :=
  .congruenceFunction oddCase (.congruenceFunction evenCase (.congruenceFunction zeroCase equal))

/-- (8) three times: (M + N) a b c = M a b c + N a b c. -/
theorem applyCasesChoice (left right zeroCase evenCase oddCase : Term) :
    DerivableLatticeEta hypotheses (applyCases (choice left right) zeroCase evenCase oddCase)
      (choice (applyCases left zeroCase evenCase oddCase)
        (applyCases right zeroCase evenCase oddCase)) := by
  have once : DerivableLatticeEta hypotheses (application (choice left right) zeroCase)
      (choice (application left zeroCase) (application right zeroCase)) :=
    DerivableLatticeEta.choiceFunctionDistributive _ _ _
  have twice : DerivableLatticeEta hypotheses
      (application (application (choice left right) zeroCase) evenCase)
      (choice (application (application left zeroCase) evenCase)
        (application (application right zeroCase) evenCase)) :=
    .transitive (.congruenceFunction evenCase once)
      (DerivableLatticeEta.choiceFunctionDistributive _ _ _)
  exact .transitive (.congruenceFunction oddCase twice)
    (DerivableLatticeEta.choiceFunctionDistributive _ _ _)

/-- `top` = (λx. F (x x)) (λx. F (x x)) for F = λz. λx. z ∥ x, one β step at the head of Y F. -/
theorem topSelfApplication :
    DerivableLatticeEta hypotheses top (selfApplicationFixedPoint functionalOfTop) :=
  betaTo rfl

/-- `top` P = `top` ∥ P: `top` is (λx. F (x x)) (λx. F (x x)), which is F ((λx. F (x x)) (λx. F (x x))) and
λx. (λx. F (x x)) (λx. F (x x)) ∥ x by the β rule, and that applied to P is `top` ∥ P. -/
theorem topApply (argument : Term) :
    DerivableLatticeEta hypotheses (application top argument) (parallel top argument) := by
  have unfolded : DerivableLatticeEta hypotheses (selfApplicationFixedPoint functionalOfTop)
      (abstraction
        (parallel (shift (selfApplicationFixedPoint functionalOfTop)) (boundVariable 0))) :=
    .transitive (betaTo rfl) (betaTo rfl)
  have applied : DerivableLatticeEta hypotheses
      (application (abstraction
        (parallel (shift (selfApplicationFixedPoint functionalOfTop)) (boundVariable 0))) argument)
      (parallel (selfApplicationFixedPoint functionalOfTop) argument) := by
    apply betaTo
    show parallel (substitute 0 argument (shift (selfApplicationFixedPoint functionalOfTop)))
      (substitute 0 argument (boundVariable 0)) = _
    rw [substituteShift]
    rfl
  exact .transitive (.congruenceFunction argument (.transitive topSelfApplication unfolded))
    (.transitive applied
      (DerivableLatticeEta.congruenceParallelLeft argument (.symmetric topSelfApplication)))

/-- `top` a b c = ((`top` ∥ c) ∥ b c) ∥ a b c: `topApply` three times, with (9) distributing each argument
over the parallel. -/
theorem applyCasesTop (zeroCase evenCase oddCase : Term) :
    DerivableLatticeEta hypotheses (applyCases top zeroCase evenCase oddCase)
      (parallel (parallel (parallel top oddCase) (application evenCase oddCase))
        (application (application zeroCase evenCase) oddCase)) := by
  have twice : DerivableLatticeEta hypotheses (application (application top zeroCase) evenCase)
      (parallel (parallel top evenCase) (application zeroCase evenCase)) :=
    .transitive (.congruenceFunction evenCase (topApply zeroCase))
      (.transitive (DerivableLatticeEta.parallelFunctionDistributive _ _ _)
        (DerivableLatticeEta.congruenceParallelLeft _ (topApply evenCase)))
  exact .transitive (.congruenceFunction oddCase twice)
    (.transitive (DerivableLatticeEta.parallelFunctionDistributive _ _ _)
      (DerivableLatticeEta.congruenceParallelLeft _
        (.transitive (DerivableLatticeEta.parallelFunctionDistributive _ _ _)
          (DerivableLatticeEta.congruenceParallelLeft _ (topApply oddCase)))))

/-- Z a b c = a. -/
theorem zeroCases (zeroCase evenCase oddCase : Term) :
    DerivableLatticeEta hypotheses (applyCases binaryZero zeroCase evenCase oddCase) zeroCase := by
  have first : DerivableLatticeEta hypotheses (application binaryZero zeroCase)
      (abstraction (abstraction (shift (shift zeroCase)))) :=
    betaTo rfl
  have second : DerivableLatticeEta hypotheses
      (application (abstraction (abstraction (shift (shift zeroCase)))) evenCase)
      (abstraction (shift zeroCase)) := by
    apply betaTo
    show abstraction (substitute 1 (shift evenCase) (shift (shift zeroCase))) = _
    rw [substituteOneShiftTwice]
  have third : DerivableLatticeEta hypotheses (application (abstraction (shift zeroCase)) oddCase)
      zeroCase :=
    betaTo (substituteShift zeroCase oddCase)
  exact .transitive (.congruenceFunction oddCase (.congruenceFunction evenCase first))
    (.transitive (.congruenceFunction oddCase second) third)

/-- (λz.λe.λo. e h) a b c = b h. -/
theorem evenCases (half zeroCase evenCase oddCase : Term) :
    DerivableLatticeEta hypotheses (applyCases (evenNormal half) zeroCase evenCase oddCase)
      (application evenCase half) := by
  have first : DerivableLatticeEta hypotheses (application (evenNormal half) zeroCase)
      (abstraction (abstraction
        (application (boundVariable 1) (shift (shift half))))) := by
    apply betaTo
    show abstraction (abstraction (application (boundVariable 1)
      (substitute 2 (shift (shift zeroCase)) (shift (shift (shift half)))))) = _
    rw [substituteTwoShiftThrice]
  have second : DerivableLatticeEta hypotheses
      (application (abstraction (abstraction
        (application (boundVariable 1) (shift (shift half))))) evenCase)
      (abstraction (application (shift evenCase) (shift half))) := by
    apply betaTo
    show abstraction (application (shift evenCase)
      (substitute 1 (shift evenCase) (shift (shift half)))) = _
    rw [substituteOneShiftTwice]
  have third : DerivableLatticeEta hypotheses
      (application (abstraction (application (shift evenCase) (shift half))) oddCase)
      (application evenCase half) := by
    apply betaTo
    show application (substitute 0 oddCase (shift evenCase))
      (substitute 0 oddCase (shift half)) = _
    rw [substituteShift, substituteShift]
  exact .transitive (.congruenceFunction oddCase (.congruenceFunction evenCase first))
    (.transitive (.congruenceFunction oddCase second) third)

/-- (λz.λe.λo. o h) a b c = c h. -/
theorem oddCases (half zeroCase evenCase oddCase : Term) :
    DerivableLatticeEta hypotheses (applyCases (oddNormal half) zeroCase evenCase oddCase)
      (application oddCase half) := by
  have first : DerivableLatticeEta hypotheses (application (oddNormal half) zeroCase)
      (abstraction (abstraction
        (application (boundVariable 0) (shift (shift half))))) := by
    apply betaTo
    show abstraction (abstraction (application (boundVariable 0)
      (substitute 2 (shift (shift zeroCase)) (shift (shift (shift half)))))) = _
    rw [substituteTwoShiftThrice]
  have second : DerivableLatticeEta hypotheses
      (application (abstraction (abstraction
        (application (boundVariable 0) (shift (shift half))))) evenCase)
      (abstraction (application (boundVariable 0) (shift half))) := by
    apply betaTo
    show abstraction (application (boundVariable 0)
      (substitute 1 (shift evenCase) (shift (shift half)))) = _
    rw [substituteOneShiftTwice]
  have third : DerivableLatticeEta hypotheses
      (application (abstraction (application (boundVariable 0) (shift half))) oddCase)
      (application oddCase half) := by
    apply betaTo
    show application oddCase (substitute 0 oddCase (shift half)) = _
    rw [substituteShift]
  exact .transitive (.congruenceFunction oddCase (.congruenceFunction evenCase first))
    (.transitive (.congruenceFunction oddCase second) third)

/-- `binary_even h` = λz.λe.λo. e h, the β rule. -/
theorem evenApply (half : Term) :
    DerivableLatticeEta hypotheses (application binaryEven half) (evenNormal half) :=
  betaTo rfl

/-- `binary_odd h` = λz.λe.λo. o h, the β rule. -/
theorem oddApply (half : Term) :
    DerivableLatticeEta hypotheses (application binaryOdd half) (oddNormal half) :=
  betaTo rfl

/-- `constructor M` = (λy.λz. y) M M = M, by the β rule alone. -/
theorem constructorApply (term : Term) :
    DerivableLatticeEta hypotheses (application constructor term) term :=
  .transitive
    (betaTo (result := application (application zero term) term) rfl)
    (zeroApply term term)

/-- `true x y` = x. -/
theorem trueApply (chosen other : Term) :
    DerivableLatticeEta hypotheses (application (application nativeTrue chosen) other) chosen :=
  .transitive (.congruenceFunction other (.congruenceFunction chosen (constructorApply _)))
    (zeroApply chosen other)

/-- `false x y` = y. -/
theorem falseApply (other chosen : Term) :
    DerivableLatticeEta hypotheses (application (application nativeFalse other) chosen) chosen :=
  .transitive (.congruenceFunction chosen (.congruenceFunction other (constructorApply _)))
    (.transitive (.congruenceFunction chosen (betaTo rfl)) (betaTo rfl))

/-- `p x top`: x at true, `top` at false. -/
def picked : Bool → Term → Term
  | true, term => term
  | false, _ => top

theorem booleanSelect (parameter : Bool) (term : Term) :
    DerivableLatticeEta hypotheses (application (application (booleanTerm parameter) term) top)
      (picked parameter term) := by
  cases parameter
  · exact falseApply term top
  · exact trueApply term top

/-- The `fixpoint` of `native_types` is Turing's: `generic M` = (λy.λz. z) M M = M, the β rule
alone. -/
theorem nativeFixpointIsFixpoint : DerivableLatticeEta hypotheses nativeFixpoint fixpoint :=
  .transitive
    (betaTo
      (result := application (application (abstraction (abstraction (boundVariable 0))) fixpoint)
        fixpoint) rfl)
    (.transitive (.congruenceFunction fixpoint (betaTo rfl)) (betaTo rfl))

/-- `binary_set p` = `fixpoint binarySetStep p`. -/
theorem binarySetAtRecursion (parameter : Bool) :
    DerivableLatticeEta hypotheses (binarySetAt parameter)
      (application (application fixpoint binarySetStep) (booleanTerm parameter)) :=
  .congruenceFunction _ (.congruenceFunction _ nativeFixpointIsFixpoint)

/-- One unfolding of the step: two contractions of the β rule. -/
theorem binarySetStepApply (recursion boolean : Term) :
    DerivableLatticeEta hypotheses (application (application binarySetStep recursion) boolean)
      (choice (application (application boolean binaryZero) top)
        (choice (application binaryEven (application recursion nativeFalse))
          (application binaryOdd (application recursion nativeTrue)))) := by
  have first : DerivableLatticeEta hypotheses (application binarySetStep recursion)
      (abstraction
        (choice (application (application (boundVariable 0) binaryZero) top)
          (choice (application binaryEven (application (shift recursion) nativeFalse))
            (application binaryOdd (application (shift recursion) nativeTrue))))) :=
    betaTo rfl
  have second : DerivableLatticeEta hypotheses
      (application (abstraction
        (choice (application (application (boundVariable 0) binaryZero) top)
          (choice (application binaryEven (application (shift recursion) nativeFalse))
            (application binaryOdd (application (shift recursion) nativeTrue))))) boolean)
      (choice (application (application boolean binaryZero) top)
        (choice (application binaryEven (application recursion nativeFalse))
          (application binaryOdd (application recursion nativeTrue)))) := by
    apply betaTo
    show choice (application (application boolean binaryZero) top)
        (choice (application binaryEven (application (substitute 0 boolean (shift recursion))
          nativeFalse))
          (application binaryOdd (application (substitute 0 boolean (shift recursion))
            nativeTrue))) = _
    rw [substituteShift]
  exact .transitive (.congruenceFunction boolean first) second

/-- Section 8.1's U_t and U_f: S_p = p Z `top` + E S_f + O S_t, with p Z `top` read off the boolean. -/
theorem binarySetUnfold (parameter : Bool) :
    DerivableLatticeEta hypotheses (binarySetAt parameter)
      (choice (picked parameter binaryZero)
        (choice (evenNormal (binarySetAt false)) (oddNormal (binarySetAt true)))) := by
  have unfolded : DerivableLatticeEta hypotheses (binarySetAt parameter)
      (application (application binarySetStep (application fixpoint binarySetStep))
        (booleanTerm parameter)) :=
    .transitive (binarySetAtRecursion parameter)
      (.congruenceFunction _ (fixpointUnfold binarySetStep))
  have even : DerivableLatticeEta hypotheses
      (application binaryEven (application (application fixpoint binarySetStep) nativeFalse))
      (evenNormal (binarySetAt false)) :=
    .transitive (.congruenceArgument _ (.symmetric (binarySetAtRecursion false)))
      (evenApply _)
  have odd : DerivableLatticeEta hypotheses
      (application binaryOdd (application (application fixpoint binarySetStep) nativeTrue))
      (oddNormal (binarySetAt true)) :=
    .transitive (.congruenceArgument _ (.symmetric (binarySetAtRecursion true)))
      (oddApply _)
  exact .transitive unfolded
    (.transitive (binarySetStepApply _ _)
      (DerivableLatticeEta.congruenceChoice (booleanSelect parameter binaryZero)
        (DerivableLatticeEta.congruenceChoice even odd)))

/-- What the zero case of S_p gives on a b c: a at true, `top` a b c at false. -/
def zeroPart : Bool → Term → Term → Term → Term
  | true, zeroCase, _, _ => zeroCase
  | false, zeroCase, evenCase, oddCase => applyCases top zeroCase evenCase oddCase

theorem pickedCases (parameter : Bool) (zeroCase evenCase oddCase : Term) :
    DerivableLatticeEta hypotheses
      (applyCases (picked parameter binaryZero) zeroCase evenCase oddCase)
      (zeroPart parameter zeroCase evenCase oddCase) := by
  cases parameter
  · exact .reflexive _
  · exact zeroCases zeroCase evenCase oddCase

/-- Section 8.2: S_p a b c = (a at true, `top` a b c at false) + b S_f + c S_t. -/
theorem binarySetCases (parameter : Bool) (zeroCase evenCase oddCase : Term) :
    DerivableLatticeEta hypotheses (applyCases (binarySetAt parameter) zeroCase evenCase oddCase)
      (choice (zeroPart parameter zeroCase evenCase oddCase)
        (choice (application evenCase (binarySetAt false))
          (application oddCase (binarySetAt true)))) :=
  .transitive (applyCasesCongruence zeroCase evenCase oddCase (binarySetUnfold parameter))
    (.transitive (applyCasesChoice _ _ _ _ _)
      (DerivableLatticeEta.congruenceChoice (pickedCases parameter zeroCase evenCase oddCase)
        (.transitive (applyCasesChoice _ _ _ _ _)
          (DerivableLatticeEta.congruenceChoice (evenCases _ _ _ _) (oddCases _ _ _ _)))))

/-! ### The order A ≤ B, that is A + B = B -/

/-- A ≤ A. -/
theorem refinesReflexive (term : Term) :
    DerivableLatticeEta hypotheses (choice term term) term :=
  DerivableLatticeEta.choiceIdempotent term

/-- A ≤ A + B: the first half of section 6's lemma (ii). -/
theorem refinesChoiceLeft (left right : Term) :
    DerivableLatticeEta hypotheses (choice left (choice left right)) (choice left right) :=
  DerivableLatticeEta.ofDerivableFrom (FourEquations.DerivableFrom.leftRefinesChoiceWithoutUnitLaw
    DerivableLatticeEta.equationOne DerivableLatticeEta.equationThree
    DerivableLatticeEta.equationFive DerivableLatticeEta.equationTen left right)

/-- A + B = C when A ≤ C, B ≤ C and C ≤ A + B: section 6's lemma (iii) and step 丙. -/
theorem choiceEqualOfRefines {left right whole : Term}
    (leftRefines : DerivableLatticeEta hypotheses (choice left whole) whole)
    (rightRefines : DerivableLatticeEta hypotheses (choice right whole) whole)
    (wholeRefines : DerivableLatticeEta hypotheses (choice whole (choice left right))
      (choice left right)) :
    DerivableLatticeEta hypotheses (choice left right) whole :=
  DerivableLatticeEta.antisymmetric (choiceRefinesOfRefines leftRefines rightRefines) wholeRefines

/-- `top` a b c ≤ `top`. -/
theorem applyCasesTopRefinesTop (zeroCase evenCase oddCase : Term) :
    DerivableLatticeEta hypotheses (choice (applyCases top zeroCase evenCase oddCase) top) top :=
  refinesOfEqualLower (applyCasesTop zeroCase evenCase oddCase)
    (refinesTransitive (parallelRefinesLeft _ _)
      (refinesTransitive (parallelRefinesLeft _ _) (parallelRefinesLeft _ _)))

/-- `top` a b c ≤ b c. -/
theorem applyCasesTopRefinesEvenCase (zeroCase evenCase oddCase : Term) :
    DerivableLatticeEta hypotheses
      (choice (applyCases top zeroCase evenCase oddCase) (application evenCase oddCase))
      (application evenCase oddCase) :=
  refinesOfEqualLower (applyCasesTop zeroCase evenCase oddCase)
    (refinesTransitive (parallelRefinesLeft _ _) (DerivableLatticeEta.parallelRefinesRight _ _))

/-- λ_. M, the term whose application to anything is M. -/
def constant (term : Term) : Term := abstraction (shift term)

theorem constantApply (term argument : Term) :
    DerivableLatticeEta hypotheses (application (constant term) argument) term :=
  betaTo (substituteShift term argument)

/-- λx. x. -/
def identity : Term := abstraction (boundVariable 0)

theorem identityApply (term : Term) :
    DerivableLatticeEta hypotheses (application identity term) term :=
  betaTo rfl

/-- From N + S = S, the same equation applied to three arguments, the left side distributed:
N a b c + S a b c = S a b c. -/
theorem observed {numeral set : Term} (zeroCase evenCase oddCase : Term)
    (member : DerivableLatticeEta hypotheses (choice numeral set) set) :
    DerivableLatticeEta hypotheses
      (choice (applyCases numeral zeroCase evenCase oddCase)
        (applyCases set zeroCase evenCase oddCase))
      (applyCases set zeroCase evenCase oddCase) :=
  .transitive (.symmetric (applyCasesChoice _ _ _ _ _))
    (applyCasesCongruence zeroCase evenCase oddCase member)

/-- S_f x (λ_. y) (λ_. y) = y: the even and odd members are y, and `top` x (λ_. y) (λ_. y) ≤ y. -/
theorem binarySetFalseConstantCases (zeroCase other : Term) :
    DerivableLatticeEta hypotheses
      (applyCases (binarySetAt false) zeroCase (constant other) (constant other)) other := by
  have members : DerivableLatticeEta hypotheses
      (choice (application (constant other) (binarySetAt false))
        (application (constant other) (binarySetAt true))) other :=
    .transitive (DerivableLatticeEta.congruenceChoice (constantApply _ _) (constantApply _ _))
      (refinesReflexive other)
  exact .transitive (binarySetCases false zeroCase (constant other) (constant other))
    (.transitive (DerivableLatticeEta.congruenceChoiceRight _ members)
      (refinesOfEqualUpper (applyCasesTopRefinesEvenCase zeroCase (constant other) (constant other))
        (constantApply _ _)))

/-- S_p `top` I `binary_odd` = S_f, whichever p is: `top` a b c ≤ `top`, and `top` and `binary_odd` S_t are
members of S_f. -/
theorem binarySetEvenCase (parameter : Bool) :
    DerivableLatticeEta hypotheses (applyCases (binarySetAt parameter) top identity binaryOdd)
      (binarySetAt false) := by
  have unfold : DerivableLatticeEta hypotheses (binarySetAt false)
      (choice top (choice (evenNormal (binarySetAt false)) (oddNormal (binarySetAt true)))) :=
    binarySetUnfold false
  have topRefines : DerivableLatticeEta hypotheses (choice top (binarySetAt false))
      (binarySetAt false) :=
    refinesOfEqualUpper (refinesChoiceLeft _ _) (.symmetric unfold)
  have zeroRefines : DerivableLatticeEta hypotheses
      (choice (zeroPart parameter top identity binaryOdd) (binarySetAt false)) (binarySetAt false) := by
    cases parameter
    · exact refinesTransitive (applyCasesTopRefinesTop _ _ _) topRefines
    · exact topRefines
  have oddRefines : DerivableLatticeEta hypotheses
      (choice (application binaryOdd (binarySetAt true)) (binarySetAt false)) (binarySetAt false) :=
    refinesOfEqualLower (oddApply _)
      (refinesOfEqualUpper
        (refinesTransitive (refinesChoiceRight _ _) (refinesChoiceRight _ _)) (.symmetric unfold))
  have rest : DerivableLatticeEta hypotheses
      (choice (application identity (binarySetAt false)) (application binaryOdd (binarySetAt true)))
      (binarySetAt false) :=
    .transitive (DerivableLatticeEta.congruenceChoiceLeft _ (identityApply _))
      (choiceEqualOfRefines (refinesReflexive _) oddRefines (refinesChoiceLeft _ _))
  exact .transitive (binarySetCases parameter top identity binaryOdd)
    (.transitive (DerivableLatticeEta.congruenceChoiceRight _ rest)
      (choiceEqualOfRefines zeroRefines (refinesReflexive _) (refinesChoiceRight _ _)))

/-- S_p Z (λ_. Z) I = S_t, whichever p is: `top` a b c ≤ (λ_. Z) I = Z, and Z is a member of S_t. -/
theorem binarySetOddCase (parameter : Bool) :
    DerivableLatticeEta hypotheses
      (applyCases (binarySetAt parameter) binaryZero (constant binaryZero) identity)
      (binarySetAt true) := by
  have unfold : DerivableLatticeEta hypotheses (binarySetAt true)
      (choice binaryZero
        (choice (evenNormal (binarySetAt false)) (oddNormal (binarySetAt true)))) :=
    binarySetUnfold true
  have zeroRefinesSet : DerivableLatticeEta hypotheses (choice binaryZero (binarySetAt true))
      (binarySetAt true) :=
    refinesOfEqualUpper (refinesChoiceLeft _ _) (.symmetric unfold)
  have zeroRefines : DerivableLatticeEta hypotheses
      (choice (zeroPart parameter binaryZero (constant binaryZero) identity) (binarySetAt true))
      (binarySetAt true) := by
    cases parameter
    · exact refinesTransitive
        (refinesOfEqualUpper (applyCasesTopRefinesEvenCase _ _ _) (constantApply _ _))
        zeroRefinesSet
    · exact zeroRefinesSet
  have rest : DerivableLatticeEta hypotheses
      (choice (application (constant binaryZero) (binarySetAt false))
        (application identity (binarySetAt true)))
      (binarySetAt true) :=
    .transitive (DerivableLatticeEta.congruenceChoice (constantApply _ _) (identityApply _))
      (choiceEqualOfRefines zeroRefinesSet (refinesReflexive _) (refinesChoiceRight _ _))
  exact .transitive (binarySetCases parameter binaryZero (constant binaryZero) identity)
    (.transitive (DerivableLatticeEta.congruenceChoiceRight _ rest)
      (choiceEqualOfRefines zeroRefines (refinesReflexive _) (refinesChoiceRight _ _)))

end Equations

/-! ## The theorem -/

/-- The hypotheses `listed [(left, right)]`, the one equation left = right. -/
theorem listedHypothesis (left right : Term) : listed [(left, right)] left right :=
  List.mem_singleton_self _

/-- An equation derivable from the hypotheses carries every derivation from the one equation to
them: weakening. -/
theorem fromDerived {hypotheses : Term → Term → Prop} {left right : Term}
    (derived : DerivableLatticeEta hypotheses left right)
    (inconsistent : DerivableLatticeEta (listed [(left, right)]) first second) :
    DerivableLatticeEta hypotheses first second :=
  DerivableLatticeEta.weakenByDerivations
    (fun weakerLeft weakerRight isListed => by
      simp only [listed, List.mem_singleton, Prod.mk.injEq] at isListed
      obtain ⟨rfl, rfl⟩ := isListed
      exact derived)
    inconsistent

/-- Lemma 8.3: {Z + S_f = S_f} ⊢_{λ-lattice-η} K = K*. Applied to (x, λ_. y, λ_. y), the
equation gives x + y = y (`binarySetFalseConstantCases`); at (K, K*) and at (K*, K) that is
K + K* = K* and K* + K = K, so K = K* (section 6's step 丙). -/
theorem zeroNotPositive :
    DerivableLatticeEta (listed [(choice binaryZero (binarySetAt false), binarySetAt false)])
      first second := by
  have member : DerivableLatticeEta
      (listed [(choice binaryZero (binarySetAt false), binarySetAt false)])
      (choice binaryZero (binarySetAt false)) (binarySetAt false) :=
    .hypothesis (listedHypothesis _ _)
  have refines : ∀ lower upper, DerivableLatticeEta
      (listed [(choice binaryZero (binarySetAt false), binarySetAt false)])
      (choice lower upper) upper :=
    fun lower upper =>
      .transitive
        (DerivableLatticeEta.congruenceChoice
          (.symmetric (zeroCases lower (constant upper) (constant upper)))
          (.symmetric (binarySetFalseConstantCases lower upper)))
        (.transitive (observed lower (constant upper) (constant upper) member)
          (binarySetFalseConstantCases lower upper))
  exact DerivableLatticeEta.antisymmetric (refines first second) (refines second first)

/-- Section 8.4, the first half: for every numeral n and boolean p with member(n, p) false,
{ñ + S_p = S_p} ⊢_{λ-lattice-η} λx.λy. x = λx.λy. y. By induction on n: the zero case is lemma 8.3;
for `binary_even h`, the equation applied to (`top`, I, `binary_odd`) gives h̃ + S_f = S_f
(`binarySetEvenCase`), and for `binary_odd h`, applied to (Z, λ_. Z, I), h̃ + S_t = S_t
(`binarySetOddCase`); the induction hypothesis then derives K = K* from it, and so from the
equation it was derived from. -/
theorem nonMemberIncompatible : ∀ (numeral : Numeral) (parameter : Bool),
    numeral.member parameter = false →
      DerivableLatticeEta
        (listed [(choice numeral.term (binarySetAt parameter), binarySetAt parameter)])
        first second
  | .zero, false, _ => zeroNotPositive
  | .zero, true, isMember => by simp [Numeral.member] at isMember
  | .even half, parameter, notMember => by
      have member : DerivableLatticeEta
          (listed [(choice (Numeral.even half).term (binarySetAt parameter),
            binarySetAt parameter)])
          (choice (Numeral.even half).term (binarySetAt parameter)) (binarySetAt parameter) :=
        .hypothesis (listedHypothesis _ _)
      have halfMember : DerivableLatticeEta
          (listed [(choice (Numeral.even half).term (binarySetAt parameter),
            binarySetAt parameter)])
          (choice half.term (binarySetAt false)) (binarySetAt false) :=
        .transitive
          (DerivableLatticeEta.congruenceChoice
            (.transitive (.symmetric (identityApply _))
              (.symmetric (evenCases half.term top identity binaryOdd)))
            (.symmetric (binarySetEvenCase parameter)))
          (.transitive (observed top identity binaryOdd member)
            (binarySetEvenCase parameter))
      exact fromDerived halfMember (nonMemberIncompatible half false notMember)
  | .odd half, parameter, notMember => by
      have member : DerivableLatticeEta
          (listed [(choice (Numeral.odd half).term (binarySetAt parameter),
            binarySetAt parameter)])
          (choice (Numeral.odd half).term (binarySetAt parameter)) (binarySetAt parameter) :=
        .hypothesis (listedHypothesis _ _)
      have halfMember : DerivableLatticeEta
          (listed [(choice (Numeral.odd half).term (binarySetAt parameter),
            binarySetAt parameter)])
          (choice half.term (binarySetAt true)) (binarySetAt true) :=
        .transitive
          (DerivableLatticeEta.congruenceChoice
            (.transitive (.symmetric (identityApply _))
              (.symmetric (oddCases half.term binaryZero (constant binaryZero) identity)))
            (.symmetric (binarySetOddCase parameter)))
          (.transitive (observed binaryZero (constant binaryZero) identity member)
            (binarySetOddCase parameter))
      exact fromDerived halfMember (nonMemberIncompatible half true notMember)

/-- ñ ∉ NF◇(`binary_set p`) when member(n, p) is false, by Definition 14: `binary_set p` ⊑_O ñ is
false, since it would make every equation derivable from ñ + S_p = S_p in ⊢_{λ-lattice-η} a
contextual equivalence, K = K* among them
(`ContextualPreorder.consistentEquationLatticeEtaOfContextualPreorder`). -/
theorem nonMemberNotContextualPreorder (numeral : Numeral) (parameter : Bool)
    (notMember : numeral.member parameter = false) :
    ¬ ContextualPreorder.ContextualPreorder (binarySetAt parameter) numeral.term :=
  fun preorder => ContextualPreorder.consistentEquationLatticeEtaOfContextualPreorder preorder
    (nonMemberIncompatible numeral parameter notMember)

end LambdaJit.BinaryNaturalsNonMember
