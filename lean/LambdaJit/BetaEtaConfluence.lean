import LambdaJit.Semantics
import LambdaJit.TermSubstitution

/-!
# Confluence of βη on the terms of the calculus

This module proves that βη-conversion does not equate λx.λy. x and λx.λy. y
(`firstNotConvertibleSecond`), by the Church–Rosser property of β and η, which module
`SyntacticConsistency` needs as its last step: there, the readings of two terms equal by
⊢_{λ-lattice-η} are compared up to βη-conversion.

`Convertible` is βη-conversion on the terms of module `Terms`: the least equivalence relation,
closed under abstraction and application, that contains the β rule and the η rule. On pure terms
it is the conversion of λβη; choices and parallels are inert in it.

The proof is Hindley and Rosen's, with Takahashi's parallel reductions (M. Takahashi, Parallel
reductions in λ-calculus, Information and Computation 118, 1995), called simultaneous here, as in
module `Confluence`, because the calculus already has an operator named parallel:

- `BetaSimultaneous`, simultaneous β reduction, has the triangle property with its complete
  development `developBeta`.
- `EtaSimultaneous`, simultaneous η reduction, whose η step at an abstraction may first reduce the
  body to the shape of an η redex, has the triangle property with `developEta`, which contracts an
  abstraction after developing its body.
- A simultaneous β step and a simultaneous η step of one term close in a simultaneous η step and a
  simultaneous β step (`betaEtaCommute`).

So one simultaneous step of either kind has the diamond property, its reflexive transitive closure
is confluent, βη-convertible terms reduce to a common term, and two different terms with no redex
are not convertible. Both simultaneous reductions also reduce under choices and parallels; that
only makes the reduction larger than the conversion needs.
-/

namespace LambdaJit.BetaEtaConfluence

open LambdaJit.Semantics
open LambdaJit.Semantics.Term

/-! ## Shifting and substitution -/

/-- Shifting commutes with substitution above the substituted index: shifting the result of
substituting at `depth` from a cutoff at least `depth` is substituting the shifted replacement into
the term shifted from one more. -/
theorem shiftFromSubstitute : ∀ (term : Term) (cutoff depth : Nat) (replacement : Term),
    depth ≤ cutoff →
      shiftFrom cutoff (substitute depth replacement term) =
        substitute depth (shiftFrom cutoff replacement) (shiftFrom (cutoff + 1) term)
  | .boundVariable index, cutoff, depth, replacement, ordered => by
      by_cases belowDepth : index < depth
      · have belowCutoff : index < cutoff := by omega
        have belowNext : index < cutoff + 1 := by omega
        simp [shiftFrom, substitute, belowDepth, belowCutoff, belowNext]
      · by_cases atDepth : index = depth
        · subst atDepth
          have belowNext : index < cutoff + 1 := by omega
          simp [shiftFrom, substitute, belowNext]
        · by_cases belowNext : index < cutoff + 1
          · have loweredBelow : index - 1 < cutoff := by omega
            simp [shiftFrom, substitute, belowDepth, atDepth, belowNext, loweredBelow]
          · have loweredNotBelow : ¬ index - 1 < cutoff := by omega
            have notBelowDepth : ¬ index + 1 < depth := by omega
            have notAtDepth : ¬ index + 1 = depth := by omega
            have restored : index + 1 - 1 = index - 1 + 1 := by omega
            simp [shiftFrom, substitute, belowDepth, atDepth, belowNext, loweredNotBelow,
              notBelowDepth, notAtDepth, restored]
  | .abstraction body, cutoff, depth, replacement, ordered => by
      have shifted : shift (shiftFrom cutoff replacement) =
          shiftFrom (cutoff + 1) (shift replacement) :=
        shiftFromShiftFrom replacement cutoff 0 (Nat.zero_le cutoff)
      simp only [shiftFrom, substitute, shifted,
        shiftFromSubstitute body (cutoff + 1) (depth + 1) (shift replacement) (by omega)]
  | .application function argument, cutoff, depth, replacement, ordered => by
      simp only [shiftFrom, substitute,
        shiftFromSubstitute function cutoff depth replacement ordered,
        shiftFromSubstitute argument cutoff depth replacement ordered]
  | .choice left right, cutoff, depth, replacement, ordered => by
      simp only [shiftFrom, substitute,
        shiftFromSubstitute left cutoff depth replacement ordered,
        shiftFromSubstitute right cutoff depth replacement ordered]
  | .parallel left right, cutoff, depth, replacement, ordered => by
      simp only [shiftFrom, substitute,
        shiftFromSubstitute left cutoff depth replacement ordered,
        shiftFromSubstitute right cutoff depth replacement ordered]

/-- Shifting a β contractum: the contractum of the shifted redex. -/
theorem shiftFromInstantiate (body argument : Term) (cutoff : Nat) :
    shiftFrom cutoff (instantiate body argument) =
      instantiate (shiftFrom (cutoff + 1) body) (shiftFrom cutoff argument) :=
  shiftFromSubstitute body cutoff 0 argument (Nat.zero_le cutoff)

/-- Shifting below the substituted index: the case of `Term.substituteShiftFromCommute` read
from right to left. -/
theorem shiftFromSubstituteBelow (term : Term) (cutoff depth : Nat) (replacement : Term)
    (ordered : cutoff ≤ depth) :
    shiftFrom cutoff (substitute depth replacement term) =
      substitute (depth + 1) (shiftFrom cutoff replacement) (shiftFrom cutoff term) :=
  (Term.substituteShiftFromCommute term cutoff depth replacement ordered).symm

/-- The substitution lemma: substituting at `depth` after substituting at `inner ≤ depth` is
substituting at `depth + 1` first, the replacement shifted past index `inner`, and then
substituting the substituted inner replacement at `inner`. -/
theorem substituteSubstitute :
    ∀ (term : Term) (inner depth : Nat) (innerReplacement replacement : Term), inner ≤ depth →
      substitute depth replacement (substitute inner innerReplacement term) =
        substitute inner (substitute depth replacement innerReplacement)
          (substitute (depth + 1) (shiftFrom inner replacement) term)
  | .boundVariable index, inner, depth, innerReplacement, replacement, ordered => by
      by_cases belowInner : index < inner
      · have belowDepth : index < depth := by omega
        have belowNext : index < depth + 1 := by omega
        simp [substitute, belowInner, belowDepth, belowNext]
      · by_cases atInner : index = inner
        · subst atInner
          have belowNext : index < depth + 1 := by omega
          simp [substitute, belowNext]
        · by_cases belowNext : index < depth + 1
          · have loweredBelow : index - 1 < depth := by omega
            simp [substitute, belowInner, atInner, belowNext, loweredBelow]
          · by_cases atNext : index = depth + 1
            · subst atNext
              have loweredAt : depth + 1 - 1 = depth := by omega
              simp only [substitute, belowInner, atInner, belowNext, loweredAt, ite_false,
                ite_true, Nat.lt_irrefl]
              exact (substituteShiftFromCancel replacement inner
                (substitute depth replacement innerReplacement)).symm
            · have loweredNotBelow : ¬ index - 1 < depth := by omega
              have loweredNotAt : ¬ index - 1 = depth := by omega
              have twiceNotBelow : ¬ index - 1 < inner := by omega
              have twiceNotAt : ¬ index - 1 = inner := by omega
              simp [substitute, belowInner, atInner, belowNext, atNext, loweredNotBelow,
                loweredNotAt, twiceNotBelow, twiceNotAt]
  | .abstraction body, inner, depth, innerReplacement, replacement, ordered => by
      have shiftedInner : shift (substitute depth replacement innerReplacement) =
          substitute (depth + 1) (shift replacement) (shift innerReplacement) :=
        shiftFromSubstituteBelow innerReplacement 0 depth replacement (Nat.zero_le depth)
      have shiftedReplacement : shift (shiftFrom inner replacement) =
          shiftFrom (inner + 1) (shift replacement) :=
        shiftFromShiftFrom replacement inner 0 (Nat.zero_le inner)
      simp only [substitute, shiftedInner, shiftedReplacement,
        substituteSubstitute body (inner + 1) (depth + 1) (shift innerReplacement)
          (shift replacement) (by omega)]
  | .application function argument, inner, depth, innerReplacement, replacement, ordered => by
      simp only [substitute,
        substituteSubstitute function inner depth innerReplacement replacement ordered,
        substituteSubstitute argument inner depth innerReplacement replacement ordered]
  | .choice left right, inner, depth, innerReplacement, replacement, ordered => by
      simp only [substitute,
        substituteSubstitute left inner depth innerReplacement replacement ordered,
        substituteSubstitute right inner depth innerReplacement replacement ordered]
  | .parallel left right, inner, depth, innerReplacement, replacement, ordered => by
      simp only [substitute,
        substituteSubstitute left inner depth innerReplacement replacement ordered,
        substituteSubstitute right inner depth innerReplacement replacement ordered]

/-- Substituting into a β contractum: the contractum of the substituted redex. -/
theorem substituteInstantiate (body argument replacement : Term) (depth : Nat) :
    substitute depth replacement (instantiate body argument) =
      instantiate (substitute (depth + 1) (shift replacement) body)
        (substitute depth replacement argument) :=
  substituteSubstitute body 0 depth argument replacement (Nat.zero_le depth)

/-- Substituting into a shifted term: the shift of the substituted term. -/
theorem substituteShifted (term replacement : Term) (depth : Nat) :
    substitute (depth + 1) (shift replacement) (shift term) =
      shift (substitute depth replacement term) :=
  Term.substituteShiftFromCommute term 0 depth replacement (Nat.zero_le depth)

/-- Shifting a shifted term from one more: the shift of the shifted term. -/
theorem shiftFromShifted (term : Term) (cutoff : Nat) :
    shiftFrom (cutoff + 1) (shift term) = shift (shiftFrom cutoff term) :=
  (shiftFromShiftFrom term cutoff 0 (Nat.zero_le cutoff)).symm

/-! ## βη-conversion, the target of the readings -/

/-- βη-conversion: the least equivalence relation on terms, closed under abstraction and
application, that contains the β rule and the η rule. On pure terms it is the conversion of λβη.
Choices and parallels are inert in it: no rule rewrites under them. -/
inductive Convertible : Term → Term → Prop where
  /-- Reflexivity. -/
  | reflexive (term : Term) : Convertible term term
  /-- Symmetry. -/
  | symmetric {left right : Term} : Convertible left right → Convertible right left
  /-- Transitivity. -/
  | transitive {left middle right : Term} :
      Convertible left middle → Convertible middle right → Convertible left right
  /-- Under an abstraction. -/
  | abstraction {left right : Term} :
      Convertible left right → Convertible (.abstraction left) (.abstraction right)
  /-- In both sides of an application. -/
  | application {function functionOther argument argumentOther : Term} :
      Convertible function functionOther → Convertible argument argumentOther →
        Convertible (.application function argument) (.application functionOther argumentOther)
  /-- The β rule. -/
  | beta (body argument : Term) :
      Convertible (.application (.abstraction body) argument) (instantiate body argument)
  /-- The η rule, λx. M x = M with x ∉ FV(M). -/
  | eta (function : Term) :
      Convertible (.abstraction (.application (shift function) (.boundVariable 0))) function

namespace Convertible

/-- βη-conversion is closed under shifting. -/
theorem shiftFrom {left right : Term} (convertible : Convertible left right) :
    ∀ cutoff, Convertible (Term.shiftFrom cutoff left) (Term.shiftFrom cutoff right) := by
  induction convertible with
  | reflexive term => intro cutoff; exact .reflexive _
  | symmetric _ inner => intro cutoff; exact .symmetric (inner cutoff)
  | transitive _ _ leftInner rightInner =>
      intro cutoff; exact .transitive (leftInner cutoff) (rightInner cutoff)
  | abstraction _ inner => intro cutoff; exact .abstraction (inner (cutoff + 1))
  | application _ _ functionInner argumentInner =>
      intro cutoff; exact .application (functionInner cutoff) (argumentInner cutoff)
  | beta body argument =>
      intro cutoff
      rw [shiftFromInstantiate]
      exact .beta _ _
  | eta function =>
      intro cutoff
      have variableKept : Term.shiftFrom (cutoff + 1) (.boundVariable 0) = .boundVariable 0 := by
        simp [Term.shiftFrom]
      simp only [Term.shiftFrom, shiftFromShifted] at variableKept ⊢
      rw [variableKept]
      exact .eta _

/-- βη-conversion is closed under substitution. -/
theorem substitute {left right : Term} (convertible : Convertible left right) :
    ∀ depth replacement,
      Convertible (Term.substitute depth replacement left)
        (Term.substitute depth replacement right) := by
  induction convertible with
  | reflexive term => intro depth replacement; exact .reflexive _
  | symmetric _ inner => intro depth replacement; exact .symmetric (inner depth replacement)
  | transitive _ _ leftInner rightInner =>
      intro depth replacement
      exact .transitive (leftInner depth replacement) (rightInner depth replacement)
  | abstraction _ inner =>
      intro depth replacement; exact .abstraction (inner (depth + 1) (shift replacement))
  | application _ _ functionInner argumentInner =>
      intro depth replacement
      exact .application (functionInner depth replacement) (argumentInner depth replacement)
  | beta body argument =>
      intro depth replacement
      rw [substituteInstantiate]
      exact .beta _ _
  | eta function =>
      intro depth replacement
      have variableKept :
          Term.substitute (depth + 1) (shift replacement) (.boundVariable 0) =
            .boundVariable 0 := by
        simp [Term.substitute]
      simp only [Term.substitute, substituteShifted] at variableKept ⊢
      rw [variableKept]
      exact .eta _

/-- βη-conversion reflects shifting: substituting at the cutoff undoes the shift. -/
theorem ofShiftFrom {left right : Term} (cutoff : Nat)
    (convertible : Convertible (Term.shiftFrom cutoff left) (Term.shiftFrom cutoff right)) :
    Convertible left right := by
  have substituted := convertible.substitute cutoff (.boundVariable 0)
  rw [substituteShiftFromCancel, substituteShiftFromCancel] at substituted
  exact substituted

end Convertible

/-! ## Simultaneous β reduction -/

/-- Simultaneous β reduction: any set of β redexes contracted at once, under every constructor. -/
inductive BetaSimultaneous : Term → Term → Prop where
  /-- A variable reduces to itself. -/
  | boundVariable (index : Nat) : BetaSimultaneous (.boundVariable index) (.boundVariable index)
  /-- Under an abstraction. -/
  | abstraction {body result : Term} :
      BetaSimultaneous body result → BetaSimultaneous (.abstraction body) (.abstraction result)
  /-- In both sides of an application. -/
  | application {function functionResult argument argumentResult : Term} :
      BetaSimultaneous function functionResult → BetaSimultaneous argument argumentResult →
        BetaSimultaneous (.application function argument)
          (.application functionResult argumentResult)
  /-- In both sides of a choice. -/
  | choice {left leftResult right rightResult : Term} :
      BetaSimultaneous left leftResult → BetaSimultaneous right rightResult →
        BetaSimultaneous (.choice left right) (.choice leftResult rightResult)
  /-- In both sides of a parallel. -/
  | parallel {left leftResult right rightResult : Term} :
      BetaSimultaneous left leftResult → BetaSimultaneous right rightResult →
        BetaSimultaneous (.parallel left right) (.parallel leftResult rightResult)
  /-- The β rule. -/
  | beta {body bodyResult argument argumentResult : Term} :
      BetaSimultaneous body bodyResult → BetaSimultaneous argument argumentResult →
        BetaSimultaneous (.application (.abstraction body) argument)
          (instantiate bodyResult argumentResult)

namespace BetaSimultaneous

/-- Every term reduces to itself. -/
theorem reflexive : ∀ term : Term, BetaSimultaneous term term
  | .boundVariable index => .boundVariable index
  | .abstraction body => .abstraction (reflexive body)
  | .application function argument => .application (reflexive function) (reflexive argument)
  | .choice left right => .choice (reflexive left) (reflexive right)
  | .parallel left right => .parallel (reflexive left) (reflexive right)

/-- Simultaneous β reduction commutes with shifting. -/
theorem shiftFrom {term result : Term} (reduces : BetaSimultaneous term result) :
    ∀ cutoff, BetaSimultaneous (Term.shiftFrom cutoff term) (Term.shiftFrom cutoff result) := by
  induction reduces with
  | boundVariable index => intro cutoff; exact reflexive _
  | abstraction _ inner => intro cutoff; exact .abstraction (inner (cutoff + 1))
  | application _ _ functionInner argumentInner =>
      intro cutoff; exact .application (functionInner cutoff) (argumentInner cutoff)
  | choice _ _ leftInner rightInner =>
      intro cutoff; exact .choice (leftInner cutoff) (rightInner cutoff)
  | parallel _ _ leftInner rightInner =>
      intro cutoff; exact .parallel (leftInner cutoff) (rightInner cutoff)
  | beta _ _ bodyInner argumentInner =>
      intro cutoff
      rw [shiftFromInstantiate]
      exact .beta (bodyInner (cutoff + 1)) (argumentInner cutoff)

/-- Simultaneous β reduction is closed under substitution. -/
theorem substitute {term result : Term} (reduces : BetaSimultaneous term result) :
    ∀ {replacement replacementResult : Term}, BetaSimultaneous replacement replacementResult →
      ∀ depth, BetaSimultaneous (Term.substitute depth replacement term)
        (Term.substitute depth replacementResult result) := by
  induction reduces with
  | boundVariable index =>
      intro replacement replacementResult replacementReduces depth
      by_cases below : index < depth
      · simp only [Term.substitute, below, ite_true]; exact reflexive _
      · by_cases atDepth : index = depth
        · subst atDepth
          simp only [Term.substitute, Nat.lt_irrefl, ite_false, ite_true]
          exact replacementReduces
        · simp only [Term.substitute, below, atDepth, ite_false]; exact reflexive _
  | abstraction _ inner =>
      intro _ _ replacementReduces depth
      exact .abstraction (inner (replacementReduces.shiftFrom 0) (depth + 1))
  | application _ _ functionInner argumentInner =>
      intro _ _ replacementReduces depth
      exact .application (functionInner replacementReduces depth)
        (argumentInner replacementReduces depth)
  | choice _ _ leftInner rightInner =>
      intro _ _ replacementReduces depth
      exact .choice (leftInner replacementReduces depth) (rightInner replacementReduces depth)
  | parallel _ _ leftInner rightInner =>
      intro _ _ replacementReduces depth
      exact .parallel (leftInner replacementReduces depth) (rightInner replacementReduces depth)
  | beta _ _ bodyInner argumentInner =>
      intro _ _ replacementReduces depth
      rw [substituteInstantiate]
      exact .beta (bodyInner (replacementReduces.shiftFrom 0) (depth + 1))
        (argumentInner replacementReduces depth)

/-- An abstraction reduces to an abstraction. -/
theorem abstractionInversion {body result : Term}
    (reduces : BetaSimultaneous (.abstraction body) result) :
    ∃ bodyResult, result = .abstraction bodyResult ∧ BetaSimultaneous body bodyResult := by
  cases reduces with
  | abstraction inner => exact ⟨_, rfl, inner⟩

/-- A simultaneous β reduct of a shifted term is the shift of a simultaneous β reduct of the
term. -/
theorem ofShiftFrom : ∀ (term : Term) (cutoff : Nat) {result : Term},
    BetaSimultaneous (Term.shiftFrom cutoff term) result →
      ∃ unshifted, result = Term.shiftFrom cutoff unshifted ∧ BetaSimultaneous term unshifted
  | .boundVariable index, cutoff, result, reduces => by
      by_cases below : index < cutoff
      · simp only [Term.shiftFrom, below, ite_true] at reduces
        cases reduces
        exact ⟨.boundVariable index, by simp [Term.shiftFrom, below], .boundVariable index⟩
      · simp only [Term.shiftFrom, below, ite_false] at reduces
        cases reduces
        exact ⟨.boundVariable index, by simp [Term.shiftFrom, below], .boundVariable index⟩
  | .abstraction body, cutoff, result, reduces => by
      simp only [Term.shiftFrom] at reduces
      cases reduces with
      | abstraction bodyReduces =>
          obtain ⟨unshifted, unshiftedEqual, unshiftedReduces⟩ :=
            ofShiftFrom body (cutoff + 1) bodyReduces
          subst unshiftedEqual
          exact ⟨.abstraction unshifted, rfl, .abstraction unshiftedReduces⟩
  | .choice left right, cutoff, result, reduces => by
      simp only [Term.shiftFrom] at reduces
      cases reduces with
      | choice leftReduces rightReduces =>
          obtain ⟨leftUnshifted, leftEqual, leftUnshiftedReduces⟩ :=
            ofShiftFrom left cutoff leftReduces
          obtain ⟨rightUnshifted, rightEqual, rightUnshiftedReduces⟩ :=
            ofShiftFrom right cutoff rightReduces
          subst leftEqual rightEqual
          exact ⟨.choice leftUnshifted rightUnshifted, rfl,
            .choice leftUnshiftedReduces rightUnshiftedReduces⟩
  | .parallel left right, cutoff, result, reduces => by
      simp only [Term.shiftFrom] at reduces
      cases reduces with
      | parallel leftReduces rightReduces =>
          obtain ⟨leftUnshifted, leftEqual, leftUnshiftedReduces⟩ :=
            ofShiftFrom left cutoff leftReduces
          obtain ⟨rightUnshifted, rightEqual, rightUnshiftedReduces⟩ :=
            ofShiftFrom right cutoff rightReduces
          subst leftEqual rightEqual
          exact ⟨.parallel leftUnshifted rightUnshifted, rfl,
            .parallel leftUnshiftedReduces rightUnshiftedReduces⟩
  | .application function argument, cutoff, result, reduces => by
      have congruenceCase : ∀ {functionResult argumentResult : Term},
          BetaSimultaneous (Term.shiftFrom cutoff function) functionResult →
          BetaSimultaneous (Term.shiftFrom cutoff argument) argumentResult →
            ∃ unshifted, Term.application functionResult argumentResult =
              Term.shiftFrom cutoff unshifted ∧
                BetaSimultaneous (.application function argument) unshifted := by
        intro functionResult argumentResult functionReduces argumentReduces
        obtain ⟨functionUnshifted, functionEqual, functionUnshiftedReduces⟩ :=
          ofShiftFrom function cutoff functionReduces
        obtain ⟨argumentUnshifted, argumentEqual, argumentUnshiftedReduces⟩ :=
          ofShiftFrom argument cutoff argumentReduces
        subst functionEqual argumentEqual
        exact ⟨.application functionUnshifted argumentUnshifted, rfl,
          .application functionUnshiftedReduces argumentUnshiftedReduces⟩
      cases function with
      | abstraction body =>
          simp only [Term.shiftFrom] at reduces congruenceCase
          cases reduces with
          | application functionReduces argumentReduces =>
              exact congruenceCase functionReduces argumentReduces
          | beta bodyReduces argumentReduces =>
              obtain ⟨bodyUnshifted, bodyEqual, bodyUnshiftedReduces⟩ :=
                ofShiftFrom body (cutoff + 1) bodyReduces
              obtain ⟨argumentUnshifted, argumentEqual, argumentUnshiftedReduces⟩ :=
                ofShiftFrom argument cutoff argumentReduces
              subst bodyEqual argumentEqual
              exact ⟨Term.instantiate bodyUnshifted argumentUnshifted,
                (shiftFromInstantiate bodyUnshifted argumentUnshifted cutoff).symm,
                .beta bodyUnshiftedReduces argumentUnshiftedReduces⟩
      | boundVariable index =>
          by_cases below : index < cutoff
          · simp only [Term.shiftFrom, below, ite_true] at reduces congruenceCase
            cases reduces with
            | application functionReduces argumentReduces =>
                exact congruenceCase functionReduces argumentReduces
          · simp only [Term.shiftFrom, below, ite_false] at reduces congruenceCase
            cases reduces with
            | application functionReduces argumentReduces =>
                exact congruenceCase functionReduces argumentReduces
      | application inner innerArgument =>
          cases reduces with
          | application functionReduces argumentReduces =>
              exact congruenceCase functionReduces argumentReduces
      | choice left right =>
          cases reduces with
          | application functionReduces argumentReduces =>
              exact congruenceCase functionReduces argumentReduces
      | parallel left right =>
          cases reduces with
          | application functionReduces argumentReduces =>
              exact congruenceCase functionReduces argumentReduces

end BetaSimultaneous

/-- The complete β development: every β redex contracted at once. -/
def developBeta : Term → Term
  | .boundVariable index => .boundVariable index
  | .abstraction body => .abstraction (developBeta body)
  | .application function argument =>
      match function with
      | .abstraction body => instantiate (developBeta body) (developBeta argument)
      | .boundVariable index => .application (.boundVariable index) (developBeta argument)
      | .application inner innerArgument =>
          .application (developBeta (.application inner innerArgument)) (developBeta argument)
      | .choice left right => .application (developBeta (.choice left right)) (developBeta argument)
      | .parallel left right =>
          .application (developBeta (.parallel left right)) (developBeta argument)
  | .choice left right => .choice (developBeta left) (developBeta right)
  | .parallel left right => .parallel (developBeta left) (developBeta right)

/-- Takahashi's triangle for simultaneous β reduction. -/
theorem betaSimultaneousDevelop {term result : Term} (reduces : BetaSimultaneous term result) :
    BetaSimultaneous result (developBeta term) := by
  induction reduces with
  | boundVariable index => exact .boundVariable index
  | abstraction _ inner => exact .abstraction inner
  | @application function functionResult argument argumentResult functionReduces _
      functionInner argumentInner =>
      cases function with
      | abstraction body =>
          obtain ⟨bodyResult, resultEqual, _⟩ := functionReduces.abstractionInversion
          subst resultEqual
          obtain ⟨developed, developedEqual, bodyDeveloped⟩ := functionInner.abstractionInversion
          simp only [developBeta] at developedEqual
          cases developedEqual
          exact .beta bodyDeveloped argumentInner
      | boundVariable index => exact .application functionInner argumentInner
      | application inner innerArgument => exact .application functionInner argumentInner
      | choice left right => exact .application functionInner argumentInner
      | parallel left right => exact .application functionInner argumentInner
  | choice _ _ leftInner rightInner => exact .choice leftInner rightInner
  | parallel _ _ leftInner rightInner => exact .parallel leftInner rightInner
  | beta _ _ bodyInner argumentInner => exact bodyInner.substitute argumentInner 0

/-! ## Simultaneous η reduction -/

/-- The body of the η redex of a term, shifted from one more, is the body of the η redex of the
shifted term. -/
theorem shiftFromEtaBody (function : Term) (cutoff : Nat) :
    Term.shiftFrom (cutoff + 1) (.application (shift function) (.boundVariable 0)) =
      .application (shift (Term.shiftFrom cutoff function)) (.boundVariable 0) := by
  simp only [Term.shiftFrom, shiftFromShifted]
  simp

/-- Substituting into the body of the η redex of a term, one level down, gives the body of the η
redex of the substituted term. -/
theorem substituteEtaBody (function replacement : Term) (depth : Nat) :
    Term.substitute (depth + 1) (shift replacement)
        (.application (shift function) (.boundVariable 0)) =
      .application (shift (Term.substitute depth replacement function)) (.boundVariable 0) := by
  simp only [Term.substitute, substituteShifted]
  simp

/-- An index below the cutoff that occurs free still occurs free after shifting. -/
theorem occursFreeShiftFromBelow : ∀ (term : Term) (index cutoff : Nat),
    OccursFree index term → index < cutoff → OccursFree index (Term.shiftFrom cutoff term)
  | .boundVariable other, index, cutoff, occurs, below => by
      simp only [OccursFree] at occurs
      subst occurs
      simp [Term.shiftFrom, below, OccursFree]
  | .abstraction body, index, cutoff, occurs, below =>
      occursFreeShiftFromBelow body (index + 1) (cutoff + 1) occurs (by omega)
  | .application function argument, index, cutoff, occurs, below => by
      rcases occurs with occurs | occurs
      · exact Or.inl (occursFreeShiftFromBelow function index cutoff occurs below)
      · exact Or.inr (occursFreeShiftFromBelow argument index cutoff occurs below)
  | .choice left right, index, cutoff, occurs, below => by
      rcases occurs with occurs | occurs
      · exact Or.inl (occursFreeShiftFromBelow left index cutoff occurs below)
      · exact Or.inr (occursFreeShiftFromBelow right index cutoff occurs below)
  | .parallel left right, index, cutoff, occurs, below => by
      rcases occurs with occurs | occurs
      · exact Or.inl (occursFreeShiftFromBelow left index cutoff occurs below)
      · exact Or.inr (occursFreeShiftFromBelow right index cutoff occurs below)

/-- A term whose shift from one more is a shift is itself a shift. -/
theorem shiftFromEqualShift {term other : Term} (cutoff : Nat)
    (equal : Term.shiftFrom (cutoff + 1) term = shift other) :
    ∃ lowered, term = shift lowered ∧ other = Term.shiftFrom cutoff lowered := by
  have absent : ¬ OccursFree 0 term := by
    intro occurs
    have shifted := occursFreeShiftFromBelow term 0 (cutoff + 1) occurs (by omega)
    rw [equal] at shifted
    exact notOccursFreeShiftFrom other 0 shifted
  refine ⟨lower term, (shiftLower term absent).symm, ?_⟩
  have restored : shift other = shift (Term.shiftFrom cutoff (lower term)) := by
    rw [← equal, ← shiftFromShifted, shiftLower term absent]
  have lowered := congrArg lower restored
  simp only [lower, shift, lowerFromShiftFrom] at lowered
  exact lowered

/-- Simultaneous η reduction: any set of η redexes contracted at once, under every constructor.
The η step at an abstraction may first reduce its body to the shape of an η redex, so that a redex
created by an inner contraction is contracted in the same step. -/
inductive EtaSimultaneous : Term → Term → Prop where
  /-- A variable reduces to itself. -/
  | boundVariable (index : Nat) : EtaSimultaneous (.boundVariable index) (.boundVariable index)
  /-- Under an abstraction. -/
  | abstraction {body result : Term} :
      EtaSimultaneous body result → EtaSimultaneous (.abstraction body) (.abstraction result)
  /-- In both sides of an application. -/
  | application {function functionResult argument argumentResult : Term} :
      EtaSimultaneous function functionResult → EtaSimultaneous argument argumentResult →
        EtaSimultaneous (.application function argument)
          (.application functionResult argumentResult)
  /-- In both sides of a choice. -/
  | choice {left leftResult right rightResult : Term} :
      EtaSimultaneous left leftResult → EtaSimultaneous right rightResult →
        EtaSimultaneous (.choice left right) (.choice leftResult rightResult)
  /-- In both sides of a parallel. -/
  | parallel {left leftResult right rightResult : Term} :
      EtaSimultaneous left leftResult → EtaSimultaneous right rightResult →
        EtaSimultaneous (.parallel left right) (.parallel leftResult rightResult)
  /-- The η rule, λx. M x → M with x ∉ FV(M), after the body has reduced to M x. -/
  | eta {body function : Term} :
      EtaSimultaneous body (.application (shift function) (.boundVariable 0)) →
        EtaSimultaneous (.abstraction body) function

namespace EtaSimultaneous

/-- Every term reduces to itself. -/
theorem reflexive : ∀ term : Term, EtaSimultaneous term term
  | .boundVariable index => .boundVariable index
  | .abstraction body => .abstraction (reflexive body)
  | .application function argument => .application (reflexive function) (reflexive argument)
  | .choice left right => .choice (reflexive left) (reflexive right)
  | .parallel left right => .parallel (reflexive left) (reflexive right)

/-- Simultaneous η reduction commutes with shifting. -/
theorem shiftFrom {term result : Term} (reduces : EtaSimultaneous term result) :
    ∀ cutoff, EtaSimultaneous (Term.shiftFrom cutoff term) (Term.shiftFrom cutoff result) := by
  induction reduces with
  | boundVariable index => intro cutoff; exact reflexive _
  | abstraction _ inner => intro cutoff; exact .abstraction (inner (cutoff + 1))
  | application _ _ functionInner argumentInner =>
      intro cutoff; exact .application (functionInner cutoff) (argumentInner cutoff)
  | choice _ _ leftInner rightInner =>
      intro cutoff; exact .choice (leftInner cutoff) (rightInner cutoff)
  | parallel _ _ leftInner rightInner =>
      intro cutoff; exact .parallel (leftInner cutoff) (rightInner cutoff)
  | @eta body function _ inner =>
      intro cutoff
      have shifted := inner (cutoff + 1)
      rw [shiftFromEtaBody] at shifted
      exact .eta shifted

/-- Simultaneous η reduction is closed under substitution. -/
theorem substitute {term result : Term} (reduces : EtaSimultaneous term result) :
    ∀ {replacement replacementResult : Term}, EtaSimultaneous replacement replacementResult →
      ∀ depth, EtaSimultaneous (Term.substitute depth replacement term)
        (Term.substitute depth replacementResult result) := by
  induction reduces with
  | boundVariable index =>
      intro replacement replacementResult replacementReduces depth
      by_cases below : index < depth
      · simp only [Term.substitute, below, ite_true]; exact reflexive _
      · by_cases atDepth : index = depth
        · subst atDepth
          simp only [Term.substitute, Nat.lt_irrefl, ite_false, ite_true]
          exact replacementReduces
        · simp only [Term.substitute, below, atDepth, ite_false]; exact reflexive _
  | abstraction _ inner =>
      intro _ _ replacementReduces depth
      exact .abstraction (inner (replacementReduces.shiftFrom 0) (depth + 1))
  | application _ _ functionInner argumentInner =>
      intro _ _ replacementReduces depth
      exact .application (functionInner replacementReduces depth)
        (argumentInner replacementReduces depth)
  | choice _ _ leftInner rightInner =>
      intro _ _ replacementReduces depth
      exact .choice (leftInner replacementReduces depth) (rightInner replacementReduces depth)
  | parallel _ _ leftInner rightInner =>
      intro _ _ replacementReduces depth
      exact .parallel (leftInner replacementReduces depth) (rightInner replacementReduces depth)
  | @eta body function _ inner =>
      intro replacement replacementResult replacementReduces depth
      have substituted : EtaSimultaneous (Term.substitute (depth + 1) (shift replacement) body)
          (Term.substitute (depth + 1) (shift replacementResult)
            (.application (shift function) (.boundVariable 0))) :=
        inner (replacementReduces.shiftFrom 0) (depth + 1)
      rw [substituteEtaBody] at substituted
      exact .eta substituted

/-- A simultaneous η reduct of a shifted term is the shift of a simultaneous η reduct of the
term. -/
theorem ofShiftFrom : ∀ (term : Term) (cutoff : Nat) {result : Term},
    EtaSimultaneous (Term.shiftFrom cutoff term) result →
      ∃ unshifted, result = Term.shiftFrom cutoff unshifted ∧ EtaSimultaneous term unshifted
  | .boundVariable index, cutoff, result, reduces => by
      by_cases below : index < cutoff
      · simp only [Term.shiftFrom, below, ite_true] at reduces
        cases reduces
        exact ⟨.boundVariable index, by simp [Term.shiftFrom, below], .boundVariable index⟩
      · simp only [Term.shiftFrom, below, ite_false] at reduces
        cases reduces
        exact ⟨.boundVariable index, by simp [Term.shiftFrom, below], .boundVariable index⟩
  | .abstraction body, cutoff, result, reduces => by
      simp only [Term.shiftFrom] at reduces
      cases reduces with
      | abstraction bodyReduces =>
          obtain ⟨unshifted, unshiftedEqual, unshiftedReduces⟩ :=
            ofShiftFrom body (cutoff + 1) bodyReduces
          subst unshiftedEqual
          exact ⟨.abstraction unshifted, rfl, .abstraction unshiftedReduces⟩
      | eta bodyReduces =>
          obtain ⟨unshifted, unshiftedEqual, unshiftedReduces⟩ :=
            ofShiftFrom body (cutoff + 1) bodyReduces
          cases unshifted with
          | application function argument =>
              simp only [Term.shiftFrom] at unshiftedEqual
              obtain ⟨functionEqual, argumentEqual⟩ := Term.application.inj unshiftedEqual
              obtain ⟨lowered, loweredEqual, resultEqual⟩ :=
                shiftFromEqualShift cutoff functionEqual.symm
              have argumentVariable : argument = .boundVariable 0 := by
                cases argument with
                | boundVariable index =>
                    by_cases below : index < cutoff + 1
                    · simp only [Term.shiftFrom, below, ite_true] at argumentEqual
                      cases argumentEqual
                      rfl
                    · simp only [Term.shiftFrom, below, ite_false] at argumentEqual
                      cases argumentEqual
                | abstraction _ => cases argumentEqual
                | application _ _ => cases argumentEqual
                | choice _ _ => cases argumentEqual
                | parallel _ _ => cases argumentEqual
              subst loweredEqual argumentVariable resultEqual
              exact ⟨lowered, rfl, .eta unshiftedReduces⟩
          | boundVariable index =>
              by_cases below : index < cutoff + 1
              · simp only [Term.shiftFrom, below, ite_true] at unshiftedEqual
                cases unshiftedEqual
              · simp only [Term.shiftFrom, below, ite_false] at unshiftedEqual
                cases unshiftedEqual
          | abstraction _ => cases unshiftedEqual
          | choice _ _ => cases unshiftedEqual
          | parallel _ _ => cases unshiftedEqual
  | .application function argument, cutoff, result, reduces => by
      simp only [Term.shiftFrom] at reduces
      cases reduces with
      | application functionReduces argumentReduces =>
          obtain ⟨functionUnshifted, functionEqual, functionUnshiftedReduces⟩ :=
            ofShiftFrom function cutoff functionReduces
          obtain ⟨argumentUnshifted, argumentEqual, argumentUnshiftedReduces⟩ :=
            ofShiftFrom argument cutoff argumentReduces
          subst functionEqual argumentEqual
          exact ⟨.application functionUnshifted argumentUnshifted, rfl,
            .application functionUnshiftedReduces argumentUnshiftedReduces⟩
  | .choice left right, cutoff, result, reduces => by
      simp only [Term.shiftFrom] at reduces
      cases reduces with
      | choice leftReduces rightReduces =>
          obtain ⟨leftUnshifted, leftEqual, leftUnshiftedReduces⟩ :=
            ofShiftFrom left cutoff leftReduces
          obtain ⟨rightUnshifted, rightEqual, rightUnshiftedReduces⟩ :=
            ofShiftFrom right cutoff rightReduces
          subst leftEqual rightEqual
          exact ⟨.choice leftUnshifted rightUnshifted, rfl,
            .choice leftUnshiftedReduces rightUnshiftedReduces⟩
  | .parallel left right, cutoff, result, reduces => by
      simp only [Term.shiftFrom] at reduces
      cases reduces with
      | parallel leftReduces rightReduces =>
          obtain ⟨leftUnshifted, leftEqual, leftUnshiftedReduces⟩ :=
            ofShiftFrom left cutoff leftReduces
          obtain ⟨rightUnshifted, rightEqual, rightUnshiftedReduces⟩ :=
            ofShiftFrom right cutoff rightReduces
          subst leftEqual rightEqual
          exact ⟨.parallel leftUnshifted rightUnshifted, rfl,
            .parallel leftUnshiftedReduces rightUnshiftedReduces⟩

end EtaSimultaneous

/-- The complete η development: an abstraction is contracted when its developed body is the body of
an η redex. -/
def developEta : Term → Term
  | .boundVariable index => .boundVariable index
  | .abstraction body =>
      match etaContractum (developEta body) with
      | some contractum => contractum
      | none => .abstraction (developEta body)
  | .application function argument => .application (developEta function) (developEta argument)
  | .choice left right => .choice (developEta left) (developEta right)
  | .parallel left right => .parallel (developEta left) (developEta right)

/-- An application reduces by simultaneous η to an application. -/
theorem EtaSimultaneous.applicationInversion {function argument result : Term}
    (reduces : EtaSimultaneous (.application function argument) result) :
    ∃ functionResult argumentResult, result = .application functionResult argumentResult ∧
      EtaSimultaneous function functionResult ∧ EtaSimultaneous argument argumentResult := by
  cases reduces with
  | application functionReduces argumentReduces =>
      exact ⟨_, _, rfl, functionReduces, argumentReduces⟩

/-- The triangle for simultaneous η reduction. -/
theorem etaSimultaneousDevelop {term result : Term} (reduces : EtaSimultaneous term result) :
    EtaSimultaneous result (developEta term) := by
  induction reduces with
  | boundVariable index => exact .boundVariable index
  | @abstraction body bodyResult _ inner =>
      simp only [developEta]
      split
      · next contractum found =>
          obtain ⟨function, developedEqual, absent, contractumEqual⟩ :=
            etaContractumEqualSome.mp found
          subst contractumEqual
          rw [developedEqual, ← shiftLower function absent] at inner
          exact .eta inner
      · exact .abstraction inner
  | application _ _ functionInner argumentInner => exact .application functionInner argumentInner
  | choice _ _ leftInner rightInner => exact .choice leftInner rightInner
  | parallel _ _ leftInner rightInner => exact .parallel leftInner rightInner
  | @eta body function _ inner =>
      obtain ⟨functionResult, argumentResult, developedEqual, functionReduces, argumentReduces⟩ :=
        inner.applicationInversion
      cases argumentReduces
      obtain ⟨unshifted, unshiftedEqual, unshiftedReduces⟩ :=
        EtaSimultaneous.ofShiftFrom function 0 functionReduces
      subst unshiftedEqual
      simp only [developEta]
      rw [developedEqual]
      have found : etaContractum (.application (Term.shiftFrom 0 unshifted) (.boundVariable 0)) =
          some unshifted := etaContractumShift unshifted
      rw [found]
      exact unshiftedReduces

/-! ## Commutation of the two simultaneous reductions -/

/-- A simultaneous β step of the body of an η redex: the function reduces by simultaneous β to a
term that the η step can reach from every η reduct of the body, and the application of the function
closes with the contractum. -/
theorem etaBodyBetaSimultaneous {function result : Term}
    (reduces : BetaSimultaneous (.application (shift function) (.boundVariable 0)) result) :
    ∃ functionResult, BetaSimultaneous function functionResult ∧
      (∀ {body}, EtaSimultaneous body result → EtaSimultaneous (.abstraction body) functionResult) ∧
      (∀ {argument argumentResult}, BetaSimultaneous argument argumentResult →
        BetaSimultaneous (.application function argument) (instantiate result argumentResult)) := by
  have congruenceCase : ∀ {functionReduct : Term},
      BetaSimultaneous (shift function) functionReduct →
        ∃ functionResult, BetaSimultaneous function functionResult ∧
          (∀ {body}, EtaSimultaneous body (.application functionReduct (.boundVariable 0)) →
            EtaSimultaneous (.abstraction body) functionResult) ∧
          (∀ {argument argumentResult}, BetaSimultaneous argument argumentResult →
            BetaSimultaneous (.application function argument)
              (instantiate (.application functionReduct (.boundVariable 0)) argumentResult)) := by
    intro functionReduct functionReduces
    obtain ⟨unshifted, unshiftedEqual, unshiftedReduces⟩ :=
      BetaSimultaneous.ofShiftFrom function 0 functionReduces
    subst unshiftedEqual
    refine ⟨unshifted, unshiftedReduces, fun bodyReduces => .eta bodyReduces, ?_⟩
    intro argument argumentResult argumentReduces
    have contracted : instantiate (.application (Term.shiftFrom 0 unshifted) (.boundVariable 0))
        argumentResult = .application unshifted argumentResult := by
      simp only [instantiate, Term.substitute, substituteShiftFromCancel]
      simp
    rw [contracted]
    exact .application unshiftedReduces argumentReduces
  cases function with
  | abstraction inner =>
      simp only [shift, Term.shiftFrom] at reduces congruenceCase
      cases reduces with
      | application functionReduces argumentReduces =>
          cases argumentReduces
          exact congruenceCase functionReduces
      | beta bodyReduces argumentReduces =>
          cases argumentReduces
          obtain ⟨unshifted, unshiftedEqual, unshiftedReduces⟩ :=
            BetaSimultaneous.ofShiftFrom inner 1 bodyReduces
          subst unshiftedEqual
          rw [instantiateShiftFrom]
          exact ⟨.abstraction unshifted, .abstraction unshiftedReduces,
            fun bodyReduces => .abstraction bodyReduces,
            fun argumentReduces => .beta unshiftedReduces argumentReduces⟩
  | boundVariable index =>
      simp only [shift, Term.shiftFrom, Nat.not_lt_zero, ite_false] at reduces congruenceCase
      cases reduces with
      | application functionReduces argumentReduces =>
          cases argumentReduces
          exact congruenceCase functionReduces
  | application inner innerArgument =>
      cases reduces with
      | application functionReduces argumentReduces =>
          cases argumentReduces
          exact congruenceCase functionReduces
  | choice left right =>
      cases reduces with
      | application functionReduces argumentReduces =>
          cases argumentReduces
          exact congruenceCase functionReduces
  | parallel left right =>
      cases reduces with
      | application functionReduces argumentReduces =>
          cases argumentReduces
          exact congruenceCase functionReduces

/-- A simultaneous β step and a simultaneous η step of one term close in a simultaneous η step and a
simultaneous β step. -/
theorem betaEtaCommute {term betaResult : Term} (betaReduces : BetaSimultaneous term betaResult) :
    ∀ {etaResult : Term}, EtaSimultaneous term etaResult →
      ∃ joined, EtaSimultaneous betaResult joined ∧ BetaSimultaneous etaResult joined := by
  induction betaReduces with
  | boundVariable index =>
      intro etaResult etaReduces
      cases etaReduces
      exact ⟨_, .boundVariable index, .boundVariable index⟩
  | abstraction _ inner =>
      intro etaResult etaReduces
      cases etaReduces with
      | abstraction bodyReduces =>
          obtain ⟨joined, etaJoined, betaJoined⟩ := inner bodyReduces
          exact ⟨_, .abstraction etaJoined, .abstraction betaJoined⟩
      | eta bodyReduces =>
          obtain ⟨joined, etaJoined, betaJoined⟩ := inner bodyReduces
          obtain ⟨functionResult, functionReduces, etaCloses, _⟩ :=
            etaBodyBetaSimultaneous betaJoined
          exact ⟨functionResult, etaCloses etaJoined, functionReduces⟩
  | application _ _ functionInner argumentInner =>
      intro etaResult etaReduces
      cases etaReduces with
      | application functionReduces argumentReduces =>
          obtain ⟨functionJoined, functionEta, functionBeta⟩ := functionInner functionReduces
          obtain ⟨argumentJoined, argumentEta, argumentBeta⟩ := argumentInner argumentReduces
          exact ⟨_, .application functionEta argumentEta, .application functionBeta argumentBeta⟩
  | choice _ _ leftInner rightInner =>
      intro etaResult etaReduces
      cases etaReduces with
      | choice leftReduces rightReduces =>
          obtain ⟨leftJoined, leftEta, leftBeta⟩ := leftInner leftReduces
          obtain ⟨rightJoined, rightEta, rightBeta⟩ := rightInner rightReduces
          exact ⟨_, .choice leftEta rightEta, .choice leftBeta rightBeta⟩
  | parallel _ _ leftInner rightInner =>
      intro etaResult etaReduces
      cases etaReduces with
      | parallel leftReduces rightReduces =>
          obtain ⟨leftJoined, leftEta, leftBeta⟩ := leftInner leftReduces
          obtain ⟨rightJoined, rightEta, rightBeta⟩ := rightInner rightReduces
          exact ⟨_, .parallel leftEta rightEta, .parallel leftBeta rightBeta⟩
  | beta _ _ bodyInner argumentInner =>
      intro etaResult etaReduces
      cases etaReduces with
      | application functionReduces argumentReduces =>
          obtain ⟨argumentJoined, argumentEta, argumentBeta⟩ := argumentInner argumentReduces
          cases functionReduces with
          | abstraction bodyReduces =>
              obtain ⟨bodyJoined, bodyEta, bodyBeta⟩ := bodyInner bodyReduces
              exact ⟨_, bodyEta.substitute argumentEta 0, .beta bodyBeta argumentBeta⟩
          | eta bodyReduces =>
              obtain ⟨bodyJoined, bodyEta, bodyBeta⟩ := bodyInner bodyReduces
              obtain ⟨_, _, _, applicationCloses⟩ := etaBodyBetaSimultaneous bodyBeta
              exact ⟨_, bodyEta.substitute argumentEta 0, applicationCloses argumentBeta⟩

/-! ## Confluence -/

/-- One simultaneous step, of β or of η. -/
def SimultaneousStep (term result : Term) : Prop :=
  BetaSimultaneous term result ∨ EtaSimultaneous term result

/-- One simultaneous step has the diamond property. -/
theorem simultaneousStepDiamond {term first second : Term} (firstStep : SimultaneousStep term first)
    (secondStep : SimultaneousStep term second) :
    ∃ joined, SimultaneousStep first joined ∧ SimultaneousStep second joined := by
  rcases firstStep with firstBeta | firstEta <;> rcases secondStep with secondBeta | secondEta
  · exact ⟨_, .inl (betaSimultaneousDevelop firstBeta), .inl (betaSimultaneousDevelop secondBeta)⟩
  · obtain ⟨joined, firstJoined, secondJoined⟩ := betaEtaCommute firstBeta secondEta
    exact ⟨joined, .inr firstJoined, .inl secondJoined⟩
  · obtain ⟨joined, secondJoined, firstJoined⟩ := betaEtaCommute secondBeta firstEta
    exact ⟨joined, .inl firstJoined, .inr secondJoined⟩
  · exact ⟨_, .inr (etaSimultaneousDevelop firstEta), .inr (etaSimultaneousDevelop secondEta)⟩

/-- The reflexive transitive closure of `SimultaneousStep`, βη-reduction. -/
inductive ReducesMany : Term → Term → Prop where
  /-- No step. -/
  | reflexive (term : Term) : ReducesMany term term
  /-- One simultaneous step, then more. -/
  | step {first middle last : Term} :
      SimultaneousStep first middle → ReducesMany middle last → ReducesMany first last

namespace ReducesMany

/-- Transitivity. -/
theorem transitive {first middle last : Term} (firstMany : ReducesMany first middle)
    (secondMany : ReducesMany middle last) : ReducesMany first last := by
  induction firstMany with
  | reflexive _ => exact secondMany
  | step reduces _ inner => exact .step reduces (inner secondMany)

/-- A reduction lifted through a map that lifts both kinds of simultaneous step. -/
theorem lift (map : Term → Term)
    (liftBeta : ∀ {first second}, BetaSimultaneous first second →
      BetaSimultaneous (map first) (map second))
    (liftEta : ∀ {first second}, EtaSimultaneous first second →
      EtaSimultaneous (map first) (map second))
    {first last : Term} (many : ReducesMany first last) : ReducesMany (map first) (map last) := by
  induction many with
  | reflexive term => exact .reflexive _
  | step reduces _ inner =>
      rcases reduces with betaReduces | etaReduces
      · exact .step (.inl (liftBeta betaReduces)) inner
      · exact .step (.inr (liftEta etaReduces)) inner

/-- The strip lemma. -/
theorem strip {term first : Term} (reduces : SimultaneousStep term first) {second : Term}
    (many : ReducesMany term second) :
    ∃ joined, ReducesMany first joined ∧ SimultaneousStep second joined := by
  induction many generalizing first with
  | reflexive _ => exact ⟨first, .reflexive first, reduces⟩
  | step stepReduces _ inner =>
      obtain ⟨middle, firstMiddle, stepMiddle⟩ := simultaneousStepDiamond reduces stepReduces
      obtain ⟨joined, middleMany, secondReduces⟩ := inner stepMiddle
      exact ⟨joined, .step firstMiddle middleMany, secondReduces⟩

/-- βη-reduction is confluent: the Church–Rosser property of λβη. -/
theorem confluent {term first second : Term} (firstMany : ReducesMany term first)
    (secondMany : ReducesMany term second) :
    ∃ joined, ReducesMany first joined ∧ ReducesMany second joined := by
  induction firstMany generalizing second with
  | reflexive _ => exact ⟨second, secondMany, .reflexive second⟩
  | step reduces _ inner =>
      obtain ⟨stripped, middleMany, secondReduces⟩ := strip reduces secondMany
      obtain ⟨joined, firstJoined, strippedJoined⟩ := inner middleMany
      exact ⟨joined, firstJoined, .step secondReduces strippedJoined⟩

end ReducesMany

/-- βη-convertible terms reduce to a common term. -/
theorem convertibleJoinable {left right : Term} (convertible : Convertible left right) :
    ∃ joined, ReducesMany left joined ∧ ReducesMany right joined := by
  induction convertible with
  | reflexive term => exact ⟨term, .reflexive _, .reflexive _⟩
  | symmetric _ inner =>
      obtain ⟨joined, leftMany, rightMany⟩ := inner
      exact ⟨joined, rightMany, leftMany⟩
  | transitive _ _ leftInner rightInner =>
      obtain ⟨leftJoined, leftMany, middleMany⟩ := leftInner
      obtain ⟨rightJoined, middleRightMany, rightMany⟩ := rightInner
      obtain ⟨joined, leftJoinedMany, rightJoinedMany⟩ :=
        ReducesMany.confluent middleMany middleRightMany
      exact ⟨joined, leftMany.transitive leftJoinedMany, rightMany.transitive rightJoinedMany⟩
  | abstraction _ inner =>
      obtain ⟨joined, leftMany, rightMany⟩ := inner
      exact ⟨_, ReducesMany.lift Term.abstraction (fun reduces => .abstraction reduces)
          (fun reduces => .abstraction reduces) leftMany,
        ReducesMany.lift Term.abstraction (fun reduces => .abstraction reduces)
          (fun reduces => .abstraction reduces) rightMany⟩
  | @application function functionOther argument argumentOther _ _ functionInner argumentInner =>
      obtain ⟨functionJoined, functionMany, functionOtherMany⟩ := functionInner
      obtain ⟨argumentJoined, argumentMany, argumentOtherMany⟩ := argumentInner
      have liftFunction : ∀ (argumentTerm : Term) {first last : Term}, ReducesMany first last →
          ReducesMany (.application first argumentTerm) (.application last argumentTerm) :=
        fun argumentTerm _ _ many => ReducesMany.lift (fun term => .application term argumentTerm)
          (fun reduces => .application reduces (BetaSimultaneous.reflexive argumentTerm))
          (fun reduces => .application reduces (EtaSimultaneous.reflexive argumentTerm)) many
      have liftArgument : ∀ (functionTerm : Term) {first last : Term}, ReducesMany first last →
          ReducesMany (.application functionTerm first) (.application functionTerm last) :=
        fun functionTerm _ _ many => ReducesMany.lift (fun term => .application functionTerm term)
          (fun reduces => .application (BetaSimultaneous.reflexive functionTerm) reduces)
          (fun reduces => .application (EtaSimultaneous.reflexive functionTerm) reduces) many
      exact ⟨.application functionJoined argumentJoined,
        (liftFunction argument functionMany).transitive (liftArgument functionJoined argumentMany),
        (liftFunction argumentOther functionOtherMany).transitive
          (liftArgument functionJoined argumentOtherMany)⟩
  | beta body argument =>
      exact ⟨_, .step (.inl (.beta (BetaSimultaneous.reflexive body)
        (BetaSimultaneous.reflexive argument))) (.reflexive _), .reflexive _⟩
  | eta function =>
      exact ⟨_, .step (.inr (.eta (EtaSimultaneous.reflexive _))) (.reflexive _), .reflexive _⟩

/-- λx.λy. x reduces only to itself. -/
theorem firstReducesOnlyToItself {result : Term} (many : ReducesMany first result) :
    result = first := by
  have stepKeeps : ∀ {next}, SimultaneousStep first next → next = first := by
    intro next reduces
    rcases reduces with betaReduces | etaReduces
    · simp only [first] at betaReduces
      cases betaReduces with
      | abstraction inner =>
          cases inner with
          | abstraction innermost => cases innermost; rfl
    · simp only [first] at etaReduces
      cases etaReduces with
      | abstraction inner =>
          cases inner with
          | abstraction innermost => cases innermost; rfl
          | eta innermost => cases innermost
      | eta inner =>
          cases inner with
          | eta innermost => cases innermost
  generalize firstEqual : first = start at many
  induction many with
  | reflexive _ => rfl
  | step reduces _ inner =>
      subst firstEqual
      have nextEqual := stepKeeps reduces
      subst nextEqual
      exact inner rfl

/-- λx.λy. y reduces only to itself. -/
theorem secondReducesOnlyToItself {result : Term} (many : ReducesMany second result) :
    result = second := by
  have stepKeeps : ∀ {next}, SimultaneousStep second next → next = second := by
    intro next reduces
    rcases reduces with betaReduces | etaReduces
    · simp only [second] at betaReduces
      cases betaReduces with
      | abstraction inner =>
          cases inner with
          | abstraction innermost => cases innermost; rfl
    · simp only [second] at etaReduces
      cases etaReduces with
      | abstraction inner =>
          cases inner with
          | abstraction innermost => cases innermost; rfl
          | eta innermost => cases innermost
      | eta inner =>
          cases inner with
          | eta innermost => cases innermost
  generalize secondEqual : second = start at many
  induction many with
  | reflexive _ => rfl
  | step reduces _ inner =>
      subst secondEqual
      have nextEqual := stepKeeps reduces
      subst nextEqual
      exact inner rfl

/-- λβη does not convert λx.λy. x to λx.λy. y. -/
theorem firstNotConvertibleSecond : ¬ Convertible first second := by
  intro convertible
  obtain ⟨joined, firstMany, secondMany⟩ := convertibleJoinable convertible
  have firstEqual := firstReducesOnlyToItself firstMany
  have secondEqual := secondReducesOnlyToItself secondMany
  rw [firstEqual] at secondEqual
  simp [first, second] at secondEqual

end LambdaJit.BetaEtaConfluence
