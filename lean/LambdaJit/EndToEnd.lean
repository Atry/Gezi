import LambdaJit.Interpretation
import LambdaJit.BetaConversion
import LambdaJit.ParallelTypesTheorems
import LambdaJit.ContextualPreorderUnconditional
import LambdaJit.LatticeEtaConsistency

/-!
# The end-to-end theorem: an accepted article's exported equation is a contextual equivalence

Design decision D6 (on the encoding of D7; `lean/README.md`, "Design decisions"): when the article reader accepts a text and every
equation of its import set is sound, every exported equation is sound, sound meaning that its
two sides are contextually equivalent, M ≃_O N of DdLP96's Definition 14
(`ContextualPreorder.ContextualEquivalence`), the primary definition of the semantics. The user,
2026-11-09: "我的意思是每个rewrite的正确性必须用定义14来证明。NF◇、⊢ 和 D∞都是证明定义14可靠的手段。"
NF◇ and ⊢ are means of proof here: an import equation is shown sound through its derivation in
⊢_{λ-lattice-η} (`ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta`), and for closed
sides, ≃_O gives the same consistent normal forms in every closed context
(`ContextualPreorder.consistentNormalFormLatticeEtaIffContextualPreorder`).

- `EquationSound signature left right`: for every valuation of the HOL variables by terms of the
  calculus, the interpretations of the two sides (module `Interpretation`), their thunk constants
  read under `signature` (D7.1), are contextually equivalent. An
  instance of an equation is an assignment of terms of the calculus to its variables, so this is
  the soundness of a lemma L = R, ∀σ: Lσ ≃_O Rσ, read on the article's terms; ≃_O being a
  congruence, it gives C[Lσ] ≃_O C[Rσ] for every context C. A partial application, which the
  congruence of `Article.Derivable` relates like any term, is read by its curried form.
- `endToEnd`: an accepted text whose import equations are all sound has sound exported equations.
  The proof is an induction on `Article.Derivable`, through `Article.readArticle_sound`: ≃_O is an
  equivalence relation and a congruence for application, and the interpretation of an instance
  is the interpretation under the valuation of the instantiation.
- `endToEndRead`, the corollary for exported sides that read as terms of the calculus (the reading
  ⟦·⟧ of D10, `Interpretation.read`): the two readings are contextually equivalent.

The import set of an article written by `com.yang_bo.gezi.proofs.OpentheoryArticle` has five kinds of
equations; `importChecked` recognises those of the first four kinds and takes those of the fifth
from a list of statements the caller proves sound:

- the numbered equations (1) to (6) and (8) to (10), sound for every instance
  (`numberedEquationSound`): each is derivable in ⊢_{λ-lattice-η} (module
  `LatticeEtaDerivability`), (1), (3), (5) and (10) as its axioms and the other five as its
  theorems, and its derivable equations are contextual equivalences
  (`ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta`);
- for each thunk constant, its equation of the defunctionalized β rule, filling one hole
  (`fillEquationSound`) or, with no hole left, instantiating the code (`bodyEquationSound`), and,
  for a code `apply(slot(F), slot(H))` with the one hole H, its equation of the defunctionalized η
  rule (`etaEquationSound`): sound for every thunk constant and every list of fillings, by the β
  rule and the η rule on the thunk's interpretation (module `Readback`). They need no
  well-formedness of the thunk (`Readback.DistinctSlots`, `Readback.NoClamping`): the
  interpretation reads every thunk, and only the number of fillings must be the constant's;
- for a thunk constant with holes that is not the front end's spelling, its respelling equation,
  the constant equal to the constant of its spelling applied to instances of codes over its
  fillings (`respellCheckedDerivable`): sound when the two thunks interpret as one term under
  bound variables in place of the fillings, checked on the terms, by one β step per filling on
  each side;
- for a union the e-graph made by β conversion, its conversion equation between two closed terms
  (`conversionCheckedDerivable`): sound when the left reading reduces to the right by β steps, a
  step taken anywhere, found by the search `Semantics.betaReduces` (module `BetaConversion`);
- the statements of the lemmas a derivation uses. A `Statement` carries its own signature,
  numbered from 0, so an import is recognised as a statement when the two agree under their two
  signatures (`Interpretation.agree`, `Statement.importedSound`), not by literal equality.

`endToEndOfChecked` combines them: an accepted text whose definitions give the signature, whose
import equations `importChecked` accepts, and whose one exported equation is `left = right`, makes
`left = right` sound under that signature.
-/

namespace LambdaJit.EndToEnd

open LambdaJit.Semantics (Context DerivableLatticeEta)
open LambdaJit.ContextualPreorder (ContextualEquivalence contextualEquivalenceOfDerivableLatticeEta)
open LambdaJit.Interpretation
open LambdaJit.Readback (thunkTerm interpretCode interpretCodeList finalSlots abstractions
  readSlot)

/-! ## Sound equations and the end-to-end theorem

Every statement below reads the thunk constants of its terms under one signature (D7.1): the
signature of the article's definitions, or a statement's own. -/

variable {signature : Signature}

/-- An equation between two article terms is sound under a signature: for every valuation of its
variables by terms of the calculus, its two sides are interpreted as contextually equivalent
terms, ≃_O of DdLP96's Definition 14. -/
def EquationSound (signature : Signature) (left right : Article.Term) : Prop :=
  ∀ valuation : Valuation,
    ContextualEquivalence (interpret signature valuation left) (interpret signature valuation right)

/-- An equation whose interpretations ⊢_{λ-lattice-η} derives from no hypothesis, under every
valuation, is sound (`ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta`). -/
theorem equationSoundOfDerivable {left right : Article.Term}
    (derivable : ∀ valuation : Valuation,
      DerivableLatticeEta (fun _ _ => False) (interpret signature valuation left) (interpret signature valuation right)) :
    EquationSound signature left right :=
  fun valuation => contextualEquivalenceOfDerivableLatticeEta (derivable valuation)

/-- An equation whose interpretations ⊢_{λ-lattice-η} derives from no hypothesis, under every
valuation: the numbered equations, the equations of the defunctionalized β rule and η rule,
and the lemmas that module `StatementNormalisation` and module `LibraryLemmaProofs` derive. -/
def EquationDerivable (signature : Signature) (left right : Article.Term) : Prop :=
  ∀ valuation : Valuation,
    DerivableLatticeEta (fun _ _ => False) (interpret signature valuation left) (interpret signature valuation right)

/-- Every equation `Article.Derivable` derives from sound import equations is sound, by
induction on the derivation. -/
theorem derivableSound {imports : List (Article.Term × Article.Term)}
    (importsSound : ∀ equation ∈ imports, EquationSound signature equation.1 equation.2)
    {left right : Article.Term} (derivable : Article.Derivable imports left right) :
    EquationSound signature left right := by
  induction derivable with
  | importInstance instantiation member =>
      intro valuation
      rw [interpretInstantiate, interpretInstantiate]
      exact importsSound _ member _
  | reflexivity term => exact fun _ => ContextualEquivalence.reflexive _
  | symmetry _ inner => exact fun valuation => (inner valuation).symmetric
  | transitivity _ _ first second =>
      exact fun valuation => (first valuation).transitive (second valuation)
  | congruence _ _ functions arguments =>
      exact fun valuation =>
        ContextualEquivalence.application (functions valuation) (arguments valuation)

/-- The end-to-end theorem: when the reader accepts `text` and every equation of the import set is
sound, every exported theorem is an equation `left = right` that is sound. Soundness here is
`EquationSound`, a statement under `Interpretation.interpret`, where a constant that is no operator
and no thunk constant reads as `Interpretation.unknownLiteral`; the meaning on the readings of IR
terms is carried
only by `endToEndRead` and `contextualEquivalenceOfRead`. -/
theorem endToEnd {text : String} {theory : Article.Theory}
    (accepted : Article.readArticle text = .ok theory)
    (importsSound : ∀ equation ∈ Article.importEquations theory.assumptions,
      EquationSound signature equation.1 equation.2) :
    ∀ exported ∈ theory.theorems, ∃ sideType left right,
      exported.conclusion = .equation sideType left right ∧ EquationSound signature left right := by
  intro exported member
  obtain ⟨_, sideType, left, right, isEquation, derivable⟩ :=
    (Article.readArticle_sound accepted).1 exported member
  exact ⟨sideType, left, right, isEquation, derivableSound importsSound derivable⟩

/-- A sound equation whose sides read as terms of the calculus: the two readings are contextually
equivalent. Soundness holds under every valuation, and the proof takes the one that reads every
variable as Ω; any valuation would do: a side with a reading has no variable (`readApplied` has
none for one), so its interpretation is the same under every valuation (`readDerivable`). -/
theorem contextualEquivalenceOfRead {left right : Article.Term}
    {leftTerm rightTerm : Semantics.Term} (sound : EquationSound signature left right)
    (leftRead : read signature left = some leftTerm)
    (rightRead : read signature right = some rightTerm) :
    ContextualEquivalence leftTerm rightTerm := by
  let valuation : Valuation := fun _ _ => Semantics.Omega
  have leftEqual : ContextualEquivalence (interpret signature valuation left) leftTerm :=
    contextualEquivalenceOfDerivableLatticeEta (readDerivable signature valuation leftRead)
  have rightEqual : ContextualEquivalence (interpret signature valuation right) rightTerm :=
    contextualEquivalenceOfDerivableLatticeEta (readDerivable signature valuation rightRead)
  exact leftEqual.symmetric.transitive ((sound valuation).transitive rightEqual)

/-- The corollary for exported sides that read as terms of the calculus: when the reader accepts
`text`, every import equation is sound, and an exported theorem is `left = right` with readings
⟦left⟧ and ⟦right⟧, then ⟦left⟧ ≃_O ⟦right⟧. -/
theorem endToEndRead {text : String} {theory : Article.Theory}
    (accepted : Article.readArticle text = .ok theory)
    (importsSound : ∀ equation ∈ Article.importEquations theory.assumptions,
      EquationSound signature equation.1 equation.2)
    {exported : Article.Sequent} (member : exported ∈ theory.theorems)
    {sideType : Article.LogicType} {left right : Article.Term}
    (isEquation : exported.conclusion = .equation sideType left right)
    {leftTerm rightTerm : Semantics.Term}
    (leftRead : read signature left = some leftTerm)
    (rightRead : read signature right = some rightTerm) :
    ContextualEquivalence leftTerm rightTerm := by
  obtain ⟨_, otherLeft, otherRight, otherEquation, sound⟩ :=
    endToEnd accepted importsSound exported member
  rw [isEquation] at otherEquation
  simp only [Article.Term.equation, Article.Term.application.injEq] at otherEquation
  obtain ⟨⟨_, leftSame⟩, rightSame⟩ := otherEquation
  rw [← leftSame, ← rightSame] at sound
  exact contextualEquivalenceOfRead sound leftRead rightRead

/-! ## The terms of the encoding -/

/-- The type `LambdaJit.term`. -/
def termType : Article.LogicType := .operator ⟨["LambdaJit"], "term"⟩ []

/-- The type `term → term → term` of `LambdaJit.apply`, `LambdaJit.choice` and
`LambdaJit.parallel`. -/
def binaryType : Article.LogicType := .arrow termType (.arrow termType termType)

/-- `LambdaJit.apply function argument`. -/
def applyTerm (function argument : Article.Term) : Article.Term :=
  .application (.application (.constant applyName binaryType) function) argument

/-- `LambdaJit.choice left right`. -/
def choiceTerm (left right : Article.Term) : Article.Term :=
  .application (.application (.constant choiceName binaryType) left) right

/-- `LambdaJit.parallel left right`. -/
def parallelTerm (left right : Article.Term) : Article.Term :=
  .application (.application (.constant parallelName binaryType) left) right

/-- The variable of type `LambdaJit.term` named `name` in the global namespace. -/
def termVariable (name : String) : Article.Term := .termVariable ⟨[], name⟩ termType

variable {hypotheses : Semantics.Term → Semantics.Term → Prop}

theorem operatorOfApply : operatorOf signature applyName = .apply := by
  simp [operatorOf]

theorem operatorOfChoice : operatorOf signature choiceName = .choice := by
  simp [operatorOf, applyName, choiceName]

theorem operatorOfParallel : operatorOf signature parallelName = .parallel := by
  simp [operatorOf, applyName, choiceName, parallelName]

/-- The application `LambdaJit.apply F X` is interpreted as the application of the calculus. -/
theorem interpretApply (valuation : Valuation) (type : Article.LogicType)
    (function argument : Article.Term) :
    DerivableLatticeEta hypotheses
      (interpret signature valuation
        (.application (.application (.constant applyName type) function) argument))
      (.application (interpret signature valuation function) (interpret signature valuation argument)) := by
  have applied := curriedApplied (hypotheses := hypotheses) .apply
    [interpret signature valuation function, interpret signature valuation argument] rfl
  simp only [interpret, operatorOfApply]
  exact applied

theorem interpretChoice (valuation : Valuation) (type : Article.LogicType)
    (left right : Article.Term) :
    DerivableLatticeEta hypotheses
      (interpret signature valuation (.application (.application (.constant choiceName type) left) right))
      (.choice (interpret signature valuation left) (interpret signature valuation right)) := by
  have applied := curriedApplied (hypotheses := hypotheses) .choice
    [interpret signature valuation left, interpret signature valuation right] rfl
  simp only [interpret, operatorOfChoice]
  exact applied

theorem interpretParallel (valuation : Valuation) (type : Article.LogicType)
    (left right : Article.Term) :
    DerivableLatticeEta hypotheses
      (interpret signature valuation
        (.application (.application (.constant parallelName type) left) right))
      (.parallel (interpret signature valuation left) (interpret signature valuation right)) := by
  have applied := curriedApplied (hypotheses := hypotheses) .parallel
    [interpret signature valuation left, interpret signature valuation right] rfl
  simp only [interpret, operatorOfParallel]
  exact applied

/-! ## The numbered equations (1) to (6) and (8) to (10) -/

/-- The numbered equation `number` of the formal definition over the terms `first`, `second`,
`third`, `argument` and `addition`, written as the writer's `set_equation/3` writes it with the
variables M, N, P, A and B: (1) M + N = N + M, (2) (M + N) + P = M + (N + P), (3) M ∥ N = N ∥ M,
(4) (M ∥ N) ∥ P = M ∥ (N ∥ P), (5) M ∥ (M + N) = M, (6) M + (M ∥ N) = M,
(8) (M + N) P = M P + N P, (9) (M ∥ N) P = M P ∥ N P, (10) M A + M (A + B) = M (A + B). The
numbers are names; any other number, 7 included, gives M = M. -/
def numberedEquation (number : Nat) (first second third argument addition : Article.Term) :
    Article.Term × Article.Term :=
  match number with
  | 1 => (choiceTerm first second, choiceTerm second first)
  | 2 => (choiceTerm (choiceTerm first second) third, choiceTerm first (choiceTerm second third))
  | 3 => (parallelTerm first second, parallelTerm second first)
  | 4 =>
      (parallelTerm (parallelTerm first second) third,
        parallelTerm first (parallelTerm second third))
  | 5 => (parallelTerm first (choiceTerm first second), first)
  | 6 => (choiceTerm first (parallelTerm first second), first)
  | 8 =>
      (applyTerm (choiceTerm first second) third,
        choiceTerm (applyTerm first third) (applyTerm second third))
  | 9 =>
      (applyTerm (parallelTerm first second) third,
        parallelTerm (applyTerm first third) (applyTerm second third))
  | 10 =>
      (choiceTerm (applyTerm first argument) (applyTerm first (choiceTerm argument addition)),
        applyTerm first (choiceTerm argument addition))
  | _ => (first, first)

/-- Every instance of every numbered equation is an axiom or a theorem of ⊢_{λ-lattice-η}
(`Semantics.DerivableLatticeEta`) on the interpretations of its sides. -/
theorem numberedEquationDerivable (number : Nat)
    (first second third argument addition : Article.Term) :
    EquationDerivable signature (numberedEquation number first second third argument addition).1
      (numberedEquation number first second third argument addition).2 := by
  intro valuation
  -- The interpretations of the three operators of the encoding, as the calculus's terms.
  have choiceOf := fun (left right : Article.Term) =>
    interpretChoice (signature := signature) (hypotheses := fun _ _ => False) valuation binaryType
      left right
  have parallelOf := fun (left right : Article.Term) =>
    interpretParallel (signature := signature) (hypotheses := fun _ _ => False) valuation
      binaryType left right
  have applyOf := fun (function argumentTerm : Article.Term) =>
    interpretApply (signature := signature) (hypotheses := fun _ _ => False) valuation binaryType
      function argumentTerm
  match number with
  | 0 => exact .reflexive _
  | 1 =>
      exact .transitive (choiceOf first second)
        (.transitive (.choiceCommutative _ _) (.symmetric (choiceOf second first)))
  | 2 =>
      exact .transitive (choiceOf (choiceTerm first second) third)
        (.transitive (.congruenceChoiceLeft _ (choiceOf first second))
          (.transitive (.choiceAssociative _ _ _)
            (.symmetric (.transitive (choiceOf first (choiceTerm second third))
              (.congruenceChoiceRight _ (choiceOf second third))))))
  | 3 =>
      exact .transitive (parallelOf first second)
        (.transitive (.parallelCommutative _ _) (.symmetric (parallelOf second first)))
  | 4 =>
      exact .transitive (parallelOf (parallelTerm first second) third)
        (.transitive (.congruenceParallelLeft _ (parallelOf first second))
          (.transitive (.parallelAssociative _ _ _)
            (.symmetric (.transitive (parallelOf first (parallelTerm second third))
              (.congruenceParallelRight _ (parallelOf second third))))))
  | 5 =>
      exact .transitive (parallelOf first (choiceTerm first second))
        (.transitive (.congruenceParallelRight _ (choiceOf first second))
          (.parallelAbsorption _ _))
  | 6 =>
      exact .transitive (choiceOf first (parallelTerm first second))
        (.transitive (.congruenceChoiceRight _ (parallelOf first second))
          (.choiceAbsorption _ _))
  | 7 => exact .reflexive _
  | 8 =>
      exact .transitive (applyOf (choiceTerm first second) third)
        (.transitive (.congruenceFunction _ (choiceOf first second))
          (.transitive (.choiceFunctionDistributive _ _ _)
            (.symmetric (.transitive (choiceOf (applyTerm first third) (applyTerm second third))
              (DerivableLatticeEta.congruenceChoice (applyOf first third) (applyOf second third))))))
  | 9 =>
      exact .transitive (applyOf (parallelTerm first second) third)
        (.transitive (.congruenceFunction _ (parallelOf first second))
          (.transitive (.parallelFunctionDistributive _ _ _)
            (.symmetric
              (.transitive (parallelOf (applyTerm first third) (applyTerm second third))
                (.transitive (.congruenceParallelLeft _ (applyOf first third))
                  (.congruenceParallelRight _ (applyOf second third)))))))
  | 10 =>
      have sum := choiceOf argument addition
      have applied :
          DerivableLatticeEta (fun _ _ => False)
            (interpret signature valuation (applyTerm first (choiceTerm argument addition)))
            (.application (interpret signature valuation first)
              (.choice (interpret signature valuation argument) (interpret signature valuation addition))) :=
        .transitive (applyOf first (choiceTerm argument addition))
          (.congruenceArgument _ sum)
      exact .transitive
        (choiceOf (applyTerm first argument) (applyTerm first (choiceTerm argument addition)))
        (.transitive (DerivableLatticeEta.congruenceChoice (applyOf first argument) applied)
          (.transitive (.argumentMonotone _ _ _) (.symmetric applied)))
  | _ + 11 => exact .reflexive _

/-- Every instance of every numbered equation is sound (`numberedEquationDerivable`). -/
theorem numberedEquationSound (number : Nat)
    (first second third argument addition : Article.Term) :
    EquationSound signature (numberedEquation number first second third argument addition).1
      (numberedEquation number first second third argument addition).2 :=
  equationSoundOfDerivable
    (numberedEquationDerivable number first second third argument addition)

/-! ## The equations of the defunctionalized β rule and η rule -/

/-- The first clause of the defunctionalized β rule on the interpretation of a thunk, for any
slot values: the thunk with first hole `hole` applied to `argument` is one β step from the thunk
whose fills put `argument` in at that hole (the step `Readback.interpretationBetaFill` takes on
finite terms). -/
theorem thunkTermBetaFill (code : Code) (hole : Hole) (holes : List Hole)
    (values : List Semantics.Term) (argument : Semantics.Term) :
    DerivableLatticeEta hypotheses (.application (thunkTerm code (hole :: holes) values) argument)
      (thunkTerm code holes (fill hole holes values argument)) := by
  have variableReplaced :
      Semantics.Term.substitute 0 argument (.boundVariable 0) = argument := by
    simp [Semantics.Term.substitute]
  have contracted : Semantics.Term.instantiate
      (thunkTerm code holes (fill hole holes (values.map Semantics.Term.shift) (.boundVariable 0)))
      argument = thunkTerm code holes (fill hole holes values argument) := by
    simp only [Semantics.Term.instantiate, Readback.thunkTermSubstitute, map_fill,
      Readback.substituteShiftedList, variableReplaced]
  rw [← contracted]
  exact .beta _ _

/-- The defunctionalized η rule on the interpretation of a thunk, for any slot values: the thunk
of code `apply (slot function) (slot hole)` with the one hole `hole` is the η redex
λx. (shift F) x, F the value at the position of slot `function` among the filled slots (the
statement `Readback.interpretationEta` makes on finite terms). -/
theorem thunkTermEta {function hole : Nat} {values : List Semantics.Term}
    {value : Semantics.Term} (distinct : function ≠ hole)
    (found : values[fillingPosition [.slot hole] function]? = some value) :
    thunkTerm (.apply (.slot function) (.slot hole)) [.slot hole] values =
      .abstraction (.application (Semantics.Term.shift value) (.boundVariable 0)) := by
  have shiftedFound : (values.map Semantics.Term.shift)[
      if function < hole then function else function - 1]? =
        some (Semantics.Term.shift value) := by
    rw [← Readback.fillingPositionSingleton distinct]
    simp [found]
  simp only [thunkTerm, finalSlots, List.length_singleton, abstractions, interpretCode, fill,
    Readback.fillingPositionNil, Readback.readSlotInserted,
    Readback.readSlotBesideInserted _ hole function _ _ distinct shiftedFound]

/-- Every slot value of a thunk replaced by an equal one: a chain of
`Readback.thunkTermCongruence`. -/
theorem thunkTermPointwise (code : Code) (holes : List Hole) :
    ∀ (before lefts rights : List Semantics.Term), Pointwise (DerivableLatticeEta hypotheses) lefts rights →
      DerivableLatticeEta hypotheses (thunkTerm code holes (before ++ lefts))
        (thunkTerm code holes (before ++ rights))
  | _, [], [], _ => .reflexive _
  | before, left :: lefts, right :: rights, ⟨headEqual, tailEqual⟩ => by
      have rest := thunkTermPointwise code holes (before ++ [right]) lefts rights tailEqual
      simp only [List.append_assoc, List.singleton_append] at rest
      exact .transitive (Readback.thunkTermCongruence code holes before lefts headEqual) rest
  | _, [], _ :: _, holds => holds.elim
  | _, _ :: _, [], holds => holds.elim

/-- The equation of the defunctionalized β rule that fills the first hole of a thunk constant is
derivable, for every thunk constant and every list of fillings: `LambdaJit.apply (c f₀ … fₖ₋₁) a`
equals `c′` applied to the fillings with `a` put in at the hole (`fill`), where `c` is the
constant of `code` with the holes `hole :: holes` and `c′` the constant of `code` with `holes`,
each applied to as many fillings as it takes. The writer's equation is the instance whose
fillings and argument are distinct variables. -/
theorem fillEquationDerivable {applyType firstType secondType : Article.LogicType}
    {firstName secondName : Article.Name} {code : Code} {hole : Hole} {holes : List Hole}
    (firstOperator : operatorOf signature firstName = .thunk code (hole :: holes))
    (secondOperator : operatorOf signature secondName = .thunk code holes)
    (fillings : List Article.Term) (argument : Article.Term)
    (firstArity : fillings.length = thunkArity code (hole :: holes))
    (secondArity : (fill hole holes fillings argument).length = thunkArity code holes) :
    EquationDerivable signature
      (.application (.application (.constant applyName applyType)
        (applyArguments (.constant firstName firstType) fillings)) argument)
      (applyArguments (.constant secondName secondType) (fill hole holes fillings argument)) := by
  intro valuation
  have firstApplied : DerivableLatticeEta (fun _ _ => False)
      (interpret signature valuation (applyArguments (.constant firstName firstType) fillings))
      (thunkTerm code (hole :: holes) (fillings.map (interpret signature valuation))) := by
    rw [interpretApplyArguments]
    have applied := curriedApplied (hypotheses := fun _ _ => False)
      (.thunk code (hole :: holes)) (fillings.map (interpret signature valuation))
      (by rw [List.length_map]; exact firstArity)
    simp only [interpret, firstOperator]
    exact applied
  have secondApplied : DerivableLatticeEta (fun _ _ => False)
      (interpret signature valuation
        (applyArguments (.constant secondName secondType) (fill hole holes fillings argument)))
      (thunkTerm code holes
        (fill hole holes (fillings.map (interpret signature valuation)) (interpret signature valuation argument))) := by
    rw [interpretApplyArguments, map_fill]
    have applied := curriedApplied (hypotheses := fun _ _ => False) (.thunk code holes)
      (fill hole holes (fillings.map (interpret signature valuation)) (interpret signature valuation argument))
      (by rw [← map_fill, List.length_map]; exact secondArity)
    simp only [interpret, secondOperator]
    exact applied
  exact .transitive (interpretApply valuation applyType _ argument)
    (.transitive (.congruenceFunction _ firstApplied)
      (.transitive (thunkTermBetaFill code hole holes _ _) (.symmetric secondApplied)))

/-- The equation of the defunctionalized β rule that fills the first hole of a thunk constant is
sound (`fillEquationDerivable`). -/
theorem fillEquationSound {applyType firstType secondType : Article.LogicType}
    {firstName secondName : Article.Name} {code : Code} {hole : Hole} {holes : List Hole}
    (firstOperator : operatorOf signature firstName = .thunk code (hole :: holes))
    (secondOperator : operatorOf signature secondName = .thunk code holes)
    (fillings : List Article.Term) (argument : Article.Term)
    (firstArity : fillings.length = thunkArity code (hole :: holes))
    (secondArity : (fill hole holes fillings argument).length = thunkArity code holes) :
    EquationSound signature
      (.application (.application (.constant applyName applyType)
        (applyArguments (.constant firstName firstType) fillings)) argument)
      (applyArguments (.constant secondName secondType) (fill hole holes fillings argument)) :=
  equationSoundOfDerivable
    (fillEquationDerivable firstOperator secondOperator fillings argument firstArity secondArity)

/-- The equation of the defunctionalized η rule of a thunk constant is derivable: `c f = f`,
where `c` is the constant of the code `apply (slot function) (slot hole)` with the one hole
`hole`, `function` another slot whose position among the filled slots is the first, and `c` takes
one filling. -/
theorem etaEquationDerivable {type : Article.LogicType} {name : Article.Name} {function hole : Nat}
    (operator : operatorOf signature name = .thunk (.apply (.slot function) (.slot hole)) [.slot hole])
    (distinct : function ≠ hole) (position : fillingPosition [.slot hole] function = 0)
    (arity : thunkArity (.apply (.slot function) (.slot hole)) [.slot hole] = 1)
    (filling : Article.Term) :
    EquationDerivable signature (.application (.constant name type) filling) filling := by
  intro valuation
  have applied := curriedApplied (hypotheses := fun _ _ => False)
    (.thunk (.apply (.slot function) (.slot hole)) [.slot hole]) [interpret signature valuation filling]
    arity.symm
  have found : [interpret signature valuation filling][fillingPosition [.slot hole] function]? =
      some (interpret signature valuation filling) := by
    rw [position]
    rfl
  have redex := thunkTermEta distinct found
  simp only [interpret, operator]
  exact .transitive applied (by
    show DerivableLatticeEta _ (thunkTerm _ _ _) _
    rw [redex]
    exact .eta _)

/-- The equation of the defunctionalized η rule of a thunk constant is sound
(`etaEquationDerivable`). -/
theorem etaEquationSound {type : Article.LogicType} {name : Article.Name} {function hole : Nat}
    (operator : operatorOf signature name = .thunk (.apply (.slot function) (.slot hole)) [.slot hole])
    (distinct : function ≠ hole) (position : fillingPosition [.slot hole] function = 0)
    (arity : thunkArity (.apply (.slot function) (.slot hole)) [.slot hole] = 1)
    (filling : Article.Term) :
    EquationSound signature (.application (.constant name type) filling) filling :=
  equationSoundOfDerivable (etaEquationDerivable (type := type) operator distinct position arity filling)

/-! ## The equation of the defunctionalized β rule that instantiates a code -/

mutual
/-- Whether `term` is the encoding of the instance of `code` with slot `i` read as the element `i`
of `fillings`: the writer's `code_instance/3` written out, a slot as its filling, `apply`,
`parallel` and a choice as their constants, and a nested thunk as the thunk constant of its code and holes applied
to the instances of its fillings, as many as the constant takes, under the signature. -/
def codeInstanceMatches (signature : Signature) (fillings : List Article.Term) :
    Code → Article.Term → Bool
  | .slot index, term =>
      match fillings[index]? with
      | some filling => filling == term
      | none => false
  | .apply function argument, term =>
      match term with
      | .application (.application (.constant name _) functionTerm) argumentTerm =>
          name == applyName && codeInstanceMatches signature fillings function functionTerm &&
            codeInstanceMatches signature fillings argument argumentTerm
      | _ => false
  | .thunk code holes codes, term =>
      match spine term with
      | (.constant name _, arguments) =>
          match operatorOf signature name with
          | .thunk otherCode otherHoles =>
              otherCode.equal code && otherHoles == holes &&
                arguments.length == thunkArity code holes &&
                codeInstanceListMatches signature fillings codes arguments
          | _ => false
      | _ => false
  | .choice left right, term =>
      match term with
      | .application (.application (.constant name _) leftTerm) rightTerm =>
          name == choiceName && codeInstanceMatches signature fillings left leftTerm &&
            codeInstanceMatches signature fillings right rightTerm
      | _ => false
  | .parallel left right, term =>
      match term with
      | .application (.application (.constant name _) leftTerm) rightTerm =>
          name == parallelName && codeInstanceMatches signature fillings left leftTerm &&
            codeInstanceMatches signature fillings right rightTerm
      | _ => false

/-- `codeInstanceMatches` on the codes and the terms of two lists of one length, pairwise. -/
def codeInstanceListMatches (signature : Signature) (fillings : List Article.Term) :
    List Code → List Article.Term → Bool
  | [], [] => true
  | code :: codes, term :: terms =>
      codeInstanceMatches signature fillings code term && codeInstanceListMatches signature fillings codes terms
  | _, _ => false
end

/-- A code whose instance `codeInstanceMatches` may take `term` for, applied to the codes
`arguments` of the terms the term is applied to so far: a term equal to the filling at position
`i`, applied to nothing, is slot `i`; an application collects its argument's code; a constant is
its operator over the codes collected, a thunk constant the thunk of its code and holes over them.
Nothing is proved of it: `respellChecked` checks its answer with `codeInstanceListMatches`. -/
def instanceCode (signature : Signature) (fillings : List Article.Term) (term : Article.Term)
    (arguments : List Code) : Option Code :=
  match arguments, fillings.findIdx? (· == term) with
  | [], some index => some (.slot index)
  | _, _ =>
      match term with
      | .application function argument =>
          match instanceCode signature fillings argument [] with
          | some argumentCode => instanceCode signature fillings function (argumentCode :: arguments)
          | none => none
      | .constant name _ =>
          match operatorOf signature name, arguments with
          | .apply, [function, argument] => some (.apply function argument)
          | .choice, [left, right] => some (.choice left right)
          | .parallel, [left, right] => some (.parallel left right)
          | .thunk code holes, codes => some (.thunk code holes codes)
          | _, _ => none
      | _ => none

mutual
/-- A term that `codeInstanceMatches` accepts is interpreted as the code's interpretation under
the interpretations of the fillings, up to the β rule. -/
theorem codeInstanceDerivable {hypotheses : Semantics.Term → Semantics.Term → Prop}
    (valuation : Valuation) (fillings : List Article.Term) :
    ∀ (code : Code) (term : Article.Term), codeInstanceMatches signature fillings code term = true →
      DerivableLatticeEta hypotheses (interpret signature valuation term)
        (interpretCode (fillings.map (interpret signature valuation)) code)
  | .slot index, term, matched => by
      simp only [codeInstanceMatches] at matched
      split at matched
      · rename_i filling found
        simp only [beq_iff_eq] at matched
        subst matched
        have valueFound : (fillings.map (interpret signature valuation))[index]? =
            some (interpret signature valuation filling) := by
          simp [found]
        simp only [interpretCode, Readback.readSlotOfSome valueFound]
        exact .reflexive _
      · cases matched
  | .apply function argument, term, matched => by
      simp only [codeInstanceMatches] at matched
      split at matched
      · rename_i name type functionTerm argumentTerm
        simp only [Bool.and_eq_true, beq_iff_eq] at matched
        obtain ⟨⟨nameEqual, functionMatched⟩, argumentMatched⟩ := matched
        subst nameEqual
        exact .transitive (interpretApply valuation type functionTerm argumentTerm)
          (.transitive
            (.congruenceFunction _
              (codeInstanceDerivable valuation fillings function functionTerm functionMatched))
            (.congruenceArgument _
              (codeInstanceDerivable valuation fillings argument argumentTerm argumentMatched)))
      · cases matched
  | .thunk code holes codes, term, matched => by
      simp only [codeInstanceMatches] at matched
      split at matched
      · rename_i name type arguments spineEqual
        split at matched
        · rename_i otherCode otherHoles operatorEqual
          simp only [Bool.and_eq_true, beq_iff_eq] at matched
          obtain ⟨⟨⟨codeEqual, holesEqual⟩, arity⟩, listMatched⟩ := matched
          have sameCode := Code.equality_of_equal codeEqual
          subst sameCode
          subst holesEqual
          have rebuilt : term = applyArguments (.constant name type) arguments := by
            have spineRebuilt := applyArgumentsSpine term
            rw [spineEqual] at spineRebuilt
            exact spineRebuilt.symm
          rw [rebuilt, interpretApplyArguments]
          have applied := curriedApplied (hypotheses := hypotheses) (.thunk otherCode otherHoles)
            (arguments.map (interpret signature valuation)) (by rw [List.length_map]; exact arity)
          have congruent := thunkTermPointwise (hypotheses := hypotheses) otherCode otherHoles []
            (arguments.map (interpret signature valuation))
            (interpretCodeList (fillings.map (interpret signature valuation)) codes)
            (codeInstanceListDerivable (hypotheses := hypotheses) valuation fillings codes
              arguments listMatched)
          simp only [List.nil_append] at congruent
          simp only [interpret, operatorEqual]
          exact .transitive applied congruent
        · cases matched
      · cases matched
  | .choice left right, term, matched => by
      simp only [codeInstanceMatches] at matched
      split at matched
      · rename_i name type leftTerm rightTerm
        simp only [Bool.and_eq_true, beq_iff_eq] at matched
        obtain ⟨⟨nameEqual, leftMatched⟩, rightMatched⟩ := matched
        subst nameEqual
        exact .transitive (interpretChoice valuation type leftTerm rightTerm)
          (DerivableLatticeEta.congruenceChoice
            (codeInstanceDerivable valuation fillings left leftTerm leftMatched)
            (codeInstanceDerivable valuation fillings right rightTerm rightMatched))
      · cases matched
  | .parallel left right, term, matched => by
      simp only [codeInstanceMatches] at matched
      split at matched
      · rename_i name type leftTerm rightTerm
        simp only [Bool.and_eq_true, beq_iff_eq] at matched
        obtain ⟨⟨nameEqual, leftMatched⟩, rightMatched⟩ := matched
        subst nameEqual
        exact .transitive (interpretParallel valuation type leftTerm rightTerm)
          (.transitive
            (.congruenceParallelLeft _
              (codeInstanceDerivable valuation fillings left leftTerm leftMatched))
            (.congruenceParallelRight _
              (codeInstanceDerivable valuation fillings right rightTerm rightMatched)))
      · cases matched

/-- `codeInstanceDerivable` on two lists, pairwise. -/
theorem codeInstanceListDerivable {hypotheses : Semantics.Term → Semantics.Term → Prop}
    (valuation : Valuation) (fillings : List Article.Term) :
    ∀ (codes : List Code) (terms : List Article.Term),
      codeInstanceListMatches signature fillings codes terms = true →
        Pointwise (DerivableLatticeEta hypotheses) (terms.map (interpret signature valuation))
          (interpretCodeList (fillings.map (interpret signature valuation)) codes)
  | [], [], _ => trivial
  | code :: codes, term :: terms, matched => by
      simp only [codeInstanceListMatches, Bool.and_eq_true] at matched
      exact ⟨codeInstanceDerivable valuation fillings code term matched.1,
        codeInstanceListDerivable valuation fillings codes terms matched.2⟩
  | [], _ :: _, matched => by simp [codeInstanceListMatches] at matched
  | _ :: _, [], matched => by simp [codeInstanceListMatches] at matched

end

/-- The equation of the defunctionalized β rule that instantiates the code of a thunk constant
with no hole is derivable, for every thunk constant and every list of fillings: `c f₀ … fₖ₋₁`
equals the encoding of the code's instance, slot `i` read as `fᵢ` (`codeInstanceMatches`). -/
theorem bodyEquationDerivable {type : Article.LogicType} {name : Article.Name} {code : Code}
    (operator : operatorOf signature name = .thunk code []) (fillings : List Article.Term)
    (arity : fillings.length = thunkArity code []) (right : Article.Term)
    (matched : codeInstanceMatches signature fillings code right = true) :
    EquationDerivable signature (applyArguments (.constant name type) fillings) right := by
  intro valuation
  have applied := curriedApplied (hypotheses := fun _ _ => False) (.thunk code [])
    (fillings.map (interpret signature valuation)) (by rw [List.length_map]; exact arity)
  rw [interpretApplyArguments]
  simp only [interpret, operator]
  exact .transitive applied
    (.symmetric (codeInstanceDerivable valuation fillings code right matched))

/-- The equation of the defunctionalized β rule that instantiates the code of a thunk constant
with no hole is sound (`bodyEquationDerivable`). -/
theorem bodyEquationSound {type : Article.LogicType} {name : Article.Name} {code : Code}
    (operator : operatorOf signature name = .thunk code []) (fillings : List Article.Term)
    (arity : fillings.length = thunkArity code []) (right : Article.Term)
    (matched : codeInstanceMatches signature fillings code right = true) :
    EquationSound signature (applyArguments (.constant name type) fillings) right :=
  equationSoundOfDerivable (bodyEquationDerivable (type := type) operator fillings arity right matched)

/-! ## Recognising the import set -/

/-- Whether `left = right` is the writer's equation of the defunctionalized β rule that fills the
first hole of a thunk constant, with any terms as the fillings and the argument
(`fillEquationSound`). -/
def fillChecked (signature : Signature) (left right : Article.Term) : Bool :=
  match left with
  | .application (.application (.constant name _) applied) argument =>
      match spine applied, spine right with
      | (.constant firstName _, fillings), (.constant secondName _, rightArguments) =>
          match operatorOf signature firstName, operatorOf signature secondName with
          | .thunk code (hole :: holes), .thunk otherCode otherHoles =>
              name == applyName && otherCode.equal code && otherHoles == holes &&
                fillings.length == thunkArity code (hole :: holes) &&
                rightArguments == fill hole holes fillings argument &&
                rightArguments.length == thunkArity code holes
          | _, _ => false
      | _, _ => false
  | _ => false

/-- Whether `left = right` is the writer's equation of the defunctionalized β rule that
instantiates the code of a thunk constant with no hole, with any terms as the fillings
(`bodyEquationSound`). -/
def bodyChecked (signature : Signature) (left right : Article.Term) : Bool :=
  match spine left with
  | (.constant name _, fillings) =>
      match operatorOf signature name with
      | .thunk code [] =>
          fillings.length == thunkArity code [] && codeInstanceMatches signature fillings code right
      | _ => false
  | _ => false

/-- Whether `left = right` is the writer's equation of the defunctionalized η rule of a thunk
constant, with any term as the filling (`etaEquationSound`). -/
def etaChecked (signature : Signature) (left right : Article.Term) : Bool :=
  match left with
  | .application (.constant name _) filling =>
      match operatorOf signature name with
      | .thunk (.apply (.slot function) (.slot hole)) [.slot otherHole] =>
          otherHole == hole && function != hole && fillingPosition [.slot hole] function == 0 &&
            thunkArity (.apply (.slot function) (.slot hole)) [.slot hole] == 1 && filling == right
      | _ => false
  | _ => false

/-- Whether `left = right` is the writer's equation of a thunk constant and its spelling by the
front end (`com.yang_bo.gezi.rewritetrace.Statements.respell`), with any terms as the fillings:
`c f₀ … fₙ₋₁ = c′ g₀ … gₘ₋₁`, each `gⱼ` the instance of a code `Dⱼ` over the fillings
(`codeInstanceListMatches`, the codes found by `instanceCode`), where the thunk of `c` and the thunk
of `c′` over the interpretations of the codes `D` are one term under the bound variables of `n`
abstractions in place of the fillings (`respellCheckedDerivable`). -/
def respellChecked (signature : Signature) (left right : Article.Term) : Bool :=
  match spine left, spine right with
  | (.constant firstName _, fillings), (.constant secondName _, arguments) =>
      match operatorOf signature firstName, operatorOf signature secondName,
          arguments.mapM (fun argument => instanceCode signature fillings argument []) with
      | .thunk code holes, .thunk otherCode otherHoles, some codes =>
          fillings.length == thunkArity code holes &&
            arguments.length == thunkArity otherCode otherHoles &&
            codeInstanceListMatches signature fillings codes arguments &&
            thunkTerm code holes (variablesBelow fillings.length) ==
              thunkTerm otherCode otherHoles (interpretCodeList (variablesBelow fillings.length) codes)
      | _, _, _ => false
  | _, _ => false

/-- Whether `left = right` is the writer's equation of a union the e-graph made by β conversion
(`com.yang_bo.gezi.egraph.Justification.BetaConversion`):
both sides read as terms of the calculus (`read`, so neither has a variable), and the left reading
reduces to the right by β steps within the fuel the size of the readings gives
by iterative deepening (`Semantics.betaReducesDeepening`, `Semantics.conversionFuel`). -/
def conversionChecked (signature : Signature) (left right : Article.Term) : Bool :=
  match read signature left, read signature right with
  | some leftTerm, some rightTerm =>
      Semantics.betaReducesDeepening (Semantics.conversionFuel leftTerm rightTerm) leftTerm rightTerm
  | _, _ => false

/-- Whether an equation is one of the writer's numbered equations (1) to (6) and (8) to (10), over
its variables M, N, P, A and B of type `LambdaJit.term`. -/
def numberedChecked (equation : Article.Term × Article.Term) : Bool :=
  [1, 2, 3, 4, 5, 6, 8, 9, 10].any fun number =>
    equation == numberedEquation number (termVariable "M") (termVariable "N")
      (termVariable "P") (termVariable "A") (termVariable "B")

/-- A lemma's statement: the two sides of its equation, with the signature of their thunk
constants, numbered from 0 in each statement so that a statement does not change when another
lemma is added (D7.1). -/
structure Statement where
  /-- The code and the holes of the statement's thunk constants. -/
  signature : Signature
  /-- The left side. -/
  left : Article.Term
  /-- The right side. -/
  right : Article.Term

/-- A statement is sound: its equation is sound under its own signature. -/
def Statement.Sound (statement : Statement) : Prop :=
  EquationSound statement.signature statement.left statement.right

/-- Whether an import equation of an article whose signature is `signature` is the statement
`lemma`: each side agrees with the statement's under the two signatures (`agree`). -/
def Statement.imports (signature : Signature) (lemma : Statement)
    (equation : Article.Term × Article.Term) : Bool :=
  agree lemma.signature signature lemma.left equation.1 &&
    agree lemma.signature signature lemma.right equation.2

/-- A sound statement makes sound every import equation it imports, under the article's
signature: the two sides are interpreted as the statement's (`interpretOfAgree`). -/
theorem Statement.importedSound {lemma : Statement} {equation : Article.Term × Article.Term}
    (sound : lemma.Sound) (imported : lemma.imports signature equation = true) :
    EquationSound signature equation.1 equation.2 := by
  simp only [Statement.imports, Bool.and_eq_true] at imported
  intro valuation
  rw [← interpretOfAgree valuation imported.1, ← interpretOfAgree valuation imported.2]
  exact sound valuation

/-- Whether an import equation is sound by this module, under the article's signature: a numbered
equation, an equation of the defunctionalized β rule or η rule of a thunk constant, a thunk
constant's respelling equation, a conversion equation, or the import of one of `lemmas`, the
statements the caller proves sound. -/
def importChecked (signature : Signature) (lemmas : List Statement)
    (equation : Article.Term × Article.Term) : Bool :=
  numberedChecked equation || lemmas.any (fun lemma => lemma.imports signature equation) ||
    fillChecked signature equation.1 equation.2 || bodyChecked signature equation.1 equation.2 ||
    etaChecked signature equation.1 equation.2 || respellChecked signature equation.1 equation.2 ||
    conversionChecked signature equation.1 equation.2

theorem fillCheckedDerivable {left right : Article.Term} (checked : fillChecked signature left right = true) :
    EquationDerivable signature left right := by
  unfold fillChecked at checked
  split at checked
  · rename_i name applyType applied argument
    split at checked
    · rename_i firstName firstType fillings secondName secondType rightArguments appliedSpine
        rightSpine
      split at checked
      · rename_i code hole holes otherCode otherHoles firstOperator secondOperator
        simp only [Bool.and_eq_true, beq_iff_eq] at checked
        obtain ⟨⟨⟨⟨⟨nameEqual, codeEqual⟩, holesEqual⟩, firstArity⟩, argumentsEqual⟩,
          secondArity⟩ := checked
        have sameCode := Code.equality_of_equal codeEqual
        subst nameEqual sameCode holesEqual argumentsEqual
        have appliedRebuilt := applyArgumentsSpine applied
        rw [appliedSpine] at appliedRebuilt
        have rightRebuilt := applyArgumentsSpine right
        rw [rightSpine] at rightRebuilt
        rw [← appliedRebuilt, ← rightRebuilt]
        exact fillEquationDerivable firstOperator secondOperator fillings argument firstArity
          secondArity
      · cases checked
    · cases checked
  · cases checked

theorem bodyCheckedDerivable {left right : Article.Term} (checked : bodyChecked signature left right = true) :
    EquationDerivable signature left right := by
  unfold bodyChecked at checked
  split at checked
  · rename_i name type fillings leftSpine
    split at checked
    · rename_i code operator
      simp only [Bool.and_eq_true, beq_iff_eq] at checked
      have leftRebuilt := applyArgumentsSpine left
      rw [leftSpine] at leftRebuilt
      rw [← leftRebuilt]
      exact bodyEquationDerivable operator fillings checked.1 right checked.2
    · cases checked
  · cases checked

theorem etaCheckedDerivable {left right : Article.Term} (checked : etaChecked signature left right = true) :
    EquationDerivable signature left right := by
  unfold etaChecked at checked
  split at checked
  · rename_i name type filling
    split at checked
    · rename_i function hole otherHole operator
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at checked
      obtain ⟨⟨⟨⟨holeEqual, distinct⟩, position⟩, arity⟩, same⟩ := checked
      subst holeEqual same
      exact etaEquationDerivable operator distinct position arity filling
    · cases checked
  · cases checked

/-- The respelling equation that `respellChecked` accepts is derivable: each side is its thunk's
interpretation over the fillings by the β rule (`curriedApplied`), the right side's after the
instances of its codes are read as the codes' interpretations (`codeInstanceListDerivable`); each
such interpretation is the abstraction of it over the bound variables applied to the fillings,
by one β step per filling (`Interpretation.abstractionsAppliedFrom`, its substitution lemmas
`Readback.thunkTermSubstitute` and `Readback.interpretCodeListSubstitute`); and the two
abstractions are one term by the check. -/
theorem respellCheckedDerivable {left right : Article.Term}
    (checked : respellChecked signature left right = true) :
    EquationDerivable signature left right := by
  unfold respellChecked at checked
  split at checked
  · rename_i firstName firstType fillings secondName secondType arguments leftSpine rightSpine
    split at checked
    · rename_i code holes otherCode otherHoles codes firstOperator secondOperator _
      simp only [Bool.and_eq_true, beq_iff_eq] at checked
      obtain ⟨⟨⟨firstArity, secondArity⟩, listMatched⟩, generic⟩ := checked
      have leftRebuilt := applyArgumentsSpine left
      rw [leftSpine] at leftRebuilt
      have rightRebuilt := applyArgumentsSpine right
      rw [rightSpine] at rightRebuilt
      rw [← leftRebuilt, ← rightRebuilt]
      intro valuation
      have firstApplied : DerivableLatticeEta (fun _ _ => False)
          (interpret signature valuation (applyArguments (.constant firstName firstType) fillings))
          (thunkTerm code holes (fillings.map (interpret signature valuation))) := by
        rw [interpretApplyArguments]
        have applied := curriedApplied (hypotheses := fun _ _ => False) (.thunk code holes)
          (fillings.map (interpret signature valuation)) (by rw [List.length_map]; exact firstArity)
        simp only [interpret, firstOperator]
        exact applied
      have secondApplied : DerivableLatticeEta (fun _ _ => False)
          (interpret signature valuation (applyArguments (.constant secondName secondType) arguments))
          (thunkTerm otherCode otherHoles (arguments.map (interpret signature valuation))) := by
        rw [interpretApplyArguments]
        have applied := curriedApplied (hypotheses := fun _ _ => False) (.thunk otherCode otherHoles)
          (arguments.map (interpret signature valuation)) (by rw [List.length_map]; exact secondArity)
        simp only [interpret, secondOperator]
        exact applied
      have firstGeneric := abstractionsAppliedFrom (hypotheses := fun _ _ => False)
        (thunkTerm code holes)
        (fun depth replacement values => Readback.thunkTermSubstitute code holes values depth replacement)
        fillings.length [] (fillings.map (interpret signature valuation)) (by rw [List.length_map])
      have secondGeneric := abstractionsAppliedFrom (hypotheses := fun _ _ => False)
        (fun values => thunkTerm otherCode otherHoles (interpretCodeList values codes))
        (fun depth replacement values => by
          rw [Readback.thunkTermSubstitute, Readback.interpretCodeListSubstitute])
        fillings.length [] (fillings.map (interpret signature valuation)) (by rw [List.length_map])
      simp only [List.map_nil, List.nil_append] at firstGeneric secondGeneric
      rw [generic] at firstGeneric
      have congruent := thunkTermPointwise (hypotheses := fun _ _ => False) otherCode otherHoles []
        (arguments.map (interpret signature valuation))
        (interpretCodeList (fillings.map (interpret signature valuation)) codes)
        (codeInstanceListDerivable valuation fillings codes arguments listMatched)
      simp only [List.nil_append] at congruent
      exact .transitive firstApplied (.transitive (.symmetric firstGeneric)
        (.transitive secondGeneric (.transitive (.symmetric congruent) (.symmetric secondApplied))))
    · cases checked
  · cases checked

/-- The conversion equation that `conversionChecked` accepts is derivable: each side's
interpretation equals its reading by the β rule (`readDerivable`), and the two readings are equal
by the steps of the search (`Semantics.DerivableLatticeEta.betaReducesDeepeningDerivable`). -/
theorem conversionCheckedDerivable {left right : Article.Term}
    (checked : conversionChecked signature left right = true) :
    EquationDerivable signature left right := by
  unfold conversionChecked at checked
  split at checked
  · rename_i leftTerm rightTerm leftRead rightRead
    intro valuation
    exact .transitive (readDerivable signature valuation leftRead)
      (.transitive (Semantics.DerivableLatticeEta.betaReducesDeepeningDerivable checked)
        (.symmetric (readDerivable signature valuation rightRead)))
  · cases checked

theorem numberedCheckedSound {equation : Article.Term × Article.Term}
    (checked : numberedChecked equation = true) : EquationSound signature equation.1 equation.2 := by
  simp only [numberedChecked, List.any_eq_true, beq_iff_eq] at checked
  obtain ⟨number, _, isEquation⟩ := checked
  rw [isEquation]
  exact numberedEquationSound _ _ _ _ _ _

/-- Every import equation that `importChecked` accepts is sound, when the caller's lemmas are. -/
theorem importCheckedSound {lemmas : List Statement}
    (lemmasSound : ∀ lemma ∈ lemmas, lemma.Sound)
    {equation : Article.Term × Article.Term} (checked : importChecked signature lemmas equation = true) :
    EquationSound signature equation.1 equation.2 := by
  simp only [importChecked, Bool.or_eq_true] at checked
  rcases checked with (((((numbered | lemma) | filled) | body) | eta) | respelled) | converted
  · exact numberedCheckedSound numbered
  · obtain ⟨statement, member, imported⟩ := List.any_eq_true.mp lemma
    exact Statement.importedSound (lemmasSound statement member) imported
  · exact equationSoundOfDerivable (fillCheckedDerivable filled)
  · exact equationSoundOfDerivable (bodyCheckedDerivable body)
  · exact equationSoundOfDerivable (etaCheckedDerivable eta)
  · exact equationSoundOfDerivable (respellCheckedDerivable respelled)
  · exact equationSoundOfDerivable (conversionCheckedDerivable converted)

/-- Whether two signatures are one list: the same names, in order, with the same codes
(`Code.equal`) and the same holes. -/
def signaturesSame : Signature → Signature → Bool
  | [], [] => true
  | (name, code, holes) :: rest, (otherName, otherCode, otherHoles) :: otherRest =>
      name == otherName && code.equal otherCode && holes == otherHoles &&
        signaturesSame rest otherRest
  | _, _ => false

theorem signaturesSameEqual : ∀ {first second : Signature}, signaturesSame first second = true →
    first = second
  | [], [], _ => rfl
  | (name, code, holes) :: rest, (otherName, otherCode, otherHoles) :: otherRest, same => by
      simp only [signaturesSame, Bool.and_eq_true, beq_iff_eq] at same
      obtain ⟨⟨⟨sameName, sameCode⟩, sameHoles⟩, sameRest⟩ := same
      rw [sameName, Code.equality_of_equal sameCode, sameHoles, signaturesSameEqual sameRest]
  | [], _ :: _, same | _ :: _, [], same => by simp [signaturesSame] at same

/-- Whether a theory's signature, read from its definitions (`signatureOf`), is `signature`, its
import equations are all accepted by `importChecked` under it, and its one exported equation is
`left = right`. -/
def theoryChecked (signature : Signature) (lemmas : List Statement) (left right : Article.Term)
    (theory : Article.Theory) : Bool :=
  -- `Article.importEquations` extracts the equation sides of any list of sequents, so it applies
  -- to the exported theorems as well as to the imports.
  signaturesSame (signatureOf theory.definitions) signature &&
    (Article.importEquations theory.assumptions).all (importChecked signature lemmas) &&
      Article.importEquations theory.theorems == [(left, right)]

/-- `theoryChecked` on the result of reading an article; false when the reader rejects it. -/
def resultChecked (signature : Signature) (lemmas : List Statement) (left right : Article.Term) :
    Except String Article.Theory → Bool
  | .ok theory => theoryChecked signature lemmas left right theory
  | .error _ => false

/-- The end-to-end theorem on an article whose import set `importChecked` accepts: when the reader
accepts `text`, the article's definitions give `signature`, every import equation is a numbered
equation, an equation of the defunctionalized β rule or η rule of a thunk constant, or the import
of one of the sound `lemmas`, and the one exported equation is `left = right`, then `left = right`
is sound under `signature`. -/
theorem endToEndOfChecked {text : String} {lemmas : List Statement}
    {left right : Article.Term}
    (lemmasSound : ∀ lemma ∈ lemmas, lemma.Sound)
    (checked : resultChecked signature lemmas left right (Article.readArticle text) = true) :
    EquationSound signature left right := by
  cases accepted : Article.readArticle text with
  | error message =>
      rw [accepted] at checked
      cases checked
  | ok theory =>
      rw [accepted] at checked
      simp only [resultChecked, theoryChecked, Bool.and_eq_true, List.all_eq_true,
        beq_iff_eq] at checked
      obtain ⟨⟨_, importsChecked⟩, exportedEquations⟩ := checked
      -- `Article.importEquations` extracts the equation sides of any list of sequents, so it applies
      -- to the exported theorems as well as to the imports.
      have exportedMember : (left, right) ∈ Article.importEquations theory.theorems := by
        rw [exportedEquations]
        exact List.mem_singleton_self _
      simp only [Article.importEquations, List.mem_filterMap, Option.map_eq_some_iff,
        Prod.mk.injEq] at exportedMember
      obtain ⟨exported, member, ⟨sideType, exportedLeft, exportedRight⟩, sides, leftSame,
        rightSame⟩ := exportedMember
      have isEquation := Article.Term.equationSides?_eq_some sides
      obtain ⟨_, otherLeft, otherRight, otherEquation, sound⟩ :=
        endToEnd accepted
          (fun equation member => importCheckedSound lemmasSound (importsChecked equation member))
          exported member
      rw [isEquation] at otherEquation
      simp only [Article.Term.equation, Article.Term.application.injEq] at otherEquation
      obtain ⟨⟨_, leftEqual⟩, rightEqual⟩ := otherEquation
      rw [← leftSame, ← rightSame, leftEqual, rightEqual]
      exact sound

end LambdaJit.EndToEnd
