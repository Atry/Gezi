import LambdaJit.BetaEtaConfluence

/-!
# The readings of a syntactic consistency proof

This module formalises the machinery of the syntactic consistency proof,
section 4, which module `LatticeEtaConsistency` runs on ⊢_{λ-lattice-η}: with no hypotheses it is
consistent (`Semantics.consistentLatticeEtaWithoutHypotheses`), and it relates two pure terms only
when they are βη-convertible (`derivableLatticeEtaPureConvertible`). The proof uses no model. Its
parts:

- `SimultaneousReduces`, the simultaneous version of the orthogonal reduction →o of the record
  (the β rule, (8) and (9), each oriented from left to right), and its confluence by
  Takahashi's complete development (`develop`, `simultaneousReducesDevelop`,
  `ReducesMany.confluent`), the record's lemma 1.
- `Resolves term reading`, the record's Res: `reading` is, up to βη-conversion
  (`BetaEtaConfluence.Convertible`), the pure term obtained from `term` by taking one side of every
  choice and the same reading on both sides of every parallel.
  `Reading term reading` is the record's R: some →o reduct of `term` resolves to `reading`.
  Lemmas 2 to 4 are `Resolves.substitute`, `Resolves.ofSimultaneousReduces` and
  `readingOfReducesMany`.
- `Below`, the record's simulation ≼, with the clauses the record names (变量, 抽象, 应用,
  选左, 选右, 并左, 并右, η左, η右); the clauses with a prefix λx⃗ are needed for one abstraction
  only. Lemmas 5 to 12 are `Below.reflexive`, `Below.substitute`, `Below.choiceInversion` and
  `Below.parallelEta`, `Below.abstractionApplication` with `Below.choiceApplication` and
  `Below.parallelApplication`, `Below.simultaneousReduces`, `Below.readingOfResolves`,
  `Below.reading` and `Below.fill`; lemma 13 is the cases of `derivableLatticeEtaSameReadings`
  (module `LatticeEtaConsistency`).
- Pure terms read exactly as their βη-conversions (`readingOfPure`), so two terms with the same
  readings in every one-hole context, such as two terms equal by ⊢_{λ-lattice-η} with no
  hypotheses, are βη-convertible when they are pure; λβη does not convert λx.λy. x and λx.λy. y,
  which module `BetaEtaConfluence` proves.

Lemma 7 (ii) of the record is used in the corrected form recorded there (commit 67fefae57):
`A ∥ B ≼ U` gives `λx. (A x ∥ B x) ≼′ U`, not `A ≼′ U or B ≼′ U` (`Below.parallelEta`).
-/

namespace LambdaJit.SyntacticConsistency

open LambdaJit.Semantics
open LambdaJit.Semantics.Term
open LambdaJit.BetaEtaConfluence

/-! ## The reduction →o and its confluence -/

/-- The simultaneous version of the record's →o: any set of redexes of the three oriented rules,
the β rule (λx. M) N → M[x := N], (8) (M + N) P → M P + N P and (9) (M ∥ N) P → M P ∥ N P,
contracted at once. It is the parallel reduction of Tait and Martin-Löf, called
simultaneous here, as in module `Confluence`, because the calculus already has an operator named
parallel. The rules are left-linear and do not overlap. -/
inductive SimultaneousReduces : Term → Term → Prop where
  /-- A variable reduces to itself. -/
  | boundVariable (index : Nat) : SimultaneousReduces (.boundVariable index) (.boundVariable index)
  /-- Under an abstraction. -/
  | abstraction {body result : Term} :
      SimultaneousReduces body result →
        SimultaneousReduces (.abstraction body) (.abstraction result)
  /-- In both sides of an application. -/
  | application {function functionResult argument argumentResult : Term} :
      SimultaneousReduces function functionResult → SimultaneousReduces argument argumentResult →
        SimultaneousReduces (.application function argument)
          (.application functionResult argumentResult)
  /-- In both sides of a choice. -/
  | choice {left leftResult right rightResult : Term} :
      SimultaneousReduces left leftResult → SimultaneousReduces right rightResult →
        SimultaneousReduces (.choice left right) (.choice leftResult rightResult)
  /-- In both sides of a parallel. -/
  | parallel {left leftResult right rightResult : Term} :
      SimultaneousReduces left leftResult → SimultaneousReduces right rightResult →
        SimultaneousReduces (.parallel left right) (.parallel leftResult rightResult)
  /-- The β rule, (λx. M) N → M[x := N]. -/
  | beta {body bodyResult argument argumentResult : Term} :
      SimultaneousReduces body bodyResult → SimultaneousReduces argument argumentResult →
        SimultaneousReduces (.application (.abstraction body) argument)
          (instantiate bodyResult argumentResult)
  /-- (8), (M + N) P → M P + N P. -/
  | choiceDistributive {left leftResult right rightResult argument argumentResult : Term} :
      SimultaneousReduces left leftResult → SimultaneousReduces right rightResult →
        SimultaneousReduces argument argumentResult →
          SimultaneousReduces (.application (.choice left right) argument)
            (.choice (.application leftResult argumentResult)
              (.application rightResult argumentResult))
  /-- (9), (M ∥ N) P → M P ∥ N P. -/
  | parallelDistributive {left leftResult right rightResult argument argumentResult : Term} :
      SimultaneousReduces left leftResult → SimultaneousReduces right rightResult →
        SimultaneousReduces argument argumentResult →
          SimultaneousReduces (.application (.parallel left right) argument)
            (.parallel (.application leftResult argumentResult)
              (.application rightResult argumentResult))

namespace SimultaneousReduces

/-- Every term reduces to itself. -/
theorem reflexive : ∀ term : Term, SimultaneousReduces term term
  | .boundVariable index => .boundVariable index
  | .abstraction body => .abstraction (reflexive body)
  | .application function argument => .application (reflexive function) (reflexive argument)
  | .choice left right => .choice (reflexive left) (reflexive right)
  | .parallel left right => .parallel (reflexive left) (reflexive right)

/-- Simultaneous reduction commutes with shifting. -/
theorem shiftFrom {term result : Term} (reduces : SimultaneousReduces term result) :
    ∀ cutoff, SimultaneousReduces (Term.shiftFrom cutoff term) (Term.shiftFrom cutoff result) := by
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
  | choiceDistributive _ _ _ leftInner rightInner argumentInner =>
      intro cutoff
      exact .choiceDistributive (leftInner cutoff) (rightInner cutoff) (argumentInner cutoff)
  | parallelDistributive _ _ _ leftInner rightInner argumentInner =>
      intro cutoff
      exact .parallelDistributive (leftInner cutoff) (rightInner cutoff) (argumentInner cutoff)

/-- Simultaneous reduction is closed under substitution, in the term and in the replacement. -/
theorem substitute {term result : Term} (reduces : SimultaneousReduces term result) :
    ∀ {replacement replacementResult : Term}, SimultaneousReduces replacement replacementResult →
      ∀ depth, SimultaneousReduces (Term.substitute depth replacement term)
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
      intro replacement replacementResult replacementReduces depth
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
      intro replacement replacementResult replacementReduces depth
      rw [substituteInstantiate]
      exact .beta (bodyInner (replacementReduces.shiftFrom 0) (depth + 1))
        (argumentInner replacementReduces depth)
  | choiceDistributive _ _ _ leftInner rightInner argumentInner =>
      intro _ _ replacementReduces depth
      exact .choiceDistributive (leftInner replacementReduces depth)
        (rightInner replacementReduces depth) (argumentInner replacementReduces depth)
  | parallelDistributive _ _ _ leftInner rightInner argumentInner =>
      intro _ _ replacementReduces depth
      exact .parallelDistributive (leftInner replacementReduces depth)
        (rightInner replacementReduces depth) (argumentInner replacementReduces depth)

/-- A β contractum of reducts is a reduct of the β contractum. -/
theorem instantiate {body bodyResult argument argumentResult : Term}
    (bodyReduces : SimultaneousReduces body bodyResult)
    (argumentReduces : SimultaneousReduces argument argumentResult) :
    SimultaneousReduces (Term.instantiate body argument)
      (Term.instantiate bodyResult argumentResult) :=
  bodyReduces.substitute argumentReduces 0

/-- An abstraction reduces to an abstraction. -/
theorem abstractionInversion {body result : Term}
    (reduces : SimultaneousReduces (.abstraction body) result) :
    ∃ bodyResult, result = .abstraction bodyResult ∧ SimultaneousReduces body bodyResult := by
  cases reduces with
  | abstraction inner => exact ⟨_, rfl, inner⟩

/-- A choice reduces to a choice. -/
theorem choiceInversion {left right result : Term}
    (reduces : SimultaneousReduces (.choice left right) result) :
    ∃ leftResult rightResult, result = .choice leftResult rightResult ∧
      SimultaneousReduces left leftResult ∧ SimultaneousReduces right rightResult := by
  cases reduces with
  | choice leftReduces rightReduces => exact ⟨_, _, rfl, leftReduces, rightReduces⟩

/-- A parallel reduces to a parallel. -/
theorem parallelInversion {left right result : Term}
    (reduces : SimultaneousReduces (.parallel left right) result) :
    ∃ leftResult rightResult, result = .parallel leftResult rightResult ∧
      SimultaneousReduces left leftResult ∧ SimultaneousReduces right rightResult := by
  cases reduces with
  | parallel leftReduces rightReduces => exact ⟨_, _, rfl, leftReduces, rightReduces⟩

/-- A variable reduces to itself only. -/
theorem boundVariableInversion {index : Nat} {result : Term}
    (reduces : SimultaneousReduces (.boundVariable index) result) :
    result = .boundVariable index := by
  cases reduces
  rfl

end SimultaneousReduces

/-- The complete development: every redex of the three rules contracted at once. -/
def develop : Term → Term
  | .boundVariable index => .boundVariable index
  | .abstraction body => .abstraction (develop body)
  | .application function argument =>
      match function with
      | .abstraction body => instantiate (develop body) (develop argument)
      | .choice left right =>
          .choice (.application (develop left) (develop argument))
            (.application (develop right) (develop argument))
      | .parallel left right =>
          .parallel (.application (develop left) (develop argument))
            (.application (develop right) (develop argument))
      | .boundVariable index => .application (.boundVariable index) (develop argument)
      | .application inner innerArgument =>
          .application (develop (.application inner innerArgument)) (develop argument)
  | .choice left right => .choice (develop left) (develop right)
  | .parallel left right => .parallel (develop left) (develop right)

/-- Takahashi's triangle: every simultaneous reduct of a term reduces in one simultaneous step to
its complete development. -/
theorem simultaneousReducesDevelop {term result : Term}
    (reduces : SimultaneousReduces term result) :
    SimultaneousReduces result (develop term) := by
  induction reduces with
  | boundVariable index => exact .boundVariable index
  | abstraction _ inner => exact .abstraction inner
  | @application function functionResult argument argumentResult functionReduces _
      functionInner argumentInner =>
      cases function with
      | boundVariable index =>
          cases functionReduces
          exact .application functionInner argumentInner
      | application inner innerArgument =>
          exact .application functionInner argumentInner
      | abstraction body =>
          obtain ⟨bodyResult, resultEqual, _⟩ := functionReduces.abstractionInversion
          subst resultEqual
          obtain ⟨developed, developedEqual, bodyDeveloped⟩ := functionInner.abstractionInversion
          simp only [develop] at developedEqual
          cases developedEqual
          exact .beta bodyDeveloped argumentInner
      | choice left right =>
          obtain ⟨leftResult, rightResult, resultEqual, _, _⟩ := functionReduces.choiceInversion
          subst resultEqual
          obtain ⟨_, _, developedEqual, leftDeveloped, rightDeveloped⟩ :=
            functionInner.choiceInversion
          simp only [develop] at developedEqual
          cases developedEqual
          exact .choiceDistributive leftDeveloped rightDeveloped argumentInner
      | parallel left right =>
          obtain ⟨leftResult, rightResult, resultEqual, _, _⟩ := functionReduces.parallelInversion
          subst resultEqual
          obtain ⟨_, _, developedEqual, leftDeveloped, rightDeveloped⟩ :=
            functionInner.parallelInversion
          simp only [develop] at developedEqual
          cases developedEqual
          exact .parallelDistributive leftDeveloped rightDeveloped argumentInner
  | choice _ _ leftInner rightInner => exact .choice leftInner rightInner
  | parallel _ _ leftInner rightInner => exact .parallel leftInner rightInner
  | beta _ _ bodyInner argumentInner =>
      exact SimultaneousReduces.instantiate bodyInner argumentInner
  | choiceDistributive _ _ _ leftInner rightInner argumentInner =>
      exact .choice (.application leftInner argumentInner) (.application rightInner argumentInner)
  | parallelDistributive _ _ _ leftInner rightInner argumentInner =>
      exact .parallel (.application leftInner argumentInner)
        (.application rightInner argumentInner)

/-- The reflexive transitive closure of `SimultaneousReduces`, the record's →o*. -/
inductive ReducesMany : Term → Term → Prop where
  /-- No step. -/
  | reflexive (term : Term) : ReducesMany term term
  /-- One simultaneous step, then more. -/
  | step {first middle last : Term} :
      SimultaneousReduces first middle → ReducesMany middle last → ReducesMany first last

namespace ReducesMany

/-- One simultaneous step. -/
theorem single {first second : Term} (reduces : SimultaneousReduces first second) :
    ReducesMany first second :=
  .step reduces (.reflexive second)

/-- Transitivity. -/
theorem transitive {first middle last : Term} (firstMany : ReducesMany first middle)
    (secondMany : ReducesMany middle last) : ReducesMany first last := by
  induction firstMany with
  | reflexive _ => exact secondMany
  | step reduces _ inner => exact .step reduces (inner secondMany)

/-- A reduction lifted through a map that lifts single steps. -/
theorem lift (map : Term → Term)
    (liftStep : ∀ {first second}, SimultaneousReduces first second →
      SimultaneousReduces (map first) (map second))
    {first last : Term} (many : ReducesMany first last) : ReducesMany (map first) (map last) := by
  induction many with
  | reflexive term => exact .reflexive _
  | step reduces _ inner => exact .step (liftStep reduces) inner

/-- Under an abstraction. -/
theorem abstraction {body result : Term} (many : ReducesMany body result) :
    ReducesMany (.abstraction body) (.abstraction result) :=
  lift Term.abstraction (fun reduces => .abstraction reduces) many

/-- In the function of an application. -/
theorem applicationFunction {function result : Term} (argument : Term)
    (many : ReducesMany function result) :
    ReducesMany (.application function argument) (.application result argument) :=
  lift (fun term => .application term argument)
    (fun reduces => .application reduces (SimultaneousReduces.reflexive argument)) many

/-- In the argument of an application. -/
theorem applicationArgument (function : Term) {argument result : Term}
    (many : ReducesMany argument result) :
    ReducesMany (.application function argument) (.application function result) :=
  lift (fun term => .application function term)
    (fun reduces => .application (SimultaneousReduces.reflexive function) reduces) many

/-- In both sides of an application. -/
theorem application {function functionResult argument argumentResult : Term}
    (functionMany : ReducesMany function functionResult)
    (argumentMany : ReducesMany argument argumentResult) :
    ReducesMany (.application function argument) (.application functionResult argumentResult) :=
  (applicationFunction argument functionMany).transitive
    (applicationArgument functionResult argumentMany)

/-- In the left side of a choice. -/
theorem choiceLeft {left result : Term} (right : Term) (many : ReducesMany left result) :
    ReducesMany (.choice left right) (.choice result right) :=
  lift (fun term => .choice term right)
    (fun reduces => .choice reduces (SimultaneousReduces.reflexive right)) many

/-- In the right side of a choice. -/
theorem choiceRight (left : Term) {right result : Term} (many : ReducesMany right result) :
    ReducesMany (.choice left right) (.choice left result) :=
  lift (fun term => .choice left term)
    (fun reduces => .choice (SimultaneousReduces.reflexive left) reduces) many

/-- In both sides of a parallel. -/
theorem parallel {left leftResult right rightResult : Term}
    (leftMany : ReducesMany left leftResult) (rightMany : ReducesMany right rightResult) :
    ReducesMany (.parallel left right) (.parallel leftResult rightResult) :=
  (lift (fun term => .parallel term right)
    (fun reduces => .parallel reduces (SimultaneousReduces.reflexive right)) leftMany).transitive
  (lift (fun term => .parallel leftResult term)
    (fun reduces => .parallel (SimultaneousReduces.reflexive leftResult) reduces) rightMany)

/-- Under shifting. -/
theorem shiftFrom (cutoff : Nat) {first last : Term} (many : ReducesMany first last) :
    ReducesMany (Term.shiftFrom cutoff first) (Term.shiftFrom cutoff last) :=
  lift (Term.shiftFrom cutoff) (fun reduces => reduces.shiftFrom cutoff) many

/-- Under substitution into the reducing term. -/
theorem substitute (depth : Nat) (replacement : Term) {first last : Term}
    (many : ReducesMany first last) :
    ReducesMany (Term.substitute depth replacement first)
      (Term.substitute depth replacement last) :=
  lift (Term.substitute depth replacement)
    (fun reduces => reduces.substitute (SimultaneousReduces.reflexive replacement) depth) many

/-- The strip lemma: one simultaneous step and a reduction close in a reduction and one parallel
step. -/
theorem strip {term first : Term} (reduces : SimultaneousReduces term first) {second : Term}
    (many : ReducesMany term second) :
    ∃ joined, ReducesMany first joined ∧ SimultaneousReduces second joined := by
  induction many generalizing first with
  | reflexive _ => exact ⟨first, .reflexive first, reduces⟩
  | step stepReduces _ inner =>
      obtain ⟨joined, middleMany, secondReduces⟩ := inner (simultaneousReducesDevelop stepReduces)
      exact ⟨joined, .step (simultaneousReducesDevelop reduces) middleMany, secondReduces⟩

/-- Confluence of →o (the record's lemma 1). -/
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

/-! ## The readings Res and R -/

/-- The record's Res: `Resolves term reading` when `reading` is, up to βη-conversion, the pure
term obtained from `term` by taking one side of every choice and the same reading on both sides of
every parallel. -/
inductive Resolves : Term → Term → Prop where
  /-- A variable reads as itself. -/
  | boundVariable {index : Nat} {reading : Term} :
      Convertible (.boundVariable index) reading → Resolves (.boundVariable index) reading
  /-- An abstraction reads as the abstraction of a reading of its body. -/
  | abstraction {body bodyReading reading : Term} :
      Resolves body bodyReading → Convertible (.abstraction bodyReading) reading →
        Resolves (.abstraction body) reading
  /-- An application reads as the application of readings of its sides. -/
  | application {function functionReading argument argumentReading reading : Term} :
      Resolves function functionReading → Resolves argument argumentReading →
        Convertible (.application functionReading argumentReading) reading →
          Resolves (.application function argument) reading
  /-- A choice reads as a reading of its left side. -/
  | choiceLeft {left right reading : Term} :
      Resolves left reading → Resolves (.choice left right) reading
  /-- A choice reads as a reading of its right side. -/
  | choiceRight {left right reading : Term} :
      Resolves right reading → Resolves (.choice left right) reading
  /-- A parallel reads as a reading of both of its sides. -/
  | parallel {left right reading : Term} :
      Resolves left reading → Resolves right reading → Resolves (.parallel left right) reading

/-- The record's R: some →o reduct of `term` resolves to `reading`. -/
def Reading (term reading : Term) : Prop :=
  ∃ reduct, ReducesMany term reduct ∧ Resolves reduct reading

namespace Resolves

/-- The readings of a term are closed under βη-conversion. -/
theorem convert {term reading other : Term} (resolves : Resolves term reading)
    (convertible : Convertible reading other) : Resolves term other := by
  induction resolves generalizing other with
  | boundVariable before => exact .boundVariable (before.transitive convertible)
  | abstraction bodyResolves before _ =>
      exact .abstraction bodyResolves (before.transitive convertible)
  | application functionResolves argumentResolves before _ _ =>
      exact .application functionResolves argumentResolves (before.transitive convertible)
  | choiceLeft _ inner => exact .choiceLeft (inner convertible)
  | choiceRight _ inner => exact .choiceRight (inner convertible)
  | parallel _ _ leftInner rightInner =>
      exact .parallel (leftInner convertible) (rightInner convertible)

/-- A reading of a term, shifted, is a reading of the shifted term. -/
theorem shiftFrom {term reading : Term} (resolves : Resolves term reading) :
    ∀ cutoff, Resolves (Term.shiftFrom cutoff term) (Term.shiftFrom cutoff reading) := by
  induction resolves with
  | @boundVariable index reading before =>
      intro cutoff
      have shifted := before.shiftFrom cutoff
      by_cases below : index < cutoff
      · simp only [Term.shiftFrom, below, ite_true] at shifted ⊢
        exact .boundVariable shifted
      · simp only [Term.shiftFrom, below, ite_false] at shifted ⊢
        exact .boundVariable shifted
  | abstraction _ before inner =>
      intro cutoff
      exact .abstraction (inner (cutoff + 1)) (before.shiftFrom cutoff)
  | application _ _ before functionInner argumentInner =>
      intro cutoff
      exact .application (functionInner cutoff) (argumentInner cutoff) (before.shiftFrom cutoff)
  | choiceLeft _ inner => intro cutoff; exact .choiceLeft (inner cutoff)
  | choiceRight _ inner => intro cutoff; exact .choiceRight (inner cutoff)
  | parallel _ _ leftInner rightInner =>
      intro cutoff; exact .parallel (leftInner cutoff) (rightInner cutoff)

/-- A reading of a shifted term is, up to βη-conversion, the shift of a reading of the term. -/
theorem ofShiftFrom : ∀ (term : Term) (cutoff : Nat) {reading : Term},
    Resolves (Term.shiftFrom cutoff term) reading →
      ∃ unshifted, Resolves term unshifted ∧
        Convertible reading (Term.shiftFrom cutoff unshifted)
  | .boundVariable index, cutoff, reading, resolves => by
      refine ⟨.boundVariable index, .boundVariable (.reflexive _), ?_⟩
      have shiftedVariable : ∃ shiftedIndex,
          Term.shiftFrom cutoff (.boundVariable index) = .boundVariable shiftedIndex := by
        by_cases below : index < cutoff
        · exact ⟨index, by simp [Term.shiftFrom, below]⟩
        · exact ⟨index + 1, by simp [Term.shiftFrom, below]⟩
      obtain ⟨shiftedIndex, shiftedEqual⟩ := shiftedVariable
      rw [shiftedEqual] at resolves ⊢
      cases resolves with
      | boundVariable before => exact .symmetric before
  | .abstraction body, cutoff, reading, resolves => by
      cases resolves with
      | abstraction bodyResolves before =>
          obtain ⟨bodyUnshifted, bodyUnshiftedResolves, bodyConvertible⟩ :=
            ofShiftFrom body (cutoff + 1) bodyResolves
          exact ⟨.abstraction bodyUnshifted, .abstraction bodyUnshiftedResolves (.reflexive _),
            (Convertible.symmetric before).transitive (.abstraction bodyConvertible)⟩
  | .application function argument, cutoff, reading, resolves => by
      cases resolves with
      | application functionResolves argumentResolves before =>
          obtain ⟨functionUnshifted, functionUnshiftedResolves, functionConvertible⟩ :=
            ofShiftFrom function cutoff functionResolves
          obtain ⟨argumentUnshifted, argumentUnshiftedResolves, argumentConvertible⟩ :=
            ofShiftFrom argument cutoff argumentResolves
          exact ⟨.application functionUnshifted argumentUnshifted,
            .application functionUnshiftedResolves argumentUnshiftedResolves (.reflexive _),
            (Convertible.symmetric before).transitive
              (.application functionConvertible argumentConvertible)⟩
  | .choice left right, cutoff, reading, resolves => by
      cases resolves with
      | choiceLeft leftResolves =>
          obtain ⟨unshifted, unshiftedResolves, convertible⟩ := ofShiftFrom left cutoff leftResolves
          exact ⟨unshifted, .choiceLeft unshiftedResolves, convertible⟩
      | choiceRight rightResolves =>
          obtain ⟨unshifted, unshiftedResolves, convertible⟩ :=
            ofShiftFrom right cutoff rightResolves
          exact ⟨unshifted, .choiceRight unshiftedResolves, convertible⟩
  | .parallel left right, cutoff, reading, resolves => by
      cases resolves with
      | parallel leftResolves rightResolves =>
          obtain ⟨leftUnshifted, leftUnshiftedResolves, leftConvertible⟩ :=
            ofShiftFrom left cutoff leftResolves
          obtain ⟨rightUnshifted, rightUnshiftedResolves, rightConvertible⟩ :=
            ofShiftFrom right cutoff rightResolves
          have unshiftedConvertible : Convertible rightUnshifted leftUnshifted :=
            Convertible.ofShiftFrom cutoff
              ((Convertible.symmetric rightConvertible).transitive leftConvertible)
          exact ⟨leftUnshifted,
            .parallel leftUnshiftedResolves (rightUnshiftedResolves.convert unshiftedConvertible),
            leftConvertible⟩

/-- The record's lemma 2: substituting a reading of the replacement into a reading of the term
gives a reading of the substituted term. -/
theorem substitute {term reading : Term} (resolves : Resolves term reading) :
    ∀ {replacement replacementReading : Term}, Resolves replacement replacementReading →
      ∀ depth, Resolves (Term.substitute depth replacement term)
        (Term.substitute depth replacementReading reading) := by
  induction resolves with
  | @boundVariable index reading before =>
      intro replacement replacementReading replacementResolves depth
      have variableResolves : Resolves (Term.substitute depth replacement (.boundVariable index))
          (Term.substitute depth replacementReading (.boundVariable index)) := by
        by_cases below : index < depth
        · simp only [Term.substitute, below, ite_true]
          exact .boundVariable (.reflexive _)
        · by_cases atDepth : index = depth
          · subst atDepth
            simp only [Term.substitute, Nat.lt_irrefl, ite_false, ite_true]
            exact replacementResolves
          · simp only [Term.substitute, below, atDepth, ite_false]
            exact .boundVariable (.reflexive _)
      exact variableResolves.convert (before.substitute depth replacementReading)
  | abstraction _ before inner =>
      intro replacement replacementReading replacementResolves depth
      exact .abstraction (inner (replacementResolves.shiftFrom 0) (depth + 1))
        (before.substitute depth replacementReading)
  | application _ _ before functionInner argumentInner =>
      intro replacement replacementReading replacementResolves depth
      exact .application (functionInner replacementResolves depth)
        (argumentInner replacementResolves depth) (before.substitute depth replacementReading)
  | choiceLeft _ inner =>
      intro _ _ replacementResolves depth; exact .choiceLeft (inner replacementResolves depth)
  | choiceRight _ inner =>
      intro _ _ replacementResolves depth; exact .choiceRight (inner replacementResolves depth)
  | parallel _ _ leftInner rightInner =>
      intro _ _ replacementResolves depth
      exact .parallel (leftInner replacementResolves depth) (rightInner replacementResolves depth)

/-- The record's lemma 3: a reading of a term is a reading of each of its simultaneous reducts. -/
theorem ofSimultaneousReduces {term result : Term} (reduces : SimultaneousReduces term result) :
    ∀ {reading : Term}, Resolves term reading → Resolves result reading := by
  induction reduces with
  | boundVariable index => intro reading resolves; exact resolves
  | abstraction _ inner =>
      intro reading resolves
      cases resolves with
      | abstraction bodyResolves before => exact .abstraction (inner bodyResolves) before
  | application _ _ functionInner argumentInner =>
      intro reading resolves
      cases resolves with
      | application functionResolves argumentResolves before =>
          exact .application (functionInner functionResolves) (argumentInner argumentResolves)
            before
  | choice _ _ leftInner rightInner =>
      intro reading resolves
      cases resolves with
      | choiceLeft leftResolves => exact .choiceLeft (leftInner leftResolves)
      | choiceRight rightResolves => exact .choiceRight (rightInner rightResolves)
  | parallel _ _ leftInner rightInner =>
      intro reading resolves
      cases resolves with
      | parallel leftResolves rightResolves =>
          exact .parallel (leftInner leftResolves) (rightInner rightResolves)
  | beta _ _ bodyInner argumentInner =>
      intro reading resolves
      cases resolves with
      | application functionResolves argumentResolves before =>
          cases functionResolves with
          | abstraction bodyResolves abstractionBefore =>
              have substituted :=
                (bodyInner bodyResolves).substitute (argumentInner argumentResolves) 0
              refine substituted.convert ?_
              exact (Convertible.symmetric (.beta _ _)).transitive
                ((Convertible.application abstractionBefore (.reflexive _)).transitive before)
  | choiceDistributive _ _ _ leftInner rightInner argumentInner =>
      intro reading resolves
      cases resolves with
      | application functionResolves argumentResolves before =>
          cases functionResolves with
          | choiceLeft leftResolves =>
              exact .choiceLeft
                (.application (leftInner leftResolves) (argumentInner argumentResolves) before)
          | choiceRight rightResolves =>
              exact .choiceRight
                (.application (rightInner rightResolves) (argumentInner argumentResolves) before)
  | parallelDistributive _ _ _ leftInner rightInner argumentInner =>
      intro reading resolves
      cases resolves with
      | application functionResolves argumentResolves before =>
          cases functionResolves with
          | parallel leftResolves rightResolves =>
              exact .parallel
                (.application (leftInner leftResolves) (argumentInner argumentResolves) before)
                (.application (rightInner rightResolves) (argumentInner argumentResolves) before)

/-- Lemma 3 along a reduction. -/
theorem ofReducesMany {term result : Term} (many : ReducesMany term result) {reading : Term}
    (resolves : Resolves term reading) : Resolves result reading := by
  induction many with
  | reflexive _ => exact resolves
  | step reduces _ inner => exact inner (ofSimultaneousReduces reduces resolves)

end Resolves

/-- The record's lemma 4: a reduction keeps the readings. -/
theorem readingOfReducesMany {term result : Term} (many : ReducesMany term result)
    {reading : Term} : Reading term reading ↔ Reading result reading := by
  constructor
  · intro ⟨reduct, reductMany, resolves⟩
    obtain ⟨joined, reductJoined, resultJoined⟩ := ReducesMany.confluent reductMany many
    exact ⟨joined, resultJoined, resolves.ofReducesMany reductJoined⟩
  · intro ⟨reduct, reductMany, resolves⟩
    exact ⟨reduct, many.transitive reductMany, resolves⟩

/-! ## Simultaneous reduction of a shifted term -/

/-- A simultaneous reduct of a shifted term is the shift of a simultaneous reduct of the term. -/
theorem SimultaneousReduces.ofShiftFrom : ∀ (term : Term) (cutoff : Nat) {result : Term},
    SimultaneousReduces (Term.shiftFrom cutoff term) result →
      ∃ unshifted, result = Term.shiftFrom cutoff unshifted ∧ SimultaneousReduces term unshifted
  | .boundVariable index, cutoff, result, reduces => by
      have shiftedVariable : ∃ shiftedIndex,
          Term.shiftFrom cutoff (.boundVariable index) = .boundVariable shiftedIndex := by
        by_cases below : index < cutoff
        · exact ⟨index, by simp [Term.shiftFrom, below]⟩
        · exact ⟨index + 1, by simp [Term.shiftFrom, below]⟩
      obtain ⟨shiftedIndex, shiftedEqual⟩ := shiftedVariable
      rw [shiftedEqual] at reduces
      cases reduces
      exact ⟨.boundVariable index, shiftedEqual.symm, .boundVariable index⟩
  | .abstraction body, cutoff, result, reduces => by
      simp only [Term.shiftFrom] at reduces
      obtain ⟨bodyResult, resultEqual, bodyReduces⟩ := reduces.abstractionInversion
      obtain ⟨unshifted, unshiftedEqual, unshiftedReduces⟩ :=
        ofShiftFrom body (cutoff + 1) bodyReduces
      subst resultEqual unshiftedEqual
      exact ⟨.abstraction unshifted, rfl, .abstraction unshiftedReduces⟩
  | .choice left right, cutoff, result, reduces => by
      simp only [Term.shiftFrom] at reduces
      obtain ⟨leftResult, rightResult, resultEqual, leftReduces, rightReduces⟩ :=
        reduces.choiceInversion
      obtain ⟨leftUnshifted, leftEqual, leftUnshiftedReduces⟩ := ofShiftFrom left cutoff leftReduces
      obtain ⟨rightUnshifted, rightEqual, rightUnshiftedReduces⟩ :=
        ofShiftFrom right cutoff rightReduces
      subst resultEqual leftEqual rightEqual
      exact ⟨.choice leftUnshifted rightUnshifted, rfl,
        .choice leftUnshiftedReduces rightUnshiftedReduces⟩
  | .parallel left right, cutoff, result, reduces => by
      simp only [Term.shiftFrom] at reduces
      obtain ⟨leftResult, rightResult, resultEqual, leftReduces, rightReduces⟩ :=
        reduces.parallelInversion
      obtain ⟨leftUnshifted, leftEqual, leftUnshiftedReduces⟩ := ofShiftFrom left cutoff leftReduces
      obtain ⟨rightUnshifted, rightEqual, rightUnshiftedReduces⟩ :=
        ofShiftFrom right cutoff rightReduces
      subst resultEqual leftEqual rightEqual
      exact ⟨.parallel leftUnshifted rightUnshifted, rfl,
        .parallel leftUnshiftedReduces rightUnshiftedReduces⟩
  | .application function argument, cutoff, result, reduces => by
      have congruenceCase : ∀ {functionResult argumentResult : Term},
          SimultaneousReduces (Term.shiftFrom cutoff function) functionResult →
          SimultaneousReduces (Term.shiftFrom cutoff argument) argumentResult →
            ∃ unshifted, Term.application functionResult argumentResult =
              Term.shiftFrom cutoff unshifted ∧
                SimultaneousReduces (.application function argument) unshifted := by
        intro functionResult argumentResult functionReduces argumentReduces
        obtain ⟨functionUnshifted, functionEqual, functionUnshiftedReduces⟩ :=
          ofShiftFrom function cutoff functionReduces
        obtain ⟨argumentUnshifted, argumentEqual, argumentUnshiftedReduces⟩ :=
          ofShiftFrom argument cutoff argumentReduces
        subst functionEqual argumentEqual
        exact ⟨.application functionUnshifted argumentUnshifted, rfl,
          .application functionUnshiftedReduces argumentUnshiftedReduces⟩
      cases function with
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
          simp only [Term.shiftFrom] at reduces congruenceCase
          cases reduces with
          | application functionReduces argumentReduces =>
              exact congruenceCase functionReduces argumentReduces
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
      | choice left right =>
          simp only [Term.shiftFrom] at reduces congruenceCase
          cases reduces with
          | application functionReduces argumentReduces =>
              exact congruenceCase functionReduces argumentReduces
          | choiceDistributive leftReduces rightReduces argumentReduces =>
              obtain ⟨leftUnshifted, leftEqual, leftUnshiftedReduces⟩ :=
                ofShiftFrom left cutoff leftReduces
              obtain ⟨rightUnshifted, rightEqual, rightUnshiftedReduces⟩ :=
                ofShiftFrom right cutoff rightReduces
              obtain ⟨argumentUnshifted, argumentEqual, argumentUnshiftedReduces⟩ :=
                ofShiftFrom argument cutoff argumentReduces
              subst leftEqual rightEqual argumentEqual
              exact ⟨.choice (.application leftUnshifted argumentUnshifted)
                  (.application rightUnshifted argumentUnshifted), rfl,
                .choiceDistributive leftUnshiftedReduces rightUnshiftedReduces
                  argumentUnshiftedReduces⟩
      | parallel left right =>
          simp only [Term.shiftFrom] at reduces congruenceCase
          cases reduces with
          | application functionReduces argumentReduces =>
              exact congruenceCase functionReduces argumentReduces
          | parallelDistributive leftReduces rightReduces argumentReduces =>
              obtain ⟨leftUnshifted, leftEqual, leftUnshiftedReduces⟩ :=
                ofShiftFrom left cutoff leftReduces
              obtain ⟨rightUnshifted, rightEqual, rightUnshiftedReduces⟩ :=
                ofShiftFrom right cutoff rightReduces
              obtain ⟨argumentUnshifted, argumentEqual, argumentUnshiftedReduces⟩ :=
                ofShiftFrom argument cutoff argumentReduces
              subst leftEqual rightEqual argumentEqual
              exact ⟨.parallel (.application leftUnshifted argumentUnshifted)
                  (.application rightUnshifted argumentUnshifted), rfl,
                .parallelDistributive leftUnshiftedReduces rightUnshiftedReduces
                  argumentUnshiftedReduces⟩

/-! ## The simulation ≼ -/

/-- The record's simulation ≼: `Below lower upper` says that every reading of `lower` in any
context is a reading of `upper` in that context. The clauses with a reduction of the upper side
(the record's ≼′) let each side of a choice or a parallel be simulated by a different reduct. -/
inductive Below : Term → Term → Prop where
  /-- 变量: x ≼ x. -/
  | boundVariable (index : Nat) : Below (.boundVariable index) (.boundVariable index)
  /-- 抽象: λx. T ≼ λx. U from T ≼ U. -/
  | abstraction {lower upper : Term} :
      Below lower upper → Below (.abstraction lower) (.abstraction upper)
  /-- 应用: T₁ T₂ ≼ U₁ U₂ from T₁ ≼ U₁ and T₂ ≼ U₂. -/
  | application {function functionUpper argument argumentUpper : Term} :
      Below function functionUpper → Below argument argumentUpper →
        Below (.application function argument) (.application functionUpper argumentUpper)
  /-- 选左: T₁ + T₂ ≼ U from T₁ ≼′ U and T₂ ≼′ U. -/
  | choice {left right upper leftReduct rightReduct : Term} :
      ReducesMany upper leftReduct → Below left leftReduct →
        ReducesMany upper rightReduct → Below right rightReduct →
          Below (.choice left right) upper
  /-- 选左 under one abstraction: λx. (T₁ + T₂) ≼ U from λx. T₁ ≼′ U and λx. T₂ ≼′ U. -/
  | abstractionChoice {left right upper leftReduct rightReduct : Term} :
      ReducesMany upper leftReduct → Below (.abstraction left) leftReduct →
        ReducesMany upper rightReduct → Below (.abstraction right) rightReduct →
          Below (.abstraction (.choice left right)) upper
  /-- 选右: T ≼ U₁ + U₂ from T ≼′ U₁. -/
  | choiceUpperLeft {lower upperLeft upperRight reduct : Term} :
      ReducesMany upperLeft reduct → Below lower reduct →
        Below lower (.choice upperLeft upperRight)
  /-- 选右: T ≼ U₁ + U₂ from T ≼′ U₂. -/
  | choiceUpperRight {lower upperLeft upperRight reduct : Term} :
      ReducesMany upperRight reduct → Below lower reduct →
        Below lower (.choice upperLeft upperRight)
  /-- 并左: T₁ ∥ T₂ ≼ U from T₁ ≼′ U. -/
  | parallelLeft {left right upper reduct : Term} :
      ReducesMany upper reduct → Below left reduct → Below (.parallel left right) upper
  /-- 并左: T₁ ∥ T₂ ≼ U from T₂ ≼′ U. -/
  | parallelRight {left right upper reduct : Term} :
      ReducesMany upper reduct → Below right reduct → Below (.parallel left right) upper
  /-- 并左 under one abstraction: λx. (T₁ ∥ T₂) ≼ U from λx. T₁ ≼′ U. -/
  | abstractionParallelLeft {left right upper reduct : Term} :
      ReducesMany upper reduct → Below (.abstraction left) reduct →
        Below (.abstraction (.parallel left right)) upper
  /-- 并左 under one abstraction: λx. (T₁ ∥ T₂) ≼ U from λx. T₂ ≼′ U. -/
  | abstractionParallelRight {left right upper reduct : Term} :
      ReducesMany upper reduct → Below (.abstraction right) reduct →
        Below (.abstraction (.parallel left right)) upper
  /-- 并右: T ≼ U₁ ∥ U₂ from T ≼′ U₁ and T ≼′ U₂. -/
  | parallelUpper {lower upperLeft upperRight leftReduct rightReduct : Term} :
      ReducesMany upperLeft leftReduct → Below lower leftReduct →
        ReducesMany upperRight rightReduct → Below lower rightReduct →
          Below lower (.parallel upperLeft upperRight)
  /-- η左: λx. T x ≼ U from T ≼ U, x ∉ FV(T). -/
  | etaLower {lower upper : Term} :
      Below lower upper → Below (.abstraction (.application (shift lower) (.boundVariable 0))) upper
  /-- η右: T ≼ λx. U x from T ≼ U, x ∉ FV(U). -/
  | etaUpper {lower upper : Term} :
      Below lower upper → Below lower (.abstraction (.application (shift upper) (.boundVariable 0)))

namespace Below

/-- The record's lemma 5: ≼ is reflexive. -/
theorem reflexive : ∀ term : Term, Below term term
  | .boundVariable index => .boundVariable index
  | .abstraction body => .abstraction (reflexive body)
  | .application function argument => .application (reflexive function) (reflexive argument)
  | .choice left right =>
      .choice (.reflexive _) (.choiceUpperLeft (.reflexive _) (reflexive left))
        (.reflexive _) (.choiceUpperRight (.reflexive _) (reflexive right))
  | .parallel left right =>
      .parallelUpper (.reflexive _) (.parallelLeft (.reflexive _) (reflexive left))
        (.reflexive _) (.parallelRight (.reflexive _) (reflexive right))

/-- The η redex of a shifted term, shifted from one more, is the η redex of the shifted term. -/
theorem shiftFromEtaRedex (term : Term) (cutoff : Nat) :
    Term.shiftFrom cutoff (.abstraction (.application (shift term) (.boundVariable 0))) =
      .abstraction (.application (shift (Term.shiftFrom cutoff term)) (.boundVariable 0)) := by
  simp only [Term.shiftFrom, shiftFromShifted]
  simp

/-- Substituting into the η redex of a term is the η redex of the substituted term. -/
theorem substituteEtaRedex (term replacement : Term) (depth : Nat) :
    Term.substitute depth replacement
        (.abstraction (.application (shift term) (.boundVariable 0))) =
      .abstraction
        (.application (shift (Term.substitute depth replacement term)) (.boundVariable 0)) := by
  simp only [Term.substitute, substituteShifted]
  simp

/-- ≼ is closed under shifting. -/
theorem shiftFrom {lower upper : Term} (below : Below lower upper) :
    ∀ cutoff, Below (Term.shiftFrom cutoff lower) (Term.shiftFrom cutoff upper) := by
  induction below with
  | boundVariable index => intro cutoff; exact reflexive _
  | abstraction _ inner => intro cutoff; exact .abstraction (inner (cutoff + 1))
  | application _ _ functionInner argumentInner =>
      intro cutoff; exact .application (functionInner cutoff) (argumentInner cutoff)
  | choice leftMany _ rightMany _ leftInner rightInner =>
      intro cutoff
      exact .choice (leftMany.shiftFrom cutoff) (leftInner cutoff) (rightMany.shiftFrom cutoff)
        (rightInner cutoff)
  | abstractionChoice leftMany _ rightMany _ leftInner rightInner =>
      intro cutoff
      exact .abstractionChoice (leftMany.shiftFrom cutoff) (leftInner cutoff)
        (rightMany.shiftFrom cutoff) (rightInner cutoff)
  | choiceUpperLeft many _ inner =>
      intro cutoff; exact .choiceUpperLeft (many.shiftFrom cutoff) (inner cutoff)
  | choiceUpperRight many _ inner =>
      intro cutoff; exact .choiceUpperRight (many.shiftFrom cutoff) (inner cutoff)
  | parallelLeft many _ inner =>
      intro cutoff; exact .parallelLeft (many.shiftFrom cutoff) (inner cutoff)
  | parallelRight many _ inner =>
      intro cutoff; exact .parallelRight (many.shiftFrom cutoff) (inner cutoff)
  | abstractionParallelLeft many _ inner =>
      intro cutoff; exact .abstractionParallelLeft (many.shiftFrom cutoff) (inner cutoff)
  | abstractionParallelRight many _ inner =>
      intro cutoff; exact .abstractionParallelRight (many.shiftFrom cutoff) (inner cutoff)
  | parallelUpper leftMany _ rightMany _ leftInner rightInner =>
      intro cutoff
      exact .parallelUpper (leftMany.shiftFrom cutoff) (leftInner cutoff)
        (rightMany.shiftFrom cutoff) (rightInner cutoff)
  | @etaLower lower upper _ inner =>
      intro cutoff
      rw [shiftFromEtaRedex]
      exact .etaLower (inner cutoff)
  | @etaUpper lower upper _ inner =>
      intro cutoff
      rw [shiftFromEtaRedex]
      exact .etaUpper (inner cutoff)

/-- The record's lemma 6: ≼ is closed under substitution. -/
theorem substitute {lower upper : Term} (below : Below lower upper) :
    ∀ {replacement replacementUpper : Term}, Below replacement replacementUpper →
      ∀ depth, Below (Term.substitute depth replacement lower)
        (Term.substitute depth replacementUpper upper) := by
  induction below with
  | boundVariable index =>
      intro replacement replacementUpper replacementBelow depth
      by_cases belowDepth : index < depth
      · simp only [Term.substitute, belowDepth, ite_true]; exact reflexive _
      · by_cases atDepth : index = depth
        · subst atDepth
          simp only [Term.substitute, Nat.lt_irrefl, ite_false, ite_true]
          exact replacementBelow
        · simp only [Term.substitute, belowDepth, atDepth, ite_false]; exact reflexive _
  | abstraction _ inner =>
      intro _ _ replacementBelow depth
      exact .abstraction (inner (replacementBelow.shiftFrom 0) (depth + 1))
  | application _ _ functionInner argumentInner =>
      intro _ _ replacementBelow depth
      exact .application (functionInner replacementBelow depth)
        (argumentInner replacementBelow depth)
  | choice leftMany _ rightMany _ leftInner rightInner =>
      intro _ replacementUpper replacementBelow depth
      exact .choice (leftMany.substitute depth replacementUpper) (leftInner replacementBelow depth)
        (rightMany.substitute depth replacementUpper) (rightInner replacementBelow depth)
  | abstractionChoice leftMany _ rightMany _ leftInner rightInner =>
      intro _ replacementUpper replacementBelow depth
      exact .abstractionChoice (leftMany.substitute depth replacementUpper)
        (leftInner replacementBelow depth) (rightMany.substitute depth replacementUpper)
        (rightInner replacementBelow depth)
  | choiceUpperLeft many _ inner =>
      intro _ replacementUpper replacementBelow depth
      exact .choiceUpperLeft (many.substitute depth replacementUpper) (inner replacementBelow depth)
  | choiceUpperRight many _ inner =>
      intro _ replacementUpper replacementBelow depth
      exact .choiceUpperRight (many.substitute depth replacementUpper)
        (inner replacementBelow depth)
  | parallelLeft many _ inner =>
      intro _ replacementUpper replacementBelow depth
      exact .parallelLeft (many.substitute depth replacementUpper) (inner replacementBelow depth)
  | parallelRight many _ inner =>
      intro _ replacementUpper replacementBelow depth
      exact .parallelRight (many.substitute depth replacementUpper) (inner replacementBelow depth)
  | abstractionParallelLeft many _ inner =>
      intro _ replacementUpper replacementBelow depth
      exact .abstractionParallelLeft (many.substitute depth replacementUpper)
        (inner replacementBelow depth)
  | abstractionParallelRight many _ inner =>
      intro _ replacementUpper replacementBelow depth
      exact .abstractionParallelRight (many.substitute depth replacementUpper)
        (inner replacementBelow depth)
  | parallelUpper leftMany _ rightMany _ leftInner rightInner =>
      intro _ replacementUpper replacementBelow depth
      exact .parallelUpper (leftMany.substitute depth replacementUpper)
        (leftInner replacementBelow depth) (rightMany.substitute depth replacementUpper)
        (rightInner replacementBelow depth)
  | etaLower _ inner =>
      intro _ _ replacementBelow depth
      rw [substituteEtaRedex]
      exact .etaLower (inner replacementBelow depth)
  | etaUpper _ inner =>
      intro _ _ replacementBelow depth
      rw [substituteEtaRedex]
      exact .etaUpper (inner replacementBelow depth)

/-- The η redex of a reduct is a reduct of the η redex. -/
theorem etaRedexReducesMany {term result : Term} (many : ReducesMany term result) :
    ReducesMany (.abstraction (.application (shift term) (.boundVariable 0)))
      (.abstraction (.application (shift result) (.boundVariable 0))) :=
  ReducesMany.abstraction (ReducesMany.applicationFunction _ (many.shiftFrom 0))

/-- The record's lemma 7 (i): a choice below an upper term has each side below a reduct of it. -/
theorem choiceInversion {lower upper : Term} (below : Below lower upper) :
    ∀ {left right : Term}, lower = .choice left right →
      (∃ reduct, ReducesMany upper reduct ∧ Below left reduct) ∧
        (∃ reduct, ReducesMany upper reduct ∧ Below right reduct) := by
  induction below with
  | choice leftMany leftBelow rightMany rightBelow =>
      intro left right equal
      cases equal
      exact ⟨⟨_, leftMany, leftBelow⟩, ⟨_, rightMany, rightBelow⟩⟩
  | choiceUpperLeft many _ inner =>
      intro left right equal
      obtain ⟨⟨_, leftMany, leftBelow⟩, ⟨_, rightMany, rightBelow⟩⟩ := inner equal
      exact ⟨⟨_, .reflexive _, .choiceUpperLeft (many.transitive leftMany) leftBelow⟩,
        ⟨_, .reflexive _, .choiceUpperLeft (many.transitive rightMany) rightBelow⟩⟩
  | choiceUpperRight many _ inner =>
      intro left right equal
      obtain ⟨⟨_, leftMany, leftBelow⟩, ⟨_, rightMany, rightBelow⟩⟩ := inner equal
      exact ⟨⟨_, .reflexive _, .choiceUpperRight (many.transitive leftMany) leftBelow⟩,
        ⟨_, .reflexive _, .choiceUpperRight (many.transitive rightMany) rightBelow⟩⟩
  | parallelUpper upperLeftMany _ upperRightMany _ upperLeftInner upperRightInner =>
      intro left right equal
      obtain ⟨⟨_, firstMany, firstBelow⟩, ⟨_, secondMany, secondBelow⟩⟩ := upperLeftInner equal
      obtain ⟨⟨_, thirdMany, thirdBelow⟩, ⟨_, fourthMany, fourthBelow⟩⟩ := upperRightInner equal
      exact ⟨⟨_, .reflexive _, .parallelUpper (upperLeftMany.transitive firstMany) firstBelow
          (upperRightMany.transitive thirdMany) thirdBelow⟩,
        ⟨_, .reflexive _, .parallelUpper (upperLeftMany.transitive secondMany) secondBelow
          (upperRightMany.transitive fourthMany) fourthBelow⟩⟩
  | etaUpper _ inner =>
      intro left right equal
      obtain ⟨⟨_, leftMany, leftBelow⟩, ⟨_, rightMany, rightBelow⟩⟩ := inner equal
      exact ⟨⟨_, etaRedexReducesMany leftMany, .etaUpper leftBelow⟩,
        ⟨_, etaRedexReducesMany rightMany, .etaUpper rightBelow⟩⟩
  | boundVariable => intro _ _ equal; cases equal
  | abstraction => intro _ _ equal; cases equal
  | application => intro _ _ equal; cases equal
  | abstractionChoice => intro _ _ equal; cases equal
  | parallelLeft => intro _ _ equal; cases equal
  | parallelRight => intro _ _ equal; cases equal
  | abstractionParallelLeft => intro _ _ equal; cases equal
  | abstractionParallelRight => intro _ _ equal; cases equal
  | etaLower => intro _ _ equal; cases equal

/-- The record's lemma 7 (ii), as corrected: a parallel A ∥ B below an upper term gives
λx. (A x ∥ B x) below a reduct of it. -/
theorem parallelEta {lower upper : Term} (below : Below lower upper) :
    ∀ {left right : Term}, lower = .parallel left right →
      ∃ reduct, ReducesMany upper reduct ∧
        Below (.abstraction (.parallel (.application (shift left) (.boundVariable 0))
          (.application (shift right) (.boundVariable 0)))) reduct := by
  induction below with
  | parallelLeft many leftBelow =>
      intro left right equal
      cases equal
      exact ⟨_, many, .abstractionParallelLeft (.reflexive _) (.etaLower leftBelow)⟩
  | parallelRight many rightBelow =>
      intro left right equal
      cases equal
      exact ⟨_, many, .abstractionParallelRight (.reflexive _) (.etaLower rightBelow)⟩
  | choiceUpperLeft many _ inner =>
      intro left right equal
      obtain ⟨_, innerMany, innerBelow⟩ := inner equal
      exact ⟨_, .reflexive _, .choiceUpperLeft (many.transitive innerMany) innerBelow⟩
  | choiceUpperRight many _ inner =>
      intro left right equal
      obtain ⟨_, innerMany, innerBelow⟩ := inner equal
      exact ⟨_, .reflexive _, .choiceUpperRight (many.transitive innerMany) innerBelow⟩
  | parallelUpper upperLeftMany _ upperRightMany _ upperLeftInner upperRightInner =>
      intro left right equal
      obtain ⟨_, leftMany, leftBelow⟩ := upperLeftInner equal
      obtain ⟨_, rightMany, rightBelow⟩ := upperRightInner equal
      exact ⟨_, .reflexive _, .parallelUpper (upperLeftMany.transitive leftMany) leftBelow
        (upperRightMany.transitive rightMany) rightBelow⟩
  | etaUpper _ inner =>
      intro left right equal
      obtain ⟨_, innerMany, innerBelow⟩ := inner equal
      exact ⟨_, etaRedexReducesMany innerMany, .etaUpper innerBelow⟩
  | boundVariable => intro _ _ equal; cases equal
  | abstraction => intro _ _ equal; cases equal
  | application => intro _ _ equal; cases equal
  | choice => intro _ _ equal; cases equal
  | abstractionChoice => intro _ _ equal; cases equal
  | abstractionParallelLeft => intro _ _ equal; cases equal
  | abstractionParallelRight => intro _ _ equal; cases equal
  | etaLower => intro _ _ equal; cases equal

end Below

/-! ## The root of an application (the record's lemma 8) -/

namespace Below

/-- The β step of an η redex applied to an argument: (λx. U x) A → U A. -/
theorem etaRedexApplication (upper argumentUpper : Term) :
    ReducesMany
      (.application (.abstraction (.application (shift upper) (.boundVariable 0))) argumentUpper)
      (.application upper argumentUpper) := by
  have step := ReducesMany.single (SimultaneousReduces.beta
    (SimultaneousReduces.reflexive (.application (shift upper) (.boundVariable 0)))
    (SimultaneousReduces.reflexive argumentUpper))
  simp only [instantiate, Term.substitute, substituteShift, Nat.lt_irrefl, ite_false,
    ite_true] at step
  exact step

/-- The (8) step of an upper choice applied to an argument. -/
theorem choiceApplicationStep (upperLeft upperRight argumentUpper : Term) :
    ReducesMany (.application (.choice upperLeft upperRight) argumentUpper)
      (.choice (.application upperLeft argumentUpper) (.application upperRight argumentUpper)) :=
  ReducesMany.single (.choiceDistributive (SimultaneousReduces.reflexive _)
    (SimultaneousReduces.reflexive _) (SimultaneousReduces.reflexive _))

/-- The (9) step of an upper parallel applied to an argument. -/
theorem parallelApplicationStep (upperLeft upperRight argumentUpper : Term) :
    ReducesMany (.application (.parallel upperLeft upperRight) argumentUpper)
      (.parallel (.application upperLeft argumentUpper) (.application upperRight argumentUpper)) :=
  ReducesMany.single (.parallelDistributive (SimultaneousReduces.reflexive _)
    (SimultaneousReduces.reflexive _) (SimultaneousReduces.reflexive _))

/-- The record's lemma 8 (a): an abstraction below an upper term, applied to an argument below an
upper argument, contracts to a term below a reduct of the upper application. -/
theorem abstractionApplication {lower upper : Term} (below : Below lower upper) :
    ∀ {body argument argumentUpper : Term}, lower = .abstraction body →
      Below argument argumentUpper →
        ∃ result, ReducesMany (.application upper argumentUpper) result ∧
          Below (instantiate body argument) result := by
  induction below with
  | abstraction bodyBelow =>
      intro body argument argumentUpper equal argumentBelow
      cases equal
      exact ⟨_, ReducesMany.single (.beta (SimultaneousReduces.reflexive _)
        (SimultaneousReduces.reflexive _)), bodyBelow.substitute argumentBelow 0⟩
  | abstractionChoice leftMany _ rightMany _ leftInner rightInner =>
      intro body argument argumentUpper equal argumentBelow
      cases equal
      obtain ⟨leftResult, leftResultMany, leftResultBelow⟩ := leftInner rfl argumentBelow
      obtain ⟨rightResult, rightResultMany, rightResultBelow⟩ := rightInner rfl argumentBelow
      exact ⟨_, .reflexive _, .choice
        ((ReducesMany.applicationFunction _ leftMany).transitive leftResultMany) leftResultBelow
        ((ReducesMany.applicationFunction _ rightMany).transitive rightResultMany)
          rightResultBelow⟩
  | abstractionParallelLeft many _ inner =>
      intro body argument argumentUpper equal argumentBelow
      cases equal
      obtain ⟨result, resultMany, resultBelow⟩ := inner rfl argumentBelow
      exact ⟨_, .reflexive _,
        .parallelLeft ((ReducesMany.applicationFunction _ many).transitive resultMany) resultBelow⟩
  | abstractionParallelRight many _ inner =>
      intro body argument argumentUpper equal argumentBelow
      cases equal
      obtain ⟨result, resultMany, resultBelow⟩ := inner rfl argumentBelow
      exact ⟨_, .reflexive _,
        .parallelRight ((ReducesMany.applicationFunction _ many).transitive resultMany) resultBelow⟩
  | etaLower innerBelow =>
      intro body argument argumentUpper equal argumentBelow
      cases equal
      refine ⟨_, .reflexive _, ?_⟩
      simp only [instantiate, Term.substitute, substituteShift, Nat.lt_irrefl, ite_false, ite_true]
      exact .application innerBelow argumentBelow
  | choiceUpperLeft many _ inner =>
      intro body argument argumentUpper equal argumentBelow
      obtain ⟨result, resultMany, resultBelow⟩ := inner equal argumentBelow
      exact ⟨_, choiceApplicationStep _ _ _,
        .choiceUpperLeft ((ReducesMany.applicationFunction _ many).transitive resultMany)
          resultBelow⟩
  | choiceUpperRight many _ inner =>
      intro body argument argumentUpper equal argumentBelow
      obtain ⟨result, resultMany, resultBelow⟩ := inner equal argumentBelow
      exact ⟨_, choiceApplicationStep _ _ _,
        .choiceUpperRight ((ReducesMany.applicationFunction _ many).transitive resultMany)
          resultBelow⟩
  | parallelUpper leftMany _ rightMany _ leftInner rightInner =>
      intro body argument argumentUpper equal argumentBelow
      obtain ⟨leftResult, leftResultMany, leftResultBelow⟩ := leftInner equal argumentBelow
      obtain ⟨rightResult, rightResultMany, rightResultBelow⟩ := rightInner equal argumentBelow
      exact ⟨_, parallelApplicationStep _ _ _,
        .parallelUpper ((ReducesMany.applicationFunction _ leftMany).transitive leftResultMany)
          leftResultBelow ((ReducesMany.applicationFunction _ rightMany).transitive rightResultMany)
          rightResultBelow⟩
  | @etaUpper lower upper _ inner =>
      intro body argument argumentUpper equal argumentBelow
      obtain ⟨result, resultMany, resultBelow⟩ := inner equal argumentBelow
      exact ⟨_, (etaRedexApplication upper argumentUpper).transitive resultMany, resultBelow⟩
  | boundVariable => intro _ _ _ equal; cases equal
  | application => intro _ _ _ equal; cases equal
  | choice => intro _ _ _ equal; cases equal
  | parallelLeft => intro _ _ _ equal; cases equal
  | parallelRight => intro _ _ _ equal; cases equal

/-- The record's lemma 8 (b): a choice below an upper term, applied to an argument below an upper
argument, distributes to a term below a reduct of the upper application. -/
theorem choiceApplication {lower upper : Term} (below : Below lower upper) :
    ∀ {left right argument argumentUpper : Term}, lower = .choice left right →
      Below argument argumentUpper →
        ∃ result, ReducesMany (.application upper argumentUpper) result ∧
          Below (.choice (.application left argument) (.application right argument)) result := by
  induction below with
  | choice leftMany leftBelow rightMany rightBelow =>
      intro left right argument argumentUpper equal argumentBelow
      cases equal
      exact ⟨_, .reflexive _, .choice (ReducesMany.applicationFunction _ leftMany)
        (.application leftBelow argumentBelow) (ReducesMany.applicationFunction _ rightMany)
        (.application rightBelow argumentBelow)⟩
  | choiceUpperLeft many _ inner =>
      intro left right argument argumentUpper equal argumentBelow
      obtain ⟨result, resultMany, resultBelow⟩ := inner equal argumentBelow
      exact ⟨_, choiceApplicationStep _ _ _,
        .choiceUpperLeft ((ReducesMany.applicationFunction _ many).transitive resultMany)
          resultBelow⟩
  | choiceUpperRight many _ inner =>
      intro left right argument argumentUpper equal argumentBelow
      obtain ⟨result, resultMany, resultBelow⟩ := inner equal argumentBelow
      exact ⟨_, choiceApplicationStep _ _ _,
        .choiceUpperRight ((ReducesMany.applicationFunction _ many).transitive resultMany)
          resultBelow⟩
  | parallelUpper leftMany _ rightMany _ leftInner rightInner =>
      intro left right argument argumentUpper equal argumentBelow
      obtain ⟨leftResult, leftResultMany, leftResultBelow⟩ := leftInner equal argumentBelow
      obtain ⟨rightResult, rightResultMany, rightResultBelow⟩ := rightInner equal argumentBelow
      exact ⟨_, parallelApplicationStep _ _ _,
        .parallelUpper ((ReducesMany.applicationFunction _ leftMany).transitive leftResultMany)
          leftResultBelow ((ReducesMany.applicationFunction _ rightMany).transitive rightResultMany)
          rightResultBelow⟩
  | @etaUpper lower upper _ inner =>
      intro left right argument argumentUpper equal argumentBelow
      obtain ⟨result, resultMany, resultBelow⟩ := inner equal argumentBelow
      exact ⟨_, (etaRedexApplication upper argumentUpper).transitive resultMany, resultBelow⟩
  | boundVariable => intro _ _ _ _ equal; cases equal
  | abstraction => intro _ _ _ _ equal; cases equal
  | application => intro _ _ _ _ equal; cases equal
  | abstractionChoice => intro _ _ _ _ equal; cases equal
  | parallelLeft => intro _ _ _ _ equal; cases equal
  | parallelRight => intro _ _ _ _ equal; cases equal
  | abstractionParallelLeft => intro _ _ _ _ equal; cases equal
  | abstractionParallelRight => intro _ _ _ _ equal; cases equal
  | etaLower => intro _ _ _ _ equal; cases equal

/-- The record's lemma 8 (c): a parallel below an upper term, applied to an argument below an
upper argument, distributes to a term below a reduct of the upper application. -/
theorem parallelApplication {lower upper : Term} (below : Below lower upper) :
    ∀ {left right argument argumentUpper : Term}, lower = .parallel left right →
      Below argument argumentUpper →
        ∃ result, ReducesMany (.application upper argumentUpper) result ∧
          Below (.parallel (.application left argument) (.application right argument)) result := by
  induction below with
  | parallelLeft many leftBelow =>
      intro left right argument argumentUpper equal argumentBelow
      cases equal
      exact ⟨_, ReducesMany.applicationFunction _ many,
        .parallelLeft (.reflexive _) (.application leftBelow argumentBelow)⟩
  | parallelRight many rightBelow =>
      intro left right argument argumentUpper equal argumentBelow
      cases equal
      exact ⟨_, ReducesMany.applicationFunction _ many,
        .parallelRight (.reflexive _) (.application rightBelow argumentBelow)⟩
  | choiceUpperLeft many _ inner =>
      intro left right argument argumentUpper equal argumentBelow
      obtain ⟨result, resultMany, resultBelow⟩ := inner equal argumentBelow
      exact ⟨_, choiceApplicationStep _ _ _,
        .choiceUpperLeft ((ReducesMany.applicationFunction _ many).transitive resultMany)
          resultBelow⟩
  | choiceUpperRight many _ inner =>
      intro left right argument argumentUpper equal argumentBelow
      obtain ⟨result, resultMany, resultBelow⟩ := inner equal argumentBelow
      exact ⟨_, choiceApplicationStep _ _ _,
        .choiceUpperRight ((ReducesMany.applicationFunction _ many).transitive resultMany)
          resultBelow⟩
  | parallelUpper leftMany _ rightMany _ leftInner rightInner =>
      intro left right argument argumentUpper equal argumentBelow
      obtain ⟨leftResult, leftResultMany, leftResultBelow⟩ := leftInner equal argumentBelow
      obtain ⟨rightResult, rightResultMany, rightResultBelow⟩ := rightInner equal argumentBelow
      exact ⟨_, parallelApplicationStep _ _ _,
        .parallelUpper ((ReducesMany.applicationFunction _ leftMany).transitive leftResultMany)
          leftResultBelow ((ReducesMany.applicationFunction _ rightMany).transitive rightResultMany)
          rightResultBelow⟩
  | @etaUpper lower upper _ inner =>
      intro left right argument argumentUpper equal argumentBelow
      obtain ⟨result, resultMany, resultBelow⟩ := inner equal argumentBelow
      exact ⟨_, (etaRedexApplication upper argumentUpper).transitive resultMany, resultBelow⟩
  | boundVariable => intro _ _ _ _ equal; cases equal
  | abstraction => intro _ _ _ _ equal; cases equal
  | application => intro _ _ _ _ equal; cases equal
  | choice => intro _ _ _ _ equal; cases equal
  | abstractionChoice => intro _ _ _ _ equal; cases equal
  | abstractionParallelLeft => intro _ _ _ _ equal; cases equal
  | abstractionParallelRight => intro _ _ _ _ equal; cases equal
  | etaLower => intro _ _ _ _ equal; cases equal

/-- The η case of the record's lemma 9: a simultaneous step of the body of λx. T x, where T is
below an upper term and every simultaneous step of T is simulated, is simulated. -/
theorem etaLowerSimultaneousReduces {inner upper : Term}
    (innerSimulated : ∀ {innerResult}, SimultaneousReduces inner innerResult →
      ∃ reduct, ReducesMany upper reduct ∧ Below innerResult reduct)
    {bodyResult : Term}
    (reduces : SimultaneousReduces (.application (shift inner) (.boundVariable 0)) bodyResult) :
    ∃ reduct, ReducesMany upper reduct ∧ Below (.abstraction bodyResult) reduct := by
  have congruenceCase : ∀ {functionResult : Term},
      SimultaneousReduces (shift inner) functionResult →
        ∃ reduct, ReducesMany upper reduct ∧
          Below (.abstraction (.application functionResult (.boundVariable 0))) reduct := by
    intro functionResult functionReduces
    obtain ⟨unshifted, unshiftedEqual, unshiftedReduces⟩ :=
      SimultaneousReduces.ofShiftFrom inner 0 functionReduces
    subst unshiftedEqual
    obtain ⟨reduct, reductMany, reductBelow⟩ := innerSimulated unshiftedReduces
    exact ⟨reduct, reductMany, .etaLower reductBelow⟩
  cases inner with
  | boundVariable index =>
      simp only [shift, Term.shiftFrom, Nat.not_lt_zero, ite_false] at reduces congruenceCase
      cases reduces with
      | application functionReduces argumentReduces =>
          cases argumentReduces
          exact congruenceCase functionReduces
  | application function argument =>
      cases reduces with
      | application functionReduces argumentReduces =>
          cases argumentReduces
          exact congruenceCase functionReduces
  | abstraction body =>
      simp only [shift, Term.shiftFrom] at reduces congruenceCase
      cases reduces with
      | application functionReduces argumentReduces =>
          cases argumentReduces
          exact congruenceCase functionReduces
      | beta bodyReduces argumentReduces =>
          cases argumentReduces
          obtain ⟨unshifted, unshiftedEqual, unshiftedReduces⟩ :=
            SimultaneousReduces.ofShiftFrom body 1 bodyReduces
          subst unshiftedEqual
          rw [instantiateShiftFrom]
          exact innerSimulated (.abstraction unshiftedReduces)
  | choice left right =>
      simp only [shift, Term.shiftFrom] at reduces congruenceCase
      cases reduces with
      | application functionReduces argumentReduces =>
          cases argumentReduces
          exact congruenceCase functionReduces
      | choiceDistributive leftReduces rightReduces argumentReduces =>
          cases argumentReduces
          obtain ⟨leftUnshifted, leftEqual, leftUnshiftedReduces⟩ :=
            SimultaneousReduces.ofShiftFrom left 0 leftReduces
          obtain ⟨rightUnshifted, rightEqual, rightUnshiftedReduces⟩ :=
            SimultaneousReduces.ofShiftFrom right 0 rightReduces
          subst leftEqual rightEqual
          obtain ⟨reduct, reductMany, reductBelow⟩ :=
            innerSimulated (.choice leftUnshiftedReduces rightUnshiftedReduces)
          obtain ⟨⟨_, leftMany, leftBelow⟩, ⟨_, rightMany, rightBelow⟩⟩ :=
            reductBelow.choiceInversion rfl
          exact ⟨reduct, reductMany,
            .abstractionChoice leftMany (.etaLower leftBelow) rightMany (.etaLower rightBelow)⟩
  | parallel left right =>
      simp only [shift, Term.shiftFrom] at reduces congruenceCase
      cases reduces with
      | application functionReduces argumentReduces =>
          cases argumentReduces
          exact congruenceCase functionReduces
      | parallelDistributive leftReduces rightReduces argumentReduces =>
          cases argumentReduces
          obtain ⟨leftUnshifted, leftEqual, leftUnshiftedReduces⟩ :=
            SimultaneousReduces.ofShiftFrom left 0 leftReduces
          obtain ⟨rightUnshifted, rightEqual, rightUnshiftedReduces⟩ :=
            SimultaneousReduces.ofShiftFrom right 0 rightReduces
          subst leftEqual rightEqual
          obtain ⟨reduct, reductMany, reductBelow⟩ :=
            innerSimulated (.parallel leftUnshiftedReduces rightUnshiftedReduces)
          obtain ⟨etaReduct, etaMany, etaBelow⟩ := reductBelow.parallelEta rfl
          exact ⟨etaReduct, reductMany.transitive etaMany, etaBelow⟩

/-- The record's lemma 9: a simultaneous step of a lower term is simulated by a reduction of the
upper term. -/
theorem simultaneousReduces {lower upper : Term} (below : Below lower upper) :
    ∀ {lowerResult : Term}, SimultaneousReduces lower lowerResult →
      ∃ reduct, ReducesMany upper reduct ∧ Below lowerResult reduct := by
  induction below with
  | boundVariable index =>
      intro lowerResult reduces
      cases reduces
      exact ⟨_, .reflexive _, .boundVariable index⟩
  | abstraction _ inner =>
      intro lowerResult reduces
      obtain ⟨bodyResult, resultEqual, bodyReduces⟩ := reduces.abstractionInversion
      subst resultEqual
      obtain ⟨reduct, reductMany, reductBelow⟩ := inner bodyReduces
      exact ⟨_, reductMany.abstraction, .abstraction reductBelow⟩
  | @application function functionUpper argument argumentUpper _ _ functionInner argumentInner =>
      intro lowerResult reduces
      cases reduces with
      | application functionReduces argumentReduces =>
          obtain ⟨functionReduct, functionMany, functionBelow⟩ := functionInner functionReduces
          obtain ⟨argumentReduct, argumentMany, argumentBelow⟩ := argumentInner argumentReduces
          exact ⟨_, ReducesMany.application functionMany argumentMany,
            .application functionBelow argumentBelow⟩
      | beta bodyReduces argumentReduces =>
          obtain ⟨functionReduct, functionMany, functionBelow⟩ :=
            functionInner (.abstraction bodyReduces)
          obtain ⟨argumentReduct, argumentMany, argumentBelow⟩ := argumentInner argumentReduces
          obtain ⟨result, resultMany, resultBelow⟩ :=
            functionBelow.abstractionApplication rfl argumentBelow
          exact ⟨result, (ReducesMany.application functionMany argumentMany).transitive resultMany,
            resultBelow⟩
      | choiceDistributive leftReduces rightReduces argumentReduces =>
          obtain ⟨functionReduct, functionMany, functionBelow⟩ :=
            functionInner (.choice leftReduces rightReduces)
          obtain ⟨argumentReduct, argumentMany, argumentBelow⟩ := argumentInner argumentReduces
          obtain ⟨result, resultMany, resultBelow⟩ :=
            functionBelow.choiceApplication rfl argumentBelow
          exact ⟨result, (ReducesMany.application functionMany argumentMany).transitive resultMany,
            resultBelow⟩
      | parallelDistributive leftReduces rightReduces argumentReduces =>
          obtain ⟨functionReduct, functionMany, functionBelow⟩ :=
            functionInner (.parallel leftReduces rightReduces)
          obtain ⟨argumentReduct, argumentMany, argumentBelow⟩ := argumentInner argumentReduces
          obtain ⟨result, resultMany, resultBelow⟩ :=
            functionBelow.parallelApplication rfl argumentBelow
          exact ⟨result, (ReducesMany.application functionMany argumentMany).transitive resultMany,
            resultBelow⟩
  | choice leftMany _ rightMany _ leftInner rightInner =>
      intro lowerResult reduces
      obtain ⟨leftResult, rightResult, resultEqual, leftReduces, rightReduces⟩ :=
        reduces.choiceInversion
      subst resultEqual
      obtain ⟨leftReduct, leftReductMany, leftReductBelow⟩ := leftInner leftReduces
      obtain ⟨rightReduct, rightReductMany, rightReductBelow⟩ := rightInner rightReduces
      exact ⟨_, .reflexive _, .choice (leftMany.transitive leftReductMany) leftReductBelow
        (rightMany.transitive rightReductMany) rightReductBelow⟩
  | abstractionChoice leftMany _ rightMany _ leftInner rightInner =>
      intro lowerResult reduces
      obtain ⟨bodyResult, resultEqual, bodyReduces⟩ := reduces.abstractionInversion
      subst resultEqual
      obtain ⟨leftResult, rightResult, bodyEqual, leftReduces, rightReduces⟩ :=
        bodyReduces.choiceInversion
      subst bodyEqual
      obtain ⟨leftReduct, leftReductMany, leftReductBelow⟩ := leftInner (.abstraction leftReduces)
      obtain ⟨rightReduct, rightReductMany, rightReductBelow⟩ :=
        rightInner (.abstraction rightReduces)
      exact ⟨_, .reflexive _, .abstractionChoice (leftMany.transitive leftReductMany)
        leftReductBelow (rightMany.transitive rightReductMany) rightReductBelow⟩
  | choiceUpperLeft many _ inner =>
      intro lowerResult reduces
      obtain ⟨reduct, reductMany, reductBelow⟩ := inner reduces
      exact ⟨_, .reflexive _, .choiceUpperLeft (many.transitive reductMany) reductBelow⟩
  | choiceUpperRight many _ inner =>
      intro lowerResult reduces
      obtain ⟨reduct, reductMany, reductBelow⟩ := inner reduces
      exact ⟨_, .reflexive _, .choiceUpperRight (many.transitive reductMany) reductBelow⟩
  | parallelLeft many _ inner =>
      intro lowerResult reduces
      obtain ⟨leftResult, rightResult, resultEqual, leftReduces, _⟩ := reduces.parallelInversion
      subst resultEqual
      obtain ⟨reduct, reductMany, reductBelow⟩ := inner leftReduces
      exact ⟨_, .reflexive _, .parallelLeft (many.transitive reductMany) reductBelow⟩
  | parallelRight many _ inner =>
      intro lowerResult reduces
      obtain ⟨leftResult, rightResult, resultEqual, _, rightReduces⟩ := reduces.parallelInversion
      subst resultEqual
      obtain ⟨reduct, reductMany, reductBelow⟩ := inner rightReduces
      exact ⟨_, .reflexive _, .parallelRight (many.transitive reductMany) reductBelow⟩
  | abstractionParallelLeft many _ inner =>
      intro lowerResult reduces
      obtain ⟨bodyResult, resultEqual, bodyReduces⟩ := reduces.abstractionInversion
      subst resultEqual
      obtain ⟨leftResult, rightResult, bodyEqual, leftReduces, _⟩ := bodyReduces.parallelInversion
      subst bodyEqual
      obtain ⟨reduct, reductMany, reductBelow⟩ := inner (.abstraction leftReduces)
      exact ⟨_, .reflexive _, .abstractionParallelLeft (many.transitive reductMany) reductBelow⟩
  | abstractionParallelRight many _ inner =>
      intro lowerResult reduces
      obtain ⟨bodyResult, resultEqual, bodyReduces⟩ := reduces.abstractionInversion
      subst resultEqual
      obtain ⟨leftResult, rightResult, bodyEqual, _, rightReduces⟩ := bodyReduces.parallelInversion
      subst bodyEqual
      obtain ⟨reduct, reductMany, reductBelow⟩ := inner (.abstraction rightReduces)
      exact ⟨_, .reflexive _, .abstractionParallelRight (many.transitive reductMany) reductBelow⟩
  | parallelUpper leftMany _ rightMany _ leftInner rightInner =>
      intro lowerResult reduces
      obtain ⟨leftReduct, leftReductMany, leftReductBelow⟩ := leftInner reduces
      obtain ⟨rightReduct, rightReductMany, rightReductBelow⟩ := rightInner reduces
      exact ⟨_, .reflexive _, .parallelUpper (leftMany.transitive leftReductMany) leftReductBelow
        (rightMany.transitive rightReductMany) rightReductBelow⟩
  | etaLower _ inner =>
      intro lowerResult reduces
      obtain ⟨bodyResult, resultEqual, bodyReduces⟩ := reduces.abstractionInversion
      subst resultEqual
      exact etaLowerSimultaneousReduces inner bodyReduces
  | etaUpper _ inner =>
      intro lowerResult reduces
      obtain ⟨reduct, reductMany, reductBelow⟩ := inner reduces
      exact ⟨_, etaRedexReducesMany reductMany, .etaUpper reductBelow⟩

/-- The record's lemma 10: a reading of a lower term is a reading of the upper term. -/
theorem readingOfResolves {lower upper : Term} (below : Below lower upper) :
    ∀ {reading : Term}, Resolves lower reading → Reading upper reading := by
  induction below with
  | boundVariable index => intro reading resolves; exact ⟨_, .reflexive _, resolves⟩
  | abstraction _ inner =>
      intro reading resolves
      cases resolves with
      | abstraction bodyResolves before =>
          obtain ⟨reduct, reductMany, reductResolves⟩ := inner bodyResolves
          exact ⟨_, reductMany.abstraction, .abstraction reductResolves before⟩
  | application _ _ functionInner argumentInner =>
      intro reading resolves
      cases resolves with
      | application functionResolves argumentResolves before =>
          obtain ⟨functionReduct, functionMany, functionReductResolves⟩ :=
            functionInner functionResolves
          obtain ⟨argumentReduct, argumentMany, argumentReductResolves⟩ :=
            argumentInner argumentResolves
          exact ⟨_, ReducesMany.application functionMany argumentMany,
            .application functionReductResolves argumentReductResolves before⟩
  | choice leftMany _ rightMany _ leftInner rightInner =>
      intro reading resolves
      cases resolves with
      | choiceLeft leftResolves =>
          obtain ⟨reduct, reductMany, reductResolves⟩ := leftInner leftResolves
          exact ⟨reduct, leftMany.transitive reductMany, reductResolves⟩
      | choiceRight rightResolves =>
          obtain ⟨reduct, reductMany, reductResolves⟩ := rightInner rightResolves
          exact ⟨reduct, rightMany.transitive reductMany, reductResolves⟩
  | abstractionChoice leftMany _ rightMany _ leftInner rightInner =>
      intro reading resolves
      cases resolves with
      | abstraction bodyResolves before =>
          cases bodyResolves with
          | choiceLeft leftResolves =>
              obtain ⟨reduct, reductMany, reductResolves⟩ :=
                leftInner (.abstraction leftResolves before)
              exact ⟨reduct, leftMany.transitive reductMany, reductResolves⟩
          | choiceRight rightResolves =>
              obtain ⟨reduct, reductMany, reductResolves⟩ :=
                rightInner (.abstraction rightResolves before)
              exact ⟨reduct, rightMany.transitive reductMany, reductResolves⟩
  | choiceUpperLeft many _ inner =>
      intro reading resolves
      obtain ⟨reduct, reductMany, reductResolves⟩ := inner resolves
      exact ⟨_, ReducesMany.choiceLeft _ (many.transitive reductMany), .choiceLeft reductResolves⟩
  | choiceUpperRight many _ inner =>
      intro reading resolves
      obtain ⟨reduct, reductMany, reductResolves⟩ := inner resolves
      exact ⟨_, ReducesMany.choiceRight _ (many.transitive reductMany), .choiceRight reductResolves⟩
  | parallelLeft many _ inner =>
      intro reading resolves
      cases resolves with
      | parallel leftResolves _ =>
          obtain ⟨reduct, reductMany, reductResolves⟩ := inner leftResolves
          exact ⟨reduct, many.transitive reductMany, reductResolves⟩
  | parallelRight many _ inner =>
      intro reading resolves
      cases resolves with
      | parallel _ rightResolves =>
          obtain ⟨reduct, reductMany, reductResolves⟩ := inner rightResolves
          exact ⟨reduct, many.transitive reductMany, reductResolves⟩
  | abstractionParallelLeft many _ inner =>
      intro reading resolves
      cases resolves with
      | abstraction bodyResolves before =>
          cases bodyResolves with
          | parallel leftResolves _ =>
              obtain ⟨reduct, reductMany, reductResolves⟩ :=
                inner (.abstraction leftResolves before)
              exact ⟨reduct, many.transitive reductMany, reductResolves⟩
  | abstractionParallelRight many _ inner =>
      intro reading resolves
      cases resolves with
      | abstraction bodyResolves before =>
          cases bodyResolves with
          | parallel _ rightResolves =>
              obtain ⟨reduct, reductMany, reductResolves⟩ :=
                inner (.abstraction rightResolves before)
              exact ⟨reduct, many.transitive reductMany, reductResolves⟩
  | parallelUpper leftMany _ rightMany _ leftInner rightInner =>
      intro reading resolves
      obtain ⟨leftReduct, leftReductMany, leftReductResolves⟩ := leftInner resolves
      obtain ⟨rightReduct, rightReductMany, rightReductResolves⟩ := rightInner resolves
      exact ⟨_, ReducesMany.parallel (leftMany.transitive leftReductMany)
        (rightMany.transitive rightReductMany), .parallel leftReductResolves rightReductResolves⟩
  | @etaLower inner upper _ innerReading =>
      intro reading resolves
      cases resolves with
      | abstraction bodyResolves before =>
          cases bodyResolves with
          | application functionResolves argumentResolves applicationBefore =>
              obtain ⟨unshifted, unshiftedResolves, unshiftedConvertible⟩ :=
                Resolves.ofShiftFrom inner 0 functionResolves
              cases argumentResolves with
              | boundVariable variableBefore =>
                  have readingConvertible : Convertible unshifted reading :=
                    (Convertible.symmetric (.eta unshifted)).transitive
                      ((Convertible.abstraction
                        ((Convertible.application (.symmetric unshiftedConvertible)
                          variableBefore).transitive applicationBefore)).transitive before)
                  exact innerReading (unshiftedResolves.convert readingConvertible)
  | etaUpper _ inner =>
      intro reading resolves
      obtain ⟨reduct, reductMany, reductResolves⟩ := inner resolves
      exact ⟨_, etaRedexReducesMany reductMany,
        .abstraction (.application (reductResolves.shiftFrom 0) (.boundVariable (.reflexive _))
          (.reflexive _)) (.eta reading)⟩

/-- Lemma 9 along a reduction. -/
theorem reducesMany {lower upper : Term} (below : Below lower upper) {lowerResult : Term}
    (many : ReducesMany lower lowerResult) :
    ∃ reduct, ReducesMany upper reduct ∧ Below lowerResult reduct := by
  induction many generalizing upper with
  | reflexive _ => exact ⟨upper, .reflexive _, below⟩
  | step reduces _ inner =>
      obtain ⟨middleReduct, middleMany, middleBelow⟩ := below.simultaneousReduces reduces
      obtain ⟨reduct, reductMany, reductBelow⟩ := inner middleBelow
      exact ⟨reduct, middleMany.transitive reductMany, reductBelow⟩

/-- The record's lemma 11: every reading of a lower term is a reading of the upper term. -/
theorem reading {lower upper : Term} (below : Below lower upper) {reading : Term}
    (lowerReading : Reading lower reading) : Reading upper reading := by
  obtain ⟨reduct, many, resolves⟩ := lowerReading
  obtain ⟨upperReduct, upperMany, reductBelow⟩ := below.reducesMany many
  obtain ⟨final, finalMany, finalResolves⟩ := reductBelow.readingOfResolves resolves
  exact ⟨final, upperMany.transitive finalMany, finalResolves⟩

/-- The record's lemma 12: ≼ is closed under every one-hole context. -/
theorem fill {lower upper : Term} (below : Below lower upper) :
    ∀ context : Context, Below (context.fill lower) (context.fill upper)
  | .hole => below
  | .abstraction body => .abstraction (fill below body)
  | .applicationFunction function argument =>
      .application (fill below function) (reflexive argument)
  | .applicationArgument function argument =>
      .application (reflexive function) (fill below argument)
  | .choiceLeft left right =>
      .choice (.reflexive _) (.choiceUpperLeft (.reflexive _) (fill below left))
        (.reflexive _) (.choiceUpperRight (.reflexive _) (reflexive right))
  | .choiceRight left right =>
      .choice (.reflexive _) (.choiceUpperLeft (.reflexive _) (reflexive left))
        (.reflexive _) (.choiceUpperRight (.reflexive _) (fill below right))
  | .parallelLeft left right =>
      .parallelUpper (.reflexive _) (.parallelLeft (.reflexive _) (fill below left))
        (.reflexive _) (.parallelRight (.reflexive _) (reflexive right))
  | .parallelRight left right =>
      .parallelUpper (.reflexive _) (.parallelLeft (.reflexive _) (reflexive left))
        (.reflexive _) (.parallelRight (.reflexive _) (fill below right))

end Below

/-- A simultaneous step in every one-hole context. -/
theorem SimultaneousReduces.fill {term result : Term} (reduces : SimultaneousReduces term result) :
    ∀ context : Context, SimultaneousReduces (context.fill term) (context.fill result)
  | .hole => reduces
  | .abstraction body => .abstraction (fill reduces body)
  | .applicationFunction function argument =>
      .application (fill reduces function) (SimultaneousReduces.reflexive argument)
  | .applicationArgument function argument =>
      .application (SimultaneousReduces.reflexive function) (fill reduces argument)
  | .choiceLeft left right => .choice (fill reduces left) (SimultaneousReduces.reflexive right)
  | .choiceRight left right => .choice (SimultaneousReduces.reflexive left) (fill reduces right)
  | .parallelLeft left right => .parallel (fill reduces left) (SimultaneousReduces.reflexive right)
  | .parallelRight left right => .parallel (SimultaneousReduces.reflexive left) (fill reduces right)

/-! ## The theorem -/

/-- The context whose hole is the hole of `inner` placed in the hole of `outer`. -/
def composeContexts : Context → Context → Context
  | .hole, inner => inner
  | .abstraction body, inner => .abstraction (composeContexts body inner)
  | .applicationFunction function argument, inner =>
      .applicationFunction (composeContexts function inner) argument
  | .applicationArgument function argument, inner =>
      .applicationArgument function (composeContexts argument inner)
  | .choiceLeft left right, inner => .choiceLeft (composeContexts left inner) right
  | .choiceRight left right, inner => .choiceRight left (composeContexts right inner)
  | .parallelLeft left right, inner => .parallelLeft (composeContexts left inner) right
  | .parallelRight left right, inner => .parallelRight left (composeContexts right inner)

/-- Filling a composed context fills the inner context, then the outer one. -/
theorem composeContextsFill : ∀ (outer inner : Context) (term : Term),
    (composeContexts outer inner).fill term = outer.fill (inner.fill term)
  | .hole, _, _ => rfl
  | .abstraction body, inner, term => by
      simp only [composeContexts, Context.fill, composeContextsFill body inner term]
  | .applicationFunction function argument, inner, term => by
      simp only [composeContexts, Context.fill, composeContextsFill function inner term]
  | .applicationArgument function argument, inner, term => by
      simp only [composeContexts, Context.fill, composeContextsFill argument inner term]
  | .choiceLeft left right, inner, term => by
      simp only [composeContexts, Context.fill, composeContextsFill left inner term]
  | .choiceRight left right, inner, term => by
      simp only [composeContexts, Context.fill, composeContextsFill right inner term]
  | .parallelLeft left right, inner, term => by
      simp only [composeContexts, Context.fill, composeContextsFill left inner term]
  | .parallelRight left right, inner, term => by
      simp only [composeContexts, Context.fill, composeContextsFill right inner term]

/-- Two terms have the same readings in every one-hole context. -/
def SameReadings (left right : Term) : Prop :=
  ∀ (context : Context) (reading : Term),
    Reading (context.fill left) reading ↔ Reading (context.fill right) reading

/-- Same readings in every context are kept by placing both terms in a context. -/
theorem SameReadings.fill {left right : Term} (same : SameReadings left right)
    (outer : Context) : SameReadings (outer.fill left) (outer.fill right) := by
  intro context reading
  rw [← composeContextsFill, ← composeContextsFill]
  exact same _ reading

/-- Two terms each below the other have the same readings in every context (lemmas 11 and 12). -/
theorem sameReadingsOfBelow {left right : Term} (leftBelow : Below left right)
    (rightBelow : Below right left) : SameReadings left right :=
  fun context _ => ⟨(leftBelow.fill context).reading, (rightBelow.fill context).reading⟩

/-- A simultaneous step keeps the readings in every context (lemma 4). -/
theorem sameReadingsOfSimultaneousReduces {left right : Term}
    (reduces : SimultaneousReduces left right) :
    SameReadings left right :=
  fun context _ => readingOfReducesMany (ReducesMany.single (reduces.fill context))

/-! ## Pure terms: conservativity over λβη -/

/-- Shifting keeps a term pure. -/
theorem pureShiftFrom :
    ∀ (term : Term) (cutoff : Nat), Pure term → Pure (Term.shiftFrom cutoff term)
  | .boundVariable index, cutoff, _ => by
      by_cases below : index < cutoff
      · simp [Term.shiftFrom, below, Term.Pure]
      · simp [Term.shiftFrom, below, Term.Pure]
  | .abstraction body, cutoff, pure => pureShiftFrom body (cutoff + 1) pure
  | .application function argument, cutoff, pure =>
      ⟨pureShiftFrom function cutoff pure.1, pureShiftFrom argument cutoff pure.2⟩
  | .choice _ _, _, pure => pure.elim
  | .parallel _ _, _, pure => pure.elim

/-- Substituting a pure term into a pure term gives a pure term. -/
theorem pureSubstitute : ∀ (term : Term) (depth : Nat) {replacement : Term},
    Pure term → Pure replacement → Pure (Term.substitute depth replacement term)
  | .boundVariable index, depth, replacement, _, replacementPure => by
      by_cases below : index < depth
      · simp [Term.substitute, below, Term.Pure]
      · by_cases atDepth : index = depth
        · simp [Term.substitute, atDepth, replacementPure]
        · simp [Term.substitute, below, atDepth, Term.Pure]
  | .abstraction body, depth, replacement, pure, replacementPure =>
      pureSubstitute body (depth + 1) pure (pureShiftFrom replacement 0 replacementPure)
  | .application function argument, depth, _, pure, replacementPure =>
      ⟨pureSubstitute function depth pure.1 replacementPure,
        pureSubstitute argument depth pure.2 replacementPure⟩
  | .choice _ _, _, _, pure, _ => pure.elim
  | .parallel _ _, _, _, pure, _ => pure.elim

/-- A simultaneous step of a pure term is β steps: its result is pure and βη-convertible to it. -/
theorem SimultaneousReduces.pure {term result : Term} (reduces : SimultaneousReduces term result) :
    Pure term → Pure result ∧ Convertible term result := by
  induction reduces with
  | boundVariable index => intro pure; exact ⟨pure, .reflexive _⟩
  | abstraction _ inner =>
      intro pure
      obtain ⟨resultPure, convertible⟩ := inner pure
      exact ⟨resultPure, .abstraction convertible⟩
  | application _ _ functionInner argumentInner =>
      intro pure
      obtain ⟨functionPure, functionConvertible⟩ := functionInner pure.1
      obtain ⟨argumentPure, argumentConvertible⟩ := argumentInner pure.2
      exact ⟨⟨functionPure, argumentPure⟩, .application functionConvertible argumentConvertible⟩
  | choice => intro pure; exact pure.elim
  | parallel => intro pure; exact pure.elim
  | beta _ _ bodyInner argumentInner =>
      intro pure
      obtain ⟨bodyPure, bodyConvertible⟩ := bodyInner pure.1
      obtain ⟨argumentPure, argumentConvertible⟩ := argumentInner pure.2
      exact ⟨pureSubstitute _ 0 bodyPure argumentPure,
        (Convertible.application (.abstraction bodyConvertible) argumentConvertible).transitive
          (.beta _ _)⟩
  | choiceDistributive => intro pure; exact pure.1.elim
  | parallelDistributive => intro pure; exact pure.1.elim

/-- A reduction of a pure term keeps it pure and βη-convertible. -/
theorem ReducesMany.pure {term result : Term} (many : ReducesMany term result) (pure : Pure term) :
    Pure result ∧ Convertible term result := by
  induction many with
  | reflexive _ => exact ⟨pure, .reflexive _⟩
  | step reduces _ inner =>
      obtain ⟨middlePure, middleConvertible⟩ := reduces.pure pure
      obtain ⟨resultPure, resultConvertible⟩ := inner middlePure
      exact ⟨resultPure, middleConvertible.transitive resultConvertible⟩

/-- A pure term reads as itself. -/
theorem Resolves.ofPure : ∀ {term : Term}, Pure term → Resolves term term
  | .boundVariable _, _ => .boundVariable (.reflexive _)
  | .abstraction _, pure => .abstraction (ofPure pure) (.reflexive _)
  | .application _ _, pure => .application (ofPure pure.1) (ofPure pure.2) (.reflexive _)
  | .choice _ _, pure => pure.elim
  | .parallel _ _, pure => pure.elim

/-- A reading of a pure term is βη-convertible to it. -/
theorem Resolves.convertibleOfPure {term reading : Term} (resolves : Resolves term reading) :
    Pure term → Convertible term reading := by
  induction resolves with
  | boundVariable before => intro _; exact before
  | abstraction _ before inner =>
      intro pure; exact (Convertible.abstraction (inner pure)).transitive before
  | application _ _ before functionInner argumentInner =>
      intro pure
      exact (Convertible.application (functionInner pure.1) (argumentInner pure.2)).transitive
        before
  | choiceLeft => intro pure; exact pure.elim
  | choiceRight => intro pure; exact pure.elim
  | parallel => intro pure; exact pure.elim

/-- The readings of a pure term are the terms βη-convertible to it. -/
theorem readingOfPure {term reading : Term} (pure : Pure term) :
    Reading term reading ↔ Convertible term reading := by
  constructor
  · intro ⟨reduct, many, resolves⟩
    obtain ⟨reductPure, reductConvertible⟩ := many.pure pure
    exact reductConvertible.transitive (resolves.convertibleOfPure reductPure)
  · intro convertible
    exact ⟨term, .reflexive _, (Resolves.ofPure pure).convert convertible⟩

end LambdaJit.SyntacticConsistency
