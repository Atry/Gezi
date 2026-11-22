import LambdaJit.EndToEnd
import LambdaJit.Normalisation
import LambdaJit.ContextualPreorderTop

/-!
# Lemma statements proved sound by kernel decisions

A lemma's statement, as `gezi/prolog/gezi/lean_statements.pl` exports it, is a pair of
article terms whose variables are the lemma's metavariables, and it is sound, `EquationSound`, when
the interpretations of its two sides are contextually equivalent (≃_O of DdLP96's Definition 14)
under every valuation of the variables (module `EndToEnd`). This module proves a statement sound,
for every valuation at once, by four decisions that the kernel evaluates: the fuelled normal form
of module `Normalisation` (`Semantics.Term.normalFormWithin`) brings its two sides to one term, leftmost outermost contraction
brings them to a common term, the statement is an instance of a numbered equation, or its two
sides have one simplification by absorption and idempotence.

- `abstracted signature variables term`: the interpretation of `term` with the variables `variables`
  abstracted, the variable `variables[i]` read as the variable bound by the i-th of
  `variables.length` abstractions, the outermost first (`listedValuation`).
- `abstractedApplied`: that term applied to the values a valuation gives the variables equals,
  by the β rule, the interpretation under the valuation, when every variable of `term` is listed.
  Substitution passes into the interpretation (`Interpretation.substituteInterpret`), since the
  curried form of a constant is closed (`Interpretation.substituteCurried`), so the general lemma
  `Interpretation.abstractionsAppliedFrom` applies.
- `equationSoundOfAbstractedDerivable`: a statement is sound when its two abstracted sides, the
  variables being those of both sides, are equal by ⊢_{λ-lattice-η} from no hypothesis, since
  so are they applied to the values of any valuation, and each applied term is the interpretation
  of its side by the β rule. The decisions below and module `LibraryLemmaProofs` prove that
  equation.
- `normalisedEqual signature fuel left right`: the normal form by weak head reduction and then the
  subterms, making at most `fuel` contractions on each side, brings `abstracted signature variables left` and
  `abstracted signature variables right` to one term, the variables being those of both sides.
  `equationSoundOfNormalisedEqual`: then the statement is sound, since the two abstracted terms are equal by
  ⊢_{λ-lattice-η} (`Semantics.derivableOfNormalFormWithinEqual`).
- `statementNormalised`, `statementSoundOfNormalised`: the same for a statement as a pair, at the
  fixed fuel `normalisationFuel`.

The normaliser uses the β rule and the η rule only, none of the numbered equations, so it proves a
lemma derivable by those rules and congruence whose sides have normal forms within the fuel. A
lemma whose sides have no normal form, such as a row of a recursive function whose fixpoint
unfolds without end, may still have sides that leftmost outermost contraction brings to a common
term, which a third decision finds:

- `contractions fuel term`: the terms that leftmost outermost contraction
  (`Semantics.Term.step`) reaches from `term` with at most `fuel` contractions, each equal to
  `term` by the β rule and the η rule (`contractionsSound`, from `Semantics.stepSound`).
- `contractionsMeet fuel left right`, `derivableOfContractionsMeet`: whether the two lists share a
  term, and then `left` and `right` are equal by ⊢_{λ-lattice-η}.
- `statementContracted`, `statementSoundOfContracted`: the same for a statement as a pair, its
  sides abstracted, at the fixed fuel `contractionFuel`.

A statement that is itself an instance of a numbered equation is proved by a decision of its own:

- `numberedOperands number left`: the operands of the numbered equation `number`
  (`EndToEnd.numberedEquation`) read off a left side by the shape of that equation's left side.
- `numberedInstance`, `numberedInstanceSound`: whether, for one of the numbers 1 to 10 (7 gives M = M), the
  equation over the operands read off the statement's left side is the statement, term for term;
  a statement it accepts is sound by `EndToEnd.numberedEquationSound`.

The lemmas of the native route's knowledge modules put, beside a term, members that the λ-lattice
laws and the greatest element `top` remove: a judgment S + (S ∥ T), the typed version of an
application, a marker equal to its argument by its body and the idempotence of the parallel, a
guard whose body is `top` + t or t + `top`, and a type of the zero universe, a parallel with an operand
that is `top`. Here `top` = Y (λz. λx. z ∥ x), the term that stands for no answer: the library's file `top`,
which an article encodes as the constant `apply` applied to the thunk constants of Y and of
λz. λx. z ∥ x (`articleTop`). Its interpretation, `interpretedTop`, is `top` after two β steps
(`interpretedTopDerivable`), and `withTop` writes `top` for it. `top` is greatest for ⊑_O
(`ContextualPreorder.contextualTop`), so `top` + M ≃_O M, M + `top` ≃_O M, `top` ∥ M ≃_O `top` and M ∥ `top` ≃_O `top`
(module `ContextualPreorderTop`); these are contextual equivalences, not equations of
⊢_{λ-lattice-η}, which does not derive them. A fourth decision finds those members:

- `developed term`: one development, every application whose developed function is an abstraction
  contracted by the β rule, `top` kept whole (`developedSound`).
- `simplified term`: the term simplified bottom up by `top` ∥ M = `top`, M ∥ `top` = `top`, `top` + M = M and
  M + `top` = M (contextual equivalences), and by M ∥ M = M, M + M = M, M + (M ∥ N) = M by (6),
  f a + (f (a ∥ d) ∥ r) = f a and f a + f (a ∥ d) = f a by context monotonicity, T10, and the η
  rule, λx. f x = f when x ∉ FV(f) (`typedVersionAbsorbed`, `filteredApplicationRefines`,
  `parallelSimplified`, `choiceSimplified`, `abstractionSimplified`, `simplifiedSound`), `top` kept
  whole.
- `absorbedWithin count left right`, `absorbedWithinSound`: whether the two terms have one
  simplification after the same number of developments, at most `count`, each development made on
  the simplified terms; then they are contextually equivalent.
- `statementAbsorbed`, `statementSoundOfAbsorbed`: the same for a statement as a pair, its sides
  interpreted under the abstractions of its variables, at the fixed bound
  `absorptionDevelopments`, `top` written as `ContextualPreorder.top` in each side first;
  `equationSoundOfAbstractedEquivalent` takes the contextual equivalence of the abstracted sides to
  the statement's soundness.

The command `lemma_soundness` (module `LemmaSoundness`) has the kernel check, on each exported
statement that module `LibraryLemmaProofs` does not prove by hand, the theorem of each decision in
turn (`LemmaSoundness.decisionTheorems`), and states the statement as a theorem proved by the first
the kernel accepts. A lemma that no decision accepts stays a named axiom unless module
`LibraryLemmaProofs` proves it.
-/

namespace LambdaJit.StatementNormalisation

open LambdaJit.Semantics (DerivableLatticeEta)
open LambdaJit.Interpretation
open LambdaJit.EndToEnd (EquationSound EquationDerivable equationSoundOfDerivable numberedEquation
  numberedEquationSound)
open LambdaJit.Readback (abstractions)

-- The signature of a statement's thunk constants, under which every theorem below reads its
-- terms (D7.1).
variable {signature : Signature}

/-- The valuation that reads a variable, by name and type, as `values[i]` for the first position
`i` at which `variables` lists it, and any other variable as `top` (`ContextualPreorder.top`):
any closed term serves there, since no proof reads it. -/
def listedValuation : List (Article.Name × Article.LogicType) → List Semantics.Term →
    Article.Name → Article.LogicType → Semantics.Term
  | (variableName, variableType) :: variables, value :: values, name, type =>
      if variableName = name ∧ variableType = type then value
      else listedValuation variables values name type
  | _, _, _, _ => ContextualPreorder.top

/-- Listing the values a valuation gives the listed variables gives the valuation back on every
listed variable. -/
theorem listedValuationMapped (valuation : Valuation) :
    ∀ (variables : List (Article.Name × Article.LogicType)), ∀ occurrence ∈ variables,
      listedValuation variables (variables.map fun listed => valuation listed.1 listed.2)
        occurrence.1 occurrence.2 = valuation occurrence.1 occurrence.2
  | [], _, member => nomatch member
  | (variableName, variableType) :: variables, (name, type), member => by
      simp only [List.map_cons, listedValuation]
      by_cases same : variableName = name ∧ variableType = type
      · rw [if_pos same, same.1, same.2]
      · rw [if_neg same]
        have inRest : (name, type) ∈ variables := by
          cases member with
          | head => exact absurd ⟨rfl, rfl⟩ same
          | tail _ rest => exact rest
        exact listedValuationMapped valuation variables (name, type) inRest

/-- Substitution passes into the listed values. -/
theorem substituteListedValuation (depth : Nat) (replacement : Semantics.Term) :
    ∀ (variables : List (Article.Name × Article.LogicType)) (values : List Semantics.Term)
      (name : Article.Name) (type : Article.LogicType),
      Semantics.Term.substitute depth replacement (listedValuation variables values name type) =
        listedValuation variables (values.map (Semantics.Term.substitute depth replacement))
          name type
  | (variableName, variableType) :: variables, value :: values, name, type => by
      simp only [listedValuation, List.map_cons]
      by_cases same : variableName = name ∧ variableType = type
      · rw [if_pos same, if_pos same]
      · rw [if_neg same, if_neg same]
        exact substituteListedValuation depth replacement variables values name type
  | [], _, _, _ => by
      simp only [listedValuation]
      exact ContextualPreorder.substituteClosed ContextualPreorder.closedTop _ _
  | _ :: _, [], _, _ => by
      simp only [listedValuation, List.map_nil]
      exact ContextualPreorder.substituteClosed ContextualPreorder.closedTop _ _

/-- The variables of a term, from the last occurrence to the first, before `found`, without the
appends of `termVariables`, which are quadratic in the length of a spine. -/
def variablesInto (found : List (Article.Name × Article.LogicType)) :
    Article.Term → List (Article.Name × Article.LogicType)
  | .termVariable name type => (name, type) :: found
  | .constant _ _ => found
  | .application function argument => variablesInto (variablesInto found argument) function

theorem variablesIntoListed : ∀ (term : Article.Term) (found : List (Article.Name × Article.LogicType))
    (occurrence : Article.Name × Article.LogicType),
    occurrence ∈ termVariables term ∨ occurrence ∈ found → occurrence ∈ variablesInto found term
  | .termVariable name type, found, occurrence, member => by
      simp only [termVariables, List.mem_singleton] at member
      simp only [variablesInto, List.mem_cons]
      exact member
  | .constant _ _, found, occurrence, member => by
      simp only [termVariables, List.not_mem_nil, false_or] at member
      exact member
  | .application function argument, found, occurrence, member => by
      simp only [termVariables, List.mem_append] at member
      apply variablesIntoListed function
      rcases member with (inFunction | inArgument) | inFound
      · exact Or.inl inFunction
      · exact Or.inr (variablesIntoListed argument found occurrence (Or.inl inArgument))
      · exact Or.inr (variablesIntoListed argument found occurrence (Or.inr inFound))

/-- Whether `candidate` is one of `variables`. -/
def variableListed (candidate : Article.Name × Article.LogicType) :
    List (Article.Name × Article.LogicType) → Bool
  | [] => false
  | other :: rest => if other = candidate then true else variableListed candidate rest

theorem memberOfVariableListed {candidate : Article.Name × Article.LogicType} :
    ∀ {variables : List (Article.Name × Article.LogicType)}, variableListed candidate variables = true →
      candidate ∈ variables
  | [], listed => by simp only [variableListed] at listed; cases listed
  | other :: rest, listed => by
      simp only [variableListed] at listed
      split at listed
      · rename_i same; subst same; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (memberOfVariableListed listed)

/-- The variables of `variables` not in `found`, each once, before `found`. -/
def distinctVariables (found : List (Article.Name × Article.LogicType)) :
    List (Article.Name × Article.LogicType) → List (Article.Name × Article.LogicType)
  | [] => found
  | candidate :: rest =>
      if variableListed candidate found then distinctVariables found rest
      else distinctVariables (candidate :: found) rest

theorem distinctVariablesListed {occurrence : Article.Name × Article.LogicType} :
    ∀ (found variables : List (Article.Name × Article.LogicType)),
      occurrence ∈ variables ∨ occurrence ∈ found → occurrence ∈ distinctVariables found variables
  | found, [], member => by
      simp only [List.not_mem_nil, false_or] at member
      exact member
  | found, candidate :: rest, member => by
      simp only [distinctVariables]
      split
      · rename_i listed
        apply distinctVariablesListed found rest
        rcases member with inVariables | inFound
        · rcases List.mem_cons.mp inVariables with same | inRest
          · subst same; exact Or.inr (memberOfVariableListed listed)
          · exact Or.inl inRest
        · exact Or.inr inFound
      · apply distinctVariablesListed (candidate :: found) rest
        rcases member with inVariables | inFound
        · rcases List.mem_cons.mp inVariables with same | inRest
          · subst same; exact Or.inr List.mem_cons_self
          · exact Or.inl inRest
        · exact Or.inr (List.mem_cons_of_mem _ inFound)

/-- The variables of the two sides of an equation, each once: the binders `statementAbsorbed`
abstracts. `termVariables` lists a variable as often as it occurs, and a statement whose common
constants are read as variables (`openedStatement`) has thousands of occurrences of a dozen, which,
listed as they occur, would put thousands of abstractions around its sides. -/
def sidesVariables (left right : Article.Term) : List (Article.Name × Article.LogicType) :=
  distinctVariables [] (variablesInto (variablesInto [] right) left)

theorem leftVariableListed {left right : Article.Term} {occurrence : Article.Name × Article.LogicType}
    (member : occurrence ∈ termVariables left) : occurrence ∈ sidesVariables left right :=
  distinctVariablesListed [] _ (Or.inl (variablesIntoListed left _ occurrence (Or.inl member)))

theorem rightVariableListed {left right : Article.Term} {occurrence : Article.Name × Article.LogicType}
    (member : occurrence ∈ termVariables right) : occurrence ∈ sidesVariables left right :=
  distinctVariablesListed [] _
    (Or.inl (variablesIntoListed left _ occurrence (Or.inr (variablesIntoListed right [] occurrence (Or.inl member)))))

/-- `term` with the variables `variables` abstracted: its interpretation under the valuation that
reads `variables[i]` as the variable bound by the i-th of `variables.length` enclosing
abstractions, the outermost first, under those abstractions. -/
def abstracted (signature : Signature) (variables : List (Article.Name × Article.LogicType))
    (term : Article.Term) : Semantics.Term :=
  abstractions variables.length
    (interpret signature (listedValuation variables (variablesBelow variables.length)) term)

/-- `term` with its variables abstracted, applied to the values a valuation gives them, equals the
interpretation of `term` under the valuation by the β rule, when every variable of `term` is
listed. -/
theorem abstractedApplied {hypotheses : Semantics.Term → Semantics.Term → Prop}
    (valuation : Valuation) (variables : List (Article.Name × Article.LogicType))
    (term : Article.Term) (listed : ∀ occurrence ∈ termVariables term, occurrence ∈ variables) :
    DerivableLatticeEta hypotheses
      (applyAll (abstracted signature variables term)
        (variables.map fun listedVariable => valuation listedVariable.1 listedVariable.2))
      (interpret signature valuation term) := by
  have applied := abstractionsAppliedFrom (hypotheses := hypotheses)
    (fun values => interpret signature (listedValuation variables values) term)
    (fun depth replacement values => by
      simp only [substituteInterpret]
      congr 1
      funext name type
      exact substituteListedValuation depth replacement variables values name type)
    variables.length []
    (variables.map fun listedVariable => valuation listedVariable.1 listedVariable.2)
    (List.length_map _)
  simp only [List.map_nil, List.nil_append] at applied
  rw [interpretAgree term (fun occurrence member =>
    listedValuationMapped valuation variables occurrence (listed occurrence member))] at applied
  exact applied

/-- An equation is derivable under every valuation when its two sides with their variables
abstracted, the variables of both sides, are equal by ⊢_{λ-lattice-η} from no hypothesis: for
every valuation, each side's interpretation is its abstracted side applied to the values of the
variables (`abstractedApplied`), and applying the two equal abstracted sides to the same values
gives equal terms. -/
theorem equationDerivableOfAbstractedDerivable {left right : Article.Term}
    (abstractedEqual : DerivableLatticeEta (fun _ _ => False)
      (abstracted signature (termVariables left ++ termVariables right) left)
      (abstracted signature (termVariables left ++ termVariables right) right)) :
    EquationDerivable signature left right := by
  intro valuation
  have leftApplied := abstractedApplied (signature := signature) (hypotheses := fun _ _ => False)
    valuation
    (termVariables left ++ termVariables right) left
    (fun _ member => List.mem_append_left _ member)
  have rightApplied := abstractedApplied (signature := signature) (hypotheses := fun _ _ => False)
    valuation
    (termVariables left ++ termVariables right) right
    (fun _ member => List.mem_append_right _ member)
  exact .transitive (.symmetric leftApplied)
    (.transitive (applyAllCongruence _ abstractedEqual) rightApplied)

/-- An equation whose two sides, their variables abstracted, are equal by ⊢_{λ-lattice-η} from
no hypothesis is sound (`equationDerivableOfAbstractedDerivable`). -/
theorem equationSoundOfAbstractedDerivable {left right : Article.Term}
    (abstractedEqual : DerivableLatticeEta (fun _ _ => False)
      (abstracted signature (termVariables left ++ termVariables right) left)
      (abstracted signature (termVariables left ++ termVariables right) right)) :
    EquationSound signature left right :=
  equationSoundOfDerivable (equationDerivableOfAbstractedDerivable abstractedEqual)

/-- Whether the normal form by weak head reduction and then the subterms
(`Semantics.Term.normalFormWithin`), making at most `fuel` contractions on each side, brings the two
sides with their variables abstracted, the variables of both sides, to one term. -/
def normalisedEqual (signature : Signature) (fuel : Nat) (left right : Article.Term) : Bool :=
  match Semantics.Term.normalFormWithin fuel
      (abstracted signature (termVariables left ++ termVariables right) left),
      Semantics.Term.normalFormWithin fuel
        (abstracted signature (termVariables left ++ termVariables right) right) with
  | some leftNormal, some rightNormal => leftNormal == rightNormal
  | _, _ => false

/-- The two sides of an equation the normaliser brings to one normal form, their variables
abstracted, are equal by ⊢_{λ-lattice-η} from no hypothesis
(`Semantics.derivableOfNormalFormWithinEqual`). -/
theorem abstractedDerivableOfNormalisedEqual {fuel : Nat} {left right : Article.Term}
    (normalised : normalisedEqual signature fuel left right = true) :
    DerivableLatticeEta (fun _ _ => False)
      (abstracted signature (termVariables left ++ termVariables right) left)
      (abstracted signature (termVariables left ++ termVariables right) right) := by
  unfold normalisedEqual at normalised
  split at normalised
  · rename_i leftNormal rightNormal leftNormalised rightNormalised
    simp only [beq_iff_eq] at normalised
    subst normalised
    exact Semantics.derivableOfNormalFormWithinEqual leftNormalised rightNormalised
  · cases normalised

/-- An equation whose two sides the normaliser brings to one normal form, with their variables
abstracted, is sound (`abstractedDerivableOfNormalisedEqual`). -/
theorem equationSoundOfNormalisedEqual {fuel : Nat} {left right : Article.Term}
    (normalised : normalisedEqual signature fuel left right = true) : EquationSound signature left right :=
  equationSoundOfAbstractedDerivable (abstractedDerivableOfNormalisedEqual normalised)

/-- The fuel at which the exported lemma statements are normalised, the depth and the budget of
`Semantics.Term.normalFormWithin`. Of the 26 lemmas of prelude, guard_laws, parallel_types and
filtered_recursion_naturals, the 15 whose sides have normal forms take at most 25 contractions on a
side, and the other 11 have none within 3000 (measured 2026-10-07 with `#eval` and the leftmost
outermost normaliser `Semantics.Term.normalise`, the metavariables abstracted). A statement whose
sides have no normal form spends the whole budget before the decision fails, so a larger fuel only
makes the decision longer on the statements without one; `statementNormalisedLong` is tried at a
larger fuel after the decisions that accept those. -/
def normalisationFuel : Nat := 100

/-- Whether the normal form brings the two sides of `statement` to one term within
`normalisationFuel` contractions on each side. -/
def statementNormalised (statement : EndToEnd.Statement) : Bool :=
  normalisedEqual statement.signature normalisationFuel statement.left statement.right

/-- A statement that `statementNormalised` accepts is sound. -/
theorem statementSoundOfNormalised {statement : EndToEnd.Statement}
    (normalised : statementNormalised statement = true) : statement.Sound :=
  equationSoundOfNormalisedEqual normalised

/-! ## A common term under leftmost outermost contraction -/

/-- The terms that leftmost outermost contraction (`Semantics.Term.step`) reaches from `term` with
at most `fuel` contractions, in order, `term` first; the list stops early at a term with no redex. -/
def contractions : Nat → Semantics.Term → List Semantics.Term
  | 0, term => [term]
  | fuel + 1, term =>
      term :: match Semantics.Term.step term with
        | some contracted => contractions fuel contracted
        | none => []

/-- Every term of `contractions fuel term` is equal to `term` by ⊢_{λ-lattice-η} from any
hypotheses: the β rule and the η rule at each contraction (`Semantics.stepSound`), joined by
transitivity. -/
theorem contractionsSound {hypotheses : Semantics.Term → Semantics.Term → Prop} :
    ∀ {fuel : Nat} {term reached : Semantics.Term}, reached ∈ contractions fuel term →
      DerivableLatticeEta hypotheses term reached := by
  intro fuel
  induction fuel with
  | zero =>
      intro term reached member
      simp only [contractions, List.mem_singleton] at member
      subst member
      exact .reflexive _
  | succ remaining remainingSound =>
      intro term reached member
      simp only [contractions, List.mem_cons] at member
      rcases member with same | later
      · subst same
        exact .reflexive _
      · split at later
        · rename_i contracted stepped
          exact .transitive (Semantics.stepSound stepped) (remainingSound later)
        · cases later

/-- Whether some term that leftmost outermost contraction reaches from `left` with at most `fuel`
contractions is one that it reaches from `right` with at most `fuel` contractions. -/
def contractionsMeet (fuel : Nat) (left right : Semantics.Term) : Bool :=
  (contractions fuel left).any fun reached => (contractions fuel right).contains reached

/-- Two terms whose contractions meet are equal by ⊢_{λ-lattice-η} from any hypotheses: each
is equal to the common term (`contractionsSound`). -/
theorem derivableOfContractionsMeet {hypotheses : Semantics.Term → Semantics.Term → Prop}
    {fuel : Nat} {left right : Semantics.Term} (meet : contractionsMeet fuel left right = true) :
    DerivableLatticeEta hypotheses left right := by
  simp only [contractionsMeet, List.any_eq_true, List.contains_iff_mem] at meet
  obtain ⟨reached, leftMember, rightMember⟩ := meet
  exact .transitive (contractionsSound leftMember) (.symmetric (contractionsSound rightMember))

/-- The fuel of the joint contraction of the exported lemma statements, on each side. The four
rows of recursive functions of prelude that neither the normaliser nor a numbered equation proves,
natural_equal_successor_successor, natural_at_least_successor_successor,
natural_difference_successor_successor and natural_double_successor, have sides without normal
forms, since each side unfolds a fixpoint; their two sides, the metavariables abstracted, reach a
common term after 27 and 8, 27 and 8, 26 and 8, and 20 and 12 contractions, the left side's
first (measured 2026-10-07 with `#eval` on the export of prelude, guard_laws, parallel_types,
filtered_recursion_naturals, lattice_types and contracts, the pair with the fewest contractions in
all). The 18 lemmas of that export that the normaliser proves reach a common term within 25
contractions on a side as well, and the 12 that module `LibraryLemmaProofs` proves by hand reach
none within 60. The kernel's evaluation of the decision on a statement takes about 2.5 to 4
seconds, about as long as the normaliser's at its fuel, whether it accepts the statement or not
(measured 2026-10-07), so that the time is not in the contractions. -/
def contractionFuel : Nat := 30

/-- Whether the two sides of `statement`, with their variables abstracted, the variables of both
sides, reach a common term under leftmost outermost contraction within `contractionFuel`
contractions on each side. -/
def statementContracted (statement : EndToEnd.Statement) : Bool :=
  contractionsMeet contractionFuel
    (abstracted statement.signature (termVariables statement.left ++ termVariables statement.right)
      statement.left)
    (abstracted statement.signature (termVariables statement.left ++ termVariables statement.right)
      statement.right)

/-- A statement that `statementContracted` accepts is sound: its abstracted sides are equal by
⊢_{λ-lattice-η} from no hypothesis (`derivableOfContractionsMeet`). -/
theorem statementSoundOfContracted {statement : EndToEnd.Statement}
    (contracted : statementContracted statement = true) : statement.Sound :=
  equationSoundOfAbstractedDerivable (derivableOfContractionsMeet contracted)

/-! ## The article term of `top` -/

/-- The signature of `articleTop`'s two thunk constants: Y = λf. (λx. f (x x)) (λx. f (x x)) and
λz. λx. z ∥ x. -/
def topSignature : Signature :=
  [(⟨["LambdaJit", "thunk"], "0"⟩,
      .apply (.thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 1))) [.slot 1] [.slot 0])
        (.thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 1))) [.slot 1] [.slot 0]),
      [.slot 0]),
    (⟨["LambdaJit", "thunk"], "1"⟩, .parallel (.slot 0) (.slot 1), [.slot 0, .slot 1])]

/-- The article term an article encodes the library's `top` as (`corpora/library/top.lambdalattice`),
under `topSignature`: the constant `apply` applied to the thunk constant of Y and to that of
λz. λx. z ∥ x. The interpretation reads no type, so the constants carry the type of terms here. -/
def articleTop : Article.Term :=
  .application
    (.application (.constant applyName (.operator ⟨["LambdaJit"], "term"⟩ []))
      (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
    (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))

/-! ## Instances of the numbered equations -/

/-- The operands M, N, P, A and B of the numbered equation `number` (`EndToEnd.numberedEquation`)
read off `left` by the shape of that equation's left side alone, each operator of the encoding
taken as any constant applied to two terms and each operand the equation does not use read as
`articleTop`, a closed article term that no equation reads; `none` when `left` lacks the shape or
`number` is none of 1 to 6 and 8 to 10. Nothing is checked here: `numberedInstance` compares the
whole statement with the equation built from the operands. -/
def numberedOperands : Nat → Article.Term →
    Option (Article.Term × Article.Term × Article.Term × Article.Term × Article.Term)
  -- (1) M + N and (3) M ∥ N.
  | 1, .application (.application (.constant _ _) first) second
  | 3, .application (.application (.constant _ _) first) second =>
      some (first, second, articleTop, articleTop, articleTop)
  -- (2) (M + N) + P, (4) (M ∥ N) ∥ P, (8) (M + N) P and (9) (M ∥ N) P.
  | 2, .application (.application (.constant _ _)
        (.application (.application (.constant _ _) first) second)) third
  | 4, .application (.application (.constant _ _)
        (.application (.application (.constant _ _) first) second)) third
  | 8, .application (.application (.constant _ _)
        (.application (.application (.constant _ _) first) second)) third
  | 9, .application (.application (.constant _ _)
        (.application (.application (.constant _ _) first) second)) third =>
      some (first, second, third, articleTop, articleTop)
  -- (5) M ∥ (M + N) and (6) M + (M ∥ N).
  | 5, .application (.application (.constant _ _) first)
        (.application (.application (.constant _ _) _) second)
  | 6, .application (.application (.constant _ _) first)
        (.application (.application (.constant _ _) _) second) =>
      some (first, second, articleTop, articleTop, articleTop)
  -- (10) M A + M (A + B).
  | 10, .application (.application (.constant _ _)
        (.application (.application (.constant _ _) first) argument))
        (.application (.application (.constant _ _) _)
          (.application (.application (.constant _ _) _) addition)) =>
      some (first, articleTop, articleTop, argument, addition)
  | _, _ => none

/-- Whether `statement` is an instance of one of the numbered equations (1) to (6) and (8) to (10),
for which `numberedOperands` is defined: for some number, the equation over the operands `numberedOperands` reads off the statement's left side is,
term for term, the statement. -/
def numberedInstance (statement : EndToEnd.Statement) : Bool :=
  (List.range 10).any fun index =>
    match numberedOperands (index + 1) statement.left with
    | some (first, second, third, argument, addition) =>
        (statement.left, statement.right) ==
          numberedEquation (index + 1) first second third argument addition
    | none => false

/-- A statement that `numberedInstance` accepts is sound, as every instance of a numbered equation
is (`EndToEnd.numberedEquationSound`). -/
theorem numberedInstanceSound {statement : EndToEnd.Statement}
    (isInstance : numberedInstance statement = true) : statement.Sound := by
  simp only [numberedInstance, List.any_eq_true] at isInstance
  obtain ⟨index, _, matched⟩ := isInstance
  split at matched
  · simp only [beq_iff_eq, Prod.ext_iff] at matched
    show EquationSound statement.signature statement.left statement.right
    rw [matched.1, matched.2]
    exact numberedEquationSound _ _ _ _ _ _
  · cases matched

/-! ## Members that absorption removes -/

/-! ### `top`

`topSignature` and `articleTop` are defined before the numbered equations, which use `articleTop`. -/

/-- The interpretation of `articleTop`, written out: (λa. λb. a b) Y (λz. λx. z ∥ x). -/
def interpretedTop : Semantics.Term :=
  .application
    (.application
      (.abstraction (.abstraction (.application (.boundVariable 1) (.boundVariable 0))))
      ContextualPreorder.fixedPointCombinator)
    ContextualPreorder.functionalOfTop

/-- `interpretedTop` is the interpretation of `articleTop` under every valuation: the article term
holds no variable. -/
theorem interpretArticleTop (valuation : Valuation) :
    interpret topSignature valuation articleTop = interpretedTop := by
  simp only [articleTop, interpret]
  decide +kernel

/-- `interpretedTop` is `top` by the β rule, twice: (λa. λb. a b) Y F = (λb. Y b) F = Y F. -/
theorem interpretedTopDerivable {hypotheses : Semantics.Term → Semantics.Term → Prop} :
    DerivableLatticeEta hypotheses interpretedTop ContextualPreorder.top :=
  .transitive
    (DerivableLatticeEta.congruenceFunction ContextualPreorder.functionalOfTop
      (.transitive (.beta _ _) (by
        simp only [Semantics.Term.instantiate, Semantics.Term.substitute, Semantics.Term.shift,
          Semantics.Term.shiftFrom]
        exact .reflexive _)))
    (.transitive (.beta _ _) (by
      simp only [Semantics.Term.instantiate, Semantics.Term.substitute, Semantics.Term.shift,
        Semantics.Term.shiftFrom]
      exact .reflexive _))

/-- `term` with `top` = Y (λz. λx. z ∥ x) (`ContextualPreorder.top`) written for every
occurrence of `interpretedTop`, so that the simplification below finds `top` in one spelling. -/
def withTop : Semantics.Term → Semantics.Term
  | .application function argument =>
      if Semantics.Term.application function argument = interpretedTop then
        ContextualPreorder.top
      else .application (withTop function) (withTop argument)
  | .abstraction body => .abstraction (withTop body)
  | .choice left right => .choice (withTop left) (withTop right)
  | .parallel left right => .parallel (withTop left) (withTop right)
  | other => other

/-- A term equals itself with `top` in one spelling, by the β rule at each occurrence of
`interpretedTop` (`interpretedTopDerivable`) under the congruences. -/
theorem withTopDerivable {hypotheses : Semantics.Term → Semantics.Term → Prop} :
    ∀ term : Semantics.Term, DerivableLatticeEta hypotheses term (withTop term)
  | .application function argument => by
      simp only [withTop]
      split
      · rename_i isTop
        rw [isTop]
        exact interpretedTopDerivable
      · exact .transitive
          (DerivableLatticeEta.congruenceFunction argument (withTopDerivable function))
          (.congruenceArgument _ (withTopDerivable argument))
  | .abstraction body => by
      simp only [withTop]
      exact .congruenceAbstraction (withTopDerivable body)
  | .choice left right => by
      simp only [withTop]
      exact DerivableLatticeEta.congruenceChoice (withTopDerivable left)
        (withTopDerivable right)
  | .parallel left right => by
      simp only [withTop]
      exact .transitive
        (DerivableLatticeEta.congruenceParallelLeft right (withTopDerivable left))
        (DerivableLatticeEta.congruenceParallelRight _ (withTopDerivable right))
  | .boundVariable _ => by simp only [withTop]; exact .reflexive _

/-! ### Developments and simplifications that keep `top` whole -/

/-- An equation derived by ⊢_{λ-lattice-η} holds under any number of abstractions, by the
congruence of the abstraction. -/
theorem derivableUnderAbstractions {left right : Semantics.Term}
    (equal : DerivableLatticeEta (fun _ _ => False) left right) :
    ∀ count : Nat, DerivableLatticeEta (fun _ _ => False) (abstractions count left) (abstractions count right)
  | 0 => equal
  | count + 1 => .congruenceAbstraction (derivableUnderAbstractions equal count)

/-- `Semantics.Term.shiftFrom cutoff term`, written with the recursor of `Semantics.Term` rather
than by structural recursion, for the kernel's evaluation of the decisions (`shiftFromKernelEq`):
the kernel reduces a definition by structural recursion through its `brecOn`, which carries the
results of every recursive call, and the recursor by iota steps alone. Compiled code runs
`Semantics.Term.shiftFrom` itself. -/
@[implemented_by Semantics.Term.shiftFrom]
def shiftFromKernel (cutoff : Nat) (term : Semantics.Term) : Semantics.Term :=
  Semantics.Term.rec (motive := fun _ => Nat → Semantics.Term)
    (fun index cutoff => if index < cutoff then .boundVariable index else .boundVariable (index + 1))
    (fun _ body cutoff => .abstraction (body (cutoff + 1)))
    (fun _ _ function argument cutoff => .application (function cutoff) (argument cutoff))
    (fun _ _ left right cutoff => .choice (left cutoff) (right cutoff))
    (fun _ _ left right cutoff => .parallel (left cutoff) (right cutoff))
    term cutoff

theorem shiftFromKernelEq (term : Semantics.Term) :
    ∀ cutoff : Nat, shiftFromKernel cutoff term = Semantics.Term.shiftFrom cutoff term := by
  induction term with
  | boundVariable index => intro cutoff; rfl
  | abstraction body bodyEqual =>
      intro cutoff
      show Semantics.Term.abstraction (shiftFromKernel (cutoff + 1) body) = _
      rw [bodyEqual]; rfl
  | application function argument functionEqual argumentEqual =>
      intro cutoff
      show Semantics.Term.application (shiftFromKernel cutoff function) (shiftFromKernel cutoff argument) = _
      rw [functionEqual, argumentEqual]; rfl
  | choice left right leftEqual rightEqual =>
      intro cutoff
      show Semantics.Term.choice (shiftFromKernel cutoff left) (shiftFromKernel cutoff right) = _
      rw [leftEqual, rightEqual]; rfl
  | parallel left right leftEqual rightEqual =>
      intro cutoff
      show Semantics.Term.parallel (shiftFromKernel cutoff left) (shiftFromKernel cutoff right) = _
      rw [leftEqual, rightEqual]; rfl

/-- `Semantics.Term.substitute depth replacement term`, written with the recursor of
`Semantics.Term` for the kernel's evaluation of the decisions, as `shiftFromKernel` is
(`substituteKernelEq`). Measured 2026-11-19:
one development of the left side of the native route's `even_scheme` took 23.7 to 30.8 s in the
kernel with `Semantics.Term.instantiate`, and 5.9 s with the recursor's substitution and shift,
in one process. Compiled code runs `Semantics.Term.substitute` itself. -/
@[implemented_by Semantics.Term.substitute]
def substituteKernel (depth : Nat) (replacement term : Semantics.Term) : Semantics.Term :=
  Semantics.Term.rec (motive := fun _ => Nat → Semantics.Term → Semantics.Term)
    (fun index depth replacement =>
      if index < depth then .boundVariable index
      else if index = depth then replacement
      else .boundVariable (index - 1))
    (fun _ body depth replacement => .abstraction (body (depth + 1) (shiftFromKernel 0 replacement)))
    (fun _ _ function argument depth replacement =>
      .application (function depth replacement) (argument depth replacement))
    (fun _ _ left right depth replacement => .choice (left depth replacement) (right depth replacement))
    (fun _ _ left right depth replacement => .parallel (left depth replacement) (right depth replacement))
    term depth replacement

theorem substituteKernelEq (term : Semantics.Term) :
    ∀ (depth : Nat) (replacement : Semantics.Term),
      substituteKernel depth replacement term = Semantics.Term.substitute depth replacement term := by
  induction term with
  | boundVariable index => intro depth replacement; rfl
  | abstraction body bodyEqual =>
      intro depth replacement
      show Semantics.Term.abstraction (substituteKernel (depth + 1) (shiftFromKernel 0 replacement) body) = _
      rw [bodyEqual, shiftFromKernelEq]; rfl
  | application function argument functionEqual argumentEqual =>
      intro depth replacement
      show Semantics.Term.application (substituteKernel depth replacement function)
        (substituteKernel depth replacement argument) = _
      rw [functionEqual, argumentEqual]; rfl
  | choice left right leftEqual rightEqual =>
      intro depth replacement
      show Semantics.Term.choice (substituteKernel depth replacement left) (substituteKernel depth replacement right) = _
      rw [leftEqual, rightEqual]; rfl
  | parallel left right leftEqual rightEqual =>
      intro depth replacement
      show Semantics.Term.parallel (substituteKernel depth replacement left)
        (substituteKernel depth replacement right) = _
      rw [leftEqual, rightEqual]; rfl

/-- `Readback.finalSlots`, its shift `shiftFromKernel` (`finalSlotsKernelEq`): the slots of a
thunk's code under its lambda chain, which `readbackCodeKernel` builds at every thunk it reads,
each slot value shifted once per hole. Measured 2026-11-19: reading the two sides of the native route's
`zero_scheme`, `double_scheme` and `successor_scheme` (`interpretReading`) took 1.8 to 2.4 s in the
kernel with `Semantics.Term.shift`, and 0.7 to 1.0 s with this shift, in one process. -/
def finalSlotsKernel : List Hole → List Semantics.Term → List Semantics.Term
  | [], slots => slots
  | hole :: holes, slots =>
      finalSlotsKernel holes (LambdaJit.fill hole holes (slots.map (shiftFromKernel 0)) (.boundVariable 0))

theorem finalSlotsKernelEq : ∀ (holes : List Hole) (slots : List Semantics.Term),
    finalSlotsKernel holes slots = Readback.finalSlots holes slots
  | [], slots => rfl
  | hole :: holes, slots => by
      have shifted : slots.map (shiftFromKernel 0) = slots.map Semantics.Term.shift :=
        List.map_congr_left (fun term _ => shiftFromKernelEq term 0)
      simp only [finalSlotsKernel, Readback.finalSlots, shifted]
      exact finalSlotsKernelEq holes _

mutual
/-- `Readback.readbackCode` with `finalSlotsKernel` (`readbackCodeKernelEq`). -/
def readbackCodeKernel : List Semantics.Term → Code → Option Semantics.Term
  | slots, .slot index => slots[index]?
  | slots, .apply function argument => do
      let functionTerm ← readbackCodeKernel slots function
      let argumentTerm ← readbackCodeKernel slots argument
      pure (.application functionTerm argumentTerm)
  | slots, .thunk code holes fillings => do
      let fillingTerms ← readbackCodeListKernel slots fillings
      let body ← readbackCodeKernel (finalSlotsKernel holes fillingTerms) code
      pure (abstractions holes.length body)
  | slots, .choice left right => do
      let leftTerm ← readbackCodeKernel slots left
      let rightTerm ← readbackCodeKernel slots right
      pure (.choice leftTerm rightTerm)
  | slots, .parallel left right => do
      let leftTerm ← readbackCodeKernel slots left
      let rightTerm ← readbackCodeKernel slots right
      pure (.parallel leftTerm rightTerm)

/-- `Readback.readbackCodeList` with `finalSlotsKernel`. -/
def readbackCodeListKernel : List Semantics.Term → List Code → Option (List Semantics.Term)
  | _, [] => some []
  | slots, code :: codes => do
      let term ← readbackCodeKernel slots code
      let terms ← readbackCodeListKernel slots codes
      pure (term :: terms)
end

mutual
theorem readbackCodeKernelEq : ∀ (slots : List Semantics.Term) (code : Code),
    readbackCodeKernel slots code = Readback.readbackCode slots code
  | slots, .slot index => by simp only [readbackCodeKernel, Readback.readbackCode]
  | slots, .apply function argument => by
      simp only [readbackCodeKernel, Readback.readbackCode, readbackCodeKernelEq slots function,
        readbackCodeKernelEq slots argument]
  | slots, .thunk code holes fillings => by
      have body := fun bodySlots => readbackCodeKernelEq bodySlots code
      simp only [readbackCodeKernel, Readback.readbackCode, readbackCodeListKernelEq slots fillings,
        finalSlotsKernelEq, body]
  | slots, .choice left right => by
      simp only [readbackCodeKernel, Readback.readbackCode, readbackCodeKernelEq slots left,
        readbackCodeKernelEq slots right]
  | slots, .parallel left right => by
      simp only [readbackCodeKernel, Readback.readbackCode, readbackCodeKernelEq slots left,
        readbackCodeKernelEq slots right]

theorem readbackCodeListKernelEq : ∀ (slots : List Semantics.Term) (codes : List Code),
    readbackCodeListKernel slots codes = Readback.readbackCodeList slots codes
  | _, [] => by simp only [readbackCodeListKernel, Readback.readbackCodeList]
  | slots, code :: codes => by
      simp only [readbackCodeListKernel, Readback.readbackCodeList, readbackCodeKernelEq slots code,
        readbackCodeListKernelEq slots codes]
end

/-- `Operator.readLiteral` with `readbackCodeKernel` (`readLiteralKernelEq`). -/
def readLiteralKernel : Operator → List Semantics.Term → Option Semantics.Term
  | .thunk code holes, values =>
      if values.length = thunkArity code holes then
        (readbackCodeKernel (finalSlotsKernel holes values) code).map (abstractions holes.length)
      else none
  | operator, values => operator.readLiteral values

theorem readLiteralKernelEq (operator : Operator) (values : List Semantics.Term) :
    readLiteralKernel operator values = operator.readLiteral values := by
  cases operator <;> simp only [readLiteralKernel, Operator.readLiteral, readbackCodeKernelEq, finalSlotsKernelEq]

/-- `interpretReading` with `readLiteralKernel`, for the kernel's evaluation of
`statementAbsorbed` (`interpretReadingKernelEq`). Compiled code runs `interpretReading` itself. -/
@[implemented_by interpretReading]
def interpretReadingKernel (signature : Signature) (valuation : Valuation) :
    Article.Term → List Semantics.Term → Semantics.Term
  | .termVariable name type, values => applyAll (valuation name type) values
  | .constant name _, values =>
      match readLiteralKernel (operatorOf signature name) values with
      | some literal => literal
      | none => applyAll (curried (operatorOf signature name)) values
  | .application function argument, values =>
      interpretReadingKernel signature valuation function
        (interpretReadingKernel signature valuation argument [] :: values)

theorem interpretReadingKernelEq (signature : Signature) (valuation : Valuation) :
    ∀ (term : Article.Term) (values : List Semantics.Term),
      interpretReadingKernel signature valuation term values = interpretReading signature valuation term values
  | .termVariable _ _, _ => rfl
  | .constant name _, values => by
      simp only [interpretReadingKernel, readLiteralKernelEq]
      rfl
  | .application function argument, values => by
      simp only [interpretReadingKernel, interpretReading, interpretReadingKernelEq signature valuation argument,
        interpretReadingKernelEq signature valuation function]

/-- One development of `term`: each application whose function, once developed, is an
abstraction is contracted by the β rule, its argument developed. `top` (`ContextualPreorder.top`) is kept
whole: developing it would unfold Y once at each development. -/
def developed : Semantics.Term → Semantics.Term
  | .application function argument =>
      if Semantics.Term.application function argument = ContextualPreorder.top then
        ContextualPreorder.top
      else
        match developed function with
        | .abstraction body => substituteKernel 0 (developed argument) body
        | developedFunction => .application developedFunction (developed argument)
  | .abstraction body => .abstraction (developed body)
  | .choice left right => .choice (developed left) (developed right)
  | .parallel left right => .parallel (developed left) (developed right)
  | other => other

/-- A development is equal to the term it develops, by the β rule under the congruences. -/
theorem developedSound {hypotheses : Semantics.Term → Semantics.Term → Prop} :
    ∀ term : Semantics.Term, DerivableLatticeEta hypotheses term (developed term)
  | .application function argument => by
      simp only [developed]
      split
      · rename_i isTop
        rw [isTop]
        exact .reflexive _
      · have both : DerivableLatticeEta hypotheses (.application function argument)
            (.application (developed function) (developed argument)) :=
          .transitive (DerivableLatticeEta.congruenceFunction argument (developedSound function))
            (.congruenceArgument (developed function) (developedSound argument))
        split
        · rename_i body developedAbstraction
          rw [developedAbstraction] at both
          rw [substituteKernelEq]
          exact .transitive both (.beta body (developed argument))
        · exact both
  | .abstraction body => by
      simp only [developed]
      exact .congruenceAbstraction (developedSound body)
  | .choice left right => by
      simp only [developed]
      exact DerivableLatticeEta.congruenceChoice (developedSound left) (developedSound right)
  | .parallel left right => by
      simp only [developed]
      exact .transitive (DerivableLatticeEta.congruenceParallelLeft right (developedSound left))
        (DerivableLatticeEta.congruenceParallelRight (developed left) (developedSound right))
  | .boundVariable _ => by simp only [developed]; exact .reflexive _

/-- A filtered application refines its application, f (a ∥ d) + f a = f a: (a ∥ d) + a = a by (1)
and (6), so the equation holds by context monotonicity in the context f □ (T10,
`DerivableLatticeEta.contextMonotone`). -/
theorem filteredApplicationRefines {hypotheses : Semantics.Term → Semantics.Term → Prop}
    (function argument domain : Semantics.Term) :
    DerivableLatticeEta hypotheses
      (.choice (.application function (.parallel argument domain)) (.application function argument))
      (.application function argument) :=
  DerivableLatticeEta.contextMonotone
    (.transitive (.choiceCommutative _ _) (DerivableLatticeEta.choiceAbsorption argument domain))
    (.applicationArgument function .hole)

/-- A typed version beside its application is absorbed, f a + (f (a ∥ d) ∥ r) = f a:
f (a ∥ d) + f a = f a (`filteredApplicationRefines`); f (a ∥ d) + (f (a ∥ d) ∥ r) = f (a ∥ d) by
(6); and (1), (2) join them. -/
theorem typedVersionAbsorbed {hypotheses : Semantics.Term → Semantics.Term → Prop}
    (function argument domain range : Semantics.Term) :
    DerivableLatticeEta hypotheses
      (.choice (.application function argument)
        (.parallel (.application function (.parallel argument domain)) range))
      (.application function argument) := by
  have applied := filteredApplicationRefines (hypotheses := hypotheses) function argument domain
  -- f a + (f (a ∥ d) ∥ r) = (f (a ∥ d) + f a) + (f (a ∥ d) ∥ r) = (f a + f (a ∥ d)) + (f (a ∥ d) ∥ r)
  -- = f a + (f (a ∥ d) + (f (a ∥ d) ∥ r)) = f a + f (a ∥ d) = f (a ∥ d) + f a = f a
  exact .transitive (DerivableLatticeEta.congruenceChoiceLeft _ (.symmetric applied))
    (.transitive (DerivableLatticeEta.congruenceChoiceLeft _ (.choiceCommutative _ _))
      (.transitive (DerivableLatticeEta.choiceAssociative _ _ _)
        (.transitive
          (DerivableLatticeEta.congruenceChoiceRight _ (DerivableLatticeEta.choiceAbsorption _ range))
          (.transitive (.choiceCommutative _ _) applied))))

/-- Whether `kept + other` equals `kept` by absorption: `other` is `kept ∥ N` (6), or `kept` is an
application f a and `other` is f (a ∥ d) ∥ r (`typedVersionAbsorbed`) or f (a ∥ d)
(`filteredApplicationRefines`, turned round by (1)). -/
def absorbs (kept other : Semantics.Term) : Bool :=
  match other with
  | .parallel member _ =>
      member == kept ||
        match member, kept with
        | .application function (.parallel argument _), .application keptFunction keptArgument =>
            function == keptFunction && argument == keptArgument
        | _, _ => false
  | .application function (.parallel argument _) =>
      match kept with
      | .application keptFunction keptArgument => function == keptFunction && argument == keptArgument
      | _ => false
  | _ => false

/-- A choice that `absorbs` accepts equals its left operand. -/
theorem absorbsSound {hypotheses : Semantics.Term → Semantics.Term → Prop}
    {kept other : Semantics.Term} (accepted : absorbs kept other = true) :
    DerivableLatticeEta hypotheses (.choice kept other) kept := by
  unfold absorbs at accepted
  split at accepted
  · rename_i member criterion
    simp only [Bool.or_eq_true, beq_iff_eq] at accepted
    rcases accepted with rfl | typed
    · exact DerivableLatticeEta.choiceAbsorption _ _
    · split at typed
      · simp only [Bool.and_eq_true, beq_iff_eq] at typed
        obtain ⟨rfl, rfl⟩ := typed
        exact typedVersionAbsorbed _ _ _ _
      · cases typed
  · split at accepted
    · simp only [Bool.and_eq_true, beq_iff_eq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact .transitive (.choiceCommutative _ _) (filteredApplicationRefines _ _ _)
    · cases accepted
  · cases accepted

/-- The choice of two simplified operands, simplified: the other operand when one is `top`
(`top` + M ≃_O M and M + `top` ≃_O M, `top` being greatest for ⊑_O), `kept` when the two are equal (M + M = M)
or when `absorbs` accepts them, else their choice. -/
def choiceSimplified (kept other : Semantics.Term) : Semantics.Term :=
  if kept = ContextualPreorder.top then other
  else if other = ContextualPreorder.top then kept
  else if kept = other then kept
  else if absorbs kept other then kept
  else .choice kept other

theorem choiceSimplifiedSound (kept other : Semantics.Term) :
    ContextualPreorder.ContextualEquivalence (.choice kept other) (choiceSimplified kept other) := by
  unfold choiceSimplified
  split
  · rename_i isTop
    rw [isTop]
    exact ContextualPreorder.contextualEquivalenceTopChoice other
  · split
    · rename_i isTop
      rw [isTop]
      exact ContextualPreorder.contextualEquivalenceChoiceTop kept
    · split
      · rename_i same
        rw [same]
        exact ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta
          (DerivableLatticeEta.choiceIdempotent _)
      · split
        · rename_i accepted
          exact ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta (absorbsSound accepted)
        · exact ContextualPreorder.ContextualEquivalence.reflexive _

/-- The parallel of two simplified operands, simplified: `top` when one operand is `top` (`top` ∥ M ≃_O `top` and
M ∥ `top` ≃_O `top`), the one operand when the two are equal (M ∥ M = M), else their parallel. -/
def parallelSimplified (left right : Semantics.Term) : Semantics.Term :=
  if left = ContextualPreorder.top then ContextualPreorder.top
  else if right = ContextualPreorder.top then ContextualPreorder.top
  else if left = right then left
  else .parallel left right

theorem parallelSimplifiedSound (left right : Semantics.Term) :
    ContextualPreorder.ContextualEquivalence (.parallel left right)
      (parallelSimplified left right) := by
  unfold parallelSimplified
  split
  · rename_i isTop
    rw [isTop]
    exact ContextualPreorder.contextualEquivalenceTopParallel right
  · split
    · rename_i isTop
      rw [isTop]
      exact ContextualPreorder.contextualEquivalenceParallelTop left
    · split
      · rename_i same
        rw [same]
        exact ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta
          (DerivableLatticeEta.parallelIdempotent _)
      · exact ContextualPreorder.ContextualEquivalence.reflexive _

/-- The abstraction of a simplified body, simplified by the η rule: λx. f x with x ∉ FV(f) is f,
taken out from under the abstraction; any other abstraction stays. -/
def abstractionSimplified : Semantics.Term → Semantics.Term
  | .application function (.boundVariable 0) =>
      if Semantics.Term.OccursFree 0 function then .abstraction (.application function (.boundVariable 0))
      else Semantics.Term.lower function
  | body => .abstraction body

theorem abstractionSimplifiedSound {hypotheses : Semantics.Term → Semantics.Term → Prop}
    (body : Semantics.Term) :
    DerivableLatticeEta hypotheses (.abstraction body) (abstractionSimplified body) := by
  unfold abstractionSimplified
  split
  · rename_i function
    split
    · exact .reflexive _
    · rename_i absent
      have eta := DerivableLatticeEta.eta (hypotheses := hypotheses) (Semantics.Term.lower function)
      rw [Semantics.Term.shiftLower function absent] at eta
      exact eta
  · exact .reflexive _

/-- `term` simplified bottom up, the operands of each layer first, wherever the left sides of these
equations appear: `top` ∥ M = `top`, M ∥ `top` = `top`, `top` + M = M and M + `top` = M, contextual equivalences since `top` is
greatest for ⊑_O; and M ∥ M = M, M + M = M, M + (M ∥ N) = M, f a + (f (a ∥ d) ∥ r) = f a,
f a + f (a ∥ d) = f a and the η rule, of ⊢_{λ-lattice-η}. `top` itself is kept whole. -/
def simplified : Semantics.Term → Semantics.Term
  | .parallel left right => parallelSimplified (simplified left) (simplified right)
  | .choice left right => choiceSimplified (simplified left) (simplified right)
  | .application function argument =>
      if Semantics.Term.application function argument = ContextualPreorder.top then
        ContextualPreorder.top
      else .application (simplified function) (simplified argument)
  | .abstraction body => abstractionSimplified (simplified body)
  | other => other

/-- A term is contextually equivalent to its simplification, each equation applied under the
congruences of ≃_O. -/
theorem simplifiedSound :
    ∀ term : Semantics.Term, ContextualPreorder.ContextualEquivalence term (simplified term)
  | .parallel left right => by
      simp only [simplified]
      exact (((simplifiedSound left).fill (.parallelLeft .hole right)).transitive
        ((simplifiedSound right).fill (.parallelRight (simplified left) .hole))).transitive
        (parallelSimplifiedSound _ _)
  | .choice left right => by
      simp only [simplified]
      exact (((simplifiedSound left).fill (.choiceLeft .hole right)).transitive
        ((simplifiedSound right).fill (.choiceRight (simplified left) .hole))).transitive
        (choiceSimplifiedSound _ _)
  | .application function argument => by
      simp only [simplified]
      split
      · rename_i isTop
        rw [isTop]
        exact ContextualPreorder.ContextualEquivalence.reflexive _
      · exact ContextualPreorder.ContextualEquivalence.application (simplifiedSound function)
          (simplifiedSound argument)
  | .abstraction body => by
      simp only [simplified]
      exact ((simplifiedSound body).fill (.abstraction .hole)).transitive
        (ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta
          (abstractionSimplifiedSound _))
  | .boundVariable _ => by
      simp only [simplified]
      exact ContextualPreorder.ContextualEquivalence.reflexive _

/-- Whether the two terms have one simplification after the same number of developments of each,
at most `count`, each development made on the simplified terms, fewer tried first. -/
def absorbedWithin : Nat → Semantics.Term → Semantics.Term → Bool
  | 0, left, right => simplified left == simplified right
  | count + 1, left, right =>
      simplified left == simplified right ||
        absorbedWithin count (developed (simplified left)) (developed (simplified right))

/-- Two terms that `absorbedWithin` accepts are contextually equivalent, each simplification
(`simplifiedSound`) and each development (`developedSound`) being equivalent to its term. -/
theorem absorbedWithinSound :
    ∀ {count : Nat} {left right : Semantics.Term}, absorbedWithin count left right = true →
      ContextualPreorder.ContextualEquivalence left right
  | 0, left, right, accepted => by
      simp only [absorbedWithin, beq_iff_eq] at accepted
      exact (simplifiedSound left).transitive (by rw [accepted]; exact (simplifiedSound right).symmetric)
  | count + 1, left, right, accepted => by
      simp only [absorbedWithin, Bool.or_eq_true, beq_iff_eq] at accepted
      rcases accepted with here | later
      · exact (simplifiedSound left).transitive
          (by rw [here]; exact (simplifiedSound right).symmetric)
      · have leftDeveloped := ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta
          (developedSound (hypotheses := fun _ _ => False) (simplified left))
        have rightDeveloped := ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta
          (developedSound (hypotheses := fun _ _ => False) (simplified right))
        exact (simplifiedSound left).transitive (leftDeveloped.transitive
          ((absorbedWithinSound later).transitive
            ((simplifiedSound right).transitive rightDeveloped).symmetric))

/-- The developments `statementAbsorbed` makes at most: 3, the most a lemma of the native route's
knowledge modules needed when the bound was measured (2026-10-28, with `#eval` on the export, the
fewest developments at which `absorbedWithin` accepts each: scheme_read of the knowledge module
hindley_milner_lemmas, deleted with the old e-graph, `git show
ebd6ed446:lambda_jit/corpora/standard_library/hindley_milner_lemmas.pl`). Every lemma of the
current modules (native_types, native_arithmetic, hindley_milner_unions,
native_arithmetic_unions, occurrence_erasure, closure_application and prolog_backend_shapes) is
accepted within it (the test lean_statements_native_route of tests/lean_statements.plt); the
comparisons that a refutation marks, the typed versions and the contracts of
prolog_backend_shapes after one development (measured 2026-10-29 the same way). -/
def absorptionDevelopments : Nat := 3

/-- A contextual equivalence holds under any number of abstractions, ≃_O being a congruence. -/
theorem equivalentUnderAbstractions {left right : Semantics.Term}
    (equivalent : ContextualPreorder.ContextualEquivalence left right) :
    ∀ count : Nat,
      ContextualPreorder.ContextualEquivalence (abstractions count left) (abstractions count right)
  | 0 => equivalent
  | count + 1 => (equivalentUnderAbstractions equivalent count).fill (.abstraction .hole)

/-- Two contextually equivalent terms applied to the same arguments are contextually equivalent. -/
theorem applyAllEquivalent :
    ∀ (arguments : List Semantics.Term) {left right : Semantics.Term},
      ContextualPreorder.ContextualEquivalence left right →
        ContextualPreorder.ContextualEquivalence (applyAll left arguments) (applyAll right arguments)
  | [], _, _, equivalent => equivalent
  | argument :: arguments, _, _, equivalent =>
      applyAllEquivalent arguments (equivalent.fill (.applicationFunction .hole argument))

/-- An equation whose two sides, their variables abstracted, are contextually equivalent is sound:
for every valuation, each side's interpretation is its abstracted side applied to the values of the
variables by the β rule (`abstractedApplied`), and applying two contextually equivalent terms to
the same values gives contextually equivalent terms. -/
theorem equationSoundOfAbstractedEquivalent {left right : Article.Term}
    (abstractedEquivalent : ContextualPreorder.ContextualEquivalence
      (abstracted signature (termVariables left ++ termVariables right) left)
      (abstracted signature (termVariables left ++ termVariables right) right)) :
    EquationSound signature left right := by
  intro valuation
  have leftApplied := abstractedApplied (signature := signature) (hypotheses := fun _ _ => False)
    valuation
    (termVariables left ++ termVariables right) left
    (fun _ member => List.mem_append_left _ member)
  have rightApplied := abstractedApplied (signature := signature) (hypotheses := fun _ _ => False)
    valuation
    (termVariables left ++ termVariables right) right
    (fun _ member => List.mem_append_right _ member)
  exact ((ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta
    leftApplied).symmetric.transitive (applyAllEquivalent _ abstractedEquivalent)).transitive
    (ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta rightApplied)

/-- `equationSoundOfAbstractedEquivalent` with the variables of the two sides each once
(`sidesVariables`). -/
theorem equationSoundOfSidesEquivalent {left right : Article.Term}
    (abstractedEquivalent : ContextualPreorder.ContextualEquivalence
      (abstracted signature (sidesVariables left right) left)
      (abstracted signature (sidesVariables left right) right)) :
    EquationSound signature left right := by
  intro valuation
  have leftApplied := abstractedApplied (signature := signature) (hypotheses := fun _ _ => False)
    valuation (sidesVariables left right) left (fun _ member => leftVariableListed member)
  have rightApplied := abstractedApplied (signature := signature) (hypotheses := fun _ _ => False)
    valuation (sidesVariables left right) right (fun _ member => rightVariableListed member)
  exact ((ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta
    leftApplied).symmetric.transitive (applyAllEquivalent _ abstractedEquivalent)).transitive
    (ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta rightApplied)

/-- Whether the two sides of `statement`, interpreted with their variables read as the bound
variables of the abstractions `abstracted` puts around them, each fully applied constant read by
its operator (`interpretReading`, β-equal to `interpret`'s term), and `top` written in one spelling
(`withTop`), are accepted by `absorbedWithin` within `absorptionDevelopments`
developments. Reading the constants so leaves `absorbedWithin` fewer nodes: the statement's
curried constants each a copy of their body, the first development contracted them one by one. -/
def statementAbsorbed (statement : EndToEnd.Statement) : Bool :=
  let variables := sidesVariables statement.left statement.right
  absorbedWithin absorptionDevelopments
    (withTop
      (interpretReadingKernel statement.signature (listedValuation variables (variablesBelow variables.length))
        statement.left []))
    (withTop
      (interpretReadingKernel statement.signature (listedValuation variables (variablesBelow variables.length))
        statement.right []))

/-- A statement that `statementAbsorbed` accepts is sound: its interpreted sides with `top` in one
spelling are contextually equivalent (`absorbedWithinSound`); each is equal to the side as
interpreted by the β rule (`withTopDerivable`); and so are they under the abstractions of
the statement's variables (`equivalentUnderAbstractions`), which are its abstracted sides. -/
theorem statementSoundOfAbsorbed {statement : EndToEnd.Statement}
    (absorbed : statementAbsorbed statement = true) : statement.Sound := by
  simp only [statementAbsorbed, interpretReadingKernelEq] at absorbed
  exact equationSoundOfSidesEquivalent
    (equivalentUnderAbstractions
      ((((ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta
        (interpretReadingDerivable (hypotheses := fun _ _ => False) _ _ _ [])).transitive
        (ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta
          (withTopDerivable (hypotheses := fun _ _ => False) _))).transitive
        (absorbedWithinSound absorbed)).transitive
        ((ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta
          (withTopDerivable (hypotheses := fun _ _ => False) _)).symmetric.transitive
          (ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta
            (interpretReadingDerivable (hypotheses := fun _ _ => False) _ _ _ [])).symmetric)) _)

/-! ## The four decisions in order -/

/-! ## Common constants read as variables -/

/-- The term with every constant whose name `names` lists read as the variable of its name and
type, so that it stands for any term and no decision unfolds it: a constant both sides of a
statement hold, such as one of the library's markers, whose code no decision needs, and whose code
in the markers' spelling, a variable arguments partial function of a literal
(CONTRIBUTING.md, "Terms") with `top` in every branch that misses the key, has no normal form and takes hundreds of
contractions to apply. -/
def opened (names : List Article.Name) : Article.Term → Article.Term
  | .termVariable name type => .termVariable name type
  | .constant name type => if name ∈ names then .termVariable name type else .constant name type
  | .application function argument => .application (opened names function) (opened names argument)

/-- The valuation that reads a variable named in `names` as the curried form of the constant of
that name, and any other as `valuation` does. -/
def openedValuation (signature : Signature) (names : List Article.Name) (valuation : Valuation) :
    Valuation :=
  fun name type => if name ∈ names then curried (operatorOf signature name) else valuation name type

/-- A term none of whose variables `names` names, opened at `names`, is interpreted under the
opened valuation as the term is under the valuation. -/
theorem interpretOpened (names : List Article.Name) (valuation : Valuation) :
    ∀ term : Article.Term, (termVariables term).all (fun listed => listed.1 ∉ names) = true →
      interpret signature (openedValuation signature names valuation) (opened names term) =
        interpret signature valuation term
  | .termVariable name type, fresh => by
      simp only [termVariables, List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at fresh
      simp only [opened, interpret, openedValuation, if_neg fresh]
  | .constant name type, _ => by
      by_cases named : name ∈ names
      · simp only [opened, if_pos named, interpret, openedValuation]
      · simp only [opened, if_neg named, interpret]
  | .application function argument, fresh => by
      simp only [termVariables, List.all_append, Bool.and_eq_true] at fresh
      simp only [opened, interpret]
      rw [interpretOpened names valuation function fresh.1,
        interpretOpened names valuation argument fresh.2]

/-- The names of the constants of a term, from the last to the first, before `found`: the
traversal of a term that appends the names of a function and of its argument at every
application would copy the function's at each application of a spine, quadratic in the spine's length, and the markers are spines of about
105 applications (measured 2026-11-19: the
names of the left side of the native route's `zero_scheme`, 676, took 2.9 s in the kernel with
the appends and 0.04 s with this). -/
def constantNamesInto (found : List Article.Name) : Article.Term → List Article.Name
  | .termVariable _ _ => found
  | .constant name _ => name :: found
  | .application function argument => constantNamesInto (constantNamesInto found argument) function

/-- Whether `name` is one of `names`. -/
def nameListed (name : Article.Name) : List Article.Name → Bool
  | [] => false
  | other :: rest => if other = name then true else nameListed name rest

/-- The names of `names` not in `found`, each once, after `found`. -/
def distinctNames (found : List Article.Name) : List Article.Name → List Article.Name
  | [] => found
  | name :: rest => if nameListed name found then distinctNames found rest else distinctNames (name :: found) rest

/-- The names of the constants both sides of `statement` hold, each once. -/
def commonConstants (statement : EndToEnd.Statement) : List Article.Name :=
  let rightNames := distinctNames [] (constantNamesInto [] statement.right)
  (distinctNames [] (constantNamesInto [] statement.left)).filter (fun name => nameListed name rightNames)

/-- The statement with its common constants read as variables (`opened`). -/
def openedStatement (statement : EndToEnd.Statement) : EndToEnd.Statement :=
  { signature := statement.signature
    left := opened (commonConstants statement) statement.left
    right := opened (commonConstants statement) statement.right }

/-- Whether no variable of `statement` is named as one of its common constants, so that reading
those constants as variables adds variables of their own. -/
def openedFresh (statement : EndToEnd.Statement) : Bool :=
  (termVariables statement.left ++ termVariables statement.right).all
    (fun listed => listed.1 ∉ commonConstants statement)

/-- A statement is sound when its common constants read as variables give a sound statement: the
opened statement holds under every valuation, in particular under the one that reads those
variables as the constants (`interpretOpened`). -/
theorem statementSoundOfOpened {statement : EndToEnd.Statement}
    (fresh : openedFresh statement = true) (sound : (openedStatement statement).Sound) :
    statement.Sound := by
  intro valuation
  have equivalent := sound (openedValuation statement.signature (commonConstants statement) valuation)
  simp only [openedFresh, List.all_append, Bool.and_eq_true] at fresh
  simp only [openedStatement] at equivalent
  rwa [interpretOpened _ _ _ fresh.1, interpretOpened _ _ _ fresh.2] at equivalent

/-- Whether the normaliser, contraction or the decision of absorbed members accepts `statement`
with its common constants read as variables (`openedStatement`), no variable of it named as one of
them. -/
def statementOpenedAccepted (statement : EndToEnd.Statement) : Bool :=
  openedFresh statement &&
    (statementAbsorbed (openedStatement statement) ||
      statementNormalised (openedStatement statement) ||
      statementContracted (openedStatement statement))

/-- A statement that `statementOpenedAccepted` accepts is sound (`statementSoundOfOpened`). -/
theorem statementSoundOfOpenedAccepted {statement : EndToEnd.Statement}
    (accepted : statementOpenedAccepted statement = true) : statement.Sound := by
  simp only [statementOpenedAccepted, Bool.and_eq_true, Bool.or_eq_true] at accepted
  obtain ⟨fresh, decided⟩ := accepted
  apply statementSoundOfOpened fresh
  rcases decided with (absorbed | normalised) | contracted
  · exact statementSoundOfAbsorbed absorbed
  · exact statementSoundOfNormalised normalised
  · exact statementSoundOfContracted contracted

/-! ## The normal form at a larger fuel -/

/-- The fuel of the normal form tried after leftmost outermost contraction, on each side. Of the 89
statements of the native route's library (module `NativeRouteLibraryStatements`), the three that no
decision before this one accepts, occurrence_name_erased, occurrence_closure_erased and
closure_applied, apply a marker in the markers' spelling,
a variable arguments partial function of a literal applied to the literal's bits: the marker's own equation, such as
`closure_applied`'s `$closure x₀ (λx₃. x₁ x₃) x₂ = x₁ x₂`, has nothing but that to prove. Their left
sides take 344, 512 and 516 contractions to their normal forms and their right sides at most 9, the
least fuels at which `normalFormWithin` answers (measured 2026-11-21 with `#eval`, the metavariables
abstracted). Tried after `statementContracted` and before `statementOpenedAccepted`, so that a
statement those accept pays nothing for it, and a marker's statement does not pay for the decisions
on the opened statement. -/
def longNormalisationFuel : Nat := 1000

/-- Whether the normal form brings the two sides of `statement` to one term within
`longNormalisationFuel` contractions on each side. -/
def statementNormalisedLong (statement : EndToEnd.Statement) : Bool :=
  normalisedEqual statement.signature longNormalisationFuel statement.left statement.right

/-- A statement that `statementNormalisedLong` accepts is sound, as one that `statementNormalised`
accepts is (`equationSoundOfNormalisedEqual`, at any fuel). -/
theorem statementSoundOfNormalisedLong {statement : EndToEnd.Statement}
    (normalised : statementNormalisedLong statement = true) : statement.Sound :=
  equationSoundOfNormalisedEqual normalised

end LambdaJit.StatementNormalisation
