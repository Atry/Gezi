import LambdaJit.EndToEnd
import LambdaJit.ArticleLines
import LambdaJit.ExpectedArticles
import LambdaJit.Normalisation
import LambdaJit.StatementNormalisation

/-!
# The end-to-end theorem on the expected articles

Four of the six expected articles that the writer `gezi/prolog/gezi/opentheory_article.pl`
writes for the runs made by hand of `gezi/tests/opentheory_article.plt` over the library
[prelude, guard_laws, parallel_types, filtered_recursion_naturals]
(`gezi/tests/opentheory_article_expected/`, which also holds the articles of the
fixpoint runs of module `FixpointRunFixtures`),
read by the article reader and
taken through the end-to-end theorem (module `EndToEnd`): the four whose import sets cite no lemma
but `identity_applied`. The other two, `two_thunks_of_one_class` and
`an_argument_dropped_then_spelled`, cite `successor_filtered` and `post_application_of_apply_to`,
which this module does not prove sound. For each of the four articles:

- its text, the list of its lines (`…Lines`, module `ExpectedArticles`) each followed by a newline
  (`…Text`). The lines are generated from the expected article, which is the source, by
  `gezi/tests/opentheory_article.plt`, which checks that regenerating them gives the committed
  module byte for byte;
- `…Checked`: the reader accepts the text, every equation of its import set is a numbered equation,
  an equation of the defunctionalized β rule or η rule of a thunk constant, or the statement of
  `identity_applied`, and its one exported equation is the equation of the run's two sides
  (`EndToEnd.resultChecked`). The kernel evaluates it (`decide +kernel`): the text is first split
  into its lines by `ArticleLines.articleLinesJoin`, since `String.splitOn` does not reduce in the
  kernel, and then the commands of the lines are run;
- `…Sound`: the exported equation is sound (`EndToEnd.endToEndOfChecked`), with the lemma
  discharged by `identityAppliedSound`;
- `…ContextualEquivalence`: the readings ⟦·⟧ of the two sides (`Interpretation.read`, checked by
  the kernel) are contextually equivalent, ≃_O of DdLP96's Definition 14
  (`EndToEnd.contextualEquivalenceOfRead`).

The library's terms of the sides: zero is the code `slot(0)` with the holes [0,ignored], identity
the same code with [0], and successor the code `apply(slot(0),slot(1))` with [1,ignored,0]; each is
a thunk constant without fillings.
-/

namespace LambdaJit.EndToEndFixtures

open LambdaJit.EndToEnd LambdaJit.Interpretation LambdaJit.ExpectedArticles
open LambdaJit.ContextualPreorder (ContextualEquivalence)

/-! ## The terms of the sides

Each article numbers its thunk constants from 0 in the order it first writes them (D7.1), so the
library's terms are named by their number in the article at hand. -/

/-- The type of a thunk constant that takes `arity` fillings: `term → … → term`. -/
def constantType : Nat → Article.LogicType
  | 0 => termType
  | arity + 1 => .arrow termType (constantType arity)

/-- The thunk constant `LambdaJit.thunk.<number>` that takes `arity` fillings. -/
def thunkConstant (number : String) (arity : Nat) : Article.Term :=
  .constant ⟨["LambdaJit", "thunk"], number⟩ (constantType arity)

/-- zero, `λz.λ_. z`: the code `slot 0` with the holes [0, ignored], numbered `number`. -/
def zero (number : String) : Article.Term := thunkConstant number 0

/-- identity, `λx. x`: the code `slot 0` with the hole [0], numbered `number`. -/
def identity (number : String) : Article.Term := thunkConstant number 0

/-- successor, `λn.λ_.λs. s n`: the code `apply (slot 0) (slot 1)` with the holes [1, ignored, 0],
numbered `number`. -/
def successor (number : String) : Article.Term := thunkConstant number 0

/-- The numeral one, `λz.λs. s zero`, as the e-graph spells `successor @ zero`: successor's thunk
with its first hole filled by zero, the constant of the holes [ignored, 0], numbered `filled`,
applied to zero, numbered `zeroNumber`. -/
def one (filled zeroNumber : String) : Article.Term :=
  .application (thunkConstant filled 1) (zero zeroNumber)

/-- `\x. successor x`, the thunk of successor's code with the one hole [1], numbered `expanded`, and
successor, numbered `successorNumber`, as the filling of slot 0: the shape of the defunctionalized
η rule. -/
def successorExpanded (expanded successorNumber : String) : Article.Term :=
  .application (thunkConstant expanded 1) (successor successorNumber)

/-- λz.λs. s zero, the reading of `one`. -/
def oneTerm : Semantics.Term :=
  .abstraction (.abstraction (.application (.boundVariable 0) ParallelTypesTheorems.zero))

/-- λx. successor x, the reading of `successorExpanded`. -/
def successorExpandedTerm : Semantics.Term :=
  .abstraction (.application ParallelTypesTheorems.successor (.boundVariable 0))

/-- The name `LambdaJit.thunk.<number>`. -/
def thunkName (number : String) : Article.Name := ⟨["LambdaJit", "thunk"], number⟩

/-! ## The lemma `identity_applied` -/

/-- The statement of prelude's lemma `identity_applied`, `X^(identity @ X) = X^X`, as the writer
writes it: `LambdaJit.apply identity metavariable0 = metavariable0`, identity its thunk constant 0. -/
def identityApplied : Statement :=
  { signature := [(thunkName "0", .slot 0, [.slot 0])],
    left := applyTerm (identity "0") (termVariable "metavariable0"),
    right := termVariable "metavariable0" }

/-- `identity_applied` is sound: it is a β law. identity's constant is interpreted as λx. x, and
(λx. x) X = X by the β rule. -/
theorem identityAppliedSound : identityApplied.Sound := by
  apply equationSoundOfDerivable
  intro valuation
  have identityRead :
      interpret identityApplied.signature valuation (identity "0") =
        Semantics.NormalisationFixtures.identity := by
    show curried (operatorOf identityApplied.signature (thunkName "0")) = _
    decide +kernel
  have applied := interpretApply (signature := identityApplied.signature)
    (hypotheses := fun _ _ => False) valuation binaryType (identity "0")
    (termVariable "metavariable0")
  rw [identityRead] at applied
  exact .transitive applied (.beta _ _)

/-- `identity_applied` is sound by the normaliser too, as the module of the library's statements
proves it (module `StatementNormalisation`): the kernel evaluates the normalisation of its two
sides, the metavariable abstracted, to one normal form. -/
theorem identityAppliedNormalised : identityApplied.Sound :=
  StatementNormalisation.statementSoundOfNormalised (by decide +kernel)

/-- The lemma statements the fixtures' derivations use, each sound. -/
def lemmas : List Statement := [identityApplied]

theorem lemmasSound : ∀ lemma ∈ lemmas, lemma.Sound := by
  intro lemma member
  simp only [lemmas, List.mem_singleton] at member
  rw [member]
  exact identityAppliedSound

/-! ## congruence_only

(a) of the test: `successor @ zero` beside zero in a parallel, against the literal numeral
`\z.\s. s zero` beside zero. The two are one node of the e-graph and there is no union; the
derivation is a congruence over the instance of the defunctionalized β rule that fills
successor's first hole, and the import set has no lemma. -/

/-- The text of `congruence_only.art`: its lines, each followed by a newline. -/
def congruenceOnlyText : String :=
  String.join (congruenceOnlyLines.map (· ++ "\n"))

/-- The signature of the article's thunk constants, in the order it defines them. -/
def congruenceOnlySignature : Signature :=
  [(thunkName "0", .slot 0, [.slot 0, .ignored]),
    (thunkName "1", .apply (.slot 0) (.slot 1), [.slot 1, .ignored, .slot 0]),
    (thunkName "2", .apply (.slot 0) (.slot 1), [.ignored, .slot 0]),
    (thunkName "3", .slot 0, [.ignored]),
    (thunkName "4", .apply (.slot 0) (.slot 1), [.slot 0]),
    (thunkName "5", .slot 0, []),
    (thunkName "6", .apply (.slot 0) (.slot 1), [])]

/-- The left side, `successor @ zero ∥ zero`. -/
def congruenceOnlyLeft : Article.Term :=
  parallelTerm (applyTerm (successor "1") (zero "0")) (zero "0")

/-- The right side, `one ∥ zero`, one being successor's thunk with its first hole filled by
zero. -/
def congruenceOnlyRight : Article.Term :=
  parallelTerm (one "2" "0") (zero "0")

/-- The reader accepts the article, its definitions give its signature, `importChecked` accepts
its import set, and its one exported equation is the equation of the two sides. -/
theorem congruenceOnlyChecked :
    resultChecked congruenceOnlySignature lemmas congruenceOnlyLeft congruenceOnlyRight
      (Article.readArticle congruenceOnlyText) = true := by
  unfold congruenceOnlyText Article.readArticle
  rw [ArticleLines.articleLinesJoin congruenceOnlyLines
    (ArticleLines.noNewlineOfLinesClean (by decide +kernel))]
  decide +kernel

/-- The exported equation is sound. -/
theorem congruenceOnlySound :
    EquationSound congruenceOnlySignature congruenceOnlyLeft congruenceOnlyRight :=
  endToEndOfChecked lemmasSound congruenceOnlyChecked

/-- The readings of the two sides, successor zero ∥ zero and (λz.λs. s zero) ∥ zero, are
contextually equivalent. -/
theorem congruenceOnlyContextualEquivalence :
    ContextualEquivalence
      (.parallel (.application ParallelTypesTheorems.successor ParallelTypesTheorems.zero)
        ParallelTypesTheorems.zero)
      (.parallel oneTerm ParallelTypesTheorems.zero) :=
  contextualEquivalenceOfRead congruenceOnlySound (by decide +kernel)
    (by decide +kernel)

/-! ## one_lemma_instance

(b) of the test: `identity @ zero` is zero, by one instance of the lemma
`identity_applied`. -/

/-- The text of `one_lemma_instance.art`: its lines, each followed by a newline. -/
def oneLemmaInstanceText : String :=
  String.join (oneLemmaInstanceLines.map (· ++ "\n"))

/-- The signature of the article's thunk constants, in the order it defines them. -/
def oneLemmaInstanceSignature : Signature :=
  [(thunkName "0", .slot 0, [.slot 0, .ignored]),
    (thunkName "1", .slot 0, [.slot 0]),
    (thunkName "2", .slot 0, []),
    (thunkName "3", .slot 0, [.ignored])]

/-- The left side, `identity @ zero`. -/
def oneLemmaInstanceLeft : Article.Term :=
  applyTerm (identity "1") (zero "0")

/-- The right side, zero. -/
def oneLemmaInstanceRight : Article.Term :=
  zero "0"

/-- The reader accepts the article, its definitions give its signature, `importChecked` accepts
its import set, and its one exported equation is the equation of the two sides. -/
theorem oneLemmaInstanceChecked :
    resultChecked oneLemmaInstanceSignature lemmas oneLemmaInstanceLeft oneLemmaInstanceRight
      (Article.readArticle oneLemmaInstanceText) = true := by
  unfold oneLemmaInstanceText Article.readArticle
  rw [ArticleLines.articleLinesJoin oneLemmaInstanceLines
    (ArticleLines.noNewlineOfLinesClean (by decide +kernel))]
  decide +kernel

/-- The exported equation is sound. -/
theorem oneLemmaInstanceSound :
    EquationSound oneLemmaInstanceSignature oneLemmaInstanceLeft oneLemmaInstanceRight :=
  endToEndOfChecked lemmasSound oneLemmaInstanceChecked

/-- The readings of the two sides, (λx. x) zero and zero, are contextually equivalent. -/
theorem oneLemmaInstanceContextualEquivalence :
    ContextualEquivalence
      (.application Semantics.NormalisationFixtures.identity ParallelTypesTheorems.zero)
      ParallelTypesTheorems.zero :=
  contextualEquivalenceOfRead oneLemmaInstanceSound (by decide +kernel)
    (by decide +kernel)

/-! ## two_instances_and_a_congruence

(c) of the test: `identity @ (successor @ (identity @ zero))` is `successor @ zero`. An
instance of `identity_applied` unites the outer application with its argument, a second one
unites `identity @ zero` with zero, and the e-graph's congruence then unites the two applications
of successor. -/

/-- The text of `two_instances_and_a_congruence.art`: its lines, each followed by a newline. -/
def twoInstancesAndACongruenceText : String :=
  String.join (twoInstancesAndACongruenceLines.map (· ++ "\n"))

/-- The signature of the article's thunk constants, in the order it defines them. -/
def twoInstancesAndACongruenceSignature : Signature :=
  [(thunkName "0", .slot 0, [.slot 0]),
    (thunkName "1", .apply (.slot 0) (.slot 1), [.slot 1, .ignored, .slot 0]),
    (thunkName "2", .slot 0, [.slot 0, .ignored]),
    (thunkName "3", .slot 0, []),
    (thunkName "4", .apply (.slot 0) (.slot 1), [.ignored, .slot 0]),
    (thunkName "5", .slot 0, [.ignored]),
    (thunkName "6", .apply (.slot 0) (.slot 1), [.slot 0]),
    (thunkName "7", .apply (.slot 0) (.slot 1), [])]

/-- The left side, `identity @ (successor @ (identity @ zero))`. -/
def twoInstancesAndACongruenceLeft : Article.Term :=
  applyTerm (identity "0") (applyTerm (successor "1") (applyTerm (identity "0") (zero "2")))

/-- The right side, `successor @ zero`. -/
def twoInstancesAndACongruenceRight : Article.Term :=
  applyTerm (successor "1") (zero "2")

/-- The reader accepts the article, its definitions give its signature, `importChecked` accepts
its import set, and its one exported equation is the equation of the two sides. -/
theorem twoInstancesAndACongruenceChecked :
    resultChecked twoInstancesAndACongruenceSignature lemmas twoInstancesAndACongruenceLeft
      twoInstancesAndACongruenceRight
      (Article.readArticle twoInstancesAndACongruenceText) = true := by
  unfold twoInstancesAndACongruenceText Article.readArticle
  rw [ArticleLines.articleLinesJoin twoInstancesAndACongruenceLines
    (ArticleLines.noNewlineOfLinesClean (by decide +kernel))]
  decide +kernel

/-- The exported equation is sound. -/
theorem twoInstancesAndACongruenceSound :
    EquationSound twoInstancesAndACongruenceSignature twoInstancesAndACongruenceLeft
      twoInstancesAndACongruenceRight :=
  endToEndOfChecked lemmasSound twoInstancesAndACongruenceChecked

/-- The readings of the two sides, (λx. x) (successor ((λx. x) zero)) and successor zero,
are contextually equivalent. -/
theorem twoInstancesAndACongruenceContextualEquivalence :
    ContextualEquivalence
      (.application Semantics.NormalisationFixtures.identity
        (.application ParallelTypesTheorems.successor
          (.application Semantics.NormalisationFixtures.identity ParallelTypesTheorems.zero)))
      (.application ParallelTypesTheorems.successor ParallelTypesTheorems.zero) :=
  contextualEquivalenceOfRead twoInstancesAndACongruenceSound (by decide +kernel)
    (by decide +kernel)

/-! ## eta_shaped_constant

`\x. successor x`, a thunk of the shape of the defunctionalized η rule, equal to itself: its
equation of that rule is in the import set, beside the equations of the defunctionalized β rule
of successor's constants. -/

/-- The text of `eta_shaped_constant.art`: its lines, each followed by a newline. -/
def etaShapedConstantText : String :=
  String.join (etaShapedConstantLines.map (· ++ "\n"))

/-- The signature of the article's thunk constants, in the order it defines them. -/
def etaShapedConstantSignature : Signature :=
  [(thunkName "0", .apply (.slot 0) (.slot 1), [.slot 1]),
    (thunkName "1", .apply (.slot 0) (.slot 1), [.slot 1, .ignored, .slot 0]),
    (thunkName "2", .apply (.slot 0) (.slot 1), []),
    (thunkName "3", .apply (.slot 0) (.slot 1), [.ignored, .slot 0]),
    (thunkName "4", .apply (.slot 0) (.slot 1), [.slot 0])]

/-- The left side, `\x. successor x`. -/
def etaShapedConstantLeft : Article.Term :=
  successorExpanded "0" "1"

/-- The right side, `\x. successor x`. -/
def etaShapedConstantRight : Article.Term :=
  successorExpanded "0" "1"

/-- The reader accepts the article, its definitions give its signature, `importChecked` accepts
its import set, and its one exported equation is the equation of the two sides. -/
theorem etaShapedConstantChecked :
    resultChecked etaShapedConstantSignature lemmas etaShapedConstantLeft etaShapedConstantRight
      (Article.readArticle etaShapedConstantText) = true := by
  unfold etaShapedConstantText Article.readArticle
  rw [ArticleLines.articleLinesJoin etaShapedConstantLines
    (ArticleLines.noNewlineOfLinesClean (by decide +kernel))]
  decide +kernel

/-- The exported equation is sound. -/
theorem etaShapedConstantSound :
    EquationSound etaShapedConstantSignature etaShapedConstantLeft etaShapedConstantRight :=
  endToEndOfChecked lemmasSound etaShapedConstantChecked

/-- The reading of the two sides, λx. successor x, is contextually equivalent to itself,
through the article. -/
theorem etaShapedConstantContextualEquivalence :
    ContextualEquivalence
      successorExpandedTerm
      successorExpandedTerm :=
  contextualEquivalenceOfRead etaShapedConstantSound (by decide +kernel)
    (by decide +kernel)

end LambdaJit.EndToEndFixtures
