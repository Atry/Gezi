# LambdaJit: Lean 4 verification of e-graph traces

This Lake package checks, in Lean 4, the traces that the Gezi e-graph exports as
OpenTheory articles (D7): the article reader accepts an article whose exported equation follows
from the instances of its imported equations by reflexivity, symmetry, transitivity and
congruence, and the end-to-end theorem concludes from sound imports that the two sides of the
exported equation are contextually equivalent (≃_O of DdLP96's Definition 14). The imports are the
numbered equations, the equations of the defunctionalized β rule and η rule of the thunk
constants, which Lean proves sound, and the statements of the library's lemmas, each a theorem
where a hand-written proof or a kernel decision proves it and a named axiom otherwise. The object language is the
defunctionalised IR, a flat store of thunk layers (a thunk with holes, an application, a choice, a
parallel), not a de Bruijn tree; ⊢^{defunctionalized}_{λ-lattice-η} is stated on the finite
terms a store unfolds to. A library name labels the address of its
layer; there is no constant layer and no delta step. Unproven conjectures and lemmas enter as
named axioms, so `#print axioms` lists what each trace relies on. The
package uses Lean's core library only, without Mathlib.

What stands (2026-10-07): ⊢^{defunctionalized}_{λ-lattice-η} without the numbered equations,
which of them the IR theory needs as rules being open (FIXME in `Theory`). The module `Article` reads an OpenTheory
article of D7's command subset and proves that every exported equation is in the
congruence closure of the instances of its imports (`readArticle_sound`). The
module `Readback` defines D3's readback from finite terms to the terms of the calculus and
proves the soundness direction of D3's item 4: two finite terms equal in λ-lattice-η on
defunctionalized terms whose readbacks are defined have readbacks whose equation is derivable by
⊢_{λ-lattice-η}. The module `Defunctionalization` defines the front end's defunctionalization
of a closed term (`thunk_instruction/2`) and proves D3's items 3 and 5: the readback of the
defunctionalization is the term, and two different finite terms can have one readback. D3's item 2,
that α-equivalent terms have one defunctionalization, holds by construction on de Bruijn terms;
what is proved is its converse, the injectivity of the defunctionalization, from item 3: two closed
terms with one defunctionalization are one term. The module `Adequacy` collects what is proved of
D3's items (`defunctionalizationFacts`), and proves, through
the confluence of a reduction containing the IR theory's oriented rules (module `Confluence`), that
the converse of D3's item 4 is false for ⊢^{defunctionalized}_{λ-lattice-η} as `Theory` states
it, with three witnesses: a β step under a binder, a β step at the root whose defunctionalized
contractum is hoisted differently, and equation (1). Candidate routes to a converse (a leaf for a
free variable or a fresh constant, a theory on codes lifted to thunks by a congruence on the code,
a weaker statement) are listed there as candidates; none has been built or shown impossible.
The module `PreludeLemmas` proves that the prelude's fifteen equation lemmas hold in
⊢^{defunctionalized}_{λ-lattice-η} on every instance, by head steps (D5's first tier).
The module `Interpretation` reads the terms of an article as terms of the calculus, and the module
`EndToEnd` proves the end-to-end theorem of D6:
when the reader accepts a text and every equation of its import set is sound, every exported
equation is sound, its two sides being contextually equivalent (≃_O of DdLP96's Definition 14,
`ContextualPreorder.ContextualEquivalence`) under `interpret`, where a constant that is no
operator and no thunk constant reads as λx. x (`unknownLiteral`), which no proof reads; the meaning
on the readings of IR terms is carried only by `endToEndRead` and `contextualEquivalenceOfRead`. Every instance of the numbered equations (1) to (6) and (8) to (10) and every
thunk constant's equations of the defunctionalized β rule and η rule are sound. The module
`Encoding` defines the writer's encoding of a finite term as an article term (`encode`, with the
spelling of a thunk constant's name) and proves the part of link (ii) of D6 that is about Lean:
the reading of the encoding of a finite term is its readback, as partial functions
(`readEncode`), and `decodeThunkName` is a left inverse of the spelling
(`decodeThunkNameSpelling`); `endToEndEncoded` and `endToEndEncodedOfChecked` state the end-to-end
theorem on the readbacks of two finite terms whose encodings an article exports. Link (ii) as a
whole rests also on the Prolog writer computing `encode`, which is tested, not proved (a FIXME at
`key_term_written/2` of `gezi/prolog/gezi/opentheory_article.pl`; the tests
`the_writer_encodes_as_lean_encodes_…` of `gezi/tests/opentheory_article.plt`). Six of the
expected articles of `gezi/tests/opentheory_article_expected/` are of runs made by hand: the
module `EndToEndFixtures` takes four of them through it, checked by the kernel, with only Lean's
built-in axioms, and the Lean text of the first unit of `gezi/tests/lean_statements.plt` takes
all six, among them `two_thunks_of_one_class` and `an_argument_dropped_then_spelled`, which no module
of the package takes. The seven further expected articles are of the fixpoint runs, rounds of the
baseline's search strategy `fixpoint_egraph` on small programs over the native route's library (five
type checks and two rounds of the beta rule on closures): the module `FixpointRunFixtures`, generated
by `gezi/tests/opentheory_article.plt`, takes each through the end-to-end theorem, checked by
the kernel, with the statements of the lemmas it imports from the module
`NativeRouteLibraryStatements`, the export of that library generated by
`gezi/tests/lean_statements.plt`, and states it on the readbacks of the run's input and output,
the finite terms of the module `FixpointRunSides`; the module `FixpointRunFixturesAxioms` prints its
axioms, Lean's built-in ones only. <!-- TODO (https://github.com/Atry/private-overlay/issues/1526, section 3.9,
stages D and E): the description of the module that carried the end-to-end theorem of the
type-checking runs of the old HM baseline to their source program (TypeCheckingRunSourceFixtures,
link (i) of D6) stood here; the module of the source programs of the fixpoint runs is described
here. The deleted text reads back with `git show a66f8d948:lambda_jit/lean/README.md`. --> The module
`StatementNormalisation` proves a lemma statement sound for every valuation of its metavariables by
four decisions the kernel evaluates: it is an instance of a numbered equation, the normaliser
brings its two sides, the metavariables abstracted, to one normal form, leftmost outermost
contraction brings them to a common term, or its two sides have one simplification by absorption
and idempotence after the same number of developments (which proves the lemmas of the native
route's knowledge modules). The module `LibraryLemmaProofs` proves by hand the
statements no decision proves, and the command `lemma_soundness` of the module `LemmaSoundness`
makes a lemma a theorem by its hand-written proof or by the first decision that accepts it, and a
named axiom otherwise. The module `Terms` holds the terms of the calculus (de Bruijn terms, the
codomain of D3's readback, not the IR). The semantics is DdLP96's Definition 14, the contextual
preorder ⊑_O of the module `ContextualPreorder`; the derivability ⊢_{λ-lattice-η} of the module
`LatticeEtaDerivability` is a proof tool, whose rules are the β rule, the η rule, the numbered
equations (1), (3), (5) and (10) and four closure rules of a congruence (symmetry, transitivity, the
congruence in the argument of an application and the congruence in the body of an abstraction), the
other λ-lattice laws being theorems derived in the module `FourEquations`, and every equation it
derives is a contextual equivalence (`contextualEquivalenceOfDerivableLatticeEta`). There is no unit
law: `top` = Y (λz. λx. z ∥ x) is the greatest element of ⊑_O, and `top` + M ≃_O M is a contextual
equivalence (module `ContextualPreorderTop`), not an equation of ⊢_{λ-lattice-η}. The consistent
normal forms NF◇_{λ-lattice-η} are { N ∈ NF_βη | T ⊑_O N } (module `LatticeEtaBridge`). The module
`ParallelTypesTheorems` proves the lemmas of `parallel_types.pl` and
`filtered_recursion_naturals.pl` as theorems of λ-lattice-η, on the same terms. The traces stay on
the IR.

## Trace export

A search strategy gives the proof of a round when the round asks for it, the equation steps
joining each input to its output (`proof(Terms, Unions, Equations)` of `lambda_jit_schedule`,
THE PROOF), and the trace is written once after the run as an OpenTheory article
(D7): the IR as first-order HOL terms over the type `LambdaJit.term`, the numbered equations (1)
to (6) and (8) to (10), the equations of the defunctionalized β rule and η rule and the lemmas used as the import
set, the caller's equation
as the exported theorem, and sharing through the article's dictionary (no content hash).
`gezi/tests/check_opentheory_article.sh` checks an article with Hurd's opentheory tool
(`nix build .#opentheory -L`), and the module `Article` reads it in Lean. The writer is
`gezi/prolog/gezi/opentheory_article.pl`.

## Building

With Nix, from the root of this repository:

    nix build .#lambda-jit-lean -L

In the dev shell, from this directory:

    direnv exec . lake build

The toolchain is the one `lean-toolchain` names.

## Modules

- `LambdaJit/Ir.lean`: addresses, holes, the IR layer and code grammars, stores, finite
  terms and the solution of a store (D1).
- `LambdaJit/Theory.lean`: ⊢^{defunctionalized}_{λ-lattice-η} as an inductive relation on
  finite terms, and its reading on the addresses of a store (D2).
- `LambdaJit/Terms.lean`: the terms of the calculus with de Bruijn indices, their substitution,
  the closed βη normal forms, the one-hole contexts and the lemmas on shifting and substitution
  the other modules share; the readback's codomain (D3).
- `LambdaJit/Semantics.lean`: the closed terms K = λx.λy. x, K* = λx.λy. y and
  Ω = (λx. x x) (λx. x x), and sets of equations as predicates, with `listed` for a finite list.
- `LambdaJit/TermSubstitution.lean`: lowering, eta contraction and the commutation of shifting with
  substitution on the terms of `Terms`, used by `BetaEtaConfluence`, `Normalisation` and
  `Readback`.
- `LambdaJit/Article.lean`: the reader of OpenTheory articles (format version 6) for the
  fragment of D7: types, terms without abstraction, the commands D7 lists and nothing else; and
  `readArticle_sound`, the theorem that every theorem an accepted article exports is an
  equation derivable from the instances of its imported equations under reflexivity, symmetry,
  transitivity and congruence of application, and that the machine never holds a theorem with
  hypotheses. The reader takes each line apart by one walk over its UTF-8 bytes (`characters`,
  proved equal to `String.toList`, which decodes by byte position, in time the kernel takes
  quadratic in the length of the line).
- `LambdaJit/ArticleFixtures.lean`: hand-written articles in D7's encoding, four accepted and
  eleven rejected, each outcome checked on every build, and checks of the name and number
  syntax.
- `LambdaJit/ArticleAxioms.lean`: the `#print axioms` record of `readArticle_sound`.
- `LambdaJit/Normalisation.lean`: a fuelled beta-eta normaliser on the terms of `Semantics`
  (leftmost outermost contraction, the eta step exactly `DerivableLatticeEta.eta`), its soundness
  for E ⊢_{λ-lattice-η} for every set E of hypotheses, the theorem that its result has no redex, and
  fixtures checked by the kernel; the comparison D6 needs for two sides that are only
  beta-eta equal.
- `LambdaJit/NormalisationAxioms.lean`: the `#print axioms` record of the normaliser's
  theorems.
- `LambdaJit/ParallelTypesTheorems.lean`: the defines of `parallel_types` and the prelude defines
  they name as terms of `Terms`, and the three lemmas of `parallel_types.pl` and the four of
  `filtered_recursion_naturals.pl` as theorems of λ-lattice-η, each a contextual equivalence.
- `LambdaJit/ParallelTypesTheoremsAxioms.lean`: the `#print axioms` record of those theorems.
- `LambdaJit/FourEquations.lean`: the least congruence over the β rule, the η rule and a given
  set of equations, with none of the numbered equations built in; reflexivity and the congruences
  that are theorems; T1, T9 and the order facts the derivations share; and the theorem that equation
  (8) is derivable from (1), (3), (6) and (10), without (7), (8) and (9)
  (the proofs file, section 6), which `LatticeEtaDerivability` reads
  with (1), (3), (5) and (10) as the laws.
- `LambdaJit/FourEquationsAxioms.lean`: the `#print axioms` record of the theorem on equation (8).
- `LambdaJit/Readback.lean`: the readback from finite terms to the terms of the calculus, and
  the theorem that two finite terms equal in λ-lattice-η on defunctionalized terms whose
  readbacks are defined have readbacks equal by ⊢_{λ-lattice-η} (D3, item 4, the soundness
  direction).
- `LambdaJit/ReadbackAxioms.lean`: the `#print axioms` record of that theorem.
- `LambdaJit/Interpretation.lean`: the code and holes of a thunk constant decoded from its name,
  the reading of a closed article term as a term of the calculus, and the total interpretation
  of every article term that the proofs use (D10).
- `LambdaJit/EndToEnd.lean`: the soundness of an equation between article terms, the end-to-end
  theorem and its corollary for sides that read as terms of the calculus, the soundness of the
  numbered equations and of every thunk constant's equations of the defunctionalized β rule and
  η rule, and `importChecked`, which recognises those equations in an article's import set (D10).
- `LambdaJit/Encoding.lean`: the writer's encoding of a finite term as an article term as Lean
  states it (`encode`, the writer's `key_encoding/2` and `layer_encoding/2`, undefined where the
  writer throws), the spelling of a thunk constant's name (`thunkName`, the writer's
  `code_spelling/2` and `holes_spelling/2`), and the part of link (ii) of D6 that is about Lean:
  `readEncode` (the reading of `encode t` is the readback of `t`, as partial functions),
  `decodeThunkNameSpelling` (`decodeThunkName` is a left inverse of the spelling),
  `operatorOfThunkName` (a spelled name is the operator of that thunk constant), and
  `endToEndEncoded` and `endToEndEncodedOfChecked` (the end-to-end theorem on the readbacks of two
  finite terms whose encodings an article exports). That the Prolog writer computes `encode` is
  tested, not proved (a FIXME at `key_term_written/2` of the writer).
- `LambdaJit/EncodingAxioms.lean`: the `#print axioms` record of those five theorems.
- `LambdaJit/ArticleLines.lean`: the text of lines each followed by a newline splits back into
  the lines, so that the kernel evaluates the reader on a text written as its lines
  (`readArticleOfLines`).
- `LambdaJit/ExpectedArticles.lean`: the lines of the thirteen expected articles of
  `gezi/tests/opentheory_article_expected/`, six of runs made by hand and seven of the
  fixpoint runs, generated from the files by `ExpectedArticlesModule.text` of the proofs tests
  (`proofs/Test/runMain gezi.proofs.writeExpectedArticlesModule`), and
  `ExpectedArticlesModuleTest` checks that regenerating the module gives it byte for byte; not
  edited.
- `LambdaJit/EndToEndFixtures.lean`: four of the six expected articles of the runs made by hand,
  those whose import sets cite no lemma but `identity_applied`, taken through the end-to-end
  theorem, each checked by the kernel (`decide +kernel`).
- `LambdaJit/EndToEndAxioms.lean`: the `#print axioms` record of those theorems.
- `LambdaJit/NativeRouteLibraryStatements.lean`: the export of the native route's library, the
  statement of each lemma and its soundness theorem, generated by
  `gezi/tests/lean_statements.plt`, which checks that regenerating it gives it byte for byte;
  not edited.
- `LambdaJit/FixpointRunSides.lean`: the input and the output of each fixpoint run as finite
  terms, generated by `gezi/tests/opentheory_article.plt`; not edited.
- `LambdaJit/FixpointRunFixtures.lean`: the seven expected articles of the fixpoint runs taken
  through the end-to-end theorem, each checked by the kernel, and stated on the readbacks of the
  run's input and output; generated by `gezi/tests/opentheory_article.plt`; not edited.
- `LambdaJit/FixpointRunFixturesAxioms.lean`: the `#print axioms` of those theorems, which the
  same test checks list Lean's built-in axioms only.
- `LambdaJit/StatementNormalisation.lean`: a lemma statement, a pair of article terms, is sound
  for every valuation of its variables when its two sides, the variables abstracted, are equal by
  ⊢_{λ-lattice-η} (`equationSoundOfAbstractedDerivable`), or contextually equivalent
  (`equationSoundOfAbstractedEquivalent`), and four decisions that the kernel evaluates establish
  it: the normaliser brings the two abstracted sides to one normal form (`statementNormalised`,
  `statementSoundOfNormalised`), leftmost outermost contraction brings them to a common term
  (`statementContracted`, `statementSoundOfContracted`), the statement is an instance of one of
  the numbered equations (1) to (6) and (8) to (10), its operands read off its left side (`numberedInstance`,
  `numberedInstanceSound`), or the two sides have one simplification by `top` ∥ M ≃_O `top` and
  `top` + M ≃_O M (`top` the greatest element of ⊑_O, module `ContextualPreorderTop`), the idempotence of
  the parallel and of the choice, absorption, the absorption of a typed version and of a filtered
  application (context monotonicity, T10) and the η rule after the same number of developments, at
  most `absorptionDevelopments` (`statementAbsorbed`, `statementSoundOfAbsorbed`);
  `lemma_soundness` (`LemmaSoundness.decisionTheorems`) tries the numbered equations, absorbed
  members, the normaliser and contraction, in that order.
- `LambdaJit/LibraryLemmaProofs.lean`: hand-written proofs of the exported statements that no
  decision proves, each named after its lemma and stating the soundness of its own copy of the
  statement: the three lemmas of `parallel_types.pl`, the four of `filtered_recursion_naturals.pl`
  and the five of `contracts.pl`, each joined by a bounded search that the kernel evaluates to a
  theorem of `ParallelTypesTheorems` or to a short derivation.
- `LambdaJit/LibraryLemmaProofsAxioms.lean`: the `#print axioms` record of those theorems.
- `LambdaJit/LemmaSoundness.lean`: the command `lemma_soundness`, which declares a statement's
  soundness as a theorem by its hand-written proof, after checking that the proof's type is
  definitionally equal to it (an error otherwise), or by the soundness theorem of the first
  decision that the kernel finds to accept it, and as a named axiom when there is neither.
- `LambdaJit/StatementNormalisationAxioms.lean`: the `#print axioms` record of the decisions'
  theorems and of the fixture `EndToEndFixtures.identityAppliedNormalised`, which proves
  `identity_applied` by the normaliser.
<!-- TODO (https://github.com/Atry/private-overlay/issues/1526, section 3.9, stages C, D and E): the entries of
the deleted modules of the old HM baseline stood here: `GenericLibraryStatements.lean`, the export
of its library's lemma statements; `TypeCheckingRunSides.lean`; the four modules of the articles of
its type-checking runs with their Axioms modules (`TypeCheckingRunFixtures`,
`TypeCheckingRunNineRoundsFixtures`, `TypeCheckingRunFunctionFixtures`,
`TypeCheckingRunBaselineFixtures`); and `TypeCheckingRunSource.lean` and
`TypeCheckingRunSourceFixtures.lean` with its Axioms module, link (i) of D6 on their source programs.
The modules of the new HM baseline's lemma statements and type-checking runs are described here.
The deleted text reads back with `git show a66f8d948:lambda_jit/lean/README.md`. -->
- `LambdaJit/Defunctionalization.lean`: the front end, `thunk_instruction/2` of
  `defunctionalization.pl` written clause by clause over source programs (de Bruijn terms with
  choices of any number of members and constants, a constant carrying its define's source program)
  with D1's canonical numbering, `thunkInstruction`; link (i) of D6 for it
  (`readbackThunkInstruction`: the readback of the finite term of a closed program whose constants'
  definitions are closed is δ of the program, equal as de Bruijn terms; `thunkInstructionDefined`:
  `thunkInstruction` has a value on no other program, so `readbackOfThunkInstruction` holds of every
  finite term it gives); the defunctionalization of
  a closed term of the calculus, `thunkInstruction` of the term as a program, whose readback is the
  term (D3, item 3), with the injectivity (the converse of item 2, which holds by construction); its
  agreement with the Prolog on eight programs, checked by the kernel (and, by
  `gezi/tests/defunctionalization_agreement.plt`, byte for byte on 300 random source programs,
  on every define of the prelude and on 300 random closed terms of the calculus; that the Prolog
  computes `thunkInstruction` is not proved, a FIXME); the kernel-checked witnesses that the finite
  term of a library name or of a choice of one member or of three is not the defunctionalization of
  its δ but reads back to it, so link (i) is stated on readbacks; and two different finite terms
  with one readback, one of them obtained by the first clause of the defunctionalized β rule
  (item 5).
- `LambdaJit/Confluence.lean`: a simultaneous reduction containing the rules of
  ⊢^{defunctionalized}_{λ-lattice-η} oriented from left to right, its confluence, the theorem
  that two equal finite terms reduce to a common term, and its consequence that two thunks with
  holes (the holes not empty) that are not shaped as the left side of the defunctionalized η rule
  and differ in their codes or their holes are never equal, nor are two choices whose members at
  one position are such thunks.
- `LambdaJit/Adequacy.lean`: what is proved of D3's items (`defunctionalizationFacts`),
  the refutation of the converse of D3's item 4 for `Theory` with three witnesses, and the candidate
  routes to a converse (D3).
- `LambdaJit/AdequacyAxioms.lean`: the `#print axioms` record of those theorems.
- `LambdaJit/PreludeLemmas.lean`: head steps and their soundness, the finite terms of the prelude's
  defines and of the sides of its fifteen equation lemmas, and the theorem, for each lemma, that its
  two sides applied to arbitrary finite terms, one per metavariable, are equal in
  λ-lattice-η on defunctionalized terms (D5, first tier);
  `gezi/tests/defunctionalization_agreement.plt` checks the sides against the index.
- `LambdaJit/PreludeLemmasAxioms.lean`: the `#print axioms` record of those theorems.
- `LambdaJit/BinaryNaturalsNonMember.lean`: the defines of `binary_set` and of the binary
  constructors as terms, the binary numerals, and the theorem that for every numeral n and boolean p
  with n not a member of `binary_set p`, the equation ñ + `binary_set p` = `binary_set p` derives
  λx.λy. x = λx.λy. y (the binary naturals record, sections 8.3 and 8.4).
- `LambdaJit/BinaryNaturalsNonMemberAxioms.lean`: the `#print axioms` record of those theorems.
- `LambdaJit/BetaEtaConfluence.lean`: shifting and substitution lemmas, βη-conversion on the terms
  of the calculus (`Convertible`), and the Church–Rosser property of β and η by Takahashi's
  simultaneous reductions and Hindley and Rosen's commutation, with the consequence that
  λx.λy. x and λx.λy. y are not βη-convertible (`firstNotConvertibleSecond`).
- `LambdaJit/SyntacticConsistency.lean`: the machinery of the syntactic consistency proof of
  the syntactic consistency proof: the confluent reduction →o (the β rule, (8) and
  (9)), the readings of a term and the simulation ≼, which module `LatticeEtaConsistency` runs on
  ⊢_{λ-lattice-η}.
- `LambdaJit/SyntacticConsistencyAxioms.lean`: the `#print axioms` record of its theorems.
- `LambdaJit/ContextualPreorder.lean`: the syntactic part of
  the contextual preorder record: DdLP96's head reduction →hsa on Λ_{+∥},
  solvability SOL, DdLP96's contextual preorder ⊑_O (their Definition 14, the semantics), the set
  { N ∈ NF_βη | T ⊑_O N } (our definition, `ContextualNormalForm`), and the record's (S0) to (S4),
  lemma X included.
- `LambdaJit/ContextualPreorderAxioms.lean`: the `#print axioms` record of those theorems.
- `LambdaJit/DdLP96Model.lean`: the structure `DdLP96Model`, the facts about Wadsworth's D∞ and
  DdLP96's reading in it that the record's proofs use, passed as an explicit argument and not an
  axiom (D10); its instance is `wadsworthModel`
  (`DInfinityModel.lean`). Given a model: the reading respects →hsa (`interpretHeadStep`), and a
  solvable term does not read as ⊥ (theorem 4.1, ⇒).
- `LambdaJit/ContextualPreorderAdequacy.lean`: given a model, the record's theorem 4.1 (SOL is the
  set of terms not reading as ⊥) and corollary 4.2, with `top` = Y (λz. λx. z ∥ x) as the closed
  argument of the proof, `top` and Ξ applied to closed terms solvable (`solvableApplicationsTop`,
  `solvableApplicationsXi`), and K ≄_O K* (`notContextuallyEquivalentFirstSecond`).
- `LambdaJit/ContextualPreorderAdequacyAxioms.lean`: the `#print axioms` record of those theorems.
- `LambdaJit/ContextualPreorderTop.lean`: the greatest terms of ⊑_O: a closed X is above every term
  if and only if X P₁ … Pₖ ∈ SOL for every k and all closed P⃗ (`contextualTopIff`,
  `contextualTopIffClosed`); `top` and Ξ are such terms (`contextualTop`, `contextualTopXi`); for every
  such X, X + M ≃_O M and X ∥ M ≃_O X, with their instances at `top`; and every equation derivable in
  ⊢_{λ-lattice-η} from contextual equivalences is one
  (`contextualEquivalenceOfDerivableLatticeEtaHypotheses`).
- `LambdaJit/ContextualPreorderTopAxioms.lean`: the `#print axioms` record of those theorems.
- `LambdaJit/ContextualPreorderBridge.lean`: given a model, the reading of a term depends only on
  its free variables, so a closed term reads the same in every environment.
- `LambdaJit/ContextualPreorderSeparation.lean`: the syntax of the proofs file's section 20
  (stratified approximants with ⋄ written Ω, truncation, β normal head nodes, the conflict relation
  with section 14.1's η alignment).
- `LambdaJit/ContextualPreorderSeparationProof.lean`: the parts of theorem S that do not mention a
  derivability, with no model: the tagged permutators, the components of Σ, and the layers of a
  conflict derivation.
- `LambdaJit/ContextualPreorderCompleteness.lean`: given a model, the proofs file's lemma C and the
  reading of head nodes it rests on.
- `LambdaJit/ContextualPreorderCompletenessAxioms.lean`: the `#print axioms` record of lemma C and
  of the theorems of `ContextualPreorderSeparationProof` the completeness uses.
- `LambdaJit/ContextualPreorderApproximation.lean`: the parts of the proofs file's theorem A with
  lemma C0 that do not mention a derivability: free indices, shifting and substitution of
  stratified terms and truncations, `bindVariable`, and the free indices of redexes.
- `LambdaJit/ContextualPreorderOmegaBottom.lean`: given a model, Ω below every term: Ω ∥ M ≃_O M,
  Ω ⊑_O M, Ω + M ≃_O Ω and Ω M ≃_O Ω, each by corollary 4.2.
- `LambdaJit/ContextualPreorderOmegaBottomAxioms.lean`: the `#print axioms` record of those
  theorems.
- `LambdaJit/DInfinityLevels.lean`: the finite levels Dₙ of Wadsworth's D∞ with the two-point D₀,
  D_{n+1} the monotone functions of Dₙ, as finite distributive lattices with a list of their
  elements, and Wadsworth's maps φ and ψ between any two levels with their laws.
- `LambdaJit/DInfinity.lean`: D∞ as the inverse limit, its componentwise order, meets, joins and
  suprema, the projections Pₙ with Wadsworth's (P1), (P3) and (P4), the compactness of the elements
  of 𝔻ₙ, the list of 𝔻ₙ, and the rich environment ρ₀.
- `LambdaJit/DInfinityApplication.lean`: application in D∞ by (P7) with (P6), (P8), (P11), (P12)
  and the facts (E4) and (E5), its continuity, and the abstraction of a monotone continuous
  function.
- `LambdaJit/DInfinityModel.lean`: DdLP96's reading of the terms in D∞, monotone and continuous in
  the environment, and `wadsworthModel`, the instance of `DdLP96Model` with every field proved.
- `LambdaJit/ContextualPreorderUnconditional.lean`: the theorems of modules
  `ContextualPreorderAdequacy` and `ContextualPreorderOmegaBottom` that take a model, at
  `wadsworthModel`: theorem 4.1 (`solvableIffInterpretNotBottom`), and with no hypothesis
  Ω ∥ M ≃_O M, Ω ⊑_O M, Ω + M ≃_O Ω and Ω M ≃_O Ω.
- `LambdaJit/ContextualPreorderUnconditionalAxioms.lean`: the `#print axioms` record of the instance
  and of those theorems: Lean's built-in axioms only.
- `LambdaJit/ContextualPreorderDistributive.lean`: the parallel distributes over the choice,
  M ∥ (N + P) ≃_O (M ∥ N) + (M ∥ P), with no hypothesis, by corollary 4.2 and the model's (E1).
- `LambdaJit/ContextualPreorderDistributiveAxioms.lean`: the `#print axioms` record of those
  theorems: Lean's built-in axioms only.
- `LambdaJit/LatticeEtaDerivability.lean`: ⊢_{λ-lattice-η}, the derivability of the calculus
  (`DerivableLatticeEta`; the proofs file, section 21): one
  constructor per rule, the four closure rules, β, η and the axioms (1), (3), (5), (10); (2), (4),
  (6), (8) (the second derivation, without (7)) and (9) as theorems, with no unit law.
- `LambdaJit/LatticeEtaConsistency.lean`: with no hypotheses ⊢_{λ-lattice-η} is consistent
  (`consistentLatticeEtaWithoutHypotheses`, the syntactic proof of module `SyntacticConsistency`,
  no model) and relates two pure terms only when they are βη-convertible
  (`derivableLatticeEtaPureConvertible`); every equation it derives is a contextual equivalence
  (`contextualEquivalenceOfDerivableLatticeEta`, the record's theorem 6.1).
- `LambdaJit/LatticeEtaXi.lean`: the proofs file's section 3 in ⊢_{λ-lattice-η}: bracket abstraction
  (`Combination`, `translate`, `embedTranslate`), theorem two, Ξ + M = M for closed M
  (`xiRefinesClosed`), lemma (F), Ξ A⃗ refines every closed term (`refinesClosedTermsApplyAll`), and
  K + Z = Z with such a Z derives K = K* (`inconsistentOfChoiceRefines`).
- `LambdaJit/LatticeEtaApproximation.lean`: given a model, theorem A in ⊢_{λ-lattice-η}
  (`DdLP96Model.approximationLatticeEta`).
- `LambdaJit/LatticeEtaSeparation.lean`: theorem S with Ξ A⃗ in the place of the proofs file's 0
  (`separationLatticeEta`), and the completeness of DdLP96's reading for NF◇_{λ-lattice-η}
  (`DdLP96Model.completenessLatticeEta`).
- `LambdaJit/LatticeEtaAxioms.lean`: the `#print axioms` record of the theorems of those modules:
  Lean's built-in axioms only.
- `LambdaJit/LatticeEtaBridge.lean`: for a closed T and a closed βη normal form N,
  {N + T = T} ⊬_{λ-lattice-η} K = K* if and only if T ⊑_O N
  (`consistentNormalFormLatticeEtaIffContextualPreorder`), so NF◇_{λ-lattice-η}(T) is
  { N ∈ NF_βη | T ⊑_O N } (`consistentNormalFormLatticeEtaIffContextualNormalForm`), and the
  record's proposition 7.3 read through it (`contextualPreorderIffInterpretBelowLatticeEta`).
- `LambdaJit/LatticeEtaBridgeAxioms.lean`: the `#print axioms` record of the theorems of
  `LatticeEtaConsistency` and `LatticeEtaBridge`: Lean's built-in axioms only.
- `LambdaJit/ContextualNormalFormsEquivalence.lean`: ≃_O is the equality of the sets
  { N ∈ NF_βη | C[M] ⊑_O N } in every context C (`contextualEquivalenceIffSameContextualNormalForms`),
  through Lemma A, a closed T is unsolvable if and only if T ⊑_O N for every closed βη normal form N
  (`notSolvableIffContextualPreorderNormalForms`), and the converse for NF◇_{λ-lattice-η}
  (`contextualEquivalenceOfSameConsistentNormalForms`).
- `LambdaJit/ContextualNormalFormsEquivalenceAxioms.lean`: the `#print axioms` record of those
  theorems: Lean's built-in axioms only.
- `LambdaJit/DInfinityFixedPoint.lean`: least fixed points in Wadsworth's D∞, Park's theorem, and the
  reading of Turing's fixed point combinator.
- `LambdaJit/StaticArgumentFixpoint.lean`: the static argument transformation in D∞, the proofs
  file's section 18.1.
- `LambdaJit/RefinementSearch.lean`: a search, guided by head redexes, for derivations of
  M + N = N in ⊢_{λ-lattice-η}, with its soundness (`headRefinedSound`).
- `LambdaJit/WrenLemmaProofs.lean`: hand-written proofs of lemmas of the entry `wren`, by the naming
  rule of `LibraryLemmaProofs`.
- `LambdaJit.lean`: imports all of the above.

The statements of the library's lemmas are generated and not kept in the tree
<!-- TODO (https://github.com/Atry/private-overlay/issues/1526, section 3.9, stages C and D): the old HM
baseline's library kept its export in the tree (`GenericLibraryStatements`); the new route's
knowledge module keeps its export here once it exists. -->:
`lean_statements_exported/1` of `gezi/prolog/gezi/lean_statements.pl` writes, for a
compiled library, a module that imports `LambdaJit.LemmaSoundness` and declares in
`LambdaJit.Exported`, for each lemma, its statement as the pair of `Article.Term` values that an
article imports for it, built by the article writer's own encoding; its soundness
(`EndToEnd.EquationSound`) through the command `lemma_soundness`, a theorem where a hand-written
proof of `LibraryLemmaProofs` or a kernel decision proves it and otherwise a named axiom whose
docstring says, under a FIXME, that neither did (D5); each docstring cites the lemma's proof, a
proof on paper or the test unit that replays the lemma, and says what proved the theorem; and the
list `lemmas` with `lemmasSound`, the lemma list of `EndToEnd.endToEndOfChecked`. For prelude,
guard_laws, parallel_types, filtered_recursion_naturals, lattice_types and contracts (2026-10-07),
all 36 lemmas are theorems: 12 by hand-written proofs (the lemmas proved on paper of
parallel_types, filtered_recursion_naturals and contracts), 2 as instances of the numbered
equations (8) and (9) (`choice_applied` and `parallel_applied` of lattice_types), 18 by the
normaliser, and 4 by leftmost outermost contraction (four rows of recursive functions of prelude,
whose sides unfold a fixpoint and have no normal form). `gezi/tests/lean_statements.plt`
checks, for those six modules, that Lean accepts the module, that the statement of
`identity_applied` is term for term an import of the expected article of the run
one_lemma_instance, that the six expected articles of the runs made by hand go through
`endToEndOfChecked` with the exported
soundness of the lemmas they use, that `#print axioms` of each lemma's soundness and of each
article check lists Lean's built-in axioms only, and how many lemmas each kind of proof proves.

## Design decisions

The modules name these decisions by their numbers. The paper proofs that modules formalise are
not in this repository; modules name them the proofs file (the equations of the calculus and their
proofs, the D∞ reading, the completeness of theorem A and the separation theorem S), the
contextual preorder record (Definition 14, solvability and the adequacy of DdLP96's reading), the
syntactic consistency proof and the binary naturals record, with the section a module follows.

- **D1, the object language.** The IR is a flat, content-interned system of equations, one layer
  per address: `thunk(Thunk, Holes, Fillings)` (the closure of a chain of λs: `Thunk` the address of
  its code, `Holes` the slot of each binder in λ order, `ignored` for a binder its body does not
  use, `Fillings` the values of the other slots in slot order), `apply`, `choice` and `parallel`.
  A code is the body of a λ chain over `slot(Index)`, where binders and the maximal closed subterms
  are numbered alike, in order of first occurrence in the body, one slot for equal closed subterms
  (the canonical numbering). A closure is a thunk with holes and has no code of its own: partial
  application fills the first hole, and filling the last is the instance of the body. A library
  name labels the address of its layer, so there is no constant layer and no δ. A term is a
  finite, acyclic store with a root address, one address per layer, and the solution of the store
  at an address is a finite term.
- **D2, ⊢^{defunctionalized}_{λ-lattice-η}.** The equivalence on finite terms generated by the
  defunctionalized β rule (applying a thunk with holes fills its first hole; a thunk with no hole
  is the instance of its code under its fillings), the defunctionalized η rule (a thunk of one hole
  whose code is `apply(slot(f), slot(h))`, f ≠ h, equals the filling of slot f), and congruence. It
  has no rule under a binder, so a code is never rewritten.
- **D3, the readback.** `Readback.readback` reads a finite term as a term of the calculus: a thunk
  as a λ chain, `apply` as application, `choice` as +, `parallel` as ∥. Its items: (1) the readback
  depends only on the address; (2) the defunctionalization depends only on the α class of the term
  (by construction on de Bruijn terms), and its converse, injectivity, follows from (3); (3) the
  readback of the defunctionalization of a closed term is the term; (4) a step of
  ⊢^{defunctionalized}_{λ-lattice-η} reads back to a derivation of ⊢_{λ-lattice-η} (the soundness
  direction), while the converse fails for D2's rules; (5) addresses are finer than α-equivalence:
  two different finite terms can have one readback. The consistent normal forms of a finite term
  are those of its readback (D3's S_IR).
- **D5, the three tiers of lemmas.** A lemma is sound when Lσ ≃_O Rσ for every σ (Definition 14).
  The first tier is the lemmas whose instances are derivable in ⊢^{defunctionalized}_{λ-lattice-η}
  by the defunctionalized β and η rules and congruence, the only ones a trace can replay; the second
  is the lemmas sound by Definition 14 but not derivable (set laws, coinductive lemmas), a theorem
  when proved in Lean and otherwise a named axiom whose docstring cites the paper proof; the third
  rests on a conjecture, cited as its named axiom.
- **D6, the checks.** The article reader (`Article`) accepts only the commands of D7 and proves that
  every exported equation is in the congruence closure of the instances of the imports; the
  end-to-end theorem (`EndToEnd`, on the reading ⟦·⟧ of `Interpretation`) concludes from sound
  imports that every exported equation is sound. Two links tie the theorem to a source program M:
  (i) the readback of the front end's defunctionalization of M is δ(M), M with every library name
  replaced by its definition (`Defunctionalization.readbackThunkInstruction`); (ii) the reading of
  the article term the writer writes for an IR term is that term's readback (`Encoding`).
- **D7, the trace is an OpenTheory article.** The defunctionalized IR has no binder, so it is
  written as first-order HOL terms over one type operator `LambdaJit.term`: the constants
  `LambdaJit.apply`, `LambdaJit.choice`, `LambdaJit.parallel` and `LambdaJit.emptyChoice`, and one
  constant per pair of code and holes, applied to the fillings. The imports are the numbered
  equations, the defunctionalized β and η equations of every thunk constant, and the statements of
  the lemmas used; the derivation uses `subst`, `refl`, `appThm`, `trans` and `sym`, and every type,
  constant, term and theorem is built once and shared through the dictionary.
- **D7.1, thunk constants are defined, not spelled.** A thunk constant is named
  `LambdaJit.thunk.N`, N its order of first occurrence in the article or the statement, from 0, and
  its code and holes are the defining term of an OpenTheory `defineConst`, written in the
  first-order constants `LambdaJit.Code.*`, `LambdaJit.Hole.*` and `LambdaJit.Number.*`. A reader
  reads the definitions into a signature, from names to codes and holes; an article and a statement
  number their constants each on its own, so an import matches a lemma statement when the two terms
  agree under their two signatures.
- **D8, the package.** A Lake package with Lean's core library only, no Mathlib.
- **D10, D∞ as an explicit argument.** The facts about Wadsworth's D∞ and DdLP96's reading in it
  that the paper proofs use form the structure `DdLP96Model`, passed to the theorems as an argument,
  not an axiom; its instance `DInfinity.wadsworthModel` proves every field.
