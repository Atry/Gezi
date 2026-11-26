import Lean
import LambdaJit.StatementNormalisation
import LambdaJit.LibraryLemmaProofs
import LambdaJit.WrenLemmaProofs

/-!
# The command that states a lemma sound: a theorem where Lean proves it, else an axiom

The module of the library's lemma statements that `lean_statements_exported/1` of
`gezi/prolog/gezi/lean_statements.pl` writes states the soundness of each lemma with
the command

    lemma_soundness «Name» of Statement.«Name»
      /-- … -/

where the statement is an `EndToEnd.Statement` already defined, its two sides with the signature of
their thunk constants (D7.1), and the docstring says what the
lemma is and cites its proof. The command declares, under the name `«Name»` in the current
namespace, the first of these that applies:

1. when the environment holds the hand-written proof `LambdaJit.LibraryLemmaProofs.«Name»`
   (module `LibraryLemmaProofs`, which states its naming rule): the theorem that the statement is
   sound, `EndToEnd.EquationSound`. The proof is of one of two forms, which the elaborator tells
   apart by the proof's type (`Meta.isDefEq`):
   - the statement's derivability, `EndToEnd.EquationDerivable`, from which
     `EndToEnd.equationSoundOfDerivable` gives the soundness;
   - the statement's soundness itself, `EndToEnd.EquationSound`: the two sides are contextually
     equivalent under every valuation. This is the form of a lemma that is sound by Definition 14
     and that ⊢_{λ-lattice-η} does not derive, such as one proved through a model: every lemma holds by
     Definition 14, and such lemmas are proved in Lean against the formalization of ≃_O.

   When the proof's type is neither, the command fails with an error: the proof's copy of the
   statement no longer matches the export, and the lemma does not become an axiom;
2. otherwise the kernel checks, in turn, the theorem of each of the seven decisions of module
   `StatementNormalisation` (`decisionTheorems`, `kernelAccepted`): the decision's soundness
   theorem applied to `Eq.refl true`, which the kernel accepts by evaluating the decision to
   `true`, and the command declares the first it accepts, with the environment the kernel checked
   it in:
   - `numberedInstance`, the statement being an instance of one of the numbered equations (1) to
     (6) and (8) to (10): `numberedInstanceSound`;
   - `statementAbsorbed`, the two sides, `top` written as `ContextualPreorder.top` in each,
     after the same number of developments, at most
     `absorptionDevelopments`, having one simplification by T3, `top` + M = M, the idempotence of
     the parallel and of the choice, absorption, the absorption of a typed version and of a
     filtered application, and the η rule: `statementSoundOfAbsorbed`;
   - `statementNormalised`, the normal form by weak head reduction and then the subterms bringing
     the two sides, the metavariables abstracted, to one term within `normalisationFuel`
     contractions on each side: `statementSoundOfNormalised`;
   - `statementContracted`, leftmost outermost contraction bringing the two sides, the
     metavariables abstracted, to a common term within `contractionFuel` contractions on each side:
     `statementSoundOfContracted`;
   - `statementOpenedAccepted`, one of the last three accepting the statement with the constants
     both its sides hold read as variables, which no decision unfolds:
     `statementSoundOfOpenedAccepted`;
   - `statementNormalisedLong`, the normal form of `statementNormalised` within
     `longNormalisationFuel` contractions on each side, tried before `statementOpenedAccepted`:
     `statementSoundOfNormalisedLong`;
   - `statementReached`, leftmost outermost contraction taking one side, the metavariables
     abstracted, to the other within `reachFuel` contractions, tried after
     `statementNormalisedLong` and before `statementOpenedAccepted`: `statementSoundOfReached`;
3. when none accepts it: the named axiom of the same statement.

The hand-written proof is looked up first, since a lookup costs no evaluation and the check of its
type catches a drifted copy even of a statement that a decision would prove. The command adds to
the docstring a paragraph that says which applied: the proof or the decision that proved the
theorem, with the fuel, or, for an axiom, a FIXME that says that no hand-written proof exists and
that no decision accepts the statement at its fuel.

Whether a lemma is a theorem is so decided by the environment and by the kernel's evaluation of the
decisions, and by no list of names, and `#print axioms` lists the axiom of every lemma Lean does not
prove that a theorem uses. A rejection of a decision's theorem other than by its evaluation (an
application type mismatch) is an error.
-/

namespace LambdaJit.LemmaSoundness

open Lean Elab Command

/-- `lemma_soundness name of statement doc`: the soundness of the statement `statement`, an
`EndToEnd.Statement`, declared under `name` as a theorem when a hand-written proof or a decision of module
`StatementNormalisation` proves it, and as an axiom otherwise, with the docstring `doc` and a
paragraph that says which. -/
syntax (name := lemmaSoundness) "lemma_soundness " ident " of " ident ppSpace docComment : command

/-- The name of the hand-written proof of the lemma whose soundness the command declares under
`name`: `LambdaJit.LibraryLemmaProofs.«Name»` for the name `«Name»`. -/
def handWrittenProofName (name : Name) : Name :=
  `LambdaJit.LibraryLemmaProofs ++ name

/-- The signature and the two sides of the statement `statement`, a constant of type
`EndToEnd.Statement` (D7.1): `statement.signature`, `statement.left` and `statement.right`. -/
def statementParts (statement : Name) : Expr × Expr × Expr :=
  let value := mkConst statement
  (mkApp (mkConst ``LambdaJit.EndToEnd.Statement.signature) value,
    mkApp (mkConst ``LambdaJit.EndToEnd.Statement.left) value,
    mkApp (mkConst ``LambdaJit.EndToEnd.Statement.right) value)

/-- The soundness of the statement `statement`: `EndToEnd.Statement.Sound statement`. -/
def soundnessType (statement : Name) : Expr :=
  mkApp (mkConst ``LambdaJit.EndToEnd.Statement.Sound) (mkConst statement)

/-- The derivability of the statement `statement`, the type of a hand-written proof:
`EndToEnd.EquationDerivable statement.signature statement.left statement.right`. -/
def derivabilityType (statement : Name) : Expr :=
  let (signature, left, right) := statementParts statement
  mkApp3 (mkConst ``LambdaJit.EndToEnd.EquationDerivable) signature left right

/-- `EndToEnd.equationSoundOfDerivable proof`, the soundness of the statement `statement` from the
hand-written proof `proof` of its derivability. -/
def soundnessOfDerivable (statement proof : Name) : Expr :=
  let (signature, left, right) := statementParts statement
  mkApp4 (mkConst ``LambdaJit.EndToEnd.equationSoundOfDerivable) signature left right
    (mkConst proof)

/-- `soundness statement (Eq.refl true)`, the proof that a decision proves: `soundness` is one of
the theorems `StatementNormalisation.numberedInstanceSound`, `statementSoundOfNormalised`,
`statementSoundOfContracted`, `statementSoundOfAbsorbed`, `statementSoundOfNormalisedLong`, `statementSoundOfReached` and `statementSoundOfOpenedAccepted`, whose explicit argument is the
equation `decision statement = true`.
The kernel checks `Eq.refl true` against that equation by evaluating the decision, once, when it
adds the theorem. -/
def decidedProof (soundness statement : Name) : Expr :=
  mkApp2 (mkConst soundness) (mkConst statement)
    (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))

/-- Adds the theorem `name` of type `type` proved by `value`, the kernel checking it, with the
docstring `documentation`. -/
def theoremAdded (name : Name) (type value : Expr) (documentation : String) :
    CommandElabM Unit := do
  liftCoreM <| addDecl <| .thmDecl { name, levelParams := [], type, value }
  addDocStringCore name documentation

/-- Adds the axiom `name` of type `type` with the docstring `documentation`. -/
def axiomAdded (name : Name) (type : Expr) (documentation : String) : CommandElabM Unit := do
  liftCoreM <| addDecl <| .axiomDecl { name, levelParams := [], type, isUnsafe := false }
  addDocStringCore name documentation

/-- The decisions of module `StatementNormalisation`, each by its number and its soundness theorem,
in the order `lemma_soundness` tries them; the number names the decision, not its place in the
order. `statementAbsorbed` comes second: of
the 89 statements of the native route it accepts 85, which tried the normaliser and contraction
first and failed there, and it proves a statement sound as the others do, by Definition 14, the
others by ⊢_{λ-lattice-η} under it. Measured 2026-11-19, CPUs 4 to 7: `lake build` of the package
after a change of module `StatementNormalisation` 528 s with the order 1, 2, 3, 4, and 427 s with
1, 4, 2, 3; `LeanStatementsTest`'s export, the package built, 42.1 s and 35.0 s, 14 of its 18
lemmas that the normaliser proved now proved by `statementAbsorbed`. `statementNormalisedLong` comes
before `statementOpenedAccepted`: no statement of either export is accepted by the latter, and the
three statements of the markers' spelling, which only the former accepts, would otherwise pay for
the decisions on their opened statements first. -/
def decisionTheorems : List (Nat × Name) :=
  [(1, ``StatementNormalisation.numberedInstanceSound), (4, ``StatementNormalisation.statementSoundOfAbsorbed),
    (2, ``StatementNormalisation.statementSoundOfNormalised), (3, ``StatementNormalisation.statementSoundOfContracted),
    (6, ``StatementNormalisation.statementSoundOfNormalisedLong),
    (7, ``StatementNormalisation.statementSoundOfReached),
    (5, ``StatementNormalisation.statementSoundOfOpenedAccepted)]

/-- The first of `decisions` whose theorem `name` of type `type`, its soundness theorem applied to
`Eq.refl true` (`decidedProof`), the kernel accepts on `environment`, with the environment the kernel
returns, which holds the theorem: each decision is evaluated once, by the kernel's check of its
theorem, and a decision that does not accept the statement is one whose theorem the kernel rejects
with an application type mismatch, `Eq.refl true` given where the decision's `= true` is asked.
Another error of the kernel is thrown. The kernel evaluated the decisions to choose one before
(`Lean.Kernel.whnf` of a function that tried them in order) and then the chosen one again when it
added the theorem: measured 2026-11-19, decision 4 took
about 42 s over the 89 native-route statements, each evaluation. -/
def kernelAccepted (environment : Environment) (options : Options) (name statement : Name) (type : Expr) :
    List (Nat × Name) → Except String (Option (Nat × Environment))
  | [] => .ok none
  | (number, soundness) :: rest =>
      let declaration := Declaration.thmDecl { name, levelParams := [], type, value := decidedProof soundness statement }
      match environment.addDeclCore (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
          declaration none with
      | .ok checked => .ok (some (number, checked))
      | .error (.appTypeMismatch ..) => kernelAccepted environment options name statement type rest
      | .error (.other message) => .error s!"the kernel failed on decision {number} of {statement}: {message}"
      | .error .deterministicTimeout => .error s!"the kernel ran out of heartbeats on decision {number} of {statement}"
      | .error .deepRecursion => .error s!"the kernel reached its recursion limit on decision {number} of {statement}"
      | .error _ => .error s!"the kernel rejected the theorem of decision {number} of {statement} otherwise than by its evaluation"

/-- Takes `checked`, the environment the kernel returned holding the theorem `name`, as the
environment, and adds the docstring `documentation`. -/
def theoremChecked (name : Name) (checked : Environment) (documentation : String) : CommandElabM Unit := do
  setEnv checked
  addDocStringCore name documentation

@[command_elab lemmaSoundness]
def elaborateLemmaSoundness : CommandElab
  | `(lemma_soundness $name:ident of $statement:ident $documentation:docComment) => do
      let statementName ← resolveGlobalConstNoOverload statement
      let declared := (← getCurrNamespace) ++ name.getId
      let proofName := handWrittenProofName name.getId
      let type := soundnessType statementName
      let common := (← getDocStringText documentation).trimAscii.toString ++ "\n\n"
      let normalisationFuel := StatementNormalisation.normalisationFuel
      let contractionFuel := StatementNormalisation.contractionFuel
      let longNormalisationFuel := StatementNormalisation.longNormalisationFuel
      let absorptionDevelopments := StatementNormalisation.absorptionDevelopments
      match (← getEnv).find? proofName with
      | some proof =>
          let derivable ← liftTermElabM <| Meta.isDefEq proof.type (derivabilityType statementName)
          if derivable then
            theoremAdded declared type (soundnessOfDerivable statementName proofName) <| common ++
              s!"A theorem: the hand-written proof `{proofName}` (module `LibraryLemmaProofs`), \
                whose type the elaborator finds definitionally equal to the derivability of this \
                statement, made its soundness by `EndToEnd.equationSoundOfDerivable`."
          else
            let sound ← liftTermElabM <| Meta.isDefEq proof.type type
            unless sound do
              throwError "the hand-written proof {proofName} states{indentExpr proof.type}\n\
                which is definitionally equal neither to the derivability nor to the soundness \
                of the exported statement {statementName}: its copy of the statement no longer \
                matches the export"
            theoremAdded declared type (mkConst proofName) <| common ++
              s!"A theorem: the hand-written proof `{proofName}` (module `LibraryLemmaProofs`), \
                whose type the elaborator finds definitionally equal to the soundness of this \
                statement, `EndToEnd.EquationSound`: the two sides are contextually equivalent \
                under every valuation, proved without a derivation of ⊢_\{λ-lattice-η}."
      | none =>
      let accepted ← match kernelAccepted (← getEnv) (← getOptions) declared statementName type decisionTheorems with
        | .ok accepted => pure accepted
        | .error message => throwError message
      match accepted with
      | some (1, checked) =>
        theoremChecked declared checked <| common ++
          "A theorem: the statement is an instance of one of the numbered equations (1) to (6) and (8) to (10) \
            (`EndToEnd.numberedEquation`), its operands read off its left side, as the kernel \
            evaluates (`StatementNormalisation.numberedInstance`), and every such instance is \
            sound (`StatementNormalisation.numberedInstanceSound`, through \
            `EndToEnd.numberedEquationSound`)."
      | some (2, checked) =>
        theoremChecked declared checked <|
          common ++
          s!"A theorem: the kernel evaluates the normal form by weak head reduction and then the \
            subterms and finds that it brings the two sides, the metavariables abstracted, to one \
            term within {normalisationFuel} contractions on each side (`StatementNormalisation.statementNormalised`), which \
            `StatementNormalisation.statementSoundOfNormalised` makes the soundness."
      | some (3, checked) =>
        theoremChecked declared checked <|
          common ++
          s!"A theorem: the kernel evaluates leftmost outermost contraction and finds that the \
            two sides, the metavariables abstracted, reach a common term within \
            {contractionFuel} contractions on each side \
            (`StatementNormalisation.statementContracted`), which \
            `StatementNormalisation.statementSoundOfContracted` makes the soundness."
      | some (4, checked) =>
        theoremChecked declared checked <|
          common ++
          s!"A theorem: the kernel evaluates the decision of absorbed members and finds that the \
            two sides, after the same number of developments, at most {absorptionDevelopments}, \
            have one simplification by T3, `top` + M = M, the idempotence of the parallel and of \
            the choice, absorption, the absorption of a typed version and of a filtered \
            application, and the η rule \
            (`StatementNormalisation.statementAbsorbed`), which \
            `StatementNormalisation.statementSoundOfAbsorbed` makes the soundness."
      | some (5, checked) =>
        theoremChecked declared checked <|
          common ++
          "A theorem: the kernel evaluates the decisions on the statement with the constants both \
            its sides hold read as variables, which no decision unfolds, and finds that the \
            normaliser, contraction or the decision of absorbed members accepts it \
            (`StatementNormalisation.statementOpenedAccepted`), which \
            `StatementNormalisation.statementSoundOfOpenedAccepted` makes the soundness."
      | some (6, checked) =>
        theoremChecked declared checked <|
          common ++
          s!"A theorem: the kernel evaluates the normal form by weak head reduction and then the \
            subterms and finds that it brings the two sides, the metavariables abstracted, to one \
            term within {longNormalisationFuel} contractions on each side \
            (`StatementNormalisation.statementNormalisedLong`), which \
            `StatementNormalisation.statementSoundOfNormalisedLong` makes the soundness."
      | some (7, checked) =>
        theoremChecked declared checked <|
          common ++
          s!"A theorem: the kernel evaluates leftmost outermost contraction and finds that it \
            takes one side, the metavariables abstracted, to the other within \
            {StatementNormalisation.reachFuel} contractions \
            (`StatementNormalisation.statementReached`), which \
            `StatementNormalisation.statementSoundOfReached` makes the soundness."
      | none =>
        axiomAdded declared type <| common ++
          s!"FIXME (2026-10-07): a named axiom, since Lean does not prove it yet. There is no \
            hand-written proof `{proofName}` (module `LibraryLemmaProofs`); the statement is no \
            instance of a numbered equation (1) to (6) and (8) to (10) \
            (`StatementNormalisation.numberedInstance`); the normal form does not bring the two \
            sides, the metavariables abstracted, to one term within {normalisationFuel} \
            contractions on each side (`StatementNormalisation.statementNormalised`); \
            leftmost outermost contraction does not bring them to a common term within \
            {contractionFuel} contractions on each side \
            (`StatementNormalisation.statementContracted`); and the decision of absorbed members \
            does not accept them within {absorptionDevelopments} developments \
            (`StatementNormalisation.statementAbsorbed`), as the kernel evaluates."
      | some (other, _) => throwError "decision {other} of {statementName} has no theorem"
  | _ => throwUnsupportedSyntax

end LambdaJit.LemmaSoundness
