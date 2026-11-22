import LambdaJit.Article

/-!
# Fixture articles for the article reader

Hand-written articles in the encoding of design decision D7
(`lean/README.md`, "Design decisions"): the type operator `LambdaJit.term`, and the
constants `LambdaJit.apply` and `LambdaJit.choice` of type `term → term → term`. Each article is
assembled from line fragments, and each
outcome is checked on every build by `#guard_msgs`: an accepted article prints its imports and
exports, a rejected one its reason, and the build fails when the printed text differs from the
text recorded above the check. Applications are printed with parentheses, `((f x) y)` for
`f x y`.

The accepted articles exercise `refl`; `axiom` and an instance by `subst`; congruence by
`appThm`; and a chain by `trans` and `sym`, kept in the dictionary by `def` and taken back by
`remove`. Their imports are the numbered equations (1), M + N = N + M, and (2),
(M + N) + P = M + (N + P). The rejected ones carry a command of the format outside the fragment, a misspelled
command, an ill-typed `appTerm`, a `thm` whose claim differs from its theorem, an `axiom` command
with a hypothesis, an `axiom` command whose conclusion is no equation, a `trans` whose middle
terms differ, an ill-typed `subst`, a stack that does not hold what `sym` pops, and a missing or
wrong version header.
-/

namespace LambdaJit.ArticleFixtures

open LambdaJit.Article

/-! ## Line fragments -/

/-- The lines that push the type `LambdaJit.term`. -/
def termType : List String := ["\"LambdaJit.term\"", "typeOp", "nil", "opType"]

/-- The lines that push the type `bool`. -/
def booleanType : List String := ["\"bool\"", "typeOp", "nil", "opType"]

/-- The lines that push the function type from the type `domain` pushes to the type `range`
pushes. -/
def arrowType (domain range : List String) : List String :=
  ["\"->\"", "typeOp"] ++ domain ++ range ++ ["nil", "cons", "cons", "opType"]

/-- The lines that push the variable named `name` of type `LambdaJit.term`, as a variable. -/
def variableObject (name : String) : List String := [s!"\"{name}\""] ++ termType ++ ["var"]

/-- The lines that push the variable named `name` of type `LambdaJit.term`, as a term. -/
def variableTerm (name : String) : List String := variableObject name ++ ["varTerm"]

/-- The lines that push the constant named `name` at the type that `type` pushes. -/
def constantTerm (name : String) (type : List String) : List String :=
  [s!"\"{name}\"", "const"] ++ type ++ ["constTerm"]

/-- The lines that push the application of the term `function` pushes to the term `argument`
pushes. -/
def application (function argument : List String) : List String :=
  function ++ argument ++ ["appTerm"]

/-- The lines that push `term → term → term`, the type of `LambdaJit.apply` and
`LambdaJit.choice`. -/
def binaryType : List String := arrowType termType (arrowType termType termType)

/-- The lines that push `LambdaJit.apply function argument`. -/
def applyTerm (function argument : List String) : List String :=
  application (application (constantTerm "LambdaJit.apply" binaryType) function) argument

/-- The lines that push `LambdaJit.choice left right`. -/
def choiceTerm (left right : List String) : List String :=
  application (application (constantTerm "LambdaJit.choice" binaryType) left) right

/-- The lines that push the equation `left = right` between terms of type `LambdaJit.term`. -/
def equationTerm (left right : List String) : List String :=
  application
    (application (constantTerm "=" (arrowType termType (arrowType termType booleanType))) left)
    right

/-- The lines that push the substitution of a `subst` command with no type entries and the given
term entries, each the lines that push a variable and the lines that push its replacement: the
list of the two lists, each built by `nil` and `cons`. -/
def termSubstitution (entries : List (List String × List String)) : List String :=
  ["nil"] ++
    (entries.map fun (variableLines, replacementLines) =>
      variableLines ++ replacementLines ++ ["nil", "cons", "cons"]).flatten ++
    ["nil"] ++ entries.map (fun _ => "cons") ++ ["nil", "cons", "cons"]

/-- The text of an article: the lines `6` and `version`, then `body`, each line ended by a
newline. -/
def article (body : List String) : String :=
  String.join ((["6", "version"] ++ body).map (· ++ "\n"))

/-! ## Printing a result -/

/-- A name with its components joined by dots, escapes not reproduced. -/
def renderName (name : Name) : String :=
  String.intercalate "." (name.namespaceComponents ++ [name.localName])

/-- A term with its variables and constants by name and every application in parentheses. -/
def renderTerm : Term → String
  | .termVariable name _ => renderName name
  | .constant name _ => renderName name
  | .application function argument => s!"({renderTerm function} {renderTerm argument})"

/-- A theorem as its hypotheses, `⊦`, and its conclusion, an equation as `left = right`. -/
def renderSequent (sequent : Sequent) : String :=
  let conclusion :=
    match sequent.conclusion.equationSides? with
    | some (_, left, right) => s!"{renderTerm left} = {renderTerm right}"
    | none => renderTerm sequent.conclusion
  String.intercalate ", " (sequent.hypotheses.map renderTerm) ++ s!"⊦ {conclusion}"

/-- The outcome of reading an article: its imports and exports when accepted, its reason when
rejected. -/
def describe : Except String Theory → String
  | .ok theory =>
      String.intercalate "\n"
        (["accepted", "imports:"] ++ theory.assumptions.map (fun sequent => "  " ++ renderSequent sequent) ++
          ["exports:"] ++ theory.theorems.map (fun sequent => "  " ++ renderSequent sequent))
  | .error reason => s!"rejected: {reason}"

/-! ## Accepted articles -/

/-- `refl`: proves and exports `⊦ x = x`; its third line is a comment. -/
def reflexivityArticle : String :=
  article <| ["# x = x by refl"] ++ variableTerm "x" ++ ["refl", "nil"] ++
    equationTerm (variableTerm "x") (variableTerm "x") ++ ["thm"]

/-- `axiom` and `subst`: imports (1), the commutativity of choice, `⊦ choice x y = choice y x`,
instantiates `x` to `apply u v` and `y` to `z`, and exports
`⊦ choice (apply u v) z = choice z (apply u v)`. -/
def substitutionArticle : String :=
  article <|
    termSubstitution [(variableObject "x", applyTerm (variableTerm "u") (variableTerm "v")),
      (variableObject "y", variableTerm "z")] ++
    ["nil"] ++
    equationTerm (choiceTerm (variableTerm "x") (variableTerm "y"))
      (choiceTerm (variableTerm "y") (variableTerm "x")) ++
    ["axiom", "subst", "nil"] ++
    equationTerm (choiceTerm (applyTerm (variableTerm "u") (variableTerm "v")) (variableTerm "z"))
      (choiceTerm (variableTerm "z") (applyTerm (variableTerm "u") (variableTerm "v"))) ++
    ["thm"]

/-- `appThm`: imports (1) `⊦ choice x z = choice z x` and, with `refl` of `apply y`, derives and
exports `⊦ apply y (choice x z) = apply y (choice z x)`. -/
def congruenceArticle : String :=
  article <|
    application (constantTerm "LambdaJit.apply" binaryType) (variableTerm "y") ++ ["refl", "nil"] ++
    equationTerm (choiceTerm (variableTerm "x") (variableTerm "z"))
      (choiceTerm (variableTerm "z") (variableTerm "x")) ++
    ["axiom", "appThm", "nil"] ++
    equationTerm (applyTerm (variableTerm "y") (choiceTerm (variableTerm "x") (variableTerm "z")))
      (applyTerm (variableTerm "y") (choiceTerm (variableTerm "z") (variableTerm "x"))) ++
    ["thm"]

/-- `trans` and `sym`: imports (2), `⊦ choice (choice x y) z = choice x (choice y z)`, and takes its
`sym`; imports (1) and instantiates it by `subst`, `x` to `choice x y` and `y` to `z`; derives
`⊦ choice x (choice y z) = choice z (choice x y)` by `trans`, keeps it under key 1 with `def` and
exports it, takes it back with `remove`, and exports its `sym`. -/
def chainArticle : String :=
  article <|
    ["nil"] ++
    equationTerm (choiceTerm (choiceTerm (variableTerm "x") (variableTerm "y")) (variableTerm "z"))
      (choiceTerm (variableTerm "x") (choiceTerm (variableTerm "y") (variableTerm "z"))) ++
    ["axiom", "sym"] ++
    termSubstitution [(variableObject "x", choiceTerm (variableTerm "x") (variableTerm "y")),
      (variableObject "y", variableTerm "z")] ++
    ["nil"] ++
    equationTerm (choiceTerm (variableTerm "x") (variableTerm "y"))
      (choiceTerm (variableTerm "y") (variableTerm "x")) ++
    ["axiom", "subst", "trans", "1", "def", "nil"] ++
    equationTerm (choiceTerm (variableTerm "x") (choiceTerm (variableTerm "y") (variableTerm "z")))
      (choiceTerm (variableTerm "z") (choiceTerm (variableTerm "x") (variableTerm "y"))) ++
    ["thm", "1", "remove", "sym", "nil"] ++
    equationTerm (choiceTerm (variableTerm "z") (choiceTerm (variableTerm "x") (variableTerm "y")))
      (choiceTerm (variableTerm "x") (choiceTerm (variableTerm "y") (variableTerm "z"))) ++
    ["thm"]

/--
info: accepted
imports:
exports:
  ⊦ x = x
-/
#guard_msgs in
#eval IO.println (describe (readArticle reflexivityArticle))

/--
info: accepted
imports:
  ⊦ ((LambdaJit.choice x) y) = ((LambdaJit.choice y) x)
exports:
  ⊦ ((LambdaJit.choice ((LambdaJit.apply u) v)) z) = ((LambdaJit.choice z) ((LambdaJit.apply u) v))
-/
#guard_msgs in
#eval IO.println (describe (readArticle substitutionArticle))

/--
info: accepted
imports:
  ⊦ ((LambdaJit.choice x) z) = ((LambdaJit.choice z) x)
exports:
  ⊦ ((LambdaJit.apply y) ((LambdaJit.choice x) z)) = ((LambdaJit.apply y) ((LambdaJit.choice z) x))
-/
#guard_msgs in
#eval IO.println (describe (readArticle congruenceArticle))

/--
info: accepted
imports:
  ⊦ ((LambdaJit.choice ((LambdaJit.choice x) y)) z) = ((LambdaJit.choice x) ((LambdaJit.choice y) z))
  ⊦ ((LambdaJit.choice x) y) = ((LambdaJit.choice y) x)
exports:
  ⊦ ((LambdaJit.choice x) ((LambdaJit.choice y) z)) = ((LambdaJit.choice z) ((LambdaJit.choice x) y))
  ⊦ ((LambdaJit.choice z) ((LambdaJit.choice x) y)) = ((LambdaJit.choice x) ((LambdaJit.choice y) z))
-/
#guard_msgs in
#eval IO.println (describe (readArticle chainArticle))

/-! ## Rejected articles -/

/-- `assume`, a command of the format outside the fragment. -/
def unsupportedCommandArticle : String :=
  article <| equationTerm (variableTerm "x") (variableTerm "x") ++ ["assume"]

/-- `appTerm` with the function `x` of type `LambdaJit.term`, which is no function type. -/
def illTypedApplicationArticle : String :=
  article <| application (variableTerm "x") (variableTerm "y")

/-- `thm` claiming `⊦ y = y` for the theorem `⊦ x = x`. -/
def mismatchedClaimArticle : String :=
  article <| variableTerm "x" ++ ["refl", "nil"] ++
    equationTerm (variableTerm "y") (variableTerm "y") ++ ["thm"]

/-- An `axiom` command with the hypothesis `x = x`. -/
def hypothesisArticle : String :=
  article <| equationTerm (variableTerm "x") (variableTerm "x") ++ ["nil", "cons"] ++
    equationTerm (variableTerm "x") (variableTerm "x") ++ ["axiom"]

/-- `trans` of `⊦ x = x` and `⊦ y = y`, whose middle terms differ. -/
def mismatchedTransitivityArticle : String :=
  article <| variableTerm "x" ++ ["refl"] ++ variableTerm "y" ++ ["refl", "trans"]

/-- `subst` replacing the variable `x` of type `LambdaJit.term` by the term `x = x` of type
`bool`. -/
def illTypedSubstitutionArticle : String :=
  article <|
    termSubstitution [(variableObject "x", equationTerm (variableTerm "x") (variableTerm "x"))] ++
    variableTerm "x" ++ ["refl", "subst"]

/-- The commands of `reflexivityArticle` without the version header: an article of version 5. -/
def missingVersionText : String :=
  String.join ((variableTerm "x" ++ ["refl", "pop"]).map (· ++ "\n"))

/-- `refll`, a misspelled command. -/
def misspelledCommandArticle : String :=
  article <| variableTerm "x" ++ ["refll"]

/-- An `axiom` command whose conclusion, the variable `p` of type `bool`, is no equation. -/
def nonEquationArticle : String :=
  article <| ["nil", "\"p\""] ++ booleanType ++ ["var", "varTerm", "axiom"]

/-- `sym` on a stack whose top is a term, not a theorem. -/
def malformedStackArticle : String :=
  article <| variableTerm "x" ++ ["sym"]

/-- A version header that says 5. -/
def wrongVersionText : String :=
  String.join ((["5", "version"] ++ variableTerm "x" ++ ["refl", "pop"]).map (· ++ "\n"))

/--
info: rejected: line 46: unsupported command 'assume'
-/
#guard_msgs in
#eval IO.println (describe (readArticle unsupportedCommandArticle))

/--
info: rejected: line 17: appTerm: the function's type is not an arrow from the argument's type
-/
#guard_msgs in
#eval IO.println (describe (readArticle illTypedApplicationArticle))

/--
info: rejected: line 55: thm: the claimed conclusion differs from the theorem's
-/
#guard_msgs in
#eval IO.println (describe (readArticle mismatchedClaimArticle))

/--
info: rejected: line 91: axiom: this reader accepts only an empty hypothesis list
-/
#guard_msgs in
#eval IO.println (describe (readArticle hypothesisArticle))

/--
info: rejected: line 19: trans: the middle terms differ
-/
#guard_msgs in
#eval IO.println (describe (readArticle mismatchedTransitivityArticle))

/--
info: rejected: line 69: subst: a replacement term does not have the type of its variable
-/
#guard_msgs in
#eval IO.println (describe (readArticle illTypedSubstitutionArticle))

/--
info: rejected: the article does not begin with the commands 6 and version (it would be version 5)
-/
#guard_msgs in
#eval IO.println (describe (readArticle missingVersionText))

/--
info: rejected: line 2: this reader reads only version 6 of the format, not 5
-/
#guard_msgs in
#eval IO.println (describe (readArticle wrongVersionText))

/--
info: rejected: line 10: unsupported command 'refll'
-/
#guard_msgs in
#eval IO.println (describe (readArticle misspelledCommandArticle))

/--
info: rejected: line 11: axiom: the conclusion is not an equation
-/
#guard_msgs in
#eval IO.println (describe (readArticle nonEquationArticle))

/--
info: rejected: line 10: sym: the stack does not begin with a theorem
-/
#guard_msgs in
#eval IO.println (describe (readArticle malformedStackArticle))

/-! ## Names and numbers -/

#guard parseName "\"LambdaJit.term\"" = some ⟨["LambdaJit"], "term"⟩
#guard parseName "\"a\\.b.c\"" = some ⟨["a.b"], "c"⟩
#guard parseName "\"a\\\\b\"" = some ⟨[], "a\\b"⟩
#guard parseName "\"\"" = some ⟨[], ""⟩
#guard parseName "\"a\\b\"" = none
#guard parseName "\"a\"b\"" = none
#guard parseName "\"a\\\"" = none
#guard parseNumber "0" = some 0
#guard parseNumber "-12" = some (-12)
#guard parseNumber "007" = none
#guard parseNumber "-0" = none
#guard parseNumber "+1" = none

end LambdaJit.ArticleFixtures
