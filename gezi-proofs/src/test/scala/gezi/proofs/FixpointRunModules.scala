package gezi.proofs

import gezi.standardlibrary.LeanFiniteTerms
import gezi.ir.Configured
import gezi.ir.NoFacts

/** A fixpoint run of `gezi/tests/opentheory_article.plt`: a program over
  * the library's names and the round of the native route that writes its
  * article: `type_check`, the HM baseline's type check, or `beta`, the beta
  * rule on the program's closures. `programText` is the program as the
  * module FixpointRunFixtures documents it, the deleted Prolog test's
  * surface as SWI-Prolog writes it with `~W` and `numbervars(true),
  * quoted(true), spacing(next_argument)` after `numbervars/3`: its variables
  * A, B, ... in the order they occur, `^` at 200 xfy and `@` at 100 yfx,
  * with no space around an operator. The texts are those the deleted
  * printer of the Prolog reader gave, taken from the module it generated
  * (`git show
  * 81b99e659:gezi/proofs/src/test/scala/gezi/proofs/FixpointRunModules.scala`,
  * `programText`).
  */
final case class FixpointRun(name: String, round: String, programText: String):

  /** The base name of the run's expected article: the program and the round
    * joined by `_`, since two programs run under both rounds.
    */
  def base: String = s"${name}_$round"

/** The sides of a run as module FixpointRunSides holds them: their finite
  * terms, named after the run's expected article.
  */
final case class EncodedRun(base: String, inputFinite: Configured[NoFacts.type], outputFinite: Configured[NoFacts.type])

/** A run with the lemmas whose statements its expected article imports, by
  * name in the order of the index.
  */
final case class FixpointFixture(run: FixpointRun, lemmas: Vector[String])

/** The Lean modules of the fixpoint runs, the port of the section "the Lean
  * modules of the fixpoint runs" of `gezi/tests/opentheory_article.plt`.
  *
  * The package's module FixpointRunFixtures takes the expected article of
  * every fixpoint run through the end-to-end theorem
  * (EndToEnd.endToEndOfChecked) with the statements of the lemmas it
  * imports, which the package's module NativeRouteLibraryStatements exports
  * from the native route's library and proves sound
  * (`LeanStatementsNativeRouteTest`), and states it on the readbacks of the
  * run's input and output (Encoding.endToEndEncodedOfChecked); the kernel
  * checks there that the article's exported equation is the pair of the
  * encodings of the two IR terms (`Encoding.encode`), which the module
  * FixpointRunSides holds as finite terms, named after the run's expected
  * article in lower camel case with `Input` and `Output` appended. The module
  * FixpointRunFixturesAxioms prints the axioms of the theorems of
  * FixpointRunFixtures. The three modules are generated; their texts name
  * the functions of this object that write them.
  *
  * `gezi.strategies.OpentheoryArticleFixpointRunsTest` makes the runs,
  * checks that each writes its expected article, and that the three modules
  * are their regeneration; with the environment variable
  * `GEZI_WRITE_FIXPOINT_RUNS` set, it writes them first. It replaces the test
  * deleted when the library became files reached by paths (`git show
  * 2908bffd5:lambda_jit/strategies/src/test/scala/lambdajit/strategies/OpentheoryArticleFixpointRunsTest.scala`):
  * a run's library terms are members of a fixture file, its program HOAS over
  * them, its knowledge `libraryFile`, and the lemmas of a fixture are those
  * its article's derivation names (`RewriteTrace.lemmas`), no longer read back
  * from the article.
  */
object FixpointRunModules:

  private given NoFacts.type = NoFacts

  /** The knowledge of the runs of the baseline's search strategy, the one
    * field of the file: the Prolog backend's preset, through which native
    * typing is enabled with its backend, as one preset, with the beta rule on a program's closures and
    * the erasure of the occurrence markers the preset declares.
    */
  val libraryFile: String = "tests/library_fixtures/prolog_backend_closure_application.lambdalattice"

  /** The runs, in the order of `fixpoint_run/3`. */
  val runs: Vector[FixpointRun] = Vector(
    FixpointRun("successor_zero", "type_check", "successor@zero"),
    FixpointRun("identity_zero", "type_check", "identity@zero"),
    FixpointRun("compose_redex", "type_check", "compose@successor@successor@zero"),
    FixpointRun("identity_closure", "type_check", "(A^A)@zero"),
    FixpointRun("twice_closure", "type_check", "(A^B^A@(A@B))@successor@zero"),
    FixpointRun("identity_closure", "beta", "(A^A)@zero"),
    FixpointRun("twice_closure", "beta", "(A^B^A@(A@B))@successor@zero")
  )

  /** The key of the tests' round whose knowledge the round's strategy takes
    * (`gezi.strategies.StrategyTesting.round`): the type check is the
    * Prolog backend's preset's, the beta rule's round closure_application.
    */
  def roundKey(round: String): String = round match
    case "type_check" => "prolog_backend_type_check"
    case "beta"       => "closure_application"
    case other        => throw IllegalArgumentException(s"no round $other")

  /** The budget of the round's strategy, in instances (`fixpoint_strategy/2`).
    * The budgets stay far above the runs: measured on the Prolog strategy
    * 2026-10-29, the type checks reach their fixed points at 36 to 150
    * instances (compose_redex the largest), the beta rounds at 1.
    */
  def roundBudget(round: String): Int = round match
    case "type_check" => 2000
    case "beta"       => 500
    case other        => throw IllegalArgumentException(s"no round $other")

  /** The module FixpointRunSides of the runs. */
  def sidesText(encoded: Vector[EncodedRun]): String =
    "import LambdaJit.Ir\n\n" +
      // A finite term spells every handle out, so a marker in its spelling as a
      // tag, `λx. (λ"$k". λv. v) "$k" x`, carries its key's bits as nested
      // applications.
      // MEASURED 2026-11-19 with the runs' sides of that spelling: Lean's default
      // maxRecDepth, 512, stops at eight of the definitions ("maximum recursion depth
      // has been reached"); at 1024 the module elaborates, in 92 s on two cores.
      "set_option maxRecDepth 1024\n\n" +
      "/-!\n" +
      "# The sides of the fixpoint runs\n\n" +
      "Generated by `FixpointRunModules.sidesText` of\n" +
      "`gezi/proofs/src/test/scala/gezi/proofs/FixpointRunModules.scala` from the runs of\n" +
      "`FixpointRunModules.runs`; not edited. For every run, its input and its output, the IR terms the\n" +
      "writer was asked to join, as finite terms: every handle replaced by the finite term of its layer,\n" +
      "named after the run's expected article. The test\n" +
      "`OpentheoryArticleFixpointRunsTest.theRunsWriteTheirExpectedArticlesAndTheirLeanModules` checks that\n" +
      "regenerating this module from the runs gives it byte for byte. The module `FixpointRunFixtures`\n" +
      "states the end-to-end theorem on the readbacks of these terms.\n" +
      "-/\n\n" +
      "namespace LambdaJit.FixpointRunSides\n\n" +
      encoded.map { run =>
        val lowerCamelName = LeanFiniteTerms.lowerCamelCase(run.base)
        finiteTermDefinition(run.base, lowerCamelName, "Input", "input", run.inputFinite) +
          finiteTermDefinition(run.base, lowerCamelName, "Output", "output", run.outputFinite)
      }.mkString +
      "end LambdaJit.FixpointRunSides\n"

  private def finiteTermDefinition(
      base: String,
      lowerCamelName: String,
      suffix: String,
      which: String,
      term: Configured[NoFacts.type]
  ): String =
    val tokens = LeanFiniteTerms.finiteLeanText(term).split(" ", -1).toList
    s"/-- The $which of the run of `$base.art`. -/\n" +
      s"def $lowerCamelName$suffix : FiniteTerm :=\n" +
      ProofTestFiles.tokensFilled(tokens, "  ", Vector.empty).map(_ + "\n").mkString +
      "\n"

  /** The heartbeats the kernel's check of one article (`…LinesChecked`,
    * `decide +kernel`) may take, above Lean's default of 200,000. MEASURED
    * 2026-11-17 (`OpentheoryArticleFixpointRunsTest`, `lake build`): the
    * default was exceeded (`(kernel) deterministic timeout`) by the article
    * of compose_redex_type_check, 10,030 lines once regenerated under the
    * Prolog backend's preset rounds (8,247 before); 300,000 passes every
    * article. The kernel's work grows with the article, an expected cost of
    * checking it.
    */
  val kernelCheckHeartbeats: Int = 300000

  /** The module FixpointRunFixtures of the fixtures.
    *
    * FIXME (https://github.com/Atry/private-overlay/issues/1561, D6, "定理与一次运行的源程序相连"):
    * no theorem is linked to the source program of a run. The theorems this
    * module states stop at the readbacks of the run's input and output, the
    * IR terms of module FixpointRunSides (`…Readbacks`), and that those finite
    * terms are what the front end made of the run's program rests on this
    * Scala test alone. Missing: for each run, a theorem that the readback of
    * its input is δ of its source program (link (i), Lean's
    * `Defunctionalization.readbackThunkInstruction`), joined to `…Readbacks`
    * so that the theorem reads δ(program) ≃_O readback(output). Two things
    * stand between: the source program is not in Lean (the run's program is
    * HOAS over library terms read off a fixture file as closed instructions,
    * `Term.Closed`, whose de Bruijn terms the run does not keep;
    * `StrategyTesting.programInput`), and the input is the program with its
    * occurrences tagged (`Occurrences.tagged`), whose markers are identities
    * by the β rule only, so the input reads back to δ(program) up to the
    * lemmas of occurrence_erasure, not syntactically. An entry's articles
    * (`GenericEntry.evidenceWritten`) have the same gap and no Lean module at
    * all. Candidate fixes: the run carries its source program, the library
    * terms' de Bruijn terms and the markers into a generated Lean module, as
    * `Defunctionalization.Program` with constants, and the kernel checks that
    * `thunkInstruction` of the tagged program is the input's finite term,
    * a theorem then closing the gap from the tagged to the untagged program
    * by the soundness of occurrence_erasure's statements; or Lean's
    * `thunkInstruction` compiled and run as the front end, so that the input
    * is its output by construction (the FIXME of `Defunctionalization.lean`,
    * "Agreement with the Prolog").
    */
  def fixturesText(fixtures: Vector[FixpointFixture]): String =
    "import LambdaJit.Encoding\n" +
      "import LambdaJit.ArticleLines\n" +
      "import LambdaJit.ExpectedArticles\n" +
      "import LambdaJit.NativeRouteLibraryStatements\n" +
      "import LambdaJit.FixpointRunSides\n\n" +
      "/-!\n" +
      "# The end-to-end theorem on the articles of the fixpoint runs\n\n" +
      "Generated by `FixpointRunModules.fixturesText` of\n" +
      "`gezi/proofs/src/test/scala/gezi/proofs/FixpointRunModules.scala` from the expected\n" +
      "articles of the runs of `FixpointRunModules.runs` and the index of their library; not edited. The\n" +
      "test `OpentheoryArticleFixpointRunsTest.theRunsWriteTheirExpectedArticlesAndTheirLeanModules`\n" +
      "checks that regenerating this module gives it byte for byte. A run is one round of the baseline's\n" +
      "search strategy `fixpoint_egraph` on a program over the knowledge of\n" +
      s"`gezi/$libraryFile`:\n" +
      "the native route's type check, or the beta rule on the program's closures. The writer\n" +
      "`gezi/proofs/src/main/scala/gezi/proofs/OpentheoryArticle.scala` writes its article\n" +
      "through the schedule's round with an article (`Round(Strategy, Some(File))` of\n" +
      "`gezi/strategies/src/main/scala/gezi/strategies/Schedule.scala`); the article exports\n" +
      "the one equation input = output and is kept as\n" +
      "`gezi/tests/opentheory_article_expected/<run>.art`, its lines in module `ExpectedArticles`.\n" +
      "For each article:\n\n" +
      "- `…Text`: its text, its lines each followed by a newline;\n" +
      "- `…Equation`: the one equation it exports, as the reader reads it;\n" +
      "- `…Lemmas`: the statements of the lemmas it imports, in the order of the index, from the export\n" +
      "  of the native route's library (module `NativeRouteLibraryStatements`), and `…LemmasSound`\n" +
      "  their soundness, by the soundness declarations of that module, each a theorem;\n" +
      "- `…LinesChecked`: no line holds a newline, the reader accepts the lines, every equation of the\n" +
      "  import set is a numbered equation, an equation of the defunctionalized β rule or η rule of a\n" +
      "  thunk constant, or one of those lemma statements, the article exports one equation, both of its\n" +
      "  sides have a reading (`checkedAndRead`), and its sides are the encodings of the run's input and\n" +
      "  output (`sidesEncoded`), the finite terms of module `FixpointRunSides`. The kernel evaluates it\n" +
      "  (`decide +kernel`), reading the article once (`checkedReadAndEncoded`); `…Checked`,\n" +
      "  `…LeftRead`, `…RightRead`, `…InputEncoded` and `…OutputEncoded` are its parts on the text,\n" +
      "  which the reader reads as it reads the lines (`ArticleLines.readArticleOfLines`);\n" +
      "- `…Sound`: the exported equation is sound (`EndToEnd.endToEndOfChecked`);\n" +
      "- `…ContextualEquivalence`: both sides read as terms of the calculus (`Interpretation.read`),\n" +
      "  and the two readings are contextually equivalent, ≃_O of DdLP96's Definition 14\n" +
      "  (`EndToEnd.contextualEquivalenceOfRead`);\n" +
      "- `…Readbacks`: the readbacks of the run's input and output are defined and contextually\n" +
      "  equivalent (`Encoding.endToEndEncodedOfChecked`).\n\n" +
      "Module `FixpointRunFixturesAxioms` prints the axioms of these theorems. They stop at the readbacks\n" +
      "of the run's IR terms: that the finite terms of module `FixpointRunSides` are those terms rests on\n" +
      "the Scala test that checks that module, and no module carries the theorem to the source\n" +
      "program (link (i) of D6).\n" +
      measurement.map(_ + "\n").mkString +
      "-/\n\n" +
      "namespace LambdaJit.FixpointRunFixtures\n\n" +
      "open LambdaJit.EndToEnd LambdaJit.Interpretation LambdaJit.ExpectedArticles\n" +
      "open LambdaJit.ContextualPreorder (ContextualEquivalence)\n\n" +
      helpers +
      fixtures.map(fixtureText).mkString +
      "end LambdaJit.FixpointRunFixtures\n"

  /** The paragraph of the module's documentation that records the measured
    * cost of its build.
    */
  private val measurement: Vector[String] = Vector(
    "",
    "Measured 2026-11-21 with Lean 4.35.0, in a cold `lake build` of the package on 4 CPUs (nice 10)",
    "under a machine load of 8.3 to 13.3: this module took 216 s, and the largest resident set of the",
    "build's processes, which GNU time reports, was 7.2 GB (7,220,524 kB). The kernel's check of an",
    "article is most of it: built alone, each in a module of its own (4c3d7d0c9, reverted), the",
    "articles of the markers' keys, before the markers' members took the `$` prefix, took 74 s and 8.0 GB (compose_redex_type_check), 59 s",
    "and 6.9 GB (twice_closure_type_check) and 49 s and 5.1 GB (successor_zero_type_check). The",
    "articles are of 4304 to 12682 lines of at most 41 characters."
  )

  private val helpers: String =
    "/-- The one equation that a reading `result` of an article exports, or x = x, x a variable, when\n" +
      "the reader rejected the article or it exports another number of equations. -/\n" +
      "def exportedEquation : Except String Article.Theory → Article.Term × Article.Term\n" +
      "  | .ok theory =>\n" +
      "      match Article.importEquations theory.theorems with\n" +
      "      | [equation] => equation\n" +
      "      | _ => (.termVariable ⟨[], \"x\"⟩ termType, .termVariable ⟨[], \"x\"⟩ termType)\n" +
      "  | .error _ => (.termVariable ⟨[], \"x\"⟩ termType, .termVariable ⟨[], \"x\"⟩ termType)\n\n" +
      "/-- The signature of a reading `result` of an article, read from its definitions (D7.1), or the\n" +
      "empty signature when the reader rejected the article. -/\n" +
      "def articleSignature : Except String Article.Theory → Signature\n" +
      "  | .ok theory => signatureOf theory.definitions\n" +
      "  | .error _ => []\n\n" +
      "/-- Whether `resultChecked` accepts a reading `result` of an article with the equation it exports\n" +
      "under the article's signature, and both sides of that equation have a reading. -/\n" +
      "def checkedAndRead (lemmas : List EndToEnd.Statement)\n" +
      "    (result : Except String Article.Theory) : Bool :=\n" +
      "  resultChecked (articleSignature result) lemmas (exportedEquation result).1\n" +
      "      (exportedEquation result).2 result &&\n" +
      "    (read (articleSignature result) (exportedEquation result).1).isSome &&\n" +
      "      (read (articleSignature result) (exportedEquation result).2).isSome\n\n" +
      "/-- Whether the article's signature is well formed and the equation a reading `result` of the\n" +
      "article exports is the pair of the writer's encodings (`Encoding.encode`) of the finite terms\n" +
      "`input` and `output` under it. -/\n" +
      "def sidesEncoded (input output : FiniteTerm) (result : Except String Article.Theory) : Bool :=\n" +
      "  Encoding.signatureWellFormed (articleSignature result) &&\n" +
      "    Encoding.encode (articleSignature result) input == some (exportedEquation result).1 &&\n" +
      "      Encoding.encode (articleSignature result) output == some (exportedEquation result).2\n\n" +
      "/-- `checkedAndRead` and `sidesEncoded` of one reading: one Boolean, so that the kernel reads the\n" +
      "article once for all of them. -/\n" +
      "def checkedReadAndEncoded (lemmas : List EndToEnd.Statement) (input output : FiniteTerm)\n" +
      "    (result : Except String Article.Theory) : Bool :=\n" +
      "  checkedAndRead lemmas result && sidesEncoded input output result\n\n"

  /** The name of the knowledge file of the path, its last label. */
  /** The block of one article. */
  private def fixtureText(fixture: FixpointFixture): String =
    val FixpointFixture(run, lemmas) = fixture
    val base = run.base
    val lowerCamelName = LeanFiniteTerms.lowerCamelCase(base)
    s"/-! ## $base\n\n" +
      s"The program `${run.programText}` (`${run.name}`) under the round `${run.round}`.\n" +
      s"Its strategy takes the lemmas of the tests' round `${roundKey(run.round)}`;\n" +
      s"its article imports the statements of ${lemmas.size} of them. -/\n\n" +
      s"/-- The text of `$base.art`: its lines, each followed by a newline. -/\n" +
      s"def ${lowerCamelName}Text : String :=\n" +
      s"  String.join (${lowerCamelName}Lines.map (· ++ \"\\n\"))\n\n" +
      "/-- The equation input = output that the article exports. -/\n" +
      s"def ${lowerCamelName}Equation : Article.Term × Article.Term :=\n" +
      s"  exportedEquation (Article.readArticle ${lowerCamelName}Text)\n\n" +
      "/-- The signature of the article's thunk constants, read from its definitions. -/\n" +
      s"def ${lowerCamelName}Signature : Signature :=\n" +
      s"  articleSignature (Article.readArticle ${lowerCamelName}Text)\n\n" +
      lemmasText(lowerCamelName, lemmas) +
      s"set_option maxHeartbeats $kernelCheckHeartbeats in\n" +
      "/-- No line of the article holds a newline, and `checkedReadAndEncoded` accepts the reading of its\n" +
      "lines with the lemma statements above and the run's input and output. The kernel evaluates it. -/\n" +
      s"theorem ${lowerCamelName}LinesChecked :\n" +
      s"    (ArticleLines.linesClean ${lowerCamelName}Lines &&\n" +
      s"      checkedReadAndEncoded ${lowerCamelName}Lemmas\n" +
      s"        FixpointRunSides.${lowerCamelName}Input\n" +
      s"        FixpointRunSides.${lowerCamelName}Output\n" +
      s"        (Article.readLines ${lowerCamelName}Lines)) = true := by\n" +
      "  decide +kernel\n\n" +
      "/-- The reader reads the article's text as it reads its lines. -/\n" +
      s"theorem ${lowerCamelName}Read :\n" +
      s"    Article.readArticle ${lowerCamelName}Text =\n" +
      s"      Article.readLines ${lowerCamelName}Lines := by\n" +
      s"  have verified := ${lowerCamelName}LinesChecked\n" +
      "  simp only [Bool.and_eq_true] at verified\n" +
      "  exact ArticleLines.readArticleOfLines verified.1\n\n" +
      "/-- `checkedReadAndEncoded` accepts the reading of the article's text. -/\n" +
      s"theorem ${lowerCamelName}CheckedReadAndEncoded :\n" +
      s"    checkedReadAndEncoded ${lowerCamelName}Lemmas\n" +
      s"      FixpointRunSides.${lowerCamelName}Input\n" +
      s"      FixpointRunSides.${lowerCamelName}Output\n" +
      s"      (Article.readArticle ${lowerCamelName}Text) = true := by\n" +
      s"  have verified := ${lowerCamelName}LinesChecked\n" +
      "  simp only [Bool.and_eq_true] at verified\n" +
      s"  rw [${lowerCamelName}Read]\n" +
      "  exact verified.2\n\n" +
      "/-- `checkedAndRead` accepts the reading of the article's text. -/\n" +
      s"theorem ${lowerCamelName}CheckedAndRead :\n" +
      s"    checkedAndRead ${lowerCamelName}Lemmas\n" +
      s"      (Article.readArticle ${lowerCamelName}Text) = true := by\n" +
      s"  have verified := ${lowerCamelName}CheckedReadAndEncoded\n" +
      "  simp only [checkedReadAndEncoded, Bool.and_eq_true] at verified\n" +
      "  exact verified.1\n\n" +
      "/-- The reader accepts the article, `importChecked` accepts its import set with the lemma\n" +
      s"statements above, and its one exported equation is `${lowerCamelName}Equation`. -/\n" +
      s"theorem ${lowerCamelName}Checked :\n" +
      s"    resultChecked ${lowerCamelName}Signature ${lowerCamelName}Lemmas\n" +
      s"      ${lowerCamelName}Equation.1 ${lowerCamelName}Equation.2\n" +
      s"      (Article.readArticle ${lowerCamelName}Text) = true := by\n" +
      s"  have verified := ${lowerCamelName}CheckedAndRead\n" +
      "  simp only [checkedAndRead, Bool.and_eq_true] at verified\n" +
      "  exact verified.1.1\n\n" +
      "/-- The exported equation input = output is sound: its two sides are contextually equivalent\n" +
      "under every valuation. -/\n" +
      s"theorem ${lowerCamelName}Sound :\n" +
      s"    EquationSound ${lowerCamelName}Signature ${lowerCamelName}Equation.1 ${lowerCamelName}Equation.2 :=\n" +
      s"  endToEndOfChecked ${lowerCamelName}LemmasSound ${lowerCamelName}Checked\n\n" +
      "/-- The left side, the input, reads as a term of the calculus. -/\n" +
      s"theorem ${lowerCamelName}LeftRead :\n" +
      s"    (read ${lowerCamelName}Signature ${lowerCamelName}Equation.1).isSome = true := by\n" +
      s"  have verified := ${lowerCamelName}CheckedAndRead\n" +
      "  simp only [checkedAndRead, Bool.and_eq_true] at verified\n" +
      "  exact verified.1.2\n\n" +
      "/-- The right side, the output, reads as a term of the calculus. -/\n" +
      s"theorem ${lowerCamelName}RightRead :\n" +
      s"    (read ${lowerCamelName}Signature ${lowerCamelName}Equation.2).isSome = true := by\n" +
      s"  have verified := ${lowerCamelName}CheckedAndRead\n" +
      "  simp only [checkedAndRead, Bool.and_eq_true] at verified\n" +
      "  exact verified.2\n\n" +
      "/-- The left side is the encoding of the run's input. -/\n" +
      s"theorem ${lowerCamelName}InputEncoded :\n" +
      s"    Encoding.encode ${lowerCamelName}Signature FixpointRunSides.${lowerCamelName}Input =\n" +
      s"      some ${lowerCamelName}Equation.1 := by\n" +
      s"  have verified := ${lowerCamelName}CheckedReadAndEncoded\n" +
      "  simp only [checkedReadAndEncoded, sidesEncoded, Bool.and_eq_true, beq_iff_eq] at verified\n" +
      "  exact verified.2.1.2\n\n" +
      "/-- The right side is the encoding of the run's output. -/\n" +
      s"theorem ${lowerCamelName}OutputEncoded :\n" +
      s"    Encoding.encode ${lowerCamelName}Signature FixpointRunSides.${lowerCamelName}Output =\n" +
      s"      some ${lowerCamelName}Equation.2 := by\n" +
      s"  have verified := ${lowerCamelName}CheckedReadAndEncoded\n" +
      "  simp only [checkedReadAndEncoded, sidesEncoded, Bool.and_eq_true, beq_iff_eq] at verified\n" +
      "  exact verified.2.2\n\n" +
      "/-- The readings of the input and of the output are contextually equivalent. -/\n" +
      s"theorem ${lowerCamelName}ContextualEquivalence :\n" +
      s"    ∃ leftTerm rightTerm, read ${lowerCamelName}Signature ${lowerCamelName}Equation.1 = some leftTerm ∧\n" +
      s"      read ${lowerCamelName}Signature ${lowerCamelName}Equation.2 = some rightTerm ∧\n" +
      "      ContextualEquivalence leftTerm rightTerm := by\n" +
      "  obtain ⟨leftTerm, leftRead⟩ :=\n" +
      s"    Option.isSome_iff_exists.mp ${lowerCamelName}LeftRead\n" +
      "  obtain ⟨rightTerm, rightRead⟩ :=\n" +
      s"    Option.isSome_iff_exists.mp ${lowerCamelName}RightRead\n" +
      "  exact ⟨leftTerm, rightTerm, leftRead, rightRead,\n" +
      s"    contextualEquivalenceOfRead ${lowerCamelName}Sound leftRead rightRead⟩\n\n" +
      "/-- The article's signature is well formed: its names are distinct and none of them an\n" +
      "operator's. -/\n" +
      s"theorem ${lowerCamelName}WellFormed : Encoding.signatureWellFormed ${lowerCamelName}Signature = true := by\n" +
      s"  have verified := ${lowerCamelName}CheckedReadAndEncoded\n" +
      "  simp only [checkedReadAndEncoded, sidesEncoded, Bool.and_eq_true, beq_iff_eq] at verified\n" +
      "  exact verified.2.1.1\n\n" +
      "/-- The readbacks of the run's input and of its output, IR terms, are defined and contextually\n" +
      "equivalent: readback input ≃_O readback output. -/\n" +
      s"theorem ${lowerCamelName}Readbacks :\n" +
      "    ∃ inputTerm outputTerm,\n" +
      s"      Readback.readback FixpointRunSides.${lowerCamelName}Input = some inputTerm ∧\n" +
      s"      Readback.readback FixpointRunSides.${lowerCamelName}Output = some outputTerm ∧\n" +
      "      ContextualEquivalence inputTerm outputTerm :=\n" +
      s"  Encoding.endToEndEncodedOfChecked ${lowerCamelName}WellFormed ${lowerCamelName}LemmasSound\n" +
      s"    ${lowerCamelName}Checked ${lowerCamelName}InputEncoded\n" +
      s"    ${lowerCamelName}OutputEncoded ${lowerCamelName}LeftRead\n" +
      s"    ${lowerCamelName}RightRead\n\n"

  /** The definition of the lemma statements of an article and the theorem
    * of their soundness.
    */
  private def lemmasText(lowerCamelName: String, lemmas: Vector[String]): String =
    if lemmas.isEmpty then
      "/-- The statements of the lemmas the article imports: none. -/\n" +
        s"def ${lowerCamelName}Lemmas : List EndToEnd.Statement := []\n\n" +
        "/-- Every lemma statement the article imports is sound: there is none. -/\n" +
        s"theorem ${lowerCamelName}LemmasSound :\n" +
        s"    ∀ lemma ∈ ${lowerCamelName}Lemmas, lemma.Sound :=\n" +
        "  Exported.soundNil\n\n"
    else
      val items = lemmas.map(name => s"Statement.«$name»").mkString(",\n   ")
      val steps = lemmas.map(name => s"soundCons «$name»").mkString(" <|\n  ")
      "open LambdaJit.Exported in\n" +
        "/-- The statements of the lemmas the article imports, in the order of the index. -/\n" +
        s"def ${lowerCamelName}Lemmas : List EndToEnd.Statement :=\n" +
        s"  [$items]\n\n" +
        "open LambdaJit.Exported in\n" +
        "/-- Every lemma statement the article imports is sound, by its soundness declaration. -/\n" +
        s"theorem ${lowerCamelName}LemmasSound :\n" +
        s"    ∀ lemma ∈ ${lowerCamelName}Lemmas, lemma.Sound :=\n" +
        s"  $steps soundNil\n\n"

  /** The full names of the theorems of FixpointRunFixtures whose axioms the
    * module FixpointRunFixturesAxioms prints, in its order.
    */
  def axiomsTheorems(fixtures: Vector[FixpointFixture]): Vector[String] =
    for
      fixture <- fixtures
      suffix <- Vector("LemmasSound", "Checked", "Sound", "ContextualEquivalence", "InputEncoded", "OutputEncoded", "Readbacks")
    yield s"LambdaJit.FixpointRunFixtures.${LeanFiniteTerms.lowerCamelCase(fixture.run.base)}$suffix"

  /** The module FixpointRunFixturesAxioms of the fixtures. */
  def axiomsText(fixtures: Vector[FixpointFixture]): String =
    "import LambdaJit.FixpointRunFixtures\n\n" +
      "/-!\n" +
      "# The axioms of the end-to-end theorem on the articles of the fixpoint runs\n\n" +
      "Generated by `FixpointRunModules.axiomsText` of\n" +
      "`gezi/proofs/src/test/scala/gezi/proofs/FixpointRunModules.scala`; not edited.\n" +
      "`#print axioms` for the theorems of module `FixpointRunFixtures` on each article, printed on every\n" +
      "build of this module. The test\n" +
      "`OpentheoryArticleFixpointRunsTest.leanChecksTheFixpointRunsWithTheBuiltInAxiomsOnly` runs Lean\n" +
      "on this module and checks that each theorem depends on Lean's built-in axioms only, `propext`,\n" +
      "`Classical.choice` and `Quot.sound`: the kernel checks each article (`decide +kernel`), and no\n" +
      "lemma statement an article imports is a named axiom.\n" +
      "-/\n\n" +
      axiomsTheorems(fixtures).map(theorem => s"#print axioms $theorem\n").mkString
