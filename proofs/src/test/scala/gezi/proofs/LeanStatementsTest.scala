package gezi.proofs

import java.nio.file.Files
import gezi.ir.NoFacts
import gezi.lemmaencoding.EncodedLemma
import gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import gezi.standardlibrary.LemmaProof
import gezi.standardlibrary.LibraryFiles
import gezi.standardlibrary.StandardLibrary

/** Reading Lean's output on an export, shared by the suites of the Lean
  * statements.
  */
object LeanStatementsChecks:

  /** Every lemma of direction `equation` of the library, as the baseline
    * encodes it, from which the export builds the statements.
    */
  def baselineEncodings(library: StandardLibrary): Vector[EncodedLemma[NoFacts.type]] =
    library.index.equations.map(BaselineLemmaEncoding.encoded(library.index, _))

  /** The text of the export of the library, from the standard library's
    * directory.
    */
  def exportedText(library: StandardLibrary): String =
    given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()
    LeanStatements.text(
      library,
      library.index,
      baselineEncodings(library),
      ProofTestFiles.repository
    )

  /** The name of every line of the text that states the soundness of a
    * lemma `«Name»` with the command `lemma_soundness`, in order.
    */
  def soundnessNames(text: String): Vector[String] =
    text.split("\n", -1).toVector.filter(_.startsWith("lemma_soundness «")).map { line =>
      val qualified = line.split(" ", -1)(1)
      qualified.split("\\.", -1).toVector.map(_.filterNot(character => character == '«' || character == '»')) match
        case Vector(name) => name
        case other        => throw IllegalStateException(s"no lemma name in $line")
    }

  /** The full name of a lemma's soundness declaration. */
  def lemmaAxiom(name: String): String = s"LambdaJit.Exported.$name"

  /** The Lean functions soundnessKind and soundnessPrinted, in the namespace
    * LambdaJit.LeanStatementsCheck, which read what declares the soundness
    * of a lemma off the environment.
    */
  val kindDefinitions: String =
    Vector(
      "open Lean in",
      "/-- What declares the soundness `name` of a lemma: its hand-written proof, the soundness theorem",
      "of one of the seven decisions, or an axiom. -/",
      "def soundnessKind (name : Name) : CoreM String := do",
      "  match (← getEnv).find? name with",
      "  | some (.axiomInfo _) => pure \"axiom\"",
      "  | some (.thmInfo theoremInfo) =>",
      "      match theoremInfo.value.getAppFn with",
      "      | .const proof _ =>",
      "          if proof == ``LambdaJit.StatementNormalisation.numberedInstanceSound then",
      "            pure \"numbered_instance\"",
      "          else if proof == ``LambdaJit.StatementNormalisation.statementSoundOfNormalised then",
      "            pure \"normaliser\"",
      "          else if proof == ``LambdaJit.StatementNormalisation.statementSoundOfContracted then",
      "            pure \"contraction\"",
      "          else if proof == ``LambdaJit.StatementNormalisation.statementSoundOfAbsorbed then",
      "            pure \"absorbed_members\"",
      "          else if proof == ``LambdaJit.StatementNormalisation.statementSoundOfOpenedAccepted then",
      "            pure \"opened_constants\"",
      "          else if proof == ``LambdaJit.StatementNormalisation.statementSoundOfNormalisedLong then",
      "            pure \"long_normal_form\"",
      "          else if proof == ``LambdaJit.StatementNormalisation.statementSoundOfReached then",
      "            pure \"reached_by_contraction\"",
      "          else if proof == ``LambdaJit.EndToEnd.equationSoundOfDerivable then",
      "            match theoremInfo.value.getAppArgs.back? with",
      "            | some (.const derivation _) =>",
      "                if (`LambdaJit.LibraryLemmaProofs).isPrefixOf derivation then pure \"hand_written\"",
      "                else throwError \"the soundness {name} is proved from {derivation}\"",
      "            | _ => throwError \"the soundness {name} is proved by {proof}\"",
      "          else throwError \"the soundness {name} is proved by {proof}\"",
      "      | other => throwError \"the soundness {name} is proved by {other}\"",
      "  | _ => throwError \"no soundness declaration {name}\"",
      "",
      "open Lean in",
      "/-- Prints `soundness of <name> by <kind>`, the kind of `soundnessKind`. -/",
      "def soundnessPrinted (name : Name) : CoreM Unit := do",
      "  IO.println s!\"soundness of {name} by {← soundnessKind name}\"",
      ""
    ).mkString("\n")

  /** The `#print axioms` line and the line that prints the kind of every
    * lemma's soundness declaration.
    */
  def lemmaLines(names: Vector[String]): String =
    (names.map(name => s"#print axioms LambdaJit.Exported.«$name»") ++
      names.map(name => s"#eval LambdaJit.LeanStatementsCheck.soundnessPrinted `LambdaJit.Exported.«$name»")).mkString("\n")

  /** Where the line soundnessPrinted prints for a lemma, `soundness of
    * <full name> by <kind>`, begins in the normalised output, how long it is,
    * and the kind, its last word. Throws when Lean printed none.
    */
  def kindMessage(normalised: String, name: String): (Int, Int, String) =
    val head = s"soundness of ${lemmaAxiom(name)} by "
    val before = normalised.indexOf(head)
    if before < 0 then throw IllegalStateException(s"no kind printed for $name in $normalised")
    val after = normalised.substring(before + head.length)
    val kind = after.takeWhile(_ != ' ')
    (before, head.length + kind.length, kind)

  /** The normalised output without the kind line of each lemma. */
  def kindsRemoved(normalised: String, names: Vector[String]): String =
    names.foldLeft(normalised) { (text, name) =>
      val (before, length, _) = kindMessage(text, name)
      text.substring(0, before) + text.substring(before + length)
    }

/** The Lean module of the library's lemma statements (`LeanStatements`), the port of the first two
  * units of `gezi/tests/lean_statements.plt`. The first is exported from
  * the index of prelude, guard_laws, parallel_types,
  * filtered_recursion_naturals, lattice_types and contracts, the union of the
  * libraries of the expected articles of the hand-made runs, of the examples
  * of lattice_types and of contracts, so that Lean runs once on the lemmas of
  * all three:
  *
  *   - it states the soundness of each lemma name of the index with one
  *     `lemma_soundness` command, in the order of the index, and they are the
  *     lemmas the six source files declare;
  *   - Lean accepts it, against the package gezi/lean built first with
  *     `lake build`, together with the checks of `checkText`, which take the
  *     expected articles (whose lines the package's module ExpectedArticles
  *     holds): the statement of identity_applied is, term for term, one of
  *     the imports of the article of one_lemma_instance; each of the six
  *     articles of the runs made by hand goes through
  *     `EndToEnd.endToEndOfChecked` with the list of the exported soundness
  *     declarations of the lemmas it uses, and one goes through it with
  *     `lemmas`, every statement; `#print axioms` of each lemma's soundness
  *     declaration and of each article check lists Lean's built-in axioms
  *     only: every lemma is a theorem; and what proved each lemma's soundness,
  *     read off the proof term (soundnessKind), counted by kind, is
  *     `expectedKindCounts`, the reading of 2026-11-19, after `statementAbsorbed` was tried second.
  *     The Lean environment
  *     and the kernel's evaluation decide which is which; the counts are the
  *     baseline they are checked against.
  *
  * Lean prints nothing but the `#print axioms` messages and the kinds: a
  * warning fails the test as an error does.
  *
  * The second unit exports the library of prelude, guard_laws,
  * parallel_types and lattice_types, whose lemmas cite the two design
  * documents of the paper proofs, set_equations and normality_measure, and
  * checks that each paper lemma's docstring cites the document its metadatum
  * names, once.
  */
class LeanStatementsTest extends gezi.generatedinputs.FailFastSuite:

  private given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of LeanStatementsTest, "leanAcceptsTheModuleAndMatchesTheArticlesImports", takes 111.434 s; the bound is 1.5 times that rounded up to 5 s.
  // Reason: it runs the Lean toolchain over the exported module.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(170, "s")

  /** The library of prelude, guard_laws, parallel_types,
    * filtered_recursion_naturals, lattice_types and contracts, the one field
    * of tests/library_fixtures/lean_statements_library.lambdalattice.
    */
  private lazy val library = LibraryFiles.compiled("tests/library_fixtures/lean_statements_library.lambdalattice", Vector.empty)

  /** The library of prelude, guard_laws, parallel_types and lattice_types,
    * the one field of tests/library_fixtures/paper_proof_library.lambdalattice.
    */
  private lazy val paperLibrary =
    LibraryFiles.compiled("tests/library_fixtures/paper_proof_library.lambdalattice", Vector.empty)

  /** The two libraries, forced before the first test and not charged to it (FailFastSuite). */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => library, _ => paperLibrary)

  test("oneSoundnessCommandPerLemmaNameOfTheIndex") {
    val expected = library.index.lemmaNames.collect {
      case gezi.standardlibrary.LemmaNamed(lemma, name) if library.index.sides(lemma).isDefined => name
    }
    assertEquals(LeanStatements.names(library), expected)
    val file = Files.createTempFile("lean_statements", ".lean")
    val declared =
      try
        LeanStatements.written(
          library,
          library.index,
          LeanStatementsChecks.baselineEncodings(library),
          ProofTestFiles.repository,
          file
        )
        LeanStatementsChecks.soundnessNames(ProofTestFiles.textRead(file))
      finally Files.delete(file)
    assertEquals(declared, expected)
    assertEquals(declared.size, 36)
  }

  test("theAxiomsAreTheLemmasOfTheSources") {
    // The knowledge's lemmas: those it declares, each with its proof in the
    // library.
    val sources = library.lemmaProofs.keys.toVector
    assertEquals(LeanStatements.names(library).sorted, sources.sorted)
  }

  /** How many lemmas of the library each kind of declaration proves: the
    * reading of 2026-11-19. Every lemma is a theorem: 12 have a hand-written
    * proof in Lean module LibraryLemmaProofs (the lemmas proved on paper of
    * parallel_types, filtered_recursion_naturals and contracts), 2 are
    * instances of the numbered equations (8) and (9) (lattice_types'
    * choice_applied and parallel_applied), 14 are proved by the decision of
    * absorbed members, tried second, 4 by the normaliser
    * and 4 by leftmost outermost contraction (the rows of recursive
    * functions of prelude).
    */
  private val expectedKindCounts =
    Vector("hand_written" -> 12, "numbered_instance" -> 2, "absorbed_members" -> 14, "normaliser" -> 4, "contraction" -> 4, "axiom" -> 0)

  private val checkNames = Vector(
    "identityAppliedImported",
    "congruenceOnlyByStatements",
    "oneLemmaInstanceByStatements",
    "twoInstancesAndACongruenceByStatements",
    "etaShapedConstantByStatements",
    "oneLemmaInstanceByEveryStatement",
    "twoThunksOfOneClassByStatements",
    "anArgumentDroppedThenSpelledByStatements"
  )

  /** The checks appended to the exported module, and the `#print axioms`
    * and the kind of every lemma's soundness declaration.
    */
  private def checkText(names: Vector[String]): String =
    Vector(checksText, LeanStatementsChecks.lemmaLines(names), "").mkString("\n")

  private def checksText: String =
    Vector(
      "",
      "namespace LambdaJit.LeanStatementsCheck",
      "",
      "open LambdaJit.EndToEnd LambdaJit.EndToEndFixtures LambdaJit.ExpectedArticles",
      "",
      "/-- Whether the statement `lemma` is one of the imports of the article `text`, under the article's",
      "signature and its own (`EndToEnd.Statement.imports`, D7.1). -/",
      "def importsContain (text : String) (lemma : Statement) : Bool :=",
      "  match Article.readArticle text with",
      "  | .ok theory =>",
      "      (Article.importEquations theory.assumptions).any",
      "        (lemma.imports (Interpretation.signatureOf theory.definitions))",
      "  | .error _ => false",
      "",
      "/-- The signature of the article `text`, read from its definitions, or the empty signature when",
      "the reader rejects it. -/",
      "def articleSignature (text : String) : Interpretation.Signature :=",
      "  match Article.readArticle text with",
      "  | .ok theory => Interpretation.signatureOf theory.definitions",
      "  | .error _ => []",
      "",
      "theorem identityAppliedImported :",
      "    importsContain oneLemmaInstanceText Exported.Statement.«identity_applied» = true := by",
      "  unfold importsContain oneLemmaInstanceText Article.readArticle",
      "  rw [ArticleLines.articleLinesJoin oneLemmaInstanceLines",
      "    (ArticleLines.noNewlineOfLinesClean (by decide +kernel))]",
      "  decide +kernel",
      "",
      "theorem congruenceOnlyByStatements :",
      "    EquationSound congruenceOnlySignature congruenceOnlyLeft congruenceOnlyRight :=",
      "  endToEndOfChecked (text := congruenceOnlyText) Exported.soundNil (by",
      "    unfold congruenceOnlyText Article.readArticle",
      "    rw [ArticleLines.articleLinesJoin congruenceOnlyLines",
      "      (ArticleLines.noNewlineOfLinesClean (by decide +kernel))]",
      "    decide +kernel)",
      "",
      "theorem oneLemmaInstanceByStatements :",
      "    EquationSound oneLemmaInstanceSignature oneLemmaInstanceLeft oneLemmaInstanceRight :=",
      "  endToEndOfChecked (text := oneLemmaInstanceText)",
      "    (Exported.soundCons Exported.«identity_applied» Exported.soundNil) (by",
      "    unfold oneLemmaInstanceText Article.readArticle",
      "    rw [ArticleLines.articleLinesJoin oneLemmaInstanceLines",
      "      (ArticleLines.noNewlineOfLinesClean (by decide +kernel))]",
      "    decide +kernel)",
      "",
      "theorem twoInstancesAndACongruenceByStatements :",
      "    EquationSound twoInstancesAndACongruenceSignature twoInstancesAndACongruenceLeft",
      "      twoInstancesAndACongruenceRight :=",
      "  endToEndOfChecked (text := twoInstancesAndACongruenceText)",
      "    (Exported.soundCons Exported.«identity_applied» Exported.soundNil) (by",
      "    unfold twoInstancesAndACongruenceText Article.readArticle",
      "    rw [ArticleLines.articleLinesJoin twoInstancesAndACongruenceLines",
      "      (ArticleLines.noNewlineOfLinesClean (by decide +kernel))]",
      "    decide +kernel)",
      "",
      "theorem etaShapedConstantByStatements :",
      "    EquationSound etaShapedConstantSignature etaShapedConstantLeft etaShapedConstantRight :=",
      "  endToEndOfChecked (text := etaShapedConstantText) Exported.soundNil (by",
      "    unfold etaShapedConstantText Article.readArticle",
      "    rw [ArticleLines.articleLinesJoin etaShapedConstantLines",
      "      (ArticleLines.noNewlineOfLinesClean (by decide +kernel))]",
      "    decide +kernel)",
      "",
      "theorem oneLemmaInstanceByEveryStatement :",
      "    EquationSound oneLemmaInstanceSignature oneLemmaInstanceLeft oneLemmaInstanceRight :=",
      "  endToEndOfChecked (text := oneLemmaInstanceText) Exported.lemmasSound (by",
      "    unfold oneLemmaInstanceText Article.readArticle",
      "    rw [ArticleLines.articleLinesJoin oneLemmaInstanceLines",
      "      (ArticleLines.noNewlineOfLinesClean (by decide +kernel))]",
      "    decide +kernel)",
      "",
      "/-- The one equation that the article `text` exports, or x = x, x a variable, when the reader",
      "rejects it or it exports another number of equations. -/",
      "def exportedEquation (text : String) : Article.Term × Article.Term :=",
      "  match Article.readArticle text with",
      "  | .ok theory =>",
      "      match Article.importEquations theory.theorems with",
      "      | [equation] => equation",
      "      | _ => (.termVariable ⟨[], \"x\"⟩ termType, .termVariable ⟨[], \"x\"⟩ termType)",
      "  | .error _ => (.termVariable ⟨[], \"x\"⟩ termType, .termVariable ⟨[], \"x\"⟩ termType)",
      "",
      "def twoThunksOfOneClassText : String := String.join (twoThunksOfOneClassLines.map (· ++ \"\\n\"))",
      "",
      "theorem twoThunksOfOneClassByStatements :",
      "    EquationSound (articleSignature twoThunksOfOneClassText)",
      "      (exportedEquation twoThunksOfOneClassText).1 (exportedEquation twoThunksOfOneClassText).2 :=",
      "  endToEndOfChecked (text := twoThunksOfOneClassText)",
      "    (Exported.soundCons Exported.«successor_filtered» Exported.soundNil) (by",
      "    unfold exportedEquation articleSignature twoThunksOfOneClassText Article.readArticle",
      "    rw [ArticleLines.articleLinesJoin twoThunksOfOneClassLines",
      "      (ArticleLines.noNewlineOfLinesClean (by decide +kernel))]",
      "    decide +kernel)",
      "",
      "def anArgumentDroppedThenSpelledText : String :=",
      "  String.join (anArgumentDroppedThenSpelledLines.map (· ++ \"\\n\"))",
      "",
      "theorem anArgumentDroppedThenSpelledByStatements :",
      "    EquationSound (articleSignature anArgumentDroppedThenSpelledText)",
      "      (exportedEquation anArgumentDroppedThenSpelledText).1",
      "      (exportedEquation anArgumentDroppedThenSpelledText).2 :=",
      "  endToEndOfChecked (text := anArgumentDroppedThenSpelledText)",
      "    (Exported.soundCons Exported.«post_application_of_apply_to» Exported.soundNil) (by",
      "    unfold exportedEquation articleSignature anArgumentDroppedThenSpelledText Article.readArticle",
      "    rw [ArticleLines.articleLinesJoin anArgumentDroppedThenSpelledLines",
      "      (ArticleLines.noNewlineOfLinesClean (by decide +kernel))]",
      "    decide +kernel)",
      "",
      LeanStatementsChecks.kindDefinitions,
      "end LambdaJit.LeanStatementsCheck",
      ""
    ).mkString("\n") + "\n" +
      checkNames.map(name => s"#print axioms LambdaJit.LeanStatementsCheck.$name").mkString("\n")

  stoppableTest("leanAcceptsTheModuleAndMatchesTheArticlesImports") { stopped =>
    val names = LeanStatements.names(library)
    val text = "import LambdaJit.EndToEndFixtures\n" + LeanStatementsChecks.exportedText(library) + checkText(names)
    val normalised =
      ProofTestFiles.normalisedOutput(ProofTestFiles.leanRun(text, "lean_statements_check", Seq.empty, stopped))
    val theorems = checkNames.map(name => s"LambdaJit.LeanStatementsCheck.$name") ++
      names.map(LeanStatementsChecks.lemmaAxiom)
    assertEquals(
      ProofTestFiles.otherOutput(LeanStatementsChecks.kindsRemoved(normalised, names), theorems),
      ""
    )
    theorems.foreach(theorem =>
      assertEquals((theorem, ProofTestFiles.printedAxioms(normalised, theorem)), (theorem, ProofTestFiles.builtInAxioms))
    )
    val printedCounts = names
      .map(name => LeanStatementsChecks.kindMessage(normalised, name)._3)
      .groupBy(identity)
      .map((kind, kinds) => (kind, kinds.size))
      .toVector
      .sorted
    assertEquals(printedCounts, expectedKindCounts.filter(_._2 > 0).sorted)
  }

  // A lemma whose proof is a Markdown link cites the link as it is, once, in
  // its own docstring.
  test("everyMarkdownProofLemmaCitesItsLink") {
    val expected = LeanStatements.names(paperLibrary)
    val text = LeanStatementsChecks.exportedText(paperLibrary)
    assertEquals(LeanStatementsChecks.soundnessNames(text), expected)
    val linkLemmas = expected.flatMap { name =>
      paperLibrary.lemmaProof(name).collect { case LemmaProof.Markdown(link) => (name, link) }
    }
    assert(linkLemmas.nonEmpty)
    linkLemmas.foreach { (name, link) =>
      val citation = s"The proof its declaration cites: the Markdown link\n$link."
      assertEquals((name, occurrences(docstring(text, name), citation, 0, 0)), (name, 1))
    }
  }

  // A lemma whose proof is a munit suite cites the suite, once, in its own
  // docstring: the 19 lemmas of prelude and guard_laws that
  // StandardLibraryLemmasTest replays.
  test("everyMunitProofLemmaCitesItsSuite") {
    val expected = LeanStatements.names(paperLibrary)
    val text = LeanStatementsChecks.exportedText(paperLibrary)
    val suiteLemmas = expected.flatMap { name =>
      paperLibrary.lemmaProof(name).collect { case LemmaProof.Munit(suite) => (name, suite) }
    }
    assertEquals(suiteLemmas.map(_._2).distinct, Vector("gezi.standardlibrary.StandardLibraryLemmasTest"))
    assertEquals(suiteLemmas.size, 19)
    suiteLemmas.foreach { (name, suite) =>
      val citation = s"The proof its declaration cites: the munit suite\n`$suite`."
      assertEquals((name, occurrences(docstring(text, name), citation, 0, 0)), (name, 1))
    }
    assertEquals(occurrences(text, "the munit suite", 0, 0), suiteLemmas.size)
  }

  /** The docstring of the lemma's soundness command in the text. */
  private def docstring(text: String, name: String): String =
    val command = text.indexOf(s"lemma_soundness «$name» of ")
    assert(command >= 0, s"no soundness command for $name")
    text.substring(command, text.indexOf("-/", command))

  @scala.annotation.tailrec
  private def occurrences(text: String, part: String, from: Int, found: Int): Int =
    val position = text.indexOf(part, from)
    if position < 0 then found else occurrences(text, part, position + 1, found + 1)
