package com.yang_bo.gezi.strategies

import java.nio.file.Files
import java.nio.file.Path
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.λ
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.LemmaIdentifier
import com.yang_bo.gezi.proofs.EncodedRun
import com.yang_bo.gezi.proofs.ExpectedArticlesModule
import com.yang_bo.gezi.proofs.FixpointFixture
import com.yang_bo.gezi.proofs.FixpointRun
import com.yang_bo.gezi.proofs.FixpointRunModules
import com.yang_bo.gezi.proofs.HolTermText
import com.yang_bo.gezi.proofs.OpentheoryArticle
import com.yang_bo.gezi.proofs.ProofTestFiles
import com.yang_bo.gezi.proofs.RewriteTrace
import com.yang_bo.gezi.proofs.ThunkDefinitions
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.LeanFiniteTerms
import com.yang_bo.gezi.standardlibrary.LemmaNamed
import com.yang_bo.gezi.standardlibrary.LibraryFiles
import com.yang_bo.gezi.standardlibrary.StandardLibrary
import com.yang_bo.gezi.standardlibrary.TermTables
import com.yang_bo.gezi.weakhead.Expansions

/** A fixpoint run made: its input, its output, the text of the article its
  * round wrote, and the lemmas the article's derivation names
  * (`RewriteTrace.lemmas`), by their identifiers.
  */
final case class FixpointRunMade(
    input: Configured[NoFacts.type],
    output: Configured[NoFacts.type],
    article: String,
    lemmas: Vector[LemmaIdentifier]
)

/** The runs of the baseline's search strategy, fixpoint_egraph, a round of the
  * Prolog backend's preset's type check, or of the beta rule on a program's
  * closures, over the knowledge of `FixpointRunModules.libraryFile` (the port
  * of the unit `opentheory_article_fixpoint_runs` of
  * `gezi/tests/opentheory_article.plt`).
  *
  * Each run is made as the Prolog test made it: the program through the front
  * end, which tags its occurrences (`StrategyTesting.programInput`), then one
  * round of the strategy `FixpointEgraph` of the run's round (the tests' round
  * `FixpointRunModules.roundKey`, with `roundBudget`, the extraction under
  * specialization_attraction and compression), whose article the round writes.
  * A program's library terms are read as members of
  * tests/jit_fixtures/library_terms.lambdalattice by projection and composed
  * with the HOAS case of a closed instruction, as the TODO the deleted test
  * left asked: no name of the library is free in a program.
  *
  * Its article is the run's expected article byte for byte, the opentheory tool
  * accepts it, and the tool rejects it with its first or its last `sym`
  * deleted, when it has one; the Lean modules of the runs are their
  * regeneration; and Lean's kernel checks the runs' theorems with Lean's
  * built-in axioms only. With the environment variable
  * `GEZI_WRITE_FIXPOINT_RUNS` set, the suite first writes the expected
  * articles, the module of the expected articles (`ExpectedArticlesModule`) and
  * the three modules of the runs from the runs made, then checks them as
  * always; a change of an article or of a module is reviewed in its diff.
  *
  * The writer encodes each run's sides as Lean's `Encoding.encode` encodes
  * their finite terms, under the signature of the writer's own thunk constants
  * (`theWriterEncodesAsLeanEncodesOnTheFixpointRuns`, link (ii) of D6,
  * https://github.com/Atry/private-overlay/issues/1561). That the article's one
  * exported equation is the pair of those encodings under the article's
  * signature is checked by the kernel in module FixpointRunFixtures
  * (`…LinesChecked`, `sidesEncoded`).
  *
  * The suite is in the module `strategies`, not `proofs`, because it runs the
  * strategy, and `strategies` depends on `proofs`; it reads the test helpers of
  * `proofs`.
  */
class OpentheoryArticleFixpointRunsTest
    extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  given com.yang_bo.gezi.ir.StorageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()

  private given NoFacts.type = NoFacts

  // Measured 2026-11-17 on 6 CPUs (contest.slice, CPUs 4 to 9, nice 10), the 1-minute load 2 to 4: the suite took
  // 298.8 s, the runs and their articles about 40 s and "leanChecksTheFixpointRunsWithTheBuiltInAxiomsOnly", whose
  // `lake build` rebuilt the three regenerated modules, about 259 s; the bound is 1.5 times that rounded up to 5 s.
  // Reason: it runs the Lean toolchain over the package, the kernel checking each run's article.
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(390, "s")

  private lazy val library: StandardLibrary =
    StrategyTesting.compiled(FixpointRunModules.libraryFile)

  /** The library terms the programs are built from, by name. */
  private lazy val terms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary
      .entryMembers(
        LibraryFiles.buildRoot,
        TermTables.jitLibraryTerms,
        Expansions.none
      )
      ._1

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => library, _ => terms)

  private def term(key: String): StrategyTesting.ProgramTerm =
    Term.closed(
      terms.getOrElse(
        key,
        throw IllegalArgumentException(s"no library term $key")
      )
    )

  /** The program of the run, the HOAS term `FixpointRun.programText` writes in
    * the Prolog surface.
    */
  private def program(run: FixpointRun): StrategyTesting.ProgramTerm =
    run.name match
      case "successor_zero" => term("successor")(term("zero"))
      case "identity_zero"  => term("identity")(term("zero"))
      case "compose_redex"  =>
        term("compose")(term("successor"))(term("successor"))(term("zero"))
      case "identity_closure" => λ(x => x)(term("zero"))
      case "twice_closure"    =>
        λ(f => λ(a => f(f(a))))(term("successor"))(term("zero"))
      case other =>
        throw IllegalArgumentException(s"no program of the run $other")

  /** The round's search strategy (`fixpoint_strategy/2`). */
  private def fixpointStrategy(round: String): FixpointEgraph[NoFacts.type] =
    FixpointEgraph(
      library.index,
      StandardSaturator(
        BaselineRounds.saturationOptions(
          library,
          StrategyTesting.round(FixpointRunModules.roundKey(round)),
          BuiltInRule.beforeOptIn,
          FixpointRunModules.roundBudget(round)
        )
      ),
      CountedExtractor(
        ExtractionOptions(Vector("specialization_attraction", "compression")),
        BaselineModules.table[com.yang_bo.gezi.ir.NoFacts.type]
      )
    )

  /** The run made: the program tagged, the round's strategy, and the article
    * the schedule's round writes (`Schedule.roundRan`: the proof's first
    * equation, written to a temporary file).
    */
  private def runMade(run: FixpointRun, stop: StopSignal): FixpointRunMade =
    val input = StrategyTesting.programInput(library, program(run))
    val outcome = fixpointStrategy(run.round)
      .ran(Vector(input), true, stop)
      .getOrElse(
        throw IllegalStateException(
          s"the strategy of ${run.base} gave no answer"
        )
      )
    val output = outcome.outputs match
      case Vector(only) => only
      case other        =>
        throw IllegalStateException(
          s"the strategy of ${run.base} gave ${other.size} outputs"
        )
    val proof = outcome.proof.getOrElse(
      throw IllegalStateException(s"the strategy of ${run.base} gave no proof")
    )
    val first = proof.equations.headOption.getOrElse(
      throw IllegalStateException(
        s"the proof of ${run.base} proves no equation"
      )
    )
    val firstProof = proof.copy(equations = Vector(first))
    val file = Files.createTempFile("fixpoint_run", ".art")
    OpentheoryArticle.written(library.index, input, output, firstProof, file)
    val article = ProofTestFiles.textRead(file)
    Files.delete(file)
    FixpointRunMade(
      input,
      output,
      article,
      RewriteTrace.lemmas(
        OpentheoryArticle.derivation(library.index, input, output, firstProof)
      )
    )

  /** The lemma names of the identifiers, in the order of the Lean statements of
    * the library (`LeanStatements.names`).
    */
  private def lemmaNames(lemmas: Vector[LemmaIdentifier]): Vector[String] =
    val named = library.index.lemmaNames.collect {
      case LemmaNamed(identifier, name) if lemmas.contains(identifier) => name
    }.toSet
    com.yang_bo.gezi.proofs.LeanStatements.names(library).filter(named.contains)

  private def written(file: Path, text: String): Unit =
    Files.writeString(file, text)

  /** Every run made, in the order of `FixpointRunModules.runs`. */
  private def runsMade(
      stopped: scala.concurrent.Future[Unit]
  ): Vector[(FixpointRun, FixpointRunMade)] =
    FixpointRunModules.runs.map(run =>
      (run, runMade(run, StopSignal.completedWith(stopped)))
    )

  stoppableTest("theRunsWriteTheirExpectedArticlesAndTheirLeanModules") {
    stopped =>
      val made = runsMade(stopped)
      val fixtures = made.map((run, runMade) =>
        FixpointFixture(run, lemmaNames(runMade.lemmas))
      )
      val encoded = made.map((run, runMade) =>
        EncodedRun(run.base, runMade.input, runMade.output)
      )
      if sys.env.contains("GEZI_WRITE_FIXPOINT_RUNS") then
        made.foreach((run, runMade) =>
          written(ProofTestFiles.expectedFile(run.base), runMade.article)
        )
        written(
          ProofTestFiles.leanModules.resolve("ExpectedArticles.lean"),
          ExpectedArticlesModule.text
        )
        written(
          ProofTestFiles.leanModules.resolve("FixpointRunSides.lean"),
          FixpointRunModules.sidesText(encoded)
        )
        written(
          ProofTestFiles.leanModules.resolve("FixpointRunFixtures.lean"),
          FixpointRunModules.fixturesText(fixtures)
        )
        written(
          ProofTestFiles.leanModules.resolve("FixpointRunFixturesAxioms.lean"),
          FixpointRunModules.axiomsText(fixtures)
        )
      made.foreach { (run, runMade) =>
        val text = runMade.article
        assertEquals(
          (run.base, text),
          (
            run.base,
            ProofTestFiles.textRead(ProofTestFiles.expectedFile(run.base))
          )
        )
        assertEquals(
          (run.base, ProofTestFiles.textChecked(text)),
          (run.base, (0, ""))
        )
        if text.split("\n", -1).contains("sym") then
          Vector(false, true).foreach { last =>
            val (status, errors) = ProofTestFiles.checkedWithoutSym(text, last)
            assertEquals((run.base, last, status), (run.base, last, 1))
            assert(
              errors.contains("terms not alpha-equivalent"),
              s"${run.base} without a sym: $errors"
            )
          }
      }
      assertEquals(
        ProofTestFiles.textRead(
          ProofTestFiles.leanModules.resolve("ExpectedArticles.lean")
        ),
        ExpectedArticlesModule.text
      )
      assertEquals(
        ProofTestFiles.textRead(
          ProofTestFiles.leanModules.resolve("FixpointRunSides.lean")
        ),
        FixpointRunModules.sidesText(encoded)
      )
      assertEquals(
        ProofTestFiles.textRead(
          ProofTestFiles.leanModules.resolve("FixpointRunFixtures.lean")
        ),
        FixpointRunModules.fixturesText(fixtures)
      )
      assertEquals(
        ProofTestFiles.textRead(
          ProofTestFiles.leanModules.resolve("FixpointRunFixturesAxioms.lean")
        ),
        FixpointRunModules.axiomsText(fixtures)
      )
  }

  // Link (ii) of D6 (https://github.com/Atry/private-overlay/issues/1561): Lean's `Encoding.encode`, of which
  // `Encoding.readEncode` proves that the reading of the encoding of a finite term is its readback, is meant to be
  // the writer's encoding. The writer's encoding of a side is `OpentheoryArticle.termEncoded`, a HOL term over thunk
  // constants numbered from 0 in that term, with the code and the holes of each; Lean's is `encode` of the side's
  // finite term (module FixpointRunSides, checked here to be the runs' regeneration) under the signature that names
  // each of those thunks by its constant. Lean also says whether that signature is well formed
  // (`Encoding.signatureWellFormed`, the hypothesis of `readEncode`). Both encodings are rendered by one syntax
  // (`HolTermText.text`, the Lean program's `termWritten`), and the two texts must be equal byte for byte. The
  // comparison holds on these terms only; it is a test, not a proof.
  stoppableTest("theWriterEncodesAsLeanEncodesOnTheFixpointRuns") { stopped =>
    val made = runsMade(stopped)
    assertEquals(
      ProofTestFiles.textRead(
        ProofTestFiles.leanModules.resolve("FixpointRunSides.lean")
      ),
      FixpointRunModules.sidesText(
        made.map((run, runMade) =>
          EncodedRun(run.base, runMade.input, runMade.output)
        )
      )
    )
    val sides = made.flatMap { (run, runMade) =>
      val name = LeanFiniteTerms.lowerCamelCase(run.base)
      Vector(
        SideEncoded(
          run.base,
          "left",
          s"${name}Input",
          OpentheoryArticle.termEncoded(library.index, runMade.input)
        ),
        SideEncoded(
          run.base,
          "right",
          s"${name}Output",
          OpentheoryArticle.termEncoded(library.index, runMade.output)
        )
      )
    }
    val printed = leanEncodings(sides, stopped)
    val disagreements = sides.flatMap { side =>
      val writerText = side.encoded.terms match
        case Vector(term) => HolTermText.text(term)
        case other        =>
          throw IllegalStateException(
            s"the writer encoded ${side.base}'s ${side.which} side as ${other.size} terms"
          )
      printed.get((side.base, side.which)) match
        case Some(("true", leanText)) if leanText == writerText => None
        case Some((wellFormed, leanText))                       =>
          Some(
            (
              side.base,
              side.which,
              s"well formed: $wellFormed",
              firstDifference(writerText, leanText)
            )
          )
        case None => Some((side.base, side.which, "Lean printed no line", ""))
    }
    assertEquals(disagreements, Vector.empty)
  }

  /** A side of a run as the encoding test compares it: the run's base, `left`
    * for its input or `right` for its output, the side's finite term's name in
    * module FixpointRunSides, and the writer's encoding of the side with the
    * thunks of its constants.
    */
  private final case class SideEncoded(
      base: String,
      which: String,
      leanName: String,
      encoded: ThunkDefinitions.NamedTerms
  )

  /** The first position where the writer's text and Lean's differ, with the 80
    * characters of each from there, or their lengths when one is a prefix of
    * the other.
    */
  private def firstDifference(writerText: String, leanText: String): String =
    (0 until math.min(writerText.length, leanText.length)).find(position =>
      writerText(position) != leanText(position)
    ) match
      case Some(position) =>
        s"at $position: writer ${writerText.slice(position, position + 80)}, Lean ${leanText.slice(position, position + 80)}"
      case None =>
        s"writer ${writerText.length} characters, Lean ${leanText.length}"

  /** Lean's line for each side, keyed by the run's base and the side: whether
    * the side's signature is well formed and the text of `encode` of the side's
    * finite term under it, `none` where `encode` is undefined.
    */
  private def leanEncodings(
      sides: Vector[SideEncoded],
      stopped: scala.concurrent.Future[Unit]
  ): Map[(String, String), (String, String)] =
    val entries = sides.map { side =>
      val signature = side.encoded.definitions.zipWithIndex.map {
        case ((code, holes), number) =>
          val components = ThunkDefinitions.name(number)
          val namespaceText = components.init
            .map(component => s"\"$component\"")
            .mkString("[", ", ", "]")
          s"(⟨$namespaceText, \"${components.last}\"⟩, ${LeanFiniteTerms.codeLeanText(code)}, ${LeanFiniteTerms.holesLeanText(holes)})"
      }
      s"(\"${side.base}\", \"${side.which}\",\n    ${signature.mkString("[", ",\n      ", "]")},\n    FixpointRunSides.${side.leanName})"
    }
    val program = Vector(
      "import LambdaJit.Encoding",
      "import LambdaJit.FixpointRunSides",
      "",
      // The signatures hold the markers' codes in R7's spelling, which nest about 105 applications
      // (`LeanFiniteTerms.leanLines`).
      "set_option maxRecDepth 1024",
      "",
      "open LambdaJit LambdaJit.Interpretation",
      "",
      encodingPrinter,
      "def sides : List (String × String × Signature × FiniteTerm) := [",
      "  " + entries.mkString(",\n  ") + "]",
      "",
      "def main : IO Unit := do",
      "  for (name, which, signature, term) in sides do",
      "    let text := match Encoding.encode signature term with",
      "      | some encoded => termWritten \"\" encoded",
      "      | none => \"none\"",
      "    IO.println s!\"encoding\\t{name}\\t{which}\\t{Encoding.signatureWellFormed signature}\\t{text}\"",
      "",
      "#eval main",
      ""
    ).mkString("\n")
    ProofTestFiles
      .leanRun(
        program,
        "encoding_agreement",
        Seq("LambdaJit.Encoding", "LambdaJit.FixpointRunSides"),
        stopped
      )
      .split("\n")
      .toVector
      .filter(_.nonEmpty)
      .map { line =>
        line.split("\t", -1).toVector match
          case Vector("encoding", base, which, wellFormed, text) =>
            ((base, which), (wellFormed, text))
          case _ =>
            throw IllegalStateException(
              s"Lean printed an unexpected line: ${line.take(200)}"
            )
      }
      .toMap

  // The Lean definitions of the program: `termWritten`, which appends the text of a term to the text written so far,
  // in the syntax of `HolTermText.text`, so that the text is built in time linear in its length.
  private val encodingPrinter: String =
    """def quotedComponent (component : String) : String :=
      |  "\"" ++ String.ofList (component.toList.flatMap fun character =>
      |    if character = '"' ∨ character = '\\' then ['\\', character] else [character]) ++ "\""
      |
      |def nameText (name : Article.Name) : String :=
      |  "[" ++ ",".intercalate ((name.namespaceComponents ++ [name.localName]).map quotedComponent) ++ "]"
      |
      |partial def typeText : Article.LogicType → String
      |  | .typeVariable name => s!"typeVariable({nameText name})"
      |  | .operator name arguments => s!"type({nameText name},[{",".intercalate (arguments.map typeText)}])"
      |
      |partial def termWritten (written : String) : Article.Term → String
      |  | .termVariable name type => written ++ "variable(" ++ nameText name ++ "," ++ typeText type ++ ")"
      |  | .constant name type => written ++ "constant(" ++ nameText name ++ "," ++ typeText type ++ ")"
      |  | .application function argument =>
      |      termWritten (termWritten (written ++ "application(") function ++ ",") argument ++ ")"
      |""".stripMargin

  // The package built, Lean run on the module FixpointRunFixturesAxioms:
  // every theorem it lists depends on Lean's built-in axioms only, and Lean
  // prints nothing else. The theorems are those the module lists, which the
  // test above checks to be its regeneration.
  stoppableTest("leanChecksTheFixpointRunsWithTheBuiltInAxiomsOnly") {
    stopped =>
      val axiomsModule =
        ProofTestFiles.leanModules.resolve("FixpointRunFixturesAxioms.lean")
      val theorems =
        ProofTestFiles.textRead(axiomsModule).split("\n").toVector.collect {
          case line if line.startsWith("#print axioms ") =>
            line.stripPrefix("#print axioms ")
        }
      LeanFiniteTerms.lakeOutput(Seq("build"), stopped)
      val output = LeanFiniteTerms.lakeOutput(
        Seq("env", "lean", axiomsModule.toString),
        stopped
      )
      val normalised = ProofTestFiles.normalisedOutput(output)
      // Built-in axioms only, not all three: a theorem may need fewer, such as the
      // soundness of an article that imports no lemma, which needs propext alone.
      theorems.foreach(theorem =>
        assertEquals(
          (
            theorem,
            ProofTestFiles
              .printedAxioms(normalised, theorem)
              .filterNot(ProofTestFiles.builtInAxioms.contains)
          ),
          (theorem, Vector.empty)
        )
      )
      assertEquals(ProofTestFiles.otherOutput(normalised, theorems), "")
  }
