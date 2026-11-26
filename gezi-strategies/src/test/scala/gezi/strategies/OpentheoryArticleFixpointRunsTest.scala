package gezi.strategies

import java.nio.file.Files
import java.nio.file.Path
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.ir.BuiltInRule
import gezi.ir.Instruction
import gezi.ir.LemmaIdentifier
import gezi.proofs.EncodedRun
import gezi.proofs.ExpectedArticlesModule
import gezi.proofs.FixpointFixture
import gezi.proofs.FixpointRun
import gezi.proofs.FixpointRunModules
import gezi.proofs.OpentheoryArticle
import gezi.proofs.ProofTestFiles
import gezi.proofs.RewriteTrace
import gezi.saturation.StopSignal
import gezi.standardlibrary.LeanFiniteTerms
import gezi.standardlibrary.LemmaNamed
import gezi.standardlibrary.LibraryFiles
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTables
import gezi.weakhead.Expansions

/** A fixpoint run made: its input, its output, the text of the article its
  * round wrote, and the lemmas the article's derivation names
  * (`RewriteTrace.lemmas`), by their identifiers.
  */
final case class FixpointRunMade(input: Instruction, output: Instruction, article: String, lemmas: Vector[LemmaIdentifier])

/** The runs of the baseline's search strategy, fixpoint_egraph, a round of
  * the Prolog backend's preset's type check, or of the beta rule on a
  * program's closures, over the knowledge of `FixpointRunModules.libraryFile`
  * (the port of the unit `opentheory_article_fixpoint_runs` of
  * `gezi/tests/opentheory_article.plt`).
  *
  * Each run is made as the Prolog test made it: the program through the front
  * end, which tags its occurrences (`StrategyTesting.programInput`), then one
  * round of the strategy `FixpointEgraph` of the run's round (the tests' round
  * `FixpointRunModules.roundKey`, with `roundBudget`, the extraction under
  * specialization_attraction and compression), whose article the round
  * writes. A program's library terms are read as members of
  * tests/jit_fixtures/library_terms.lambdalattice by projection and composed
  * with the HOAS case of a closed instruction, as the TODO the deleted test
  * left asked: no name of the library is free in a program.
  *
  * Its article is the run's expected article byte for byte, the opentheory
  * tool accepts it, and the tool rejects it with its first or its last `sym`
  * deleted, when it has one; the Lean modules of the runs are their
  * regeneration; and Lean's kernel checks the runs' theorems with Lean's
  * built-in axioms only. With the environment variable `GEZI_WRITE_FIXPOINT_RUNS`
  * set, the suite first writes the expected articles, the module of the
  * expected articles (`ExpectedArticlesModule`) and the three modules of the
  * runs from the runs made, then checks them as always; a change of an
  * article or of a module is reviewed in its diff.
  *
  * TODO: the check that the writer encodes the runs' sides as Lean's
  * `Encoding.encode` encodes their finite terms, and that the article's one
  * exported equation is the pair of those encodings, stood in the deleted
  * test (`theWriterEncodesAsLeanEncodesOnTheFixpointRuns`, `git show
  * 2908bffd5:lambda_jit/strategies/src/test/scala/lambdajit/strategies/OpentheoryArticleFixpointRunsTest.scala`).
  * It compared one HOL term of the writer with Lean's; the writer's encoding
  * of a side is now a term over thunk constants with their definitions
  * (`OpentheoryArticle.termEncoded`, `ThunkDefinitions.NamedTerms`, 9f962cba6),
  * and its Lean program is to be rewritten to compare that form. It is not
  * ported here.
  *
  * The suite is in the module `strategies`, not `proofs`, because it runs
  * the strategy, and `strategies` depends on `proofs`; it reads the test
  * helpers of `proofs`.
  */
class OpentheoryArticleFixpointRunsTest extends gezi.generatedinputs.FailFastSuite:

  // Measured 2026-11-17 on 6 CPUs (contest.slice, CPUs 4 to 9, nice 10), the 1-minute load 2 to 4: the suite took
  // 298.8 s, the runs and their articles about 40 s and "leanChecksTheFixpointRunsWithTheBuiltInAxiomsOnly", whose
  // `lake build` rebuilt the three regenerated modules, about 259 s; the bound is 1.5 times that rounded up to 5 s.
  // Reason: it runs the Lean toolchain over the package, the kernel checking each run's article.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(390, "s")

  private lazy val library: StandardLibrary = StrategyTesting.compiled(FixpointRunModules.libraryFile)

  /** The library terms the programs are built from, by name. */
  private lazy val terms: Map[String, Instruction] =
    StandardLibrary.entryMembers(LibraryFiles.buildRoot, TermTables.jitLibraryTerms, Expansions.none)._1

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => library, _ => terms)

  private def term(key: String): Term =
    Term.closed(terms.getOrElse(key, throw IllegalArgumentException(s"no library term $key")))

  /** The program of the run, the HOAS term `FixpointRun.programText` writes
    * in the Prolog surface.
    */
  private def program(run: FixpointRun): Term = run.name match
    case "successor_zero"   => term("successor")(term("zero"))
    case "identity_zero"    => term("identity")(term("zero"))
    case "compose_redex"    => term("compose")(term("successor"))(term("successor"))(term("zero"))
    case "identity_closure" => λ(x => x)(term("zero"))
    case "twice_closure"    => λ(f => λ(a => f(f(a))))(term("successor"))(term("zero"))
    case other              => throw IllegalArgumentException(s"no program of the run $other")

  /** The round's search strategy (`fixpoint_strategy/2`). */
  private def fixpointStrategy(round: String): FixpointEgraph =
    FixpointEgraph(
      library.index,
      StandardSaturator(
        BaselineRounds.saturationOptions(
          library,
          StrategyTesting.round(FixpointRunModules.roundKey(round)),
          BuiltInRule.all,
          FixpointRunModules.roundBudget(round)
        )
      ),
      CountedExtractor(ExtractionOptions(Vector("specialization_attraction", "compression")), BaselineModules.table)
    )

  /** The run made: the program tagged, the round's strategy, and the article
    * the schedule's round writes (`Schedule.roundRan`: the proof's first
    * equation, written to a temporary file).
    */
  private def runMade(run: FixpointRun, stop: StopSignal): FixpointRunMade =
    val input = StrategyTesting.programInput(library, program(run))
    val outcome = fixpointStrategy(run.round)
      .ran(Vector(input), true, stop)
      .getOrElse(throw IllegalStateException(s"the strategy of ${run.base} gave no answer"))
    val output = outcome.outputs match
      case Vector(only) => only
      case other        => throw IllegalStateException(s"the strategy of ${run.base} gave ${other.size} outputs")
    val proof = outcome.proof.getOrElse(throw IllegalStateException(s"the strategy of ${run.base} gave no proof"))
    val first = proof.equations.headOption.getOrElse(throw IllegalStateException(s"the proof of ${run.base} proves no equation"))
    val firstProof = proof.copy(equations = Vector(first))
    val file = Files.createTempFile("fixpoint_run", ".art")
    OpentheoryArticle.written(library.index, input, output, firstProof, file)
    val article = ProofTestFiles.textRead(file)
    Files.delete(file)
    FixpointRunMade(input, output, article, RewriteTrace.lemmas(OpentheoryArticle.derivation(library.index, input, output, firstProof)))

  /** The lemma names of the identifiers, in the order of the Lean
    * statements of the library (`LeanStatements.names`).
    */
  private def lemmaNames(lemmas: Vector[LemmaIdentifier]): Vector[String] =
    val named = library.index.lemmaNames.collect { case LemmaNamed(identifier, name) if lemmas.contains(identifier) => name }.toSet
    gezi.proofs.LeanStatements.names(library).filter(named.contains)

  private def written(file: Path, text: String): Unit = Files.writeString(file, text)

  stoppableTest("theRunsWriteTheirExpectedArticlesAndTheirLeanModules") { stopped =>
    val made = FixpointRunModules.runs.map(run => (run, runMade(run, StopSignal.completedWith(stopped))))
    val fixtures = made.map((run, runMade) => FixpointFixture(run, lemmaNames(runMade.lemmas)))
    val encoded = made.map((run, runMade) => EncodedRun(run.base, runMade.input, runMade.output, "", ""))
    if sys.env.contains("GEZI_WRITE_FIXPOINT_RUNS") then
      made.foreach((run, runMade) => written(ProofTestFiles.expectedFile(run.base), runMade.article))
      written(ProofTestFiles.leanModules.resolve("ExpectedArticles.lean"), ExpectedArticlesModule.text)
      written(ProofTestFiles.leanModules.resolve("FixpointRunSides.lean"), FixpointRunModules.sidesText(encoded))
      written(ProofTestFiles.leanModules.resolve("FixpointRunFixtures.lean"), FixpointRunModules.fixturesText(fixtures))
      written(ProofTestFiles.leanModules.resolve("FixpointRunFixturesAxioms.lean"), FixpointRunModules.axiomsText(fixtures))
    made.foreach { (run, runMade) =>
      val text = runMade.article
      assertEquals((run.base, text), (run.base, ProofTestFiles.textRead(ProofTestFiles.expectedFile(run.base))))
      assertEquals((run.base, ProofTestFiles.textChecked(text)), (run.base, (0, "")))
      if text.split("\n", -1).contains("sym") then
        Vector(false, true).foreach { last =>
          val (status, errors) = ProofTestFiles.checkedWithoutSym(text, last)
          assertEquals((run.base, last, status), (run.base, last, 1))
          assert(errors.contains("terms not alpha-equivalent"), s"${run.base} without a sym: $errors")
        }
    }
    assertEquals(ProofTestFiles.textRead(ProofTestFiles.leanModules.resolve("ExpectedArticles.lean")), ExpectedArticlesModule.text)
    assertEquals(ProofTestFiles.textRead(ProofTestFiles.leanModules.resolve("FixpointRunSides.lean")), FixpointRunModules.sidesText(encoded))
    assertEquals(
      ProofTestFiles.textRead(ProofTestFiles.leanModules.resolve("FixpointRunFixtures.lean")),
      FixpointRunModules.fixturesText(fixtures)
    )
    assertEquals(
      ProofTestFiles.textRead(ProofTestFiles.leanModules.resolve("FixpointRunFixturesAxioms.lean")),
      FixpointRunModules.axiomsText(fixtures)
    )
  }

  // The package built, Lean run on the module FixpointRunFixturesAxioms:
  // every theorem it lists depends on Lean's built-in axioms only, and Lean
  // prints nothing else. The theorems are those the module lists, which the
  // test above checks to be its regeneration.
  stoppableTest("leanChecksTheFixpointRunsWithTheBuiltInAxiomsOnly") { stopped =>
    val axiomsModule = ProofTestFiles.leanModules.resolve("FixpointRunFixturesAxioms.lean")
    val theorems = ProofTestFiles.textRead(axiomsModule).split("\n").toVector.collect {
      case line if line.startsWith("#print axioms ") => line.stripPrefix("#print axioms ")
    }
    LeanFiniteTerms.lakeOutput(Seq("build"), stopped)
    val output = LeanFiniteTerms.lakeOutput(Seq("env", "lean", axiomsModule.toString), stopped)
    val normalised = ProofTestFiles.normalisedOutput(output)
    // Built-in axioms only, not all three: a theorem may need fewer, such as the
    // soundness of an article that imports no lemma, which needs propext alone.
    theorems.foreach(theorem =>
      assertEquals(
        (theorem, ProofTestFiles.printedAxioms(normalised, theorem).filterNot(ProofTestFiles.builtInAxioms.contains)),
        (theorem, Vector.empty)
      )
    )
    assertEquals(ProofTestFiles.otherOutput(normalised, theorems), "")
  }
