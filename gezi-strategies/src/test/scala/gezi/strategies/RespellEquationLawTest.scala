package gezi.strategies

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.ir.BindingNormalForm
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.egraph.EGraph
import gezi.egraph.Justification
import gezi.frontend.Lambdalattice
import gezi.ir.LemmaIdentifier
import gezi.ir.Store
import gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import gezi.proofs.OpentheoryArticle
import gezi.proofs.RewriteReason
import gezi.proofs.RewriteTrace
import gezi.rewritetrace.ReplaySpelling
import gezi.rewritetrace.Statements
import gezi.standardlibrary.LemmaSides
import gezi.standardlibrary.StandardLibraryIndex

/** The law of the respelling equation (`Statements.respell`), the import axiom
  * `Axiom.Respell` of an article: on the thunk the defunctionalized β rule
  * leaves when it fills the first hole of a generated lambda of several binders
  * (`ResidualPrograms`), the instance of the equation's right side under the
  * bindings its left side has in the thunk has the thunk's spelling, and the
  * instance of the left side under the bindings the right side has in that is
  * the thunk again. Every generated residual is not its own spelling, and the
  * law asserts it, so that it checks the equation on every sample.
  *
  * Purpose: catch an equation whose two sides read back to different terms (a
  * filling's variable planted at the wrong place of the spelling, a placeholder
  * left in it), which would make the import axiom unsound, and one that does
  * not invert. The front end's spelling of a term is a function of the term it
  * reads back to, so equal spellings are equal readbacks. A trace has no
  * command of the equation: it replays in the e-graph's spelling, where the
  * equation is an identity (`ReplaySpelling`).
  */
class RespellEquationLawTest extends GeneratedProperties:

  given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  given gezi.ir.NoFacts.type = gezi.ir.NoFacts

  property("the respelling equation keeps the spelling and inverts") {
    for
      thunk <- ResidualPrograms.thunks.forAll
      argument <- HoasGenerators.instruction.forAll
    yield
      val residual = ResidualPrograms.residual(thunk, argument)
      residual.layer match
        case gezi.ir.Thunk(code, holes, fillings)
            if holes.nonEmpty && BindingNormalForm
              .respelled(code, holes, fillings.size)
              .nonEmpty =>
          val equation = Statements.respell(code, holes)
          val forward = Statements.instance(
            equation.right,
            Statements.bindings(equation.left, residual)
          )
          val backward = Statements.instance(
            equation.left,
            Statements.bindings(equation.right, forward)
          )
          Result
            .assert(
              Configured.same(
                BindingNormalForm.spelled(forward),
                BindingNormalForm.spelled(residual)
              )
            )
            .log(
              s"the spelling of $residual is ${BindingNormalForm.spelled(residual)}, of its respelling $forward"
            )
            .and(Result.diff(backward, residual)(Configured.same(_, _)))
        case other =>
          Result.failure.log(
            s"the generated residual $other is its own spelling: the generator drifted"
          )
  }

  private def closed(text: String): Configured[NoFacts.type] =
    Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](
      Lambdalattice.term(text)
    )(using gezi.ir.NoFacts)

  /** A lemma sound by the β rule alone whose left side is stated in another
    * spelling than the front end gives its instances: `λz. k a` is a thunk
    * whose fillings are k and a, while the front end spells `λz. f a`, f and a
    * closed, as a thunk of the one filling `f a`.
    */
  private val unspelledSideLemma: LemmaSides[NoFacts.type] =
    LemmaSides(
      LemmaIdentifier(0),
      closed("λk. λa. (λy. y) (λz. k a)"),
      closed("λk. λa. λz. k a")
    )

  private val unspelledSideIndex: StandardLibraryIndex[NoFacts.type] =
    StandardLibraryIndex(
      NoFacts,
      Vector.empty,
      Vector(unspelledSideLemma),
      Vector.empty,
      Vector.empty
    )

  /** Purpose: catch an article writer that cannot derive a lemma instance whose
    * side is stated in another spelling than the graph's node it was matched at
    * (a respelled orientation makes such matches), or that derives it by an
    * equation the OpenTheory tool rejects. On a graph built by hand, the
    * program `(λy. y) (λz. f a)` in the front end's spelling united with the
    * lemma's right side under k := f, a := a as an instance of the lemma, the
    * article of the program's equation to that instance takes a respelling step
    * (`Axiom.Respell`, through `ProofMatching`'s thunk candidate of the
    * respelled pattern), the tool accepts it, and the trace replays to the
    * instance's replay spelling. Without the respelling alternative the writer
    * throws `InstanceNotMatched`.
    */
  property(
    "an instance stated in another spelling than its matched node is derived through the respelling equation"
  ) {
    for
      function <- HoasGenerators.closedTerm.forAll
      argument <- HoasGenerators.closedTerm.forAll
    yield
      val functionInstruction =
        Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](
          function.deBruijnTerm(Map.empty)
        )(using gezi.ir.NoFacts)
      val argumentInstruction =
        Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](
          argument.deBruijnTerm(Map.empty)
        )(using gezi.ir.NoFacts)
      val input = Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](
        Term
          .λ(bound => bound)(Term.λ(_ => function(argument)))
          .deBruijnTerm(Map.empty)
      )(using gezi.ir.NoFacts)
      val output = Statements.instance(
        Statements
          .lemma(unspelledSideLemma.left, unspelledSideLemma.right)
          .right,
        Map(
          "metavariable0" -> functionInstruction,
          "metavariable1" -> argumentInstruction
        )
      )
      val (withInput, inputNode) = EGraph
        .empty(
          Store(
            noinline = Set.empty,
            gezi.ir.TermConstruction(gezi.ir.NoFacts)
          ),
          Map.empty,
          explained = true
        )
        .instructionAdded(input)
      val (withOutput, outputNode) = withInput.instructionAdded(output)
      val (withFunction, functionNode) =
        withOutput.instructionAdded(functionInstruction)
      val (withArgument, argumentNode) =
        withFunction.instructionAdded(argumentInstruction)
      val graph = withArgument.unionWorked(
        inputNode,
        outputNode,
        Justification.Lemma(
          unspelledSideLemma.lemma,
          Vector(Some(functionNode), Some(argumentNode))
        ),
        None
      )
      val proof = GraphProof.proof(
        graph,
        Vector((input, output)),
        Vector(
          BaselineLemmaEncoding.encoded(unspelledSideIndex, unspelledSideLemma)
        )
      )
      val derivation =
        OpentheoryArticle.derivation(unspelledSideIndex, input, output, proof)
      val respellings = RewriteTrace
        .of(derivation)
        .count(_.reason match
          case RewriteReason.Respell(_, _, _) => true
          case _                              => false)
      val article =
        java.nio.file.Files.createTempFile("respelled_instance", ".art")
      val checked =
        try
          OpentheoryArticle.written(
            unspelledSideIndex,
            input,
            output,
            proof,
            article
          )
          gezi.proofs.ProofTestFiles.toolChecked(article)
        finally java.nio.file.Files.delete(article)
      Result.all(
        List(
          Result
            .assert(respellings > 0)
            .log(
              "the derivation takes no respelling step: the fixture drifted"
            ),
          Result
            .diff(checked, (0, ""))(_ == _)
            .log("the OpenTheory tool's exit status and standard error"),
          Result
            .assert(
              RewriteTrace.trace(derivation).output(input) eq ReplaySpelling
                .term(output)
            )
            .log("the trace does not replay to the instance")
        )
      )
  }
