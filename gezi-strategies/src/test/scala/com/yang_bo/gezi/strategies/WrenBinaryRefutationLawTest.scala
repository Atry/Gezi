package com.yang_bo.gezi.strategies

import com.yang_bo.gezi.saturation.StopSignal
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.ir.Apply
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.saturation.End
import com.yang_bo.gezi.standardlibrary.LibraryFiles
import com.yang_bo.gezi.standardlibrary.StandardLibrary
import com.yang_bo.gezi.standardlibrary.TermTable
import com.yang_bo.gezi.weakhead.Expansions

/** The law of the binary naturals' refutations
  * (corpora/compiler/wren_binary_refutations.lambdalattice), on a generated
  * structure S of zero to four alternatives of zero to two fields each, a field
  * either a plain term or one refuted for the binary naturals: the candidacy
  * `candidate (binary_set true) (structure S)`, saturated to a fixed point
  * under the elimination preset's type check, has S refuted for
  * `binary_set true` exactly when S's shape is not the binary naturals' (three
  * alternatives, the first with no field and the other two with one field each)
  * or its second or third field is refuted. Derived before the run from the
  * lemmas: each mismatch lemma names one way a layer differs from the shape,
  * together they cover every other shape of at most four alternatives and two
  * fields, and the field lemmas carry a refuted field up; no lemma of the round
  * refutes a candidacy whose class holds no function type otherwise. Its
  * purpose is to catch a mismatch the lemmas miss and a refutation of the
  * binary naturals' own shape.
  */
class WrenBinaryRefutationLawTest extends GeneratedProperties:

  private given NoFacts.type = NoFacts

  // Measured 2026-11-25 on cores 6-11 (nice 10): the property's thirty samples, each one saturation of a type term
  // under the elimination preset's type check, with the library's compilation, take 33 s; the bound is about twice that.
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(60, "s")

  private lazy val library: StandardLibrary =
    LibraryFiles.compiled(
      "tests/library_fixtures/wren_elimination_preset.lambdalattice",
      Vector.empty
    )

  /** The budget of a run, in instances. */
  private val budget = 20000

  private lazy val options =
    BaselineRounds.saturationOptions(
      library,
      StrategyTesting.round("wren_elimination_type_check"),
      BuiltInRule.beforeOptIn,
      budget
    )

  private lazy val terms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary
      .entryMembers(
        LibraryFiles.buildRoot,
        TermTable(
          "tests/jit_fixtures/binary_refutation_terms.lambdalattice",
          Vector(
            "candidate",
            "refuted",
            "structure",
            "alternative",
            "no_alternative",
            "field",
            "no_field",
            "binary_set",
            "true",
            "zero"
          )
        ),
        Expansions.none
      )
      ._1

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => library, _ => options, _ => terms)

  private def term(key: String): StrategyTesting.ProgramTerm =
    Term.closed(
      terms.getOrElse(
        key,
        throw IllegalArgumentException(s"no fixture member $key")
      )
    )

  /** Whether each field of each alternative is refuted. */
  private type Shape = Vector[Vector[Boolean]]

  private val shape: Gen[Shape] =
    Gen
      .list(
        Gen.list(Gen.boolean, Range.linear(0, 2)).map(_.toVector),
        Range.linear(0, 4)
      )
      .map(_.toVector)

  /** The binary naturals' shape with no field refuted, which the generator also
    * draws on its own, since the law's other side is rare among the shapes
    * drawn at random.
    */
  private val binaryShape: Gen[Shape] =
    for
      even <- Gen.boolean
      odd <- Gen.boolean
    yield Vector(Vector.empty, Vector(even), Vector(odd))

  private def refutedExpected(drawn: Shape): Boolean =
    drawn.map(_.size) != Vector(0, 1, 1) || drawn.flatten.contains(true)

  private def criterion: StrategyTesting.ProgramTerm =
    term("binary_set")(term("true"))

  private def structureTerm(drawn: Shape): StrategyTesting.ProgramTerm =
    val alternatives = drawn.foldRight(term("no_alternative"))((fields, rest) =>
      val written = fields.foldRight(term("no_field"))((refuted, others) =>
        term("field")(if refuted then term("refuted")(criterion)(term("zero"))
        else term("zero"))(others)
      )
      term("alternative")(written)(rest)
    )
    term("structure")(alternatives)

  /** Whether the graph holds `refuted (binary_set true) X`, X the class of the
    * candidacy's structure.
    */
  private def refutedStructure(
      graph: EGraph[NoFacts.type],
      input: Configured[NoFacts.type]
  ): Boolean =
    def applications(node: Int): Vector[(Int, Int)] =
      graph.classMembers(node).map(_.layer).collect {
        case Apply(function, argument) =>
          (graph.root(function), graph.root(argument))
      }
    val refutedClass = graph.instructionNode(terms("refuted")).map(graph.root)
    val candidateClass =
      graph.instructionNode(terms("candidate")).map(graph.root)
    val criterionClass = graph
      .instructionNode(
        Defunctionalization.thunkInstruction[com.yang_bo.gezi.ir.NoFacts.type](
          criterion.deBruijnTerm(Map.empty)
        )(using com.yang_bo.gezi.ir.NoFacts)
      )
      .map(graph.root)
    val structureClass = (
      graph.instructionNode(input).map(graph.root),
      candidateClass,
      criterionClass
    ) match
      case (Some(root), Some(candidate), Some(binary)) =>
        applications(root).collectFirst {
          case (partial, structure)
              if applications(partial).contains((candidate, binary)) =>
            structure
        }
      case _ => None
    (refutedClass, structureClass, criterionClass) match
      case (Some(refuted), Some(structure), Some(binary)) =>
        (0 until graph.nodeCount).exists(node =>
          graph.root(node) == node && applications(node).exists(
            (partial, argument) =>
              argument == structure && applications(partial).exists(
                (head, found) => head == refuted && found == binary
              )
          )
        )
      case _ => false

  stoppableProperty(
    "a binary candidacy is refuted exactly when its structure's shape is not the binary naturals' or a field is refuted",
    _.copy(testLimit = SuccessCount(30))
  ) { stopped =>
    for drawn <- Gen.frequency1(1 -> shape, 1 -> binaryShape).forAll
    yield
      val input = Defunctionalization.thunkInstruction[com.yang_bo.gezi.ir.NoFacts.type](
        (term("candidate")(criterion)(structureTerm(drawn)))
          .deBruijnTerm(Map.empty)
      )(using com.yang_bo.gezi.ir.NoFacts)
      val saturated = FixpointEgraph.saturated(
        library.index,
        Vector(input),
        options,
        explained = false,
        StopSignal.completedWith(stopped)
      )
      Result.all(
        List(
          Result
            .assert(saturated.end.isInstanceOf[End.FixedPoint])
            .log(s"the run ended ${saturated.end}"),
          Result
            .assert(
              refutedStructure(saturated.graph, input) == refutedExpected(drawn)
            )
            .log(
              s"shape $drawn: refuted ${refutedStructure(saturated.graph, input)}, expected ${refutedExpected(drawn)}"
            )
        )
      )
  }
