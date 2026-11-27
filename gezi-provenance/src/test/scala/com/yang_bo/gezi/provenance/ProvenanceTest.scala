package com.yang_bo.gezi.provenance

import hedgehog.Gen
import hedgehog.Result
import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.egraph.Justification
import com.yang_bo.gezi.ematching.closures.ClosureCompilation
import com.yang_bo.gezi.ematching.indexing.Indexing
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.FreeNames
import com.yang_bo.gezi.frontend.Lambdalattice
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.generatedinputs.LambdalatticeText
import com.yang_bo.gezi.generatedinputs.SeededSnapshots
import com.yang_bo.gezi.extraction.CostModel
import com.yang_bo.gezi.extraction.StatelessCostModel
import com.yang_bo.gezi.extraction.CountedExtraction
import com.yang_bo.gezi.extraction.Extraction
import com.yang_bo.gezi.extraction.Shape
import com.yang_bo.gezi.extraction.Spelled
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.CodeLayer
import com.yang_bo.gezi.ir.Direction
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.LemmaIdentifier
import com.yang_bo.gezi.ir.Pattern
import com.yang_bo.gezi.ir.Store
import com.yang_bo.gezi.orientation.Orientation
import com.yang_bo.gezi.orientation.Orientations
import com.yang_bo.gezi.locations.Location
import com.yang_bo.gezi.locations.SourceMap
import com.yang_bo.gezi.saturation.Saturation
import com.yang_bo.gezi.saturation.StopSignal
import scala.jdk.StreamConverters.*
import snapshot4s.generated.snapshotConfig
import com.yang_bo.gezi.ir

/** The provenance of the nodes of a graph saturated by the β rule and one lemma
  * from the text of a generated closed term (`Provenance.of`).
  *
  *   - Law: every β union names a thunk node (`Justification.Beta`); and every
  *     location an input gives a node is a span of the text that reads, alone,
  *     to the node's instruction. Its purpose is to catch a β union recorded
  *     with another node than its closure state's thunk, and an input's map
  *     aligned with other nodes than its instructions'.
  *   - Law: the map of the input's class spelled by an extraction
  *     (`Provenance.shapeMap`, `Provenance.extracted`) has the shape of the
  *     instruction spelled, and every `Source` location of one of its places
  *     reads to a term of the class spelled there. Its purpose is to catch a
  *     map of another shape than the extracted instruction, which would put a
  *     location on another place, and a place given another class's locations.
  *   - Snapshot: each node's layer and locations, β bodies' nodes `Inlined`
  *     from the code of their thunk at the application, from a fixed seed. Its
  *     purpose is to record how the β walk locates a body, an output as complex
  *     as the walk.
  */
class ProvenanceTest extends GeneratedProperties with SeededSnapshots:

  private type C = NoFacts.type

  private given NoFacts.type = NoFacts

  private val uri: java.net.URI =
    java.net.URI.create("file:///generated.lambdalattice")

  private val application: Pattern[C] =
    Pattern.Apply(Pattern.Metavariable[C](0), Pattern.Metavariable[C](1))

  /** The choice's idempotence read backward, M N = M N + M N (a theorem of the
    * λ-lattice laws): its added side applies the function metavariable M, so
    * that the β rule reads the applications it builds, an input's included, and
    * β bodies' applications in turn.
    */
  private val idempotence: Orientation[C] = Orientation(
    index = 0,
    lemma = LemmaIdentifier(0),
    direction = Direction.Forward,
    arity = 2,
    matched = application,
    added = Pattern.Choice(application, application),
    functions = Vector(0),
    essential = Vector.empty,
    shared = Vector(application)
  )

  /** The graph saturated from the text by the idempotence and the β rule,
    * within 200 instances, and the provenance of its nodes.
    */
  private def saturated(
      text: String,
      stop: StopSignal
  ): (EGraph[C], Provenance) =
    val (graph, provenance, _) = saturatedWithInput(text, stop)
    (graph, provenance)

  /** `saturated`, with the instruction read from the text. */
  private def saturatedWithInput(
      text: String,
      stop: StopSignal
  ): (EGraph[C], Provenance, Configured[C]) =
    val read = Lambdalattice.located(text, FreeNames.Rejected)
    val (instruction, map) =
      Defunctionalization.locatedThunkInstruction(read.term, read.spans, uri)(
        using com.yang_bo.gezi.ir.NoFacts
      )
    val program = Indexing.program(
      Vector(idempotence),
      Indexing.codesMet(Vector(idempotence), Vector(instruction))
    )
    val run = Saturation.run(
      program,
      ClosureCompilation.compiled(program),
      BuiltInRule.beforeOptIn,
      Store(Set.empty[Configured[C]], com.yang_bo.gezi.ir.TermConstruction(NoFacts)),
      Orientations.headArityBounds(Vector(idempotence)),
      Vector.empty,
      Vector(instruction),
      budget = 200,
      explained = false,
      stop
    )
    val lemmas = Map(
      idempotence.lemma -> (idempotence.matched, idempotence.added)
    )
    (
      run.graph,
      Provenance.of(
        run.graph,
        Vector(Provenance.Input(instruction, map)),
        lemmas
      ),
      instruction
    )

  /** A closed term applied to a closed term, so that the β rule has a redex. */
  private val texts: Gen[String] =
    for
      function <- HoasGenerators.closedTerm
      argument <- HoasGenerators.closedTerm
    yield s"(${LambdalatticeText.text(function)}) (${LambdalatticeText.text(argument)})"

  stoppableProperty(
    "β unions name thunks, and an input's locations read back to their nodes"
  ) { stopped =>
    texts
      .forAllWithLog(identity)
      .map(text =>
        val (graph, provenance) =
          saturated(text, StopSignal.completedWith(stopped))
        val codePoints = text.codePoints.toScala(Vector).map(_.toInt)
        val thunks = graph.unions.flatMap(union =>
          union.justification match
            case Justification.Beta(thunk) =>
              graph.layer(thunk) match
                case ir.Thunk(_, _, _) => Vector.empty
                case other             =>
                  Vector(s"the β union $union names a node of $other")
            case _ => Vector.empty
        )
        val readBack = (0 until graph.nodeCount).toVector.flatMap(node =>
          graph
            .nodeInstruction(node)
            .toVector
            .flatMap(instruction =>
              provenance
                .node(node)
                .toVector
                .collect { case Location.Source(_, span) =>
                  val written = span.of(codePoints)
                  val read = scala.util
                    .Try(
                      Defunctionalization.thunkInstruction(
                        Lambdalattice.term(written)
                      )(using com.yang_bo.gezi.ir.NoFacts)
                    )
                    .toOption
                  if read.exists(Configured.same(_, instruction)) then None
                  else Some(s"node $node: `$written` reads another term")
                }
                .flatten
            )
        )
        val problems = thunks ++ readBack
        Result.assert(problems.isEmpty).log(problems.mkString("\n"))
      )
  }

  /** The cost of a spelling is its number of layers and names. */
  private object Size extends StatelessCostModel[C, Int]:
    def cost(shape: Shape[C], childCosts: Vector[Int]): Int = 1 + childCosts.sum
    val ordering: Ordering[Int] = Ordering.Int
    def pricedChildren(shape: Shape[C]): Vector[Boolean] =
      shape.children.map(_ => true)

  /** The instruction of a shape over its children's, as an extraction's caller
    * spells it.
    */
  private def shapeInstruction(
      shape: Shape[C],
      children: Vector[Configured[C]]
  ): Configured[C] =
    Shape.spelledTerm(shape, children)

  /** Where the map does not have the shape of the instruction, its code map
    * that of the code included.
    */
  private def shapeProblems(
      instruction: Configured[C],
      map: SourceMap
  ): Vector[String] =
    if map.bare then Vector.empty
    else
      val code = (instruction.layer, map.code) match
        case (ir.Thunk(code, holes, fillings), Some(codeMap)) =>
          codeShapeProblems(
            code,
            codeMap,
            Defunctionalization.slotValues(
              holes,
              Vector.fill(holes.size)(SlotValue.Hole),
              fillings.map(SlotValue.Filling(_))
            )
          )
        case (_, None)        => Vector.empty
        case (layer, Some(_)) => Vector(s"a code map on $layer")
      val children =
        if instruction.layer.children.size != map.children.size then
          Vector(s"${map.children.size} maps under ${instruction.layer}")
        else instruction.layer.children.zip(map.children).flatMap(shapeProblems)
      code ++ children

  /** What a code's slot reads, as far as the check follows it: a hole, a
    * filling of the thunk, or a filling of an inner thunk that is no slot.
    */
  private enum SlotValue:
    case Hole
    case Filling(instruction: Configured[C])
    case Unfollowed

  /** Where a code's map does not have the code's shape; a slot's place is a
    * leaf where it reads a hole and has the shape of the filling where it reads
    * one.
    */
  private def codeShapeProblems(
      code: Code,
      map: SourceMap,
      slots: Vector[SlotValue]
  ): Vector[String] =
    if map.bare then Vector.empty
    else
      code.layer match
        case ir.Apply(function, argument) =>
          sidesProblems(Vector(function, argument), map, slots)
        case ir.Choice(left, right) =>
          sidesProblems(Vector(left, right), map, slots)
        case ir.Parallel(left, right) =>
          sidesProblems(Vector(left, right), map, slots)
        case ir.Thunk(inner, holes, fillings) =>
          val innerSlots = Defunctionalization.slotValues(
            holes,
            Vector.fill(holes.size)(SlotValue.Hole),
            fillings.map(filling =>
              filling.layer match
                case ir.Slot(slot) =>
                  slots.lift(slot).getOrElse(SlotValue.Unfollowed)
                case _ => SlotValue.Unfollowed
            )
          )
          val innerProblems = map.code.fold(Vector.empty[String])(
            codeShapeProblems(inner, _, innerSlots)
          )
          if map.children.size == fillings.size then innerProblems
          else
            innerProblems :+ s"${map.children.size} maps under the fillings of $code"
        case ir.Slot(slot) =>
          slots.lift(slot) match
            case Some(SlotValue.Filling(filling)) => shapeProblems(filling, map)
            case Some(SlotValue.Unfollowed)       => Vector.empty
            case _ => Vector(s"a map below $code")

  private def sidesProblems(
      sides: Vector[Code],
      map: SourceMap,
      slots: Vector[SlotValue]
  ): Vector[String] =
    if map.code.isDefined || map.children.size != sides.size then
      Vector(s"a map of another shape under $sides")
    else sides.zip(map.children).flatMap(codeShapeProblems(_, _, slots))

  stoppableProperty(
    "an extracted spelling's map has its shape, and its places' spans read to their classes"
  ) { stopped =>
    texts
      .forAllWithLog(identity)
      .map(text =>
        val (graph, provenance, instruction) =
          saturatedWithInput(text, StopSignal.completedWith(stopped))
        val codePoints = text.codePoints.toScala(Vector).map(_.toInt)
        val root = graph
          .instructionNode(instruction)
          .fold(fail(s"the input $instruction has no node"))(graph.root)
        val extracted = CountedExtraction
          .fixed(graph, Set.empty, Size, StopSignal.completedWith(stopped))
          .getOrElse(fail("the extraction was stopped"))
        type Pair = (Configured[C], SourceMap)
        val (state, (spelling, map)) =
          Extraction.spelled(
            extracted,
            root,
            Spelled[Pair, Vector[String]](Vector.empty, Map.empty)
          )((problems, shape, children) =>
            val map = provenance.shapeMap(graph, shape, children.map(_._2))
            val classRoot =
              shape match
                case Shape.Node(node, _)        => Some(graph.root(node))
                case Shape.Specialized(node, _) => Some(graph.root(node))
                case Shape.Judged(node, _)      => Some(graph.root(node))
                case Shape.Name(instruction)    =>
                  graph.instructionNode(instruction).map(graph.root)
            val misread =
              map.locations.toVector.collect { case Location.Source(_, span) =>
                val written = span.of(codePoints)
                val read = scala.util
                  .Try(
                    Defunctionalization.thunkInstruction(
                      Lambdalattice.term(written)
                    )(using com.yang_bo.gezi.ir.NoFacts)
                  )
                  .toOption
                val readClass =
                  read.flatMap(graph.instructionNode).map(graph.root)
                if readClass.isDefined && readClass == classRoot then None
                else Some(s"`$written` reads outside the class $classRoot")
              }.flatten
            (
              problems ++ misread,
              (shapeInstruction(shape, children.map(_._1)), map)
            )
          )
        val aligned =
          if provenance.extracted(graph, extracted, Vector(root)) == Vector(map)
          then Vector.empty
          else Vector("Provenance.extracted spells another map")
        val problems =
          state.accumulator ++ shapeProblems(spelling, map) ++ aligned
        Result.assert(problems.isEmpty).log(problems.mkString("\n"))
      )
  }

  stoppableTest(
    "the locations of the nodes of graphs saturated by the β rule"
  ) { stopped =>
    assertSeededSnapshot(texts, 20261112L, 8, "provenance/beta_locations.txt")(
      identity,
      (lines: Vector[String]) => lines.mkString("\n")
    )(text =>
      val (graph, provenance) =
        saturated(text, StopSignal.completedWith(stopped))
      (0 until graph.nodeCount).toVector.map(node =>
        val kind = graph.layer(node).getClass.getSimpleName.toLowerCase
        val written = provenance
          .node(node)
          .toVector
          .map(_.written.replace(uri.toString, ""))
          .sorted
        s"node $node $kind: ${written.mkString(" ; ")}"
      )
    )
  }
