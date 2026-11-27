package gezi.extraction

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.egraph.EGraph
import gezi.egraph.Justification
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Code
import gezi.ir.DispatchPattern
import gezi.ir.Hole
import gezi.ir.Configured
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.ir.NoFacts
import gezi.ir.NonEmptyHoles
import gezi.ir.Store
import gezi.ir.Choice

/** The laws that the extraction's dispatch patterns and the refinement's are
  * one recognition (`DispatchPattern`), on generated graphs. A graph starts
  * from a few noinline leaves and a closure whose spelling is λf. f, and takes
  * a generated sequence of steps: an instruction added (an application, a
  * parallel, a choice, a specialization choice `F A + T` of each kind of typed
  * member, or a judgment `X + (X ∥ T)`, over instructions added before), or two
  * nodes united. The refinement reads an instruction as its own layer, a
  * noinline leaf as none, and no instruction as a contract
  * (`gezi.jit.StrategyDispatch`), which is the view the laws read instructions
  * with; the curried specialization choice is generated so that both read it as
  * a plain choice.
  *
  * (1) In a graph with no union, where a class is read as the one layer of its
  * instruction, the patterns the extraction makes of each choice node
  * (`Extraction.dispatchShapes`) are those the refinement reads off the node's
  * instruction, part for part through the classes. (2) In every graph, a
  * pattern production spelled over instructions of its parts' classes
  * (`Shape.spelled`) is an instruction the refinement reads first as that
  * pattern over those instructions, so that what the extraction prices as a
  * pattern is dispatched as one. Their purpose is to catch a view of classes or
  * of instructions that reads other layers than the other, and a spelling of a
  * pattern that the refinement does not read back, or reads as another pattern.
  */
class DispatchPatternLawTest extends GeneratedProperties:

  private type C = NoFacts.type

  private given NoFacts.type = NoFacts

  private val lemma = Justification.Lemma(LemmaIdentifier(0), Vector.empty)

  /** λf. λy. f y: a thunk of two holes whose code applies the first to the
    * second.
    */
  private val identity =
    NoFacts.thunk(
      Code.Apply(Code.Slot(0), Code.Slot(1)),
      NonEmptyHoles(Hole.Bound(0), Vector(Hole.Bound(1))),
      Vector.empty
    )

  /** A step of a generated graph; the numbers pick among the instructions or
    * the nodes made so far, modulo their count.
    */
  private enum Step:
    case Applied(function: Int, argument: Int)
    case Paralleled(left: Int, right: Int)
    case Chosen(left: Int, right: Int)
    case Specialized(
        function: Int,
        argument: Int,
        domain: Int,
        range: Int,
        kind: Int,
        untypedFirst: Boolean
    )
    case Judged(value: Int, criterion: Int, valueFirst: Boolean)
    case United(first: Int, second: Int)

  private val index = Gen.int(Range.linear(0, 1000))

  private def step(unions: Boolean): Gen[Step] =
    val made = List(
      for function <- index; argument <- index
      yield Step.Applied(function, argument),
      for left <- index; right <- index yield Step.Paralleled(left, right),
      for left <- index; right <- index yield Step.Chosen(left, right),
      for
        function <- index; argument <- index; domain <- index; range <- index
        kind <- Gen.int(Range.linear(0, 2)); untypedFirst <- Gen.boolean
      yield Step
        .Specialized(function, argument, domain, range, kind, untypedFirst),
      for value <- index; criterion <- index; valueFirst <- Gen.boolean
      yield Step.Judged(value, criterion, valueFirst)
    )
    val united = for first <- index; second <- index
    yield Step.United(first, second)
    val choices = if unions then made :+ united else made
    Gen.choice1(choices.head, choices.tail*)

  private final case class Generated(
      graph: EGraph[C],
      instructions: Vector[Configured[C]],
      store: Store[C]
  )

  private def generated(leafCount: Int, steps: List[Step]): Generated =
    val leaves =
      Vector.tabulate(leafCount)(number => NoFacts.opaque(s"leaf$number"))
    val store =
      Store(noinline = leaves.toSet, gezi.ir.TermConstruction(NoFacts))
    val empty = EGraph.empty(store, Map.empty, explained = false)
    val start =
      (leaves :+ identity).foldLeft(Generated(empty, Vector.empty, store))(
        (current, instruction) =>
          Generated(
            current.graph.instructionAdded(instruction)._1,
            current.instructions :+ instruction,
            store
          )
      )
    steps.foldLeft(start)((current, step) =>
      def instruction(number: Int): Configured[C] =
        current.instructions(number % current.instructions.size)
      def added(instruction: Configured[C]): Generated =
        Generated(
          current.graph.instructionAdded(instruction)._1,
          current.instructions :+ instruction,
          store
        )
      step match
        case Step.Applied(function, argument) =>
          added(
            NoFacts.application(instruction(function), instruction(argument))
          )
        case Step.Paralleled(left, right) =>
          added(NoFacts.parallel(instruction(left), instruction(right)))
        case Step.Chosen(left, right) =>
          added(NoFacts.choice(instruction(left), instruction(right)))
        case Step.Specialized(
              function,
              argument,
              domain,
              range,
              kind,
              untypedFirst
            ) =>
          val untyped =
            NoFacts.application(instruction(function), instruction(argument))
          val application = NoFacts.application(
            instruction(function),
            NoFacts.parallel(instruction(argument), instruction(domain))
          )
          val typed = kind match
            case 0 => application
            case 1 => NoFacts.parallel(application, instruction(range))
            case _ => NoFacts.application(identity, application)
          added(if untypedFirst then NoFacts.choice(untyped, typed)
          else NoFacts.choice(typed, untyped))
        case Step.Judged(value, criterion, valueFirst) =>
          val filtered =
            NoFacts.parallel(instruction(value), instruction(criterion))
          added(if valueFirst then NoFacts.choice(instruction(value), filtered)
          else NoFacts.choice(filtered, instruction(value)))
        case Step.United(first, second) =>
          val nodes = current.graph.nodeCount
          current.copy(graph =
            current.graph
              .unionWorked(first % nodes, second % nodes, lemma, None)
          )
    )

  /** The refinement's view of an instruction: its layer, a noinline leaf having
    * none.
    */
  private def instructionLayers(
      store: Store[C]
  )(instruction: Configured[C]): Vector[Layer[Configured[C]]] =
    if store.noinline.contains(instruction) then Vector.empty
    else Vector(store.expanded(instruction))

  /** The terms under the roots, the roots included, each once; no term of the
    * test holds a storage or an opaque layer but the leaves.
    */
  private def termsUnder(roots: Iterable[Configured[C]]): Set[Configured[C]] =
    @scala.annotation.tailrec
    def walked(
        pending: List[Configured[C]],
        seen: Set[Configured[C]]
    ): Set[Configured[C]] = pending match
      case Nil                         => seen
      case term :: rest if seen(term)  => walked(rest, seen)
      case term :: rest if term.opaque => walked(rest, seen + term)
      case term :: rest                =>
        walked(term.layer.children.toList ::: rest, seen + term)
    walked(roots.toList, Set.empty)

  private def patternShapes(graph: EGraph[C]): Vector[Shape[C]] =
    Extraction.productions(graph, Set.empty)._1.map(_.shape).filter {
      case Shape.Specialized(_, _) | Shape.Judged(_, _) => true
      case _                                            => false
    }

  property(
    "with no union, the extraction's patterns of a choice are the refinement's of its instruction"
  ) {
    for
      leafCount <- Gen.int(Range.linear(1, 3)).forAll
      steps <- step(unions = false).list(Range.linear(0, 30)).forAll
    yield
      val Generated(graph, instructions, store) = generated(leafCount, steps)
      val layers = instructionLayers(store)
      def classOf(instruction: Configured[C]): Int =
        graph.root(graph.instructionNode(instruction).get)
      val expected = instructions.distinct.flatMap(instruction =>
        layers(instruction) match
          case Vector(Choice(left, right)) =>
            val node = graph.instructionNode(instruction).get
            DispatchPattern
              .specializations(left, right, layers, DispatchPattern.noContract)
              .map(found =>
                Shape.Specialized[C](node, found.map(classOf))
              ) ++ DispatchPattern
              .fallbacks(left, right, layers)
              .map(found =>
                Shape.Judged[C](
                  node,
                  found.copy(
                    value = classOf(found.value),
                    criterion = classOf(found.criterion)
                  )
                )
              )
          case _ => Vector.empty
      )
      Result
        .assert(patternShapes(graph).toSet == expected.toSet)
        .log(s"steps: $steps")
  }

  property(
    "a pattern production spelled over its parts' instructions is read back as that pattern"
  ) {
    for
      leafCount <- Gen.int(Range.linear(1, 3)).forAll
      steps <- step(unions = true).list(Range.linear(0, 30)).forAll
    yield
      val Generated(graph, instructions, store) = generated(leafCount, steps)
      val layers = instructionLayers(store)
      val representative = (instructions ++ termsUnder(instructions))
        .flatMap(instruction =>
          graph
            .instructionNode(instruction)
            .map(node => (graph.root(node), instruction))
        )
        .toMap
      val misread = patternShapes(graph).flatMap { shape =>
        val parts = shape.children.map(representative)
        val spelled = Shape.spelledTerm(shape, parts)
        val Vector(Choice(left, right)) = layers(spelled): @unchecked
        val readBack = DispatchPattern
          .specializations(left, right, layers, DispatchPattern.noContract)
          .headOption match
          case Some(found) => Some(found.parts)
          case None        =>
            DispatchPattern
              .fallbacks(left, right, layers)
              .headOption
              .map(_.parts)
        val kept = shape match
          case Shape.Specialized(_, specialization) =>
            readBack.contains(parts) &&
            DispatchPattern
              .specializations(left, right, layers, DispatchPattern.noContract)
              .headOption
              .exists(found =>
                found.range.getClass == specialization.range.getClass && found.untypedFirst == specialization.untypedFirst
              )
          case Shape.Judged(_, fallback) =>
            val Vector(value, criterion) = parts: @unchecked
            DispatchPattern
              .specializations(left, right, layers, DispatchPattern.noContract)
              .isEmpty &&
            DispatchPattern
              .fallbacks(left, right, layers)
              .headOption
              .contains(fallback.copy(value = value, criterion = criterion))
          case _ => false
        if kept then None else Some((shape, parts, readBack))
      }
      Result
        .assert(misread.isEmpty)
        .log(s"misread: $misread")
        .log(s"steps: $steps")
  }
