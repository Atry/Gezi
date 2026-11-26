package gezi.egraph

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.ir.BindingNormalForm
import gezi.ir.CodeLayer
import gezi.ir.Code
import gezi.ir.Instruction
import gezi.ir.Hole
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.ir.Store
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.StateMachine
import scala.annotation.tailrec
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Slot, Thunk}

/** A command of the e-graph's state machine test. Terms are named by their
  * position among the terms added so far, the position the command that
  * added them had among the additions.
  */
enum GraphCommand:

  /** Add a noinline instruction, a leaf, through `instructionAdded`, which files its
    * head when a matched side is headed by it.
    */
  case AddInstruction(instruction: Instruction)

  /** Add one layer over terms already added, through `layerAdded`. */
  case AddLayer(layer: Layer[Int])

  /** Unite the classes of two terms already added, through `unionWorked`;
    * the unions of congruence it causes wait on the agenda.
    */
  case Union(first: Int, second: Int)

  /** Work the agenda's unions until none is left. */
  case RunAgenda

/** The model: the terms added, each a layer over the positions of earlier
  * terms, the unions asked for, and whether the agenda has run since the
  * last union.
  */
final case class GraphModel(
    terms: Vector[Layer[Int]],
    unions: Vector[(Int, Int)],
    agendaRun: Boolean
):

  /** The class of each term, named by the smallest position in it: the
    * congruence closure of the unions over the terms in the front end's
    * spelling (`spelledTerms`), recomputed from scratch by naive iteration.
    * The unions are made first; then, until a whole pass merges nothing, any
    * two terms of the same constructor, with the same code, holes or instruction,
    * whose children are pairwise in the same class, are merged.
    */
  def classes: Vector[Int] =
    val spelled = spelledTerms
    val united = unions.foldLeft(spelled.indices.toVector)((labels, pair) =>
      merged(labels, pair._1, pair._2)
    )
    closed(spelled, united).take(terms.size)

  /** The terms with each thunk in the front end's spelling, the fixed input
    * step of the model: a thunk with holes that `BindingNormalForm.respelled`
    * respells is replaced by its respelling, whose fillings are new terms
    * after the added ones, made by the fold the graph makes them with
    * (`BindingNormalForm.placeholdersFolded`), each placeholder the drawn
    * thunk's filling. A new term has a position above every added term, so
    * the smallest position of a class that holds an added term is an added
    * term's.
    */
  private def spelledTerms: Vector[Layer[Int]] =
    terms.indices.foldLeft(terms)((current, position) =>
      current(position) match
        case Thunk(code, holes, fillings) if holes.nonEmpty =>
          BindingNormalForm.respelled(code, holes, fillings.size) match
            case None => current
            case Some((spelledCode, spelledHoles, spelledFillings)) =>
              val (extended, fillingPositions) = spelledFillings.foldLeft((current, Vector.empty[Int])) {
                case ((before, positions), filling) =>
                  val (after, fillingPosition) = BindingNormalForm.placeholdersFolded(filling, fillings, before)(
                    (grown, layer) => (grown :+ layer, grown.size)
                  )
                  (after, positions :+ fillingPosition)
              }
              extended.updated(position, Thunk(spelledCode, spelledHoles, fillingPositions))
        case _ => current
    )

  /** One pass over every pair merges the congruent ones; the passes repeat
    * until one merges nothing.
    */
  @tailrec
  private def closed(spelled: Vector[Layer[Int]], labels: Vector[Int]): Vector[Int] =
    val pairs = for
      first <- spelled.indices
      second <- spelled.indices
      if first < second
    yield (first, second)
    val passed = pairs.foldLeft(labels) { case (current, (first, second)) =>
      if current(first) != current(second) && congruent(spelled(first), spelled(second), current)
      then merged(current, first, second)
      else current
    }
    if passed == labels then labels else closed(spelled, passed)

  private def congruent(first: Layer[Int], second: Layer[Int], labels: Vector[Int]): Boolean =
    first.map(labels) == second.map(labels)

  private def merged(labels: Vector[Int], first: Int, second: Int): Vector[Int] =
    val kept = math.min(labels(first), labels(second))
    val replaced = math.max(labels(first), labels(second))
    labels.map(label => if label == replaced then kept else label)

/** The system: the e-graph, and the node of each term added. */
final case class GraphSystem(graph: EGraph, nodes: Vector[Int]):

  /** The class of each term, named by the smallest position whose node has
    * the same root.
    */
  def classes: Vector[Int] =
    val roots = nodes.map(graph.root)
    roots.map(root => roots.indexOf(root))

/** The commands, the model and the system of the e-graph's state machine
  * tests, run from the initial graph given; a test adds the agreement it
  * checks.
  *
  * Sizes: four noinline instructions, two of them heading matched spines, and
  * commands that are mostly additions over few leaves, so that unions of
  * leaves make many applications congruent: duplicates, whose dead entries
  * trigger the compaction of collections half dead. Thunks have holes, so
  * their classes hold closure states, which unions join. The β rule is not
  * run: its bodies are built by a compiled program, outside this module.
  */
abstract class GraphMachine(initialGraph: EGraph) extends StateMachine[GraphCommand, GraphModel, GraphSystem]:
  import GraphMachine.instructions

  val initialModel: GraphModel = GraphModel(Vector.empty, Vector.empty, agendaRun = true)

  val initialSystem: GraphSystem = GraphSystem(initialGraph, Vector.empty)

  def precondition(model: GraphModel, command: GraphCommand): Boolean = command match
    case GraphCommand.AddInstruction(instruction) => instructions.contains(instruction)
    case GraphCommand.AddLayer(layer) =>
      !layer.isInstanceOf[NoinlineLeaf[?]] && layer.children.forall(model.terms.indices.contains)
    case GraphCommand.Union(first, second) =>
      model.terms.indices.contains(first) && model.terms.indices.contains(second)
    case GraphCommand.RunAgenda => true

  def commandGenerator(model: GraphModel): Gen[GraphCommand] =
    val count = model.terms.size
    val addInstruction = Gen.element1(instructions.head, instructions.tail*).map(GraphCommand.AddInstruction(_))
    if count == 0 then addInstruction
    else
      val leaves = model.terms.indices.filter(model.terms(_).isInstanceOf[NoinlineLeaf[?]]).toList
      val anyTerm = Gen.int(Range.constant(0, count - 1))
      val leaf = Gen.element(leaves.head, leaves.tail)
      val term = Gen.frequency1(3 -> anyTerm, 2 -> leaf)
      val thunks = model.terms.indices.filter(model.terms(_).isInstanceOf[Thunk[?]]).toList
      val pairs = List(
        2 -> (for first <- term; second <- term yield GraphCommand.Union(first, second)),
        2 -> (for first <- leaf; second <- leaf yield GraphCommand.Union(first, second))
      ) ++ thunks.headOption.toList.map(firstThunk =>
        val thunk = Gen.element(firstThunk, thunks.tail)
        2 -> (for first <- thunk; second <- thunk yield GraphCommand.Union(first, second))
      )
      Gen.frequency1(
        2 -> addInstruction,
        8 -> layerGenerator(term).map(GraphCommand.AddLayer(_)),
        4 -> Gen.frequency(pairs.head, pairs.tail),
        2 -> Gen.constant(GraphCommand.RunAgenda)
      )

  def modelAfter(model: GraphModel, command: GraphCommand): GraphModel = command match
    case GraphCommand.AddInstruction(instruction) => model.copy(terms = model.terms :+ NoinlineLeaf(instruction))
    case GraphCommand.AddLayer(layer)   => model.copy(terms = model.terms :+ layer)
    case GraphCommand.Union(first, second) =>
      model.copy(unions = model.unions :+ (first, second), agendaRun = false)
    case GraphCommand.RunAgenda => model.copy(agendaRun = true)

  def systemAfter(system: GraphSystem, command: GraphCommand): GraphSystem = command match
    case GraphCommand.AddInstruction(instruction) =>
      val (graph, node) = system.graph.instructionAdded(instruction)
      GraphSystem(graph, system.nodes :+ node)
    case GraphCommand.AddLayer(layer) =>
      val (graph, node) = system.graph.layerAdded(layer.map(system.nodes))
      GraphSystem(graph, system.nodes :+ node)
    case GraphCommand.Union(first, second) =>
      system.copy(graph =
        system.graph.unionWorked(system.nodes(first), system.nodes(second), GraphMachine.justification, None)
      )
    case GraphCommand.RunAgenda => system.copy(graph = unionsWorked(system.graph))

  /** The system after the commands, from the initial system. */
  def finalSystem(commands: Vector[GraphCommand]): GraphSystem =
    commands.foldLeft(initialSystem)(systemAfter)

  /** A layer other than a leaf over the given terms: an application, a
    * parallel, a binary choice, or a well-formed thunk of one of three codes
    * with 1 or 2 holes, its fillings exactly the code's slots no hole binds
    * (`Code.fillingCount`), in the front end's spelling or not. The e-graph
    * rejects a thunk that is not well-formed (`MalformedThunkLawTest`), so
    * none is drawn. It makes a thunk not in the front end's spelling as its
    * respelling, with new nodes for the respelled fillings, and the model
    * spells the thunks the same way before its closure
    * (`GraphModel.spelledTerms`). So this machine checks the unions over
    * spelled layers, those the respelling builds included. Whether the
    * respelling is right is `InstructionAddedLawTest`'s law and
    * `gezi.strategies.LayerRespellingLawTest`'s.
    */
  private def layerGenerator(term: Gen[Int]): Gen[Layer[Int]] =
    val hole = Gen.element1[Hole](Hole.Bound(0), Hole.Bound(1), Hole.Ignored)
    val thunk: Gen[Layer[Int]] =
      for
        code <- Gen.element1(Code(Slot(0)), Code(Slot(1)), Code(Apply(Code(Slot(0)), Code(Slot(1)))))
        holes <- hole.list(Range.linear(1, 2)).map(_.toVector).filter(holes => Code.fillingCount(code, holes).nonEmpty)
        fillings <- Code.fillingCount(code, holes) match
          case Some(count) => term.list(Range.singleton(count))
          case None        => throw IllegalStateException(s"the holes $holes were drawn for $code though they fit it not")
      yield Thunk(code, holes, fillings.toVector)
    Gen.frequency1(
      5 -> (for function <- term; argument <- term yield Apply(function, argument)),
      1 -> (for left <- term; right <- term yield Parallel(left, right)),
      1 -> (for left <- term; right <- term yield Choice(left, right)),
      2 -> thunk
    )

  @tailrec
  private def unionsWorked(graph: EGraph): EGraph = graph.unionTaken match
    case Some((pending, rest)) =>
      unionsWorked(rest.unionWorked(pending.first, pending.second, pending.justification, pending.made))
    case None => graph

object GraphMachine:

  val instructions: Vector[Instruction] = Vector(0, 1, 2, 3).map(position => Instruction.opaque(s"leaf $position"))

  private val store = Store(noinline = instructions.toSet)

  private val headArityBounds: Map[Instruction, Int] = Map(instructions(0) -> 2, instructions(1) -> 1)

  private val justification = Justification.Lemma(LemmaIdentifier(0), Vector.empty)

  /** The empty graph over the instructions, two of them heading matched spines. */
  val emptyGraph: EGraph = EGraph.empty(store, headArityBounds, explained = false)

/** The state machine test of the e-graph's incremental bookkeeping, whose
  * purpose is to catch a union whose consequences the graph fails to
  * propagate: a congruence the signature table, the user lists or their
  * compaction lose, so that two terms the congruence closure equates stay
  * in two classes (or two terms it keeps apart end in one). The model is the
  * congruence closure recomputed naively from the terms and the unions, a
  * few lines, against the graph's union-find, signature table, user and
  * member lists, heads, closure states and dead-entry compaction.
  *
  * After every command the graph's classes refine the model's (the graph
  * never equates what the closure keeps apart); after the agenda has run,
  * with no union since, they are the model's. Up to 60 commands
  * (`GraphMachine` for the sizes).
  */
class EGraphStateMachineTest extends GeneratedProperties:

  private object Machine extends GraphMachine(GraphMachine.emptyGraph):

    def agreement(model: GraphModel, system: GraphSystem, command: GraphCommand): Result =
      val expected = model.classes
      val found = system.classes
      val refined = found.indices.forall(first =>
        found.indices.forall(second =>
          found(first) != found(second) || expected(first) == expected(second)
        )
      )
      val classesText = s"graph classes $found, model classes $expected"
      if !refined then Result.failure.log(s"the graph equates terms the closure keeps apart: $classesText")
      else if model.agendaRun && found != expected then
        Result.failure.log(s"after the agenda the classes differ: $classesText")
      else Result.success

  // The coverage thresholds sit about four standard deviations below the
  // rates the generator gives, so that a run of 200 tests misses one only by
  // a defect of the generator, not by chance. Measured on 2026-10-31 with
  // 4,000 tests (seed 1): a node made a duplicate in 17% of the runs, a class
  // held two closure states in 16%; at 200 tests one standard deviation is
  // about 2.7 points. The duplicate threshold was 15%, and the property
  // failed for "Insufficient coverage" in 3 of 6 full test runs (seed
  // 484996788267871: 14%).
  property(
    "the graph's classes are the congruence closure of its unions",
    _.copy(testLimit = 200)
  ) {
    for
      commands <- StateMachine
        .forAll(Machine, 60)
        .cover(5, "a node made a duplicate", commands => Machine.finalSystem(commands).graph.nodes.exists(_.duplicate))
        .cover(
          5,
          "a class holding two closure states",
          commands =>
            val graph = Machine.finalSystem(commands).graph
            graph.classes.exists(_.closures.exists(_.items.size >= 2))
        )
    yield StateMachine.run(Machine, commands)
  }

  /** The machine over a graph whose respelling memo keeps nothing
    * (`MemoRetention.NotKept`).
    */
  private object NotKeptMachine extends GraphMachine(GraphMachine.emptyGraph.withRespellingRetention(MemoRetention.NotKept)):
    def agreement(model: GraphModel, system: GraphSystem, command: GraphCommand): Result = Result.success

  /** The same commands run on a graph whose respelling memo keeps nothing
    * make the nodes, with the same layers, and the classes that a graph
    * keeping its memo makes, and its memo stays empty. Its purpose is to
    * catch a memo whose retention changes the graph and not only time: a
    * spelling read from the memo that differs from the one computed again,
    * or a memo that keeps what its retention says it does not.
    */
  property("a graph whose respelling memo keeps nothing makes the graph a keeping one makes") {
    for commands <- StateMachine.forAll(Machine, 60)
    yield
      val kept = Machine.finalSystem(commands)
      val notKept = NotKeptMachine.finalSystem(commands)
      Result
        .diff(notKept.graph.nodes.map(_.layer), kept.graph.nodes.map(_.layer))(_ == _)
        .and(Result.diff(notKept.classes, kept.classes)(_ == _))
        .and(Result.assert(notKept.graph.respellings.isEmpty).log(s"the memo kept ${notKept.graph.respellings.size} spellings"))
  }
