package gezi.ematching.closures

import gezi.egraph.GraphBuilding
import gezi.egraph.GraphView
import gezi.egraph.PositionUser
import gezi.ematching.Backend
import gezi.ematching.Building
import gezi.ematching.CompiledProgram
import gezi.ematching.LayerTemplate
import gezi.ematching.Match
import gezi.ematching.Matching
import gezi.ematching.Program
import gezi.ematching.SeedKey
import gezi.ematching.SeedKind
import gezi.ematching.SeedTree
import gezi.ematching.Step
import gezi.ir.Code
import gezi.ir.Layer
import scala.annotation.tailrec
import gezi.ir.{Apply, Choice, Parallel, Thunk}

/** The backend that compiles a program once into a tree of Scala closures:
  * the tree of each key's seeds (`Program.trees`), each node's steps from
  * the last to the first, into nested closures, one a step, so that what a
  * step does is chosen when the program is compiled; and each building into
  * a closure from a graph and the caller's values to the graph after it and
  * the node built.
  *
  * A run of a tree holds its registers in an immutable vector, written once
  * each: a step that writes one passes on a copy. Each seed's matches come
  * out in the order of Prolog's backtracking over the baseline's seed
  * clause: the entries an `Each` step reads in their order, depth first; the
  * matches of a key are handed over grouped by seed, in the seeds' order.
  */
object ClosureCompilation extends Backend:

  def compiled(program: Program): CompiledProgram = CompiledClosures(program)

/** The registers of one run of a seed. */
private type Registers = Vector[Int]

/** The matching of a tree so far: the matches found, by the number of the
  * seed that found them, each seed's in the order found; and the entries
  * read.
  */
private final case class Searched(bySeed: Vector[Vector[Match]], entriesRead: Int):
  def read(count: Int): Searched = copy(entriesRead = entriesRead + count)

  def found(seed: Int, matched: Match): Searched =
    copy(bySeed = bySeed.updated(seed, bySeed(seed) :+ matched))

/** The steps after a point, run for every way the steps before it
  * succeeded: the matching so far, with the matches they find and the
  * entries they read added.
  */
private type Continuation = (GraphView, Registers, Searched) => Searched

/** A witness's run: the registers of its first success, if it has one, and
  * the entries its steps read up to that success.
  */
private final case class Witnessed(registers: Option[Registers], entriesRead: Int)

/** The steps after a point inside a witness: their first success and the
  * entries read on the way.
  */
private type FirstContinuation = (GraphView, Registers) => Witnessed

private val noWitness: Witnessed = Witnessed(None, 0)

/** A compiled building: the graph after building the node, and the node.
  * The values are an instance's bindings (-1 for an unbound metavariable)
  * or a β step's slot values.
  */
private type BuildingClosure =
  [Graph <: GraphBuilding[Graph]] => (Graph, Vector[Int]) => (Graph, Int)

private final class CompiledClosures(program: Program) extends CompiledProgram:

  /** The compiled tree of each kind by key, so that a lookup hashes the key
    * alone.
    */
  private val treeRuns: Map[SeedKind, Map[SeedKey, (GraphView, Int) => Matching]] =
    SeedKind.values.toVector
      .map(kind =>
        kind -> program.trees.collect {
          case ((treeKind, key), tree) if treeKind == kind =>
            key -> treeRun(tree, program.seeds((treeKind, key)).size)
        }
      )
      .toMap

  /** The closures of the codes, resolved by a reference to a code at the
    * time it is built, so that each code is compiled once and a body's
    * shared subcodes are not copied.
    */
  private lazy val codeClosures: Map[Code, BuildingClosure] =
    program.codes.map((code, building) => code -> buildingClosure(building))

  private val addedClosures: Vector[BuildingClosure] =
    program.orientations.map(plan => buildingClosure(plan.added))

  private val sharedClosures: Vector[Vector[BuildingClosure]] =
    program.orientations.map(plan => plan.shared.map(buildingClosure))

  def matches(
      kind: SeedKind,
      key: SeedKey,
      graph: GraphView,
      delta: Int
  ): Matching =
    treeRuns(kind).get(key) match
      case Some(run) => run(graph, delta)
      case None      => Matching.none

  def added[Graph <: GraphBuilding[Graph]](
      orientation: Int,
      graph: Graph,
      bindings: Vector[Option[Int]]
  ): (Graph, Int) =
    addedClosures(orientation)[Graph](graph, bindingValues(bindings))

  def shared[Graph <: GraphBuilding[Graph]](
      orientation: Int,
      part: Int,
      graph: Graph,
      bindings: Vector[Option[Int]]
  ): (Graph, Int) =
    sharedClosures(orientation)(part)[Graph](graph, bindingValues(bindings))

  def body[Graph <: GraphBuilding[Graph]](
      code: Code,
      graph: Graph,
      slotValues: Vector[Int]
  ): (Graph, Int) =
    codeClosure(code)[Graph](graph, slotValues)

  private def codeClosure(code: Code): BuildingClosure =
    codeClosures.getOrElse(
      code,
      throw IllegalArgumentException(s"the program has no $code")
    )

  private def bindingValues(bindings: Vector[Option[Int]]): Vector[Int] =
    bindings.map(_.getOrElse(-1))

  // ---- seeds ----

  /** The run of a key's tree of `seedCount` seeds from a delta: its matches
    * grouped by seed, in the seeds' order.
    */
  private def treeRun(
      tree: SeedTree,
      seedCount: Int
  ): (GraphView, Int) => Matching =
    val steps = treeClosure(tree)
    val initial: Registers = Vector.fill(SeedTree.registerCount(tree))(-1)
    val none = Searched(Vector.fill(seedCount)(Vector.empty), 0)
    (graph, delta) =>
      val searched = steps(graph, initial.updated(0, delta), none)
      Matching(searched.bySeed.flatten, searched.entriesRead)

  /** The tree's steps followed, on every way they succeed, by the matches of
    * the seeds that end there and then by each branch.
    */
  private def treeClosure(tree: SeedTree): Continuation =
    val branches = tree.branches.map(treeClosure)
    val after: Continuation = (graph, registers, searched) =>
      val ended = tree.ends.foldLeft(searched)((current, end) =>
        current.found(
          end.seed,
          Match(
            end.orientation,
            registers(end.root),
            end.bindings.map(_.map(register => registers(register)))
          )
        )
      )
      branches.foldLeft(ended)((current, branch) => branch(graph, registers, current))
    tree.steps.foldRight(after)(stepClosure)

  /** The step followed by the steps after it, for every way it succeeds. An
    * `Each` step reads every entry of its collection.
    */
  private def stepClosure(step: Step, next: Continuation): Continuation =
    step match
      case Step.Layer(node, LayerTemplate.Apply, Vector(function, argument)) =>
        (graph, registers, searched) =>
          graph.layer(registers(node)) match
            case Apply(functionNode, argumentNode) =>
              next(
                graph,
                registers.updated(function, functionNode).updated(argument, argumentNode),
                searched
              )
            case _ => searched
      case Step.Layer(node, LayerTemplate.Parallel, Vector(left, right)) =>
        (graph, registers, searched) =>
          graph.layer(registers(node)) match
            case Parallel(leftNode, rightNode) =>
              next(
                graph,
                registers.updated(left, leftNode).updated(right, rightNode),
                searched
              )
            case _ => searched
      case Step.Layer(node, template, children) =>
        val reading = layerReading(template, children)
        (graph, registers, searched) =>
          reading(graph.layer(registers(node)), registers) match
            case Some(written) => next(graph, written, searched)
            case None          => searched
      case Step.Root(node, target) =>
        (graph, registers, searched) =>
          next(graph, registers.updated(target, graph.root(registers(node))), searched)
      case Step.Same(first, second) =>
        (graph, registers, searched) =>
          if registers(first) == registers(second) then
            next(graph, registers, searched)
          else searched
      case Step.InstructionIn(instruction, root) =>
        (graph, registers, searched) =>
          graph.instructionNode(instruction) match
            case Some(node) if graph.root(node) == registers(root) =>
              next(graph, registers, searched)
            case _ => searched
      case Step.HasClosure(root) =>
        (graph, registers, searched) =>
          if graph.hasClosure(registers(root)) then next(graph, registers, searched)
          else searched
      case Step.InstructionNode(instruction, target) =>
        (graph, registers, searched) =>
          graph.instructionNode(instruction) match
            case Some(node) => next(graph, registers.updated(target, node), searched)
            case None       => searched
      case Step.Lookup(template, children, target) =>
        val layerOf = lookedUpLayer(template, children)
        (graph, registers, searched) =>
          graph.layerNode(layerOf(registers)) match
            case Some(node) => next(graph, registers.updated(target, node), searched)
            case None       => searched
      case Step.EachHeadMember(root, head, target) =>
        (graph, registers, searched) =>
          eachNode(graph.headMembers(registers(root), head), target, next)(
            graph,
            registers,
            searched
          )
      case Step.EachMember(root, shape, target) =>
        (graph, registers, searched) =>
          eachNode(graph.members(registers(root), shape), target, next)(
            graph,
            registers,
            searched
          )
      case Step.EachUser(root, role, target) =>
        (graph, registers, searched) =>
          eachNode(graph.users(registers(root), role), target, next)(
            graph,
            registers,
            searched
          )
      case Step.EachPositionUser(root, role, position, target) =>
        (graph, registers, searched) =>
          val entries = graph.positionUsers(registers(root), role)
          entries.foldLeft(searched.read(entries.size))((current, entry) =>
            if entry.position == position && graph.live(entry.user) then
              next(graph, registers.updated(target, entry.user), current)
            else current
          )
      case Step.Once(steps) =>
        val witness = steps.foldRight(firstFound)(firstStepClosure)
        (graph, registers, searched) =>
          val witnessed = witness(graph, registers)
          val withReads = searched.read(witnessed.entriesRead)
          witnessed.registers match
            case Some(written) => next(graph, written, withReads)
            case None          => withReads

  private def eachNode(
      entries: Vector[Int],
      target: Int,
      next: Continuation
  )(graph: GraphView, registers: Registers, searched: Searched): Searched =
    entries.foldLeft(searched.read(entries.size))((current, node) =>
      if graph.live(node) then next(graph, registers.updated(target, node), current)
      else current
    )

  /** The end of a witness's steps: their first success. A method, since the
    * seeds are compiled while the class is constructed.
    */
  private def firstFound: FirstContinuation = (_, registers) =>
    Witnessed(Some(registers), 0)

  /** The step followed by the steps after it, inside a witness: the first
    * way they succeed, and the entries read up to it. An `Each` step reads
    * its entries up to the first that leads to a success.
    */
  private def firstStepClosure(
      step: Step,
      next: FirstContinuation
  ): FirstContinuation = step match
    case Step.Layer(node, template, children) =>
      val reading = layerReading(template, children)
      (graph, registers) =>
        reading(graph.layer(registers(node)), registers) match
          case Some(written) => next(graph, written)
          case None          => noWitness
    case Step.Root(node, target) =>
      (graph, registers) =>
        next(graph, registers.updated(target, graph.root(registers(node))))
    case Step.Same(first, second) =>
      (graph, registers) =>
        if registers(first) == registers(second) then next(graph, registers)
        else noWitness
    case Step.InstructionIn(instruction, root) =>
      (graph, registers) =>
        graph.instructionNode(instruction) match
          case Some(node) if graph.root(node) == registers(root) =>
            next(graph, registers)
          case _ => noWitness
    case Step.HasClosure(root) =>
      (graph, registers) =>
        if graph.hasClosure(registers(root)) then next(graph, registers)
        else noWitness
    case Step.InstructionNode(instruction, target) =>
      (graph, registers) =>
        graph.instructionNode(instruction) match
          case Some(node) => next(graph, registers.updated(target, node))
          case None       => noWitness
    case Step.Lookup(template, children, target) =>
      val layerOf = lookedUpLayer(template, children)
      (graph, registers) =>
        graph.layerNode(layerOf(registers)) match
          case Some(node) => next(graph, registers.updated(target, node))
          case None       => noWitness
    case Step.EachHeadMember(root, head, target) =>
      (graph, registers) =>
        firstNode(graph.headMembers(registers(root), head), 0, 0, target, next, graph, registers)
    case Step.EachMember(root, shape, target) =>
      (graph, registers) =>
        firstNode(graph.members(registers(root), shape), 0, 0, target, next, graph, registers)
    case Step.EachUser(root, role, target) =>
      (graph, registers) =>
        firstNode(graph.users(registers(root), role), 0, 0, target, next, graph, registers)
    case Step.EachPositionUser(root, role, position, target) =>
      (graph, registers) =>
        firstPositionUser(
          graph.positionUsers(registers(root), role),
          0,
          0,
          position,
          target,
          next,
          graph,
          registers
        )
    case Step.Once(steps) =>
      val witness = steps.foldRight(firstFound)(firstStepClosure)
      (graph, registers) =>
        val inner = witness(graph, registers)
        inner.registers match
          case Some(written) =>
            val after = next(graph, written)
            Witnessed(after.registers, inner.entriesRead + after.entriesRead)
          case None => inner

  @tailrec
  private def firstNode(
      entries: Vector[Int],
      index: Int,
      read: Int,
      target: Int,
      next: FirstContinuation,
      graph: GraphView,
      registers: Registers
  ): Witnessed =
    if index >= entries.size then Witnessed(None, read)
    else
      val node = entries(index)
      val attempt =
        if graph.live(node) then next(graph, registers.updated(target, node))
        else noWitness
      val readSoFar = read + 1 + attempt.entriesRead
      if attempt.registers.isDefined then Witnessed(attempt.registers, readSoFar)
      else firstNode(entries, index + 1, readSoFar, target, next, graph, registers)

  @tailrec
  private def firstPositionUser(
      entries: Vector[PositionUser],
      index: Int,
      read: Int,
      position: Int,
      target: Int,
      next: FirstContinuation,
      graph: GraphView,
      registers: Registers
  ): Witnessed =
    if index >= entries.size then Witnessed(None, read)
    else
      val entry = entries(index)
      val attempt =
        if entry.position == position && graph.live(entry.user) then
          next(graph, registers.updated(target, entry.user))
        else noWitness
      val readSoFar = read + 1 + attempt.entriesRead
      if attempt.registers.isDefined then Witnessed(attempt.registers, readSoFar)
      else
        firstPositionUser(entries, index + 1, readSoFar, position, target, next, graph, registers)

  /** The reading of a `Layer` step, chosen when the step is compiled: the
    * registers with the layer's children written, when the layer has the
    * template's shape, its choice's number of members, its thunk's code and
    * holes and number of fillings.
    */
  private def layerReading(
      template: LayerTemplate,
      children: Vector[Int]
  ): (Layer[Int], Registers) => Option[Registers] = template match
    case LayerTemplate.Apply =>
      (layer, registers) =>
        layer match
          case Apply(function, argument) =>
            Some(childrenWritten(registers, children, Vector(function, argument)))
          case _ => None
    case LayerTemplate.Parallel =>
      (layer, registers) =>
        layer match
          case Parallel(left, right) =>
            Some(childrenWritten(registers, children, Vector(left, right)))
          case _ => None
    case LayerTemplate.Choice =>
      (layer, registers) =>
        layer match
          case Choice(left, right) =>
            Some(childrenWritten(registers, children, Vector(left, right)))
          case _ => None
    case LayerTemplate.Thunk(code, holes) =>
      (layer, registers) =>
        layer match
          case Thunk(layerCode, layerHoles, fillings)
              if layerCode == code && layerHoles == holes &&
                fillings.size == children.size =>
            Some(childrenWritten(registers, children, fillings))
          case _ => None

  /** The layer a `Lookup` step looks up, over the nodes at the registers,
    * chosen when the step is compiled.
    */
  private def lookedUpLayer(
      template: LayerTemplate,
      children: Vector[Int]
  ): Registers => Layer[Int] = template match
    case LayerTemplate.Apply =>
      require(children.size == 2, s"an application looked up over $children")
      registers => Apply(registers(children(0)), registers(children(1)))
    case LayerTemplate.Parallel =>
      require(children.size == 2, s"a parallel looked up over $children")
      registers => Parallel(registers(children(0)), registers(children(1)))
    case LayerTemplate.Choice =>
      require(children.size == 2, s"a choice looked up over $children")
      registers => Choice(registers(children(0)), registers(children(1)))
    case LayerTemplate.Thunk(code, holes) =>
      registers => Thunk(code, holes, children.map(registers))

  private def childrenWritten(
      registers: Registers,
      targets: Vector[Int],
      nodes: Vector[Int]
  ): Registers =
    require(
      targets.size == nodes.size,
      s"a layer of ${nodes.size} children read into ${targets.size} registers"
    )
    targets.indices.foldLeft(registers)((current, index) =>
      current.updated(targets(index), nodes(index))
    )

  // ---- buildings ----

  private def buildingClosure(building: Building): BuildingClosure =
    building match
      case Building.Value(index) =>
        [Graph <: GraphBuilding[Graph]] =>
          (graph: Graph, values: Vector[Int]) =>
            val node = values(index)
            require(node >= 0, s"the value at $index is unbound")
            (graph, node)
      case Building.InstructionNode(instruction) =>
        [Graph <: GraphBuilding[Graph]] =>
          (graph: Graph, _: Vector[Int]) => graph.instructionAdded(instruction)
      case Building.CodeBody(code) =>
        [Graph <: GraphBuilding[Graph]] =>
          (graph: Graph, values: Vector[Int]) =>
            codeClosure(code)[Graph](graph, values)
      case Building.Apply(function, argument, read) =>
        val functionClosure = buildingClosure(function)
        val argumentClosure = buildingClosure(argument)
        [Graph <: GraphBuilding[Graph]] =>
          (graph: Graph, values: Vector[Int]) =>
            val (withFunction, functionNode) =
              functionClosure[Graph](graph, values)
            val (withArgument, argumentNode) =
              argumentClosure[Graph](withFunction, values)
            val (withApplication, node) =
              withArgument.layerAdded(Apply(functionNode, argumentNode))
            if read then (withApplication.applicationRead(node), node)
            else (withApplication, node)
      case Building.Parallel(left, right) =>
        val leftClosure = buildingClosure(left)
        val rightClosure = buildingClosure(right)
        [Graph <: GraphBuilding[Graph]] =>
          (graph: Graph, values: Vector[Int]) =>
            val (withLeft, leftNode) = leftClosure[Graph](graph, values)
            val (withRight, rightNode) = rightClosure[Graph](withLeft, values)
            withRight.layerAdded(Parallel(leftNode, rightNode))
      case Building.Choice(left, right) =>
        val leftClosure = buildingClosure(left)
        val rightClosure = buildingClosure(right)
        [Graph <: GraphBuilding[Graph]] =>
          (graph: Graph, values: Vector[Int]) =>
            val (withLeft, leftNode) = leftClosure[Graph](graph, values)
            val (withRight, rightNode) = rightClosure[Graph](withLeft, values)
            withRight.layerAdded(Choice(leftNode, rightNode))
      case Building.Thunk(code, holes, fillings) =>
        val fillingClosures = fillings.map(buildingClosure)
        [Graph <: GraphBuilding[Graph]] =>
          (graph: Graph, values: Vector[Int]) =>
            val (withFillings, fillingNodes) =
              childrenBuilt[Graph](fillingClosures, graph, values)
            withFillings.layerAdded(Thunk(code, holes, fillingNodes))

  private def childrenBuilt[Graph <: GraphBuilding[Graph]](
      closures: Vector[BuildingClosure],
      graph: Graph,
      values: Vector[Int]
  ): (Graph, Vector[Int]) =
    closures.foldLeft((graph, Vector.empty[Int])) { case ((current, nodes), closure) =>
      val (next, node) = closure[Graph](current, values)
      (next, nodes :+ node)
    }
