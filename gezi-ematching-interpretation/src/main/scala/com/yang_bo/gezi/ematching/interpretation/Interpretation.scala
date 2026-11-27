package com.yang_bo.gezi.ematching.interpretation

import com.yang_bo.gezi.egraph.GraphBuilding
import com.yang_bo.gezi.egraph.GraphView
import com.yang_bo.gezi.ematching.Backend
import com.yang_bo.gezi.ematching.Building
import com.yang_bo.gezi.ematching.CompiledProgram
import com.yang_bo.gezi.ematching.LayerTemplate
import com.yang_bo.gezi.ematching.Match
import com.yang_bo.gezi.ematching.Matching
import com.yang_bo.gezi.ematching.Program
import com.yang_bo.gezi.ematching.SeedTree
import com.yang_bo.gezi.ematching.SeedKey
import com.yang_bo.gezi.ematching.SeedKind
import com.yang_bo.gezi.ematching.Step
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.Layer
import com.yang_bo.gezi.ir.LayerWith
import com.yang_bo.gezi.ir.NativeSpecializer
import scala.annotation.tailrec
import com.yang_bo.gezi.ir.{Apply, Choice, Parallel, Thunk}

/** The backend that interprets a program: compiling keeps the program as it is,
  * and every call walks the program's data. A match looks the kind and the key
  * up in the program's trees (`Program.trees`, a lazy value of the program
  * computed on its first use) and runs the key's tree by walking its steps from
  * the first, then the matches of the seeds that end there, then each branch; a
  * building walks its tree, a code body looked up in the program's codes where
  * it is referenced.
  *
  * A run of a tree holds its registers in an immutable array (`IArray`),
  * written once each: a step that writes one passes on a copy, grown when the
  * register lies past its end, so that the number of registers need not be
  * computed before the run; a register no step wrote reads -1. Each seed's
  * matches come out in the order of the closure backend: the entries an `Each`
  * step reads in their order, depth first; the matches of a key are handed over
  * grouped by seed, in the seeds' order.
  */
object Interpretation extends Backend:

  def compiled[C <: NativeSpecializer & Singleton](
      program: Program[C]
  ): CompiledProgram[C] = InterpretedProgram(program)

/** The registers of one run of a seed. */
private type Registers = IArray[Int]

/** A witness's run: the registers of its first success, if it has one, and the
  * entries its steps read up to that success.
  */
private final case class Witnessed(
    registers: Option[Registers],
    entriesRead: Int
)

private val noWitness: Witnessed = Witnessed(None, 0)

/** The searched of a tree so far: the matches found, by the number of the seed
  * that found them, each seed's in the order found; and the entries read.
  */
private final case class Searched(
    bySeed: Vector[Vector[Match]],
    entriesRead: Int
):
  def read(count: Int): Searched = copy(entriesRead = entriesRead + count)

  def found(seed: Int, matched: Match): Searched =
    copy(bySeed = bySeed.updated(seed, bySeed(seed) :+ matched))

private final class InterpretedProgram[C <: NativeSpecializer & Singleton](
    program: Program[C]
) extends CompiledProgram[C]:

  def matches(
      kind: SeedKind,
      key: SeedKey[C],
      graph: GraphView[C],
      delta: Int
  ): Matching =
    program.trees.get((kind, key)) match
      case Some(tree) =>
        val none = Searched(
          Vector.fill(program.seeds((kind, key)).size)(Vector.empty),
          0
        )
        val searched = runTree(tree, graph, IArray(delta), none)
        Matching(searched.bySeed.flatten, searched.entriesRead)
      case None => Matching.none

  def added[Graph <: GraphBuilding[C, Graph]](
      orientation: Int,
      graph: Graph,
      bindings: Vector[Option[Int]]
  ): (Graph, Int) =
    built(
      program.orientations(orientation).added,
      graph,
      bindings.map(_.getOrElse(-1))
    )

  def shared[Graph <: GraphBuilding[C, Graph]](
      orientation: Int,
      part: Int,
      graph: Graph,
      bindings: Vector[Option[Int]]
  ): (Graph, Int) =
    built(
      program.orientations(orientation).shared(part),
      graph,
      bindings.map(_.getOrElse(-1))
    )

  def body[Graph <: GraphBuilding[C, Graph]](
      code: Code,
      graph: Graph,
      slotValues: Vector[Int]
  ): (Graph, Int) =
    built(codeBuilding(code), graph, slotValues)

  private def codeBuilding(code: Code): Building[C] =
    program.codes.getOrElse(
      code,
      throw IllegalArgumentException(s"the program has no $code")
    )

  // ---- registers ----

  private def read(registers: Registers, register: Int): Int =
    if register < registers.length then registers(register) else -1

  private def written(
      registers: Registers,
      register: Int,
      node: Int
  ): Registers =
    if register < registers.length then registers.updated(register, node)
    else
      IArray.tabulate(register + 1)(index =>
        if index < registers.length then registers(index)
        else if index == register then node
        else -1
      )

  // ---- seeds ----

  private def runTree(
      tree: SeedTree[C],
      graph: GraphView[C],
      registers: Registers,
      searched: Searched
  ): Searched =
    run(tree, 0, graph, registers, searched)

  /** The tree's steps from the index on, for every way they succeed, then the
    * matches of the seeds that end there and each branch: the matching so far,
    * with the matches they find and the entries they read added. An `Each` step
    * reads every entry of its collection.
    */
  private def run(
      tree: SeedTree[C],
      index: Int,
      graph: GraphView[C],
      registers: Registers,
      searched: Searched
  ): Searched =
    val steps = tree.steps
    if index >= steps.size then
      val ended = tree.ends.foldLeft(searched)((current, end) =>
        current.found(
          end.seed,
          Match(
            end.orientation,
            read(registers, end.root),
            end.bindings.map(_.map(register => read(registers, register)))
          )
        )
      )
      tree.branches.foldLeft(ended)((current, branch) =>
        runTree(branch, graph, registers, current)
      )
    else
      def next(written: Registers, current: Searched): Searched =
        run(tree, index + 1, graph, written, current)
      def eachNode(entries: Vector[Int], target: Int): Searched =
        entries.foldLeft(searched.read(entries.size))((current, node) =>
          if graph.live(node) then
            next(written(registers, target, node), current)
          else current
        )
      steps(index) match
        case Step.Layer(node, template, children) =>
          layerRead(
            graph.layer(read(registers, node)),
            template,
            children,
            registers
          ) match
            case Some(withChildren) => next(withChildren, searched)
            case None               => searched
        case Step.Root(node, target) =>
          next(
            written(registers, target, graph.root(read(registers, node))),
            searched
          )
        case Step.Same(first, second) =>
          if read(registers, first) == read(registers, second) then
            next(registers, searched)
          else searched
        case Step.InstructionIn(instruction, root) =>
          graph.instructionNode(instruction) match
            case Some(node) if graph.root(node) == read(registers, root) =>
              next(registers, searched)
            case _ => searched
        case Step.HasClosure(root) =>
          if graph.hasClosure(read(registers, root)) then
            next(registers, searched)
          else searched
        case Step.InstructionNode(instruction, target) =>
          graph.instructionNode(instruction) match
            case Some(node) => next(written(registers, target, node), searched)
            case None       => searched
        case Step.Lookup(template, children, target) =>
          graph.layerNode(lookedUp(template, children, registers)) match
            case Some(node) => next(written(registers, target, node), searched)
            case None       => searched
        case Step.EachHeadMember(root, head, target) =>
          eachNode(graph.headMembers(read(registers, root), head), target)
        case Step.EachMember(root, shape, target) =>
          eachNode(graph.members(read(registers, root), shape), target)
        case Step.EachUser(root, role, target) =>
          eachNode(graph.users(read(registers, root), role), target)
        case Step.EachPositionUser(root, role, position, target) =>
          val entries = graph.positionUsers(read(registers, root), role)
          entries.foldLeft(searched.read(entries.size))((current, entry) =>
            if entry.position == position && graph.live(entry.user) then
              next(written(registers, target, entry.user), current)
            else current
          )
        case Step.Once(inner) =>
          val witnessed = first(inner, 0, graph, registers)
          val withReads = searched.read(witnessed.entriesRead)
          witnessed.registers match
            case Some(withWitness) => next(withWitness, withReads)
            case None              => withReads

  /** The steps from the index on, inside a witness: the first way they succeed,
    * and the entries read up to it. An `Each` step reads its entries up to the
    * first that leads to a success.
    */
  private def first(
      steps: Vector[Step[C]],
      index: Int,
      graph: GraphView[C],
      registers: Registers
  ): Witnessed =
    if index >= steps.size then Witnessed(Some(registers), 0)
    else
      def next(written: Registers): Witnessed =
        first(steps, index + 1, graph, written)
      steps(index) match
        case Step.Layer(node, template, children) =>
          layerRead(
            graph.layer(read(registers, node)),
            template,
            children,
            registers
          ) match
            case Some(withChildren) => next(withChildren)
            case None               => noWitness
        case Step.Root(node, target) =>
          next(written(registers, target, graph.root(read(registers, node))))
        case Step.Same(firstRegister, secondRegister) =>
          if read(registers, firstRegister) == read(registers, secondRegister)
          then next(registers)
          else noWitness
        case Step.InstructionIn(instruction, root) =>
          graph.instructionNode(instruction) match
            case Some(node) if graph.root(node) == read(registers, root) =>
              next(registers)
            case _ => noWitness
        case Step.HasClosure(root) =>
          if graph.hasClosure(read(registers, root)) then next(registers)
          else noWitness
        case Step.InstructionNode(instruction, target) =>
          graph.instructionNode(instruction) match
            case Some(node) => next(written(registers, target, node))
            case None       => noWitness
        case Step.Lookup(template, children, target) =>
          graph.layerNode(lookedUp(template, children, registers)) match
            case Some(node) => next(written(registers, target, node))
            case None       => noWitness
        case Step.EachHeadMember(root, head, target) =>
          firstNode(
            graph.headMembers(read(registers, root), head),
            0,
            0,
            target,
            steps,
            index,
            graph,
            registers
          )
        case Step.EachMember(root, shape, target) =>
          firstNode(
            graph.members(read(registers, root), shape),
            0,
            0,
            target,
            steps,
            index,
            graph,
            registers
          )
        case Step.EachUser(root, role, target) =>
          firstNode(
            graph.users(read(registers, root), role),
            0,
            0,
            target,
            steps,
            index,
            graph,
            registers
          )
        case Step.EachPositionUser(root, role, position, target) =>
          val entries = graph.positionUsers(read(registers, root), role)
          firstPositionUser(
            entries,
            0,
            0,
            position,
            target,
            steps,
            index,
            graph,
            registers
          )
        case Step.Once(inner) =>
          val witnessed = first(inner, 0, graph, registers)
          witnessed.registers match
            case Some(withWitness) =>
              val after = next(withWitness)
              Witnessed(
                after.registers,
                witnessed.entriesRead + after.entriesRead
              )
            case None => witnessed

  /** The first entry from the position on whose node is live and leads the
    * steps after the `Each` step at `index` to a success.
    */
  @tailrec
  private def firstNode(
      entries: Vector[Int],
      position: Int,
      readSoFar: Int,
      target: Int,
      steps: Vector[Step[C]],
      index: Int,
      graph: GraphView[C],
      registers: Registers
  ): Witnessed =
    if position >= entries.size then Witnessed(None, readSoFar)
    else
      val node = entries(position)
      val attempt =
        if graph.live(node) then
          first(steps, index + 1, graph, written(registers, target, node))
        else noWitness
      val readNow = readSoFar + 1 + attempt.entriesRead
      if attempt.registers.isDefined then Witnessed(attempt.registers, readNow)
      else
        firstNode(
          entries,
          position + 1,
          readNow,
          target,
          steps,
          index,
          graph,
          registers
        )

  @tailrec
  private def firstPositionUser(
      entries: Vector[com.yang_bo.gezi.egraph.PositionUser],
      entryIndex: Int,
      readSoFar: Int,
      position: Int,
      target: Int,
      steps: Vector[Step[C]],
      index: Int,
      graph: GraphView[C],
      registers: Registers
  ): Witnessed =
    if entryIndex >= entries.size then Witnessed(None, readSoFar)
    else
      val entry = entries(entryIndex)
      val attempt =
        if entry.position == position && graph.live(entry.user) then
          first(steps, index + 1, graph, written(registers, target, entry.user))
        else noWitness
      val readNow = readSoFar + 1 + attempt.entriesRead
      if attempt.registers.isDefined then Witnessed(attempt.registers, readNow)
      else
        firstPositionUser(
          entries,
          entryIndex + 1,
          readNow,
          position,
          target,
          steps,
          index,
          graph,
          registers
        )

  /** The registers with the layer's children written, when the layer has the
    * template's shape, its choice's number of members, its thunk's code and
    * holes and number of fillings.
    */
  private def layerRead(
      layer: Layer[Int],
      template: LayerTemplate,
      children: Vector[Int],
      registers: Registers
  ): Option[Registers] = (template, layer) match
    case (LayerTemplate.Apply, Apply(function, argument)) =>
      Some(childrenWritten(registers, children, Vector(function, argument)))
    case (LayerTemplate.Parallel, Parallel(left, right)) =>
      Some(childrenWritten(registers, children, Vector(left, right)))
    case (LayerTemplate.Choice, Choice(left, right)) =>
      Some(childrenWritten(registers, children, Vector(left, right)))
    case (
          LayerTemplate.Thunk(code, holes),
          Thunk(layerCode, layerHoles, fillings)
        )
        if layerCode == code && layerHoles == holes && fillings.size == children.size =>
      Some(childrenWritten(registers, children, fillings))
    case _ => None

  /** The layer a `Lookup` step looks up: the template over the nodes at the
    * registers.
    */
  private def lookedUp(
      template: LayerTemplate,
      children: Vector[Int],
      registers: Registers
  ): LayerWith[Int, Configured[C]] =
    val nodes = children.map(read(registers, _))
    template match
      case LayerTemplate.Apply =>
        require(children.size == 2, s"an application looked up over $children")
        Apply(nodes(0), nodes(1))
      case LayerTemplate.Parallel =>
        require(children.size == 2, s"a parallel looked up over $children")
        Parallel(nodes(0), nodes(1))
      case LayerTemplate.Choice =>
        require(children.size == 2, s"a choice looked up over $children")
        Choice(nodes(0), nodes(1))
      case LayerTemplate.Thunk(code, holes) => Thunk(code, holes, nodes)

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
      written(current, targets(index), nodes(index))
    )

  // ---- buildings ----

  /** The building's node added to the graph, children first; the values are an
    * instance's bindings (-1 for an unbound metavariable) or a β step's slot
    * values.
    */
  private def built[Graph <: GraphBuilding[C, Graph]](
      building: Building[C],
      graph: Graph,
      values: Vector[Int]
  ): (Graph, Int) = building match
    case Building.Value(index) =>
      val node = values(index)
      require(node >= 0, s"the value at $index is unbound")
      (graph, node)
    case Building.InstructionNode(instruction) =>
      graph.instructionAdded(instruction)
    case Building.CodeBody(code) => built(codeBuilding(code), graph, values)
    case Building.Apply(function, argument, readByBeta) =>
      val (withFunction, functionNode) = built(function, graph, values)
      val (withArgument, argumentNode) = built(argument, withFunction, values)
      val (withApplication, node) =
        withArgument.layerAdded(Apply(functionNode, argumentNode))
      if readByBeta then (withApplication.applicationRead(node), node)
      else (withApplication, node)
    case Building.Parallel(left, right) =>
      val (withLeft, leftNode) = built(left, graph, values)
      val (withRight, rightNode) = built(right, withLeft, values)
      withRight.layerAdded(Parallel(leftNode, rightNode))
    case Building.Choice(left, right) =>
      val (withLeft, leftNode) = built(left, graph, values)
      val (withRight, rightNode) = built(right, withLeft, values)
      withRight.layerAdded(Choice(leftNode, rightNode))
    case Building.Thunk(code, holes, fillings) =>
      val (withFillings, fillingNodes) = childrenBuilt(fillings, graph, values)
      withFillings.layerAdded(Thunk(code, holes, fillingNodes))

  private def childrenBuilt[Graph <: GraphBuilding[C, Graph]](
      buildings: Vector[Building[C]],
      graph: Graph,
      values: Vector[Int]
  ): (Graph, Vector[Int]) =
    buildings.foldLeft((graph, Vector.empty[Int])) {
      case ((current, nodes), building) =>
        val (next, node) = built(building, current, values)
        (next, nodes :+ node)
    }
