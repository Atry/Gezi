package gezi.egraph

import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.ir.Store
import scala.annotation.tailrec
import scala.collection.immutable.HashMap
import scala.collection.immutable.HashSet
import scala.collection.immutable.Queue
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Thunk}

/** The persistent e-graph of a saturation: every operation returns the graph
  * after it and leaves the graph it was called on unchanged.
  *
  * It holds the nodes (numbered by creation), the data of each class in its
  * root, the signature table (the node of each layer over class roots), the
  * instance keys applied, the instruction table and the instructions in filing order,
  * the unions that joined two classes, the agenda (a queue of unions and a
  * queue of β steps, both first in first out, and the deltas of the two
  * kinds of orientation, two stacks, last in first out) and the counts of
  * instances, matches, β steps and the entries the matching read. The
  * union-find is by size, without path compression, which changes no
  * result.
  *
  * The order of every operation is the Prolog baseline's, since the node
  * numbers and the union sequence must come out the same: the name of the
  * baseline's predicate is given at each operation.
  *
  * FIXME: the agenda's first in first out order, the deltas' https://github.com/Atry/private-overlay/issues/2032
  * last in first out order, the union by size and the numbering of nodes by creation are fixed in this implementation
  * and not chosen by configuration. They decide which unions and instances a saturation that a budget cuts has made
  * when it stops, that is, what a cut saturation keeps.
  *
  * @param headArityBounds
  *   the largest number of arguments a matched side of the orientations
  *   applies each instruction to, for the instructions that head an application's
  *   spine in a matched side (the baseline's `head_arity_bound/3`)
  * @param analysis
  *   the cost of each class under one cost analysis, kept up to date by the
  *   operations below, or none (`ClassAnalysis`, `EGraph.analysed`); it is
  *   read only, and changes no node number, union or order
  * @param respellings
  *   the memo of the front end's spelling of a thunk layer, by its code and
  *   holes ([[Respelling]]):
  *   every thunk node is made in that spelling, so that a node's layer
  *   depends on its λ-term and not on the derivation that made it. A pure
  *   function's results, keyed by all its inputs (`CONTRIBUTING.md`, "Tables", kind 2): emptying it changes only time. It grows with the distinct
  *   (code, holes) pairs the graph's thunk layers have, for as long as the
  *   graph value lives, over every round that graph serves, under
  *   `MemoRetention.Kept`; under `NotKept` it stays empty and every spelling
  *   is computed again (`respellingRetention`).
  * @param respellingCounts
  *   the memo's readings: the spellings computed, the spellings read back
  *   from the memo, and the thunk layers the spelling changed
  * @param respellingRetention
  *   whether the memo keeps what it computed, a round's choice
  *   ([[MemoRetention]])
  */
final case class EGraph(
    store: Store,
    headArityBounds: Map[Instruction, Int],
    nodes: Vector[NodeRecord],
    classes: Vector[ClassData],
    signatures: HashMap[Layer[Int], Int],
    instanceKeys: HashSet[InstanceKey],
    instructionTable: HashMap[Instruction, Int],
    instructionFilings: Vector[(Instruction, Int)],
    unions: Vector[UnionRecord],
    unionQueue: Queue[PendingUnion],
    betaQueue: Queue[PendingBeta],
    merges: List[Int],
    deltas: List[Int],
    instances: Int,
    matchesFound: Int,
    betaSteps: Int,
    entriesRead: Long,
    analysis: Option[AnalysisSlot[?]],
    explained: Boolean,
    madeNodes: HashMap[Layer[Int], Int],
    madeDuplicates: Int,
    respellings: HashMap[Respelling.Key, Respelling],
    respellingCounts: RespellingCounts,
    respellingRetention: MemoRetention
) extends GraphBuilding[EGraph]:

  // ---- reading (GraphView) ----

  def layer(node: Int): Layer[Int] = nodes(node).layer

  /** The layer the node was made over, its children the nodes its maker
    * passed (`NodeRecord.made`): its term is this layer over its children's
    * terms.
    */
  def madeLayer(node: Int): Layer[Int] = nodes(node).made

  @tailrec
  final def root(node: Int): Int =
    val parent = nodes(node).parent
    if parent == node then node else root(parent)

  def live(node: Int): Boolean = !nodes(node).duplicate

  def members(root: Int, shape: MemberShape): Vector[Int] =
    classes(root).members(shape).items

  def headMembers(root: Int, head: Head): Vector[Int] =
    classes(root).headEntries(head).items

  def users(root: Int, role: UserRole): Vector[Int] =
    classes(root).users(role).items

  def positionUsers(root: Int, role: PositionRole): Vector[PositionUser] =
    classes(root).positionUsers(role).items

  /** The live nodes that read the class as a child, in any role. */
  def classUsers(root: Int): Vector[Int] =
    liveNodes(
      UserRole.values.toVector.flatMap(users(root, _)) ++
        PositionRole.values.toVector.flatMap(positionUsers(root, _).map(_.user))
    ).distinct

  /** The graph with the analysis's cost of every class computed from
    * scratch and kept up to date from then on, replacing any analysis it
    * had.
    */
  def analysed[Value](costAnalysis: ClassAnalysis[Value]): EGraph =
    copy(analysis = Some(AnalysisSlot.computed(this, costAnalysis)))

  def instructionNode(instruction: Instruction): Option[Int] = instructionTable.get(instruction)

  def hasClosure(root: Int): Boolean = classes(root).closures.isDefined

  // ---- reading, beyond what a program reads ----

  /** Every node, the made duplicates included: the nodes a proof's terms
    * are read from.
    */
  def nodeCount: Int = nodes.size

  /** Every union of the log, the congruences of the made duplicates
    * included.
    */
  def unionCount: Int = unions.size

  /** The nodes that are no made duplicate: what a saturation measures as
    * the graph growing (a made duplicate is explanation, not a new term of
    * any class).
    */
  def canonicalNodeCount: Int = nodes.size - madeDuplicates

  /** The unions that joined two classes: the log without the congruences of
    * the made duplicates.
    */
  def joiningUnionCount: Int = unions.size - madeDuplicates

  def nodeHeads(node: Int): Vector[Head] = nodes(node).heads

  /** The first instruction filed onto the node. */
  def nodeInstruction(node: Int): Option[Instruction] = nodes(node).instruction

  def readable(node: Int): Boolean = nodes(node).readable

  def classHeads(classRoot: Int): Vector[Head] = classes(classRoot).heads

  /** The node of the layer, a layer over nodes of any class read over their
    * roots, when the graph has one of that signature; nothing is made (the
    * baseline's `fixpoint_egraph_layer_node/3`). A thunk with holes is
    * looked up in the spelling `layerMade` makes it in, its respelling where
    * it is not its own ([[Respelling]]),
    * so that a layer the graph was given in another spelling, such as a
    * lemma's side as stated, is found at the node made for it (measured
    * 2026-11-17: `GraphProof` found no node for a lemma's stated side
    * `λz. k a`, whose node the graph holds respelled).
    */
  def layerNode(layer: Layer[Int]): Option[Int] = layer match
    case Thunk(code, holes, fillings) if holes.nonEmpty =>
      val key = Respelling.Key(code, holes, fillings.size)
      respellings.getOrElse(key, Respelling.of(key)) match
        case Respelling.Canonical => spelledLayerNode(layer)
        case Respelling.Respelled(respelledCode, respelledHoles, respelledFillings) =>
          val fillingNodes = respelledFillings.map(filling =>
            gezi.ir.BindingNormalForm.placeholdersMapped[Option[Int]](filling, fillings.map(Some(_)))(spelled =>
              spelled.children
                .foldLeft(Option(Vector.empty[Int]))((found, child) => found.zip(child).map(_ :+ _))
                .flatMap(children => layerNode(spelled.over(children)))
            )
          )
          fillingNodes
            .foldLeft(Option(Vector.empty[Int]))((found, node) => found.zip(node).map(_ :+ _))
            .flatMap(nodes => spelledLayerNode(Thunk(respelledCode, respelledHoles, nodes)))
    case _ => spelledLayerNode(layer)

  /** `layerNode` of a layer in the front end's spelling. */
  private def spelledLayerNode(layer: Layer[Int]): Option[Int] = signatures.get(layer.map(root))

  /** The nodes that are not duplicates, in creation order, each with the
    * root of its class and its layer over the roots of its children's
    * classes now (the baseline's `fixpoint_egraph_live_node/4`).
    */
  def liveNodes: Vector[LiveNode] =
    nodes.indices.toVector
      .filter(live)
      .map(node => LiveNode(node, root(node), layer(node).map(root)))

  /** The live members of the class of the node, each with its layer over the
    * roots now: the applications first, then the parallels, the choices, the
    * thunks and the leaves, each in the order the class gained them (the
    * baseline's `fixpoint_egraph_member/4`).
    */
  def classMembers(node: Int): Vector[LiveNode] =
    val classRoot = root(node)
    MemberShape.values.toVector.flatMap(shape =>
      members(classRoot, shape).map(member =>
        LiveNode(member, classRoot, layer(member).map(root))
      )
    )

  /** The counts of the run so far (the baseline's
    * `fixpoint_egraph_statistics/2`).
    */
  def statistics: Statistics =
    Statistics(canonicalNodeCount, joiningUnionCount, instances, matchesFound)

  /** The class's closure states that are not dead, in the order added (the
    * baseline's `class_closures/2`).
    */
  def closureStates(classRoot: Int): Vector[ClosureState] =
    classes(classRoot).closures.fold(Vector.empty)(_.items.filter(liveState))

  /** A closure state is dead when its thunk is a duplicate: the thunk's twin
    * has its layer over the same classes, so that the twin's state, in the
    * same class, gives every application the same body (the baseline's
    * `entry_live/1`).
    */
  private def liveState(state: ClosureState): Boolean = live(state.thunk)

  private def liveNodes(entries: Vector[Int]): Vector[Int] =
    entries.filter(live)

  private def livePositionUsers(
      entries: Vector[PositionUser]
  ): Vector[PositionUser] =
    entries.filter(entry => live(entry.user))

  // ---- primitive updates ----

  private def nodeUpdated(node: Int)(update: NodeRecord => NodeRecord): EGraph =
    copy(nodes = nodes.updated(node, update(nodes(node))))

  private def classUpdated(classRoot: Int)(
      update: ClassData => ClassData
  ): EGraph =
    copy(classes = classes.updated(classRoot, update(classes(classRoot))))

  private def memberAdded(
      classRoot: Int,
      shape: MemberShape,
      node: Int
  ): EGraph =
    classUpdated(classRoot)(data =>
      data.membersReplaced(shape, data.members(shape).added(node))
    )

  private def userAdded(classRoot: Int, role: UserRole, node: Int): EGraph =
    classUpdated(classRoot)(data =>
      data.usersReplaced(role, data.users(role).added(node))
    )

  private def positionUserAdded(
      classRoot: Int,
      role: PositionRole,
      entry: PositionUser
  ): EGraph =
    classUpdated(classRoot)(data =>
      data.positionUsersReplaced(role, data.positionUsers(role).added(entry))
    )

  /** The baseline's `class_head_member_added/3`. */
  private def headMemberAdded(classRoot: Int, head: Head, node: Int): EGraph =
    classUpdated(classRoot)(data =>
      data.copy(headMembers =
        data.headMembers.updated(head, data.headEntries(head).added(node))
      )
    )

  /** The baseline's `class_head_added/2`. */
  private def classHeadAdded(classRoot: Int, head: Head): EGraph =
    classUpdated(classRoot)(data => data.copy(heads = data.heads :+ head))

  private def classHasHead(classRoot: Int, head: Head): Boolean =
    classes(classRoot).heads.contains(head)

  /** The baseline's `node_head_added/2`. */
  private def nodeHeadAdded(node: Int, head: Head): EGraph =
    nodeUpdated(node)(record => record.copy(heads = record.heads :+ head))

  /** The baseline's `class_closure_added/2`. */
  private def closureAdded(classRoot: Int, state: ClosureState): EGraph =
    classUpdated(classRoot)(data =>
      data.copy(closures =
        Some(data.closures.getOrElse(Entries.empty).added(state))
      )
    )

  // ---- the agenda and the counts ----

  /** The baseline's `delta_pushed/3`: the node matched again, by both kinds
    * of orientation, before the deltas pushed earlier.
    */
  def deltaPushed(node: Int): EGraph =
    copy(merges = node :: merges, deltas = node :: deltas)

  /** Every live node pushed as a delta of both kinds, the first node on top,
    * so that a saturation under another program matches the whole graph
    * again: a later lemma round on a graph an earlier round saturated
    * (rounds on one shared graph). No baseline predicate: the baseline runs one program.
    */
  def everyNodeRedone: EGraph =
    liveNodes.map(_.node).reverse.foldLeft(this)((graph, node) => graph.deltaPushed(node))

  /** The baseline's `merge_taken/3`. */
  def mergeTaken: Option[(Int, EGraph)] = merges match
    case node :: rest => Some((node, copy(merges = rest)))
    case Nil          => None

  /** The baseline's `delta_taken/3`. */
  def deltaTaken: Option[(Int, EGraph)] = deltas match
    case node :: rest => Some((node, copy(deltas = rest)))
    case Nil          => None

  /** The delta taken by `mergeTaken` put back on top of its stack, so
    * that it is matched again: the budget ended a saturation before every
    * match of the delta was applied, and a resumed saturation takes it
    * first. No baseline predicate: the baseline's run never resumes.
    */
  def mergeRestored(node: Int): EGraph =
    copy(merges = node :: merges)

  /** The delta taken by `deltaTaken` put back on top of its stack, as
    * `mergeRestored` does.
    */
  def deltaRestored(node: Int): EGraph =
    copy(deltas = node :: deltas)

  /** The baseline's `union_queued/5`, with the nodes the union's step made
    * (`UnionRecord.made`).
    */
  def unionQueued(
      first: Int,
      second: Int,
      justification: Justification,
      made: Option[MadeNodes]
  ): EGraph =
    copy(unionQueue =
      unionQueue.enqueue(PendingUnion(first, second, justification, made))
    )

  /** The baseline's `union_taken/3`. */
  def unionTaken: Option[(PendingUnion, EGraph)] =
    unionQueue.dequeueOption.map((pending, rest) =>
      (pending, copy(unionQueue = rest))
    )

  /** The baseline's `beta_queued/4`. */
  def betaQueued(application: Int, state: ClosureState): EGraph =
    copy(betaQueue = betaQueue.enqueue(PendingBeta(application, state)))

  /** The baseline's `beta_taken/3`, the β step counted. */
  def betaTaken: Option[(PendingBeta, EGraph)] =
    betaQueue.dequeueOption.map((pending, rest) =>
      (pending, copy(betaQueue = rest, betaSteps = betaSteps + 1))
    )

  /** The graph with its next pending β step taken off the queue and not
    * counted, nothing when none is pending: a round that does not enable
    * the β rule (`gezi.ir.BuiltInRule.Beta`) takes no β step.
    */
  def betaDiscarded: Option[EGraph] =
    betaQueue.dequeueOption.map((_, rest) => copy(betaQueue = rest))

  /** The baseline's `instance_key_added/3`: the graph with the key, or
    * nothing when the key is there.
    */
  def instanceKeyAdded(key: InstanceKey): Option[EGraph] =
    if instanceKeys.contains(key) then None
    else Some(copy(instanceKeys = instanceKeys + key))

  /** The baseline's `instance_counted/3`. */
  def instanceCounted: EGraph = copy(instances = instances + 1)

  /** The baseline's `matches_counted/3`, of the run's count only. */
  def matchesCounted(count: Int): EGraph =
    copy(matchesFound = matchesFound + count)

  /** The entries the matching of one delta read, counted. */
  def entriesReadCounted(count: Long): EGraph =
    copy(entriesRead = entriesRead + count)

  // ---- nodes (GraphBuilding) ----

  /** The baseline's `handle_added/4`. An instruction's term is expanded children
    * first through a stack of visits rather than the JVM's stack, since an
    * input may be as deep as it is large.
    */
  def instructionAdded(instruction: Instruction): (EGraph, Int) =
    instructionTable.get(instruction) match
      case Some(node) => (this, node)
      case None =>
        EGraph.instructionsExpanded(this, List(InstructionVisit.Enter(instruction)), Nil)

  /** The baseline's `handle_filed/4`: the instruction's node, and the node's
    * instruction when it has none.
    */
  private def instructionFiled(instruction: Instruction, node: Int): EGraph =
    val filed = copy(
      instructionTable = instructionTable.updated(instruction, node),
      instructionFilings = instructionFilings :+ (instruction, node)
    )
    if filed.nodes(node).instruction.isEmpty then
      filed.nodeUpdated(node)(record => record.copy(instruction = Some(instruction)))
    else filed

  /** The baseline's `handle_head_filed/4`: the class of the instruction's node has
    * the head of arity 0 when a matched side has a spine headed by the
    * instruction; a class that gains it has its users matched again. The node
    * may be an older node of the same layer.
    */
  private def instructionHeadFiled(instruction: Instruction, node: Int): EGraph =
    if headArityBounds.contains(instruction) then
      val classRoot = root(node)
      val head = Head(instruction, 0)
      if classHasHead(classRoot, head) then this
      else classHeadAdded(classRoot, head).classUsersPushed(classRoot)
    else this

  /** The baseline's `layer_added/4`. */
  def layerAdded(layer: Layer[Int]): (EGraph, Int) = layerMade(layer, closures = true)

  /** The layer added as `layerAdded` adds it, but a new thunk with a hole
    * gets no closure state of its own: the residual thunk of a partial
    * application, whose class has the application's closure state, which
    * holds the same arguments (`gezi.saturation.Saturation.residualThunk`).
    */
  def residualAdded(layer: Layer[Int]): (EGraph, Int) =
    require(layer.isInstanceOf[Thunk[?]], s"a residual is a thunk: $layer")
    layerMade(layer, closures = false)

  /** The graph that records the terms made from now on (explanation mode,
    * `explained`): every node's made layer filed, so that a layer made again
    * over the same nodes is that node. Only a graph with no union yet can
    * turn it on, since a node's made layer is its layer over roots only
    * while no union has moved a root (a compiled round's graph of pattern
    * instructions, which runs with or without a proof, turns it on for a run
    * whose proof is wanted). Throws `IllegalArgumentException` for a graph
    * with a union or one that records already.
    */
  def explaining: EGraph =
    require(!explained, "the graph records the terms made already")
    require(unions.isEmpty, s"a graph with ${unions.size} unions cannot start recording the terms made")
    copy(explained = true, madeNodes = HashMap.from(nodes.indices.map(node => nodes(node).made -> node)))

  /** The graph whose respelling memo keeps as the retention says from now
    * on, emptied under `MemoRetention.NotKept`, which changes only time.
    */
  def withRespellingRetention(retention: MemoRetention): EGraph =
    retention match
      case MemoRetention.Kept    => copy(respellingRetention = retention)
      case MemoRetention.NotKept => copy(respellingRetention = retention, respellings = HashMap.empty)

  /** The node of the layer over the nodes given. Without explanation mode,
    * the node of its signature (the layer over their roots) when the graph
    * has one, else a new node. In explanation mode, the node made over
    * exactly these nodes before; else, when the graph has a node of its
    * signature, a made duplicate of it; else a new node. A made duplicate
    * is born in the found node's class with its congruence only recorded,
    * not a union queued, so that the graph's classes, their sizes and every
    * choice that reads them are exactly those of the graph without it (a
    * queued union would leave it a class of its own, over which new
    * canonical nodes would be made, matched and later merged).
    *
    * A thunk with holes is made in the front end's spelling, its respelling
    * where it is not ([[Respelling]]).
    * The graph's input contract: every thunk is well-formed, its fillings
    * exactly the code's slots that no hole binds (`Code.fillingCount`).
    * Throws `IllegalArgumentException` for a thunk that is not.
    */
  private def layerMade(layer: Layer[Int], closures: Boolean): (EGraph, Int) =
    layer match
      case Thunk(code, holes, fillings) =>
        require(
          gezi.ir.Code.fillingCount(code, holes).contains(fillings.size),
          s"the thunk of the code $code with the holes $holes has ${fillings.size} fillings, but a well-formed one has " +
            s"${gezi.ir.Code.fillingCount(code, holes).fold("none (its holes bind no distinct slots of the code)")(_.toString)}"
        )
      case _ => ()
    layer match
      case Thunk(code, holes, fillings) if holes.nonEmpty =>
        val (read, respelling) = respellingRead(Respelling.Key(code, holes, fillings.size))
        respelling match
          case Respelling.Canonical => read.spelledLayerMade(layer, closures)
          case Respelling.Respelled(respelledCode, respelledHoles, respelledFillings) =>
            val (withFillings, fillingNodes) = respelledFillings.foldLeft((read, Vector.empty[Int])) {
              case ((current, made), filling) =>
                val (next, node) = gezi.ir.BindingNormalForm.placeholdersFolded(filling, fillings, current)(
                  (graph, spelled) => graph.layerMade(spelled, closures = true)
                )
                (next, made :+ node)
            }
            withFillings
              .copy(respellingCounts = withFillings.respellingCounts.withRespelled)
              .spelledLayerMade(Thunk(respelledCode, respelledHoles, fillingNodes), closures)
      case _ => spelledLayerMade(layer, closures)

  /** The memo's spelling of a thunk layer's code, holes and number of
    * fillings, computed when the memo has none and kept as the retention
    * says (`respellings`).
    */
  private def respellingRead(key: Respelling.Key): (EGraph, Respelling) =
    respellings.get(key) match
      case Some(found) => (copy(respellingCounts = respellingCounts.withRead), found)
      case None =>
        val computed = Respelling.of(key)
        val kept = respellingRetention match
          case MemoRetention.Kept    => respellings.updated(key, computed)
          case MemoRetention.NotKept => respellings
        (copy(respellings = kept, respellingCounts = respellingCounts.withComputed), computed)

  /** `layerMade` of a layer in the front end's spelling. */
  private def spelledLayerMade(layer: Layer[Int], closures: Boolean): (EGraph, Int) =
    if !explained then
      val rooted = layer.map(root)
      signatures.get(rooted) match
        case Some(found) => (this, found)
        case None        => layerNewlyMade(rooted, rooted, closures)
    else
      madeNodes.get(layer) match
        case Some(node) => (this, node)
        case None =>
          val rooted = layer.map(root)
          signatures.get(rooted) match
            case Some(found) => madeDuplicated(layer, found)
            case None        => layerNewlyMade(layer, rooted, closures)

  /** A made duplicate of the node of the signature, the layer over other
    * nodes of the same classes: a node of the found node's class from birth
    * (its parent the found node), a duplicate, never filed as a member or a
    * user, never pushed, priced or matched, and its congruence with the
    * found node recorded in the log (its children and the found node's are
    * pairwise in one class now, which the log's earlier unions explain). It
    * joins no class, so the classes, their sizes and every choice that reads
    * them are those of the graph without it.
    */
  private def madeDuplicated(layer: Layer[Int], found: Int): (EGraph, Int) =
    val node = nodes.size
    val made = copy(
      nodes = nodes :+ NodeRecord(
        // The found node's own layer object: the same signature, no copy.
        layer = nodes(found).layer,
        parent = found,
        heads = Vector.empty,
        instruction = None,
        duplicate = true,
        readable = false,
        made = layer
      ),
      classes = classes :+ ClassData.released,
      madeNodes = madeNodes.updated(layer, node),
      madeDuplicates = madeDuplicates + 1
    )
    (made.unionRecorded(node, found, Justification.Congruence, None), node)

  /** A new node of the signature, filed, pushed and priced; its made layer
    * is the layer given (the signature itself without explanation mode, so
    * that the record holds one layer object), filed when the graph records
    * the terms made.
    */
  private def layerNewlyMade(layer: Layer[Int], rooted: Layer[Int], closures: Boolean): (EGraph, Int) =
    val node = nodes.size
    val made = copy(
      nodes = nodes :+ NodeRecord(
        layer = rooted,
        parent = node,
        heads = Vector.empty,
        instruction = None,
        duplicate = false,
        readable = false,
        made = layer
      ),
      classes = classes :+ ClassData.single,
      signatures = signatures.updated(rooted, node),
      madeNodes = if explained then madeNodes.updated(layer, node) else madeNodes
    )
    val filed = made.layerFiled(rooted, node).deltaPushed(node)
    ((if closures then filed.layerClosures(rooted, node) else filed).nodePriced(node), node)

  /** The new node's class priced by the analysis, when the graph has one. */
  private def nodePriced(node: Int): EGraph =
    analysis.fold(this)(slot => copy(analysis = Some(slot.nodeMade(this, node))))

  /** The analysis's costs after a union made `big` the root of `small`'s
    * class, when the graph has one.
    */
  private def classesPriced(small: Int, big: Int): EGraph =
    analysis.fold(this)(slot => copy(analysis = Some(slot.classesJoined(this, small, big))))

  /** The baseline's `layer_filed/3`: the new node filed as a member of its
    * class and as a user of its children's classes, an application under
    * the heads its function's class gives it.
    */
  private def layerFiled(layer: Layer[Int], node: Int): EGraph = layer match
    case Apply(function, argument) =>
      val filed = memberAdded(node, MemberShape.Apply, node)
      functionHeads(function)
        .foldLeft(filed)((graph, head) => graph.newHeadFiled(node, head))
        .userAdded(function, UserRole.Function, node)
        .userAdded(argument, UserRole.Argument, node)
    case Parallel(left, right) =>
      memberAdded(node, MemberShape.Parallel, node)
        .userAdded(left, UserRole.Left, node)
        .userAdded(right, UserRole.Right, node)
    case Choice(left, right) =>
      Vector(left, right).zipWithIndex.foldLeft(
        memberAdded(node, MemberShape.Choice, node)
      ) { case (graph, (member, position)) =>
        graph.positionUserAdded(
          member,
          PositionRole.Member,
          PositionUser(position, node)
        )
      }
    case Thunk(_, _, fillings) =>
      fillings.zipWithIndex.foldLeft(
        memberAdded(node, MemberShape.Thunk, node)
      ) { case (graph, (filling, position)) =>
        graph.positionUserAdded(
          filling,
          PositionRole.Filling,
          PositionUser(position, node)
        )
      }
    case NoinlineLeaf(_) => memberAdded(node, MemberShape.Leaf, node)

  /** The baseline's `new_head_filed/2`. */
  private def newHeadFiled(node: Int, head: Head): EGraph =
    nodeHeadAdded(node, head)
      .headMemberAdded(node, head, node)
      .classHeadAdded(node, head)

  /** The baseline's `layer_closures/2`: a new thunk with a hole is the first
    * closure state of its class.
    */
  private def layerClosures(layer: Layer[Int], node: Int): EGraph =
    layer match
      case Thunk(_, holes, _) if holes.nonEmpty =>
        closureAdded(node, ClosureState(node, Nil, holes.size))
      case _ => this

  /** The baseline's `function_heads/3`: the heads an application of the
    * class has, one more argument than each head of the class within the
    * instruction's bound, in the order the class gained them.
    */
  private def functionHeads(function: Int): Vector[Head] =
    classes(function).heads.flatMap(head =>
      val arity = head.arity + 1
      headArityBounds.get(head.instruction) match
        case Some(bound) if arity <= bound => Some(Head(head.instruction, arity))
        case _                             => None
    )

  /** The baseline's `class_users_pushed/3`: every user of the class matched
    * again, an application of it filed under the heads it gains.
    */
  private def classUsersPushed(classRoot: Int): EGraph =
    val functionUsers = liveNodes(classes(classRoot).functionUsers.items)
    val afterFunctionUsers = functionUsers.foldLeft(this)((graph, user) =>
      graph.userHeadsFiled(user).deltaPushed(user)
    )
    val afterRoles =
      Vector(UserRole.Argument, UserRole.Left, UserRole.Right).foldLeft(
        afterFunctionUsers
      )((graph, role) =>
        graph
          .liveNodes(graph.classes(classRoot).users(role).items)
          .foldLeft(graph)((inner, user) => inner.deltaPushed(user))
      )
    PositionRole.values.toVector.foldLeft(afterRoles)(
      (graph, role) =>
        graph
          .livePositionUsers(graph.classes(classRoot).positionUsers(role).items)
          .foldLeft(graph)((inner, entry) => inner.deltaPushed(entry.user))
    )

  /** The baseline's `user_heads_filed/3`: an application filed under each
    * head its function's class has now.
    */
  private def userHeadsFiled(user: Int): EGraph = nodes(user).layer match
    case Apply(function, _) =>
      val functionRoot = root(function)
      val userRoot = root(user)
      functionHeads(functionRoot).foldLeft(this)((graph, head) =>
        graph.userHeadFiled(user, userRoot, head)
      )
    case _ => this

  /** The baseline's `user_head_filed/5`. */
  private def userHeadFiled(user: Int, userRoot: Int, head: Head): EGraph =
    if nodes(user).heads.contains(head) then this
    else
      val filed = nodeHeadAdded(user, head)
        .headMemberAdded(userRoot, head, user)
        .deltaPushed(user)
      if filed.classHasHead(userRoot, head) then filed
      else filed.classHeadAdded(userRoot, head).classUsersPushed(userRoot)

  // ---- the β rule ----

  /** The baseline's `application_read/3`: the application takes a β step
    * with every live closure state of its function's class, now and when the
    * class gains one. Only the node given is marked.
    */
  def applicationRead(node: Int): EGraph =
    val record = nodes(node)
    if record.readable then this
    else
      record.layer match
        case Apply(function, _) =>
          val marked = nodeUpdated(node)(_.copy(readable = true))
          marked.closureStates(marked.root(function)).foldLeft(marked)(
            (graph, state) => graph.betaQueued(node, state)
          )
        case other =>
          throw IllegalArgumentException(
            s"node $node read by the β rule is not an application: $other"
          )

  /** The branch of the baseline's `beta_worked/4` with a hole left: the
    * state is a new closure state of the application's class, which meets
    * every readable application of the class, and the application is
    * matched again.
    */
  def closureStateExtended(application: Int, state: ClosureState): EGraph =
    val applicationRoot = root(application)
    val withState = closureAdded(applicationRoot, state)
    withState
      .liveNodes(withState.classes(applicationRoot).functionUsers.items)
      .foldLeft(withState)((graph, user) => graph.stateMetUser(state, user))
      .deltaPushed(application)

  /** The baseline's `state_meets_user/4`. */
  private def stateMetUser(state: ClosureState, user: Int): EGraph =
    if nodes(user).readable then betaQueued(user, state) else this

  // ---- unions ----

  /** The baseline's `union_worked/5`: the two classes made one, the smaller
    * filed again under the larger root (the first node's root on a tie), its
    * users read again; recorded with the nodes the union's step made
    * (`UnionRecord.made`).
    */
  def unionWorked(
      first: Int,
      second: Int,
      justification: Justification,
      made: Option[MadeNodes]
  ): EGraph =
    val firstRoot = root(first)
    val secondRoot = root(second)
    if firstRoot == secondRoot then this
    else
      val firstSize = classes(firstRoot).size
      val secondSize = classes(secondRoot).size
      val (big, small) =
        if firstSize >= secondSize then (firstRoot, secondRoot)
        else (secondRoot, firstRoot)
      val joined = closuresJoined(small, big)
      val gainedHeads =
        joined.classes(small).heads.filterNot(joined.classHasHead(big, _))
      val linked = joined
        .nodeUpdated(small)(_.copy(parent = big))
        .classUpdated(big)(_.copy(size = firstSize + secondSize))
        .unionRecorded(first, second, justification, made)
      val headed =
        if gainedHeads.isEmpty then linked
        else
          gainedHeads
            .foldLeft(linked)((graph, head) => graph.classHeadAdded(big, head))
            .classUsersPushed(big)
      headed
        .membersMoved(small, big)
        .usersMoved(small, big)
        .classUpdated(small)(_ => ClassData.released)
        .classesPriced(small, big)

  private def unionRecorded(
      first: Int,
      second: Int,
      justification: Justification,
      made: Option[MadeNodes]
  ): EGraph =
    copy(unions = unions :+ UnionRecord(first, second, justification, made))

  /** The baseline's `closures_joined/4`: every live closure state of one
    * class meets every readable application of the other, the small class's
    * states added to the big one's.
    */
  private def closuresJoined(small: Int, big: Int): EGraph =
    val smallStates = closureStates(small)
    val bigStates = closureStates(big)
    smallStates
      .foldLeft(this)((graph, state) => graph.closureAdded(big, state))
      .statesMetClass(smallStates, big)
      .statesMetClass(bigStates, small)

  /** The baseline's `states_meet_class/4`. */
  private def statesMetClass(
      states: Vector[ClosureState],
      classRoot: Int
  ): EGraph =
    if states.isEmpty then this
    else
      val functionUsers = liveNodes(classes(classRoot).functionUsers.items)
      states.foldLeft(this)((graph, state) =>
        functionUsers.foldLeft(graph)((inner, user) =>
          inner.stateMetUser(state, user)
        )
      )

  /** The baseline's `members_moved/4`: the applications, then the members of
    * each head, then the other shapes.
    */
  private def membersMoved(small: Int, big: Int): EGraph =
    val afterApplications = shapeMembersMoved(small, big, MemberShape.Apply)
    val afterHeads = afterApplications
      .classes(small)
      .heads
      .foldLeft(afterApplications)((graph, head) =>
        graph.headMembersMoved(small, big, head)
      )
    Vector(
      MemberShape.Parallel,
      MemberShape.Choice,
      MemberShape.Thunk,
      MemberShape.Leaf
    ).foldLeft(afterHeads)((graph, shape) =>
      graph.shapeMembersMoved(small, big, shape)
    )

  private def shapeMembersMoved(
      small: Int,
      big: Int,
      shape: MemberShape
  ): EGraph =
    liveNodes(classes(small).members(shape).items).foldLeft(this)(
      (graph, node) => graph.memberAdded(big, shape, node).deltaPushed(node)
    )

  private def headMembersMoved(small: Int, big: Int, head: Head): EGraph =
    liveNodes(classes(small).headEntries(head).items).foldLeft(this)(
      (graph, node) => graph.headMemberAdded(big, head, node)
    )

  /** The baseline's `users_moved/4`: the users of each role, read when the
    * role's turn comes, filed under the larger class and read again.
    */
  private def usersMoved(small: Int, big: Int): EGraph =
    val afterRoles = UserRole.values.toVector.foldLeft(this)((graph, role) =>
      graph
        .liveNodes(graph.classes(small).users(role).items)
        .foldLeft(graph)((inner, user) =>
          inner.userAdded(big, role, user).userReadAgain(user)
        )
    )
    PositionRole.values.toVector.foldLeft(afterRoles)(
      (graph, role) =>
        graph
          .livePositionUsers(graph.classes(small).positionUsers(role).items)
          .foldLeft(graph)((inner, entry) =>
            inner.positionUserAdded(big, role, entry).userReadAgain(entry.user)
          )
    )

  /** The baseline's `user_read_again/3`: a user of a class that a union
    * moved, read over the roots: united with the node that has its
    * signature, itself marked a duplicate, or filed under the signature, and
    * matched again. A duplicate is not read again.
    */
  private def userReadAgain(user: Int): EGraph =
    val record = nodes(user)
    if record.duplicate then this
    else
      val key = record.layer.map(root)
      signatures.get(key) match
        case Some(found) if found == user =>
          userHeadsFiled(user).deltaPushed(user)
        case Some(found) =>
          duplicateMarked(user).unionQueued(user, found, Justification.Congruence, None)
        case None =>
          copy(signatures = signatures.updated(key, user))
            .userHeadsFiled(user)
            .deltaPushed(user)

  /** The baseline's `duplicate_marked/1`: the node marked a duplicate, which
    * every reader skips, and counted dead in the entries that hold it: of its
    * class as a member, by shape and by head, a thunk's first closure state
    * in its class, and of its children's classes as a user.
    */
  private def duplicateMarked(node: Int): EGraph =
    val marked = nodeUpdated(node)(_.copy(duplicate = true))
    val record = marked.nodes(node)
    val nodeRoot = marked.root(node)
    val shape = shapeOf(record.layer)
    val memberDead = marked.classUpdated(nodeRoot)(data =>
      data.membersReplaced(shape, data.members(shape).oneDead(marked.live))
    )
    record.heads
      .foldLeft(memberDead.closureStateDead(nodeRoot, record.layer))(
        (graph, head) => graph.headEntriesDead(nodeRoot, head)
      )
      .layerUsersDead(record.layer)

  /** The baseline's `layer_closures_dead/2`: a thunk with a hole holds the
    * first closure state of its class, dead with it. The states made from it
    * by β steps, in the classes of the applications that took them, are
    * skipped as dead and not counted.
    */
  private def closureStateDead(classRoot: Int, layer: Layer[Int]): EGraph =
    layer match
      case Thunk(_, holes, _) if holes.nonEmpty =>
        classUpdated(classRoot)(data =>
          data.copy(closures = data.closures.map(_.oneDead(liveState)))
        )
      case _ => this

  private def headEntriesDead(classRoot: Int, head: Head): EGraph =
    classes(classRoot).headMembers.get(head) match
      case Some(entries) =>
        classUpdated(classRoot)(data =>
          data.copy(headMembers =
            data.headMembers.updated(head, entries.oneDead(live))
          )
        )
      case None => this

  private def layerUsersDead(layer: Layer[Int]): EGraph = layer match
    case Apply(function, argument) =>
      childUserDead(UserRole.Function, function)
        .childUserDead(UserRole.Argument, argument)
    case Parallel(left, right) =>
      childUserDead(UserRole.Left, left).childUserDead(UserRole.Right, right)
    case Choice(left, right) =>
      childPositionUserDead(PositionRole.Member, left)
        .childPositionUserDead(PositionRole.Member, right)
    case Thunk(_, _, fillings) =>
      fillings.foldLeft(this)((graph, filling) =>
        graph.childPositionUserDead(PositionRole.Filling, filling)
      )
    case NoinlineLeaf(_) => this

  private def childUserDead(role: UserRole, child: Int): EGraph =
    classUpdated(root(child))(data =>
      data.usersReplaced(role, data.users(role).oneDead(live))
    )

  private def childPositionUserDead(role: PositionRole, child: Int): EGraph =
    classUpdated(root(child))(data =>
      data.positionUsersReplaced(
        role,
        data.positionUsers(role).oneDead(entry => live(entry.user))
      )
    )

/** A step of the expansion of an instruction: enter it (find its node, or expand
  * its children), or leave it once its children have their nodes.
  */
private enum InstructionVisit:
  case Enter(instruction: Instruction)
  case Leave(instruction: Instruction, layer: Layer[Instruction])

object EGraph:

  /** The graph of no node, over the store, filing heads within the bounds,
    * recording the terms made when `explained` (a run whose proof or trace
    * is wanted; `explaining`), its respelling memo keeping what it computes
    * (`withRespellingRetention` chooses otherwise).
    */
  def empty(store: Store, headArityBounds: Map[Instruction, Int], explained: Boolean): EGraph = EGraph(
    store = store,
    headArityBounds = headArityBounds,
    nodes = Vector.empty,
    classes = Vector.empty,
    signatures = HashMap.empty,
    instanceKeys = HashSet.empty,
    instructionTable = HashMap.empty,
    instructionFilings = Vector.empty,
    unions = Vector.empty,
    unionQueue = Queue.empty,
    betaQueue = Queue.empty,
    merges = Nil,
    deltas = Nil,
    instances = 0,
    matchesFound = 0,
    betaSteps = 0,
    entriesRead = 0,
    analysis = None,
    explained = explained,
    madeNodes = HashMap.empty,
    madeDuplicates = 0,
    respellings = HashMap.empty,
    respellingCounts = RespellingCounts(0, 0L, 0L),
    respellingRetention = MemoRetention.Kept
  )

  /** The visits of the baseline's recursive `handle_added/4`, run off a
    * stack: an instruction entered is found, or its children are entered in order
    * before it is left; leaving it adds its layer over its children's nodes,
    * files the instruction and its head. `results` holds the nodes of the
    * instructions left, the latest first.
    */
  @tailrec
  private def instructionsExpanded(
      graph: EGraph,
      visits: List[InstructionVisit],
      results: List[Int]
  ): (EGraph, Int) = visits match
    case Nil =>
      results match
        case List(node) => (graph, node)
        case other =>
          throw IllegalStateException(
            s"the expansion of an instruction ended with the nodes $other"
          )
    case InstructionVisit.Enter(instruction) :: rest =>
      graph.instructionTable.get(instruction) match
        case Some(node) => instructionsExpanded(graph, rest, node :: results)
        case None =>
          val layer = graph.store.expanded(instruction)
          instructionsExpanded(
            graph,
            layer.children.toList.map(InstructionVisit.Enter(_)) :::
              (InstructionVisit.Leave(instruction, layer) :: rest),
            results
          )
    case InstructionVisit.Leave(instruction, layer) :: rest =>
      val (childrenReversed, others) = results.splitAt(layer.children.size)
      val (added, node) =
        graph.layerAdded(layerOver(layer, childrenReversed.reverse.toVector))
      instructionsExpanded(
        added.instructionFiled(instruction, node).instructionHeadFiled(instruction, node),
        rest,
        node :: others
      )

  /** The layer with its children replaced, in child order. */
  private def layerOver(layer: Layer[Instruction], children: Vector[Int]): Layer[Int] =
    (layer, children) match
      case (Apply(_, _), Vector(function, argument)) =>
        Apply(function, argument)
      case (Parallel(_, _), Vector(left, right)) =>
        Parallel(left, right)
      case (Choice(_, _), Vector(left, right)) => Choice(left, right)
      case (Thunk(code, holes, _), fillings) =>
        Thunk(code, holes, fillings)
      case (NoinlineLeaf(instruction), Vector()) => NoinlineLeaf(instruction)
      case (other, nodes) =>
        throw IllegalStateException(
          s"the layer $other cannot take the children $nodes"
        )
