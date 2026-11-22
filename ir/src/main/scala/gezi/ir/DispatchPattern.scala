package gezi.ir

/** What stands around the typed application `F (A ∥ D)` in the typed member
  * of a specialization: nothing; a parallel by the range R,
  * `F (A ∥ D) ∥ R`; or a contract C applied to it, `C (F (A ∥ D))`, C a
  * term whose spelling is λf. f (`DispatchPattern.identityContract`), the
  * typed member of a curried function's contract.
  */
enum SpecializationRange[+Node]:
  case Absent
  case Filtered(range: Node)
  case Contracted(contract: Node)

  /** The node of the range or of the contract, if any. */
  def nodes: Vector[Node] = this match
    case Absent               => Vector.empty
    case Filtered(range)      => Vector(range)
    case Contracted(contract) => Vector(contract)

/** A specialization choice, `F A + T` in either order, T its typed member
  * `F (A ∥ D)` under the range (`SpecializationRange`): an untyped
  * application and its typed version overlapped (the vocabulary's
  * specialization). `untypedFirst` says the order the choice was written in.
  */
final case class Specialization[+Node](
    function: Node,
    argument: Node,
    domain: Node,
    range: SpecializationRange[Node],
    untypedFirst: Boolean
):

  /** The function, the argument, the domain and the range's node, in that
    * order.
    */
  def parts: Vector[Node] = Vector(function, argument, domain) ++ range.nodes

  /** The specialization with each part mapped. */
  def map[Result](mapping: Node => Result): Specialization[Result] =
    val mappedRange: SpecializationRange[Result] = range match
      case SpecializationRange.Absent               => SpecializationRange.Absent
      case SpecializationRange.Filtered(found)      => SpecializationRange.Filtered(mapping(found))
      case SpecializationRange.Contracted(contract) => SpecializationRange.Contracted(mapping(contract))
    Specialization(mapping(function), mapping(argument), mapping(domain), mappedRange, untypedFirst)

/** A judgment, `X + (X ∥ T)` in either order, which is X by law (6), the
  * absorption. `valueFirst` says the order the choice was written in.
  */
final case class Fallback[+Node](value: Node, criterion: Node, valueFirst: Boolean):

  /** The value and the criterion, in that order. */
  def parts: Vector[Node] = Vector(value, criterion)

/** THE DISPATCH PATTERNS: the one recognizer of the specialization choices
  * and the judgments, for every reader that needs them, over a view of a
  * node as the layers it may be read as (`layers`), the children compared by
  * `==`. The refinement reads them on instructions and on codes
  * (`gezi.jit.StrategyDispatch`), the extraction on the classes of an
  * e-graph (`gezi.extraction.Extraction.productions`), and the cost
  * modules on resolved codes (`gezi.strategies.TermReading`), so that
  * what the refinement dispatches is what the extraction prices (the
  * extraction's rule, `gezi.strategies.ModuleCostModel`, THE PRICE OF
  * A CHOICE). It reads layers only, and names no combinator, lemma or type
  * (`CONTRIBUTING.md`, "Types live only in the term").
  */
object DispatchPattern:

  /** The specialization choices the choice of the two members is read as,
    * the untyped member on either side. `identityContract` says whether a
    * node's spelling is λf. f, for the curried typed member.
    *
    * The curried typed member is read only where the contract's spelling is
    * fixed: in a code, a slot whose filling's own layers are read
    * (`noContract` elsewhere). In an e-graph a class whose members include
    * such a closure may be spelled by another member, which no reader of the
    * spelling takes for a contract, so the extraction would price as a
    * specialization a choice the refinement runs whole
    * (`DispatchPatternLawTest`, 2026-11-13: the contract's class spelled by an
    * application); the refinement reads an instruction the same way.
    */
  def specializations[Node](
      left: Node,
      right: Node,
      layers: Node => Vector[Layer[Node]],
      identityContract: Node => Boolean
  ): Vector[Specialization[Node]] =
    val parallels = parallelLayers(layers)
    specializationsRead(reading(left, layers, parallels, identityContract), reading(right, layers, parallels, identityContract))

  /** No node is read as a contract: the view of instructions and of e-graph
    * classes (`specializations`).
    */
  def noContract[Node](node: Node): Boolean = false

  /** The judgments the choice of the two members is read as, the value on
    * either side.
    */
  def fallbacks[Node](left: Node, right: Node, layers: Node => Vector[Layer[Node]]): Vector[Fallback[Node]] =
    val parallels = parallelLayers(layers)
    fallbacksRead(left, right, reading(left, layers, parallels, noContract), reading(right, layers, parallels, noContract))

  /** A node read once for the dispatch patterns (`reading`): the positions
    * of its applications `F A` among its layers, keyed by (F, A); the typed
    * members `F (A ∥ D)` it may be read as, each with its range, in the order
    * of its layers, of the applications each layer is read as and of the
    * parallels of each argument; and its parallels `V ∥ C`.
    *
    * A choice is matched by looking its untyped member's keys up for each
    * typed member of the other side, so that a choice costs the typed
    * members and the matches, and each node is read once for all the choices
    * it is a member of, not once per member of the other side: the join is
    * keyed by what the pattern requires. Measured on
    * 2026-11-13 (a scratch probe, programfamilies' size families at 64, 128
    * and 256): folds at 256 holds a class of 523 members, 518 of them
    * applications of one function, on both sides of eight choices, which
    * the nested loop of the members read in 606,815 class readings building
    * 146,581,966 members; nested at 256 holds a class of 521 members, one
    * side of 517 choices.
    */
  final case class Reading[Node](
      applications: Map[(Node, Node), Vector[Int]],
      typedMembers: Vector[(Node, Node, Node, SpecializationRange[Node])],
      parallels: Vector[(Node, Node)]
  )

  /** The node's reading for the dispatch patterns, over its layers, the
    * parallels of each node (`parallelLayers`) and the contracts.
    */
  def reading[Node](
      node: Node,
      layers: Node => Vector[Layer[Node]],
      parallels: Node => Vector[(Node, Node)],
      identityContract: Node => Boolean
  ): Reading[Node] =
    val nodeLayers = layers(node)
    val applications = nodeLayers.zipWithIndex
      .collect { case (Apply(function, argument), position) => ((function, argument), position) }
      .groupMap(_._1)(_._2)
    val typedMembers =
      for
        typedLayer <- nodeLayers
        (function, filtered, range) <- typedApplications(typedLayer, layers, identityContract)
        (argument, domain) <- parallels(filtered)
      yield (function, argument, domain, range)
    Reading(applications, typedMembers, parallels(node))

  /** The parallels `V ∥ C` among a node's layers, each as (V, C). */
  def parallelLayers[Node](layers: Node => Vector[Layer[Node]]): Node => Vector[(Node, Node)] =
    node => layers(node).collect { case Parallel(value, criterion) => (value, criterion) }

  /** `specializations` of the two members' readings: for each orientation,
    * the untyped member's applications in the order of its layers and, for
    * each, the typed member's matches in the order of its typed members.
    */
  def specializationsRead[Node](left: Reading[Node], right: Reading[Node]): Vector[Specialization[Node]] =
    oriented(left, right, untypedFirst = true) ++ oriented(right, left, untypedFirst = false)

  /** `fallbacks` of the two members and their readings. */
  def fallbacksRead[Node](left: Node, right: Node, leftReading: Reading[Node], rightReading: Reading[Node]): Vector[Fallback[Node]] =
    rightReading.parallels.collect { case (value, criterion) if value == left => Fallback(left, criterion, valueFirst = true) } ++
      leftReading.parallels.collect { case (value, criterion) if value == right => Fallback(right, criterion, valueFirst = false) }

  private def oriented[Node](untyped: Reading[Node], typed: Reading[Node], untypedFirst: Boolean): Vector[Specialization[Node]] =
    typed.typedMembers.zipWithIndex
      .flatMap { case ((function, argument, domain, range), typedPosition) =>
        untyped.applications
          .getOrElse((function, argument), Vector.empty)
          .map(untypedPosition => (untypedPosition, typedPosition, Specialization(function, argument, domain, range, untypedFirst)))
      }
      .sortBy((untypedPosition, typedPosition, _) => (untypedPosition, typedPosition))
      .map(_._3)

  /** The typed applications `F P` the typed member's layer is read as, each
    * with its function, its argument P and the range around it.
    */
  private def typedApplications[Node](
      layer: Layer[Node],
      layers: Node => Vector[Layer[Node]],
      identityContract: Node => Boolean
  ): Vector[(Node, Node, SpecializationRange[Node])] = layer match
    case Apply(function, filtered) =>
      val contracted =
        if identityContract(function) then
          layers(filtered).collect { case Apply(inner, argument) =>
            (inner, argument, SpecializationRange.Contracted(function))
          }
        else Vector.empty
      (function, filtered, SpecializationRange.Absent) +: contracted
    case Parallel(application, range) =>
      layers(application).collect { case Apply(function, filtered) =>
        (function, filtered, SpecializationRange.Filtered(range))
      }
    case _ => Vector.empty

  /** The typed member of the specialization, built by `make` over its
    * parts: `F (A ∥ D)`, `F (A ∥ D) ∥ R` or `C (F (A ∥ D))`.
    */
  def typedMember[Node](specialization: Specialization[Node], make: Layer[Node] => Node): Node =
    val application = make(Apply(specialization.function, make(Parallel(specialization.argument, specialization.domain))))
    specialization.range match
      case SpecializationRange.Absent               => application
      case SpecializationRange.Filtered(range)      => make(Parallel(application, range))
      case SpecializationRange.Contracted(contract) => make(Apply(contract, application))

  /** The specialization choice spelled by `make` over its parts, in the
    * order it was written in.
    */
  def spelled[Node](specialization: Specialization[Node], make: Layer[Node] => Node): Node =
    val untyped = make(Apply(specialization.function, specialization.argument))
    val typed = typedMember(specialization, make)
    make(if specialization.untypedFirst then Choice(untyped, typed) else Choice(typed, untyped))

  /** The judgment spelled by `make` over its parts, in the order it was
    * written in.
    */
  def spelled[Node](fallback: Fallback[Node], make: Layer[Node] => Node): Node =
    val filtered = make(Parallel(fallback.value, fallback.criterion))
    make(if fallback.valueFirst then Choice(fallback.value, filtered) else Choice(filtered, fallback.value))

  /** The layers of a code read as a node: its own, a slot having none. */
  def codeLayers(code: Code): Vector[Layer[Code]] = code.layer match
    case Slot(_)                      => Vector.empty
    case Apply(function, argument)    => Vector(Apply(function, argument))
    case Parallel(left, right)        => Vector(Parallel(left, right))
    case Choice(left, right)          => Vector(Choice(left, right))
    case Thunk(inner, holes, fillings) => Vector(Thunk(inner, holes, fillings))

  /** The node's spelling is λf. f by its syntax, as the refinement runs it:
    * one of its layers is an identity contract (`identityContractLayer`),
    * each filling read by this function in turn. A node met again while it
    * is being read is not one.
    */
  def identityContract[Node](node: Node, layers: Node => Vector[Layer[Node]]): Boolean =
    contracted(node, layers, Set.empty)

  private def contracted[Node](node: Node, layers: Node => Vector[Layer[Node]], visiting: Set[Node]): Boolean =
    !visiting.contains(node) && layers(node).exists(identityContractLayer(_, contracted(_, layers, visiting + node)))

  /** The layer is λf. f by its syntax, as the refinement runs it, its
    * fillings read by `fillingIdentity`: a thunk of two holes whose code,
    * read as the refinement leaves it up to its judgments (`absorbed`), is
    * `f y`, or `c (f y)` with c a filling that is one. One definition for
    * a node read through its layers (`identityContract`) and for an entry
    * of the extraction read through its children's entries.
    */
  def identityContractLayer[Node](layer: Layer[Node], fillingIdentity: Node => Boolean): Boolean = layer match
    case Thunk(code, holes @ Vector(Hole.Bound(functionHole), Hole.Bound(argumentHole)), fillings) =>
      def slotIdentity(slotCode: Code): Boolean = slotCode match
        case Code.Slot(slot) => filling(holes, fillings, slot).exists(fillingIdentity)
        case _               => false
      absorbed(code, slotIdentity) match
        case Code.Apply(Code.Slot(`functionHole`), Code.Slot(`argumentHole`)) => true
        case Code.Apply(Code.Slot(contractSlot), Code.Apply(Code.Slot(`functionHole`), Code.Slot(`argumentHole`))) =>
          filling(holes, fillings, contractSlot).exists(fillingIdentity)
        case _ => false
    case _ => false

  /** The code as the refinement runs it, read up to its judgments: each
    * judgment on its spine and in its arguments read as its value, and each
    * specialization choice as its untyped application `F A`, the contracts
    * of its curried members read by `identityContract`. The refinement turns
    * a specialization choice into its typed member with a fallback point
    * where a criterion decodes, `F (A + (A ∥ D))` and its range likewise,
    * and with no check where it does not, `F A`, both `F A` up to their
    * judgments; a curried member `C (F A)` with C read as λf. f. A contract
    * whose code holds a specialization choice, the contract of a curried
    * function's last argument, is then read as λf. f, as the refinement
    * reads it once its fillings are refined (CLOSUREPROBE, 2026-11-13:
    * `cons (f zero) nil` in a closure's body, whose typed member's contract
    * is `λf y. f y + (f (y ∥ T)) ∥ T`).
    */
  def absorbed(code: Code, identityContract: Code => Boolean): Code = code match
    case Code.Choice(left, right) =>
      fallbacks(left, right, codeLayers).headOption match
        case Some(found) => absorbed(found.value, identityContract)
        case None =>
          specializations(left, right, codeLayers, identityContract).headOption match
            case Some(found) => absorbed(Code.Apply(found.function, found.argument), identityContract)
            case None        => code
    case Code.Apply(function, argument) => Code.Apply(absorbed(function, identityContract), absorbed(argument, identityContract))
    case other                          => other

  /** The filling a thunk of the holes and fillings puts in the slot, none
    * when a hole binds it: the fillings fill the slots no hole binds, in
    * ascending order.
    */
  def filling[Node](holes: Vector[Hole], fillings: Vector[Node], slot: Int): Option[Node] =
    if holes.contains(Hole.Bound(slot)) then None
    else fillings.lift((0 until slot).count(index => !holes.contains(Hole.Bound(index))))
