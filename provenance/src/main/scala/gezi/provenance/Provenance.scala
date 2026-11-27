package gezi.provenance

import gezi.egraph.EGraph
import gezi.egraph.Justification
import gezi.extraction.Extracted
import gezi.extraction.Extraction
import gezi.extraction.Shape
import gezi.extraction.Spelled
import gezi.ir.Code
import gezi.ir.CodeLayer
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.ir.Pattern
import gezi.locations.Location
import gezi.locations.SourceMap
import scala.annotation.tailrec
import scala.collection.immutable.HashMap
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Slot, Thunk}
import gezi.ir.{Configured, NativeSpecializer}

/** The locations of an e-graph's nodes: those each node was given (`own`) and
  * the maps of the codes of its thunk nodes (`codeMaps`), one for each located
  * occurrence of the thunk, which the β steps of the thunk walk.
  */
final case class Provenance(
    own: HashMap[Int, Set[Location]],
    codeMaps: HashMap[Int, Vector[SourceMap]]
):

  /** The locations the node was given. */
  def node(node: Int): Set[Location] = own.getOrElse(node, Set.empty)

  /** The locations of the node's class: those of all its live members. */
  def ofClass[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      node: Int
  ): Set[Location] =
    graph
      .classMembers(graph.root(node))
      .flatMap(member => this.node(member.node))
      .toSet

  /** The node's own locations, or its class's when it was given none. */
  def locations[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      node: Int
  ): Set[Location] =
    val ownLocations = this.node(node)
    if ownLocations.nonEmpty then ownLocations else ofClass(graph, node)

  /** The provenance with derived locations added to the node's, unless an input
    * located the node (a `Source` among its locations), whose locations it
    * keeps: a node a walk meets at several places, such as two equal subterms
    * of one body, takes the locations of each.
    */
  private[provenance] def firstLocated(
      node: Int,
      locations: Set[Location]
  ): Provenance =
    val present = this.node(node)
    if locations.isEmpty || present.exists {
        case Location.Source(_, _) => true
        case _                     => false
      }
    then this
    else copy(own = own.updated(node, present ++ locations))

  private[provenance] def withLocations(
      node: Int,
      locations: Set[Location]
  ): Provenance =
    if locations.isEmpty then this
    else copy(own = own.updated(node, this.node(node) ++ locations))

  private[provenance] def withCodeMap(node: Int, map: SourceMap): Provenance =
    copy(codeMaps =
      codeMaps.updated(node, codeMaps.getOrElse(node, Vector.empty) :+ map)
    )

  /** The source map of a production's shape over its children's maps, in the
    * order of `Shape.children`: what `Extraction.spelled` spells of the shape,
    * located. A node's map holds the node's locations (`locations`) and, for a
    * thunk node, the code maps of the node merged; a leaf, and a name, which
    * spells its class in one leaf, are a leaf of their node's locations.
    */
  def shapeMap[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      shape: Shape[C],
      children: Vector[SourceMap]
  ): SourceMap =
    shape match
      case Shape.Name(instruction) =>
        SourceMap.leaf(
          graph
            .instructionNode(instruction)
            .fold(Set.empty[Location])(locations(graph, _))
        )
      case Shape.Node(node, NoinlineLeaf(_)) =>
        SourceMap.leaf(locations(graph, node))
      case Shape.Node(node, Thunk(_, _, _)) =>
        SourceMap(
          locations(graph, node),
          codeMaps.get(node).flatMap(_.reduceOption(_.merged(_))),
          children,
          Vector.empty
        )
      case Shape.Node(node, _) =>
        SourceMap(locations(graph, node), None, children, Vector.empty)
      case Shape.Specialized(node, _) =>
        patternMap(graph, node, shape, children)
      case Shape.Judged(node, _) => patternMap(graph, node, shape, children)

  /** The map of a dispatch pattern spelled over its parts' maps: each layer the
    * pattern builds holds the locations of the choice node it is read off.
    */
  private def patternMap[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      node: Int,
      shape: Shape[C],
      children: Vector[SourceMap]
  ): SourceMap =
    val nodeLocations = locations(graph, node)
    Shape.spelled[C, SourceMap](
      shape,
      children,
      _ => SourceMap.leaf(nodeLocations),
      layer => SourceMap(nodeLocations, None, layer.children, Vector.empty)
    )(using
      gezi.ir.NotTerm.granted[SourceMap]
    ) // a source map is locations, no term of the IR

  /** The source maps of the roots' spellings by the extraction, the roots
    * spelled in order with one memo of the classes spelled, as a caller that
    * spells its outputs of the same roots in the same order does: each map has
    * the shape of the instruction spelled of its root.
    */
  def extracted[C <: NativeSpecializer & Singleton, Cost](
      graph: EGraph[C],
      extracted: Extracted[C, Cost],
      roots: Vector[Int]
  ): Vector[SourceMap] =
    roots
      .foldLeft(
        (Spelled[SourceMap, Unit]((), Map.empty), Vector.empty[SourceMap])
      ) { case ((state, maps), root) =>
        val (after, map) = Extraction.spelled(extracted, root, state)(
          (unit, shape, children) => (unit, shapeMap(graph, shape, children))
        )
        (after, maps :+ map)
      }
      ._2

object Provenance:

  /** A term added to the graph with the source map of its occurrence. */
  final case class Input[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      map: SourceMap
  )

  /** The locations of the graph's nodes:
    *
    *   - an input's places give their locations to the nodes of their
    *     instructions, a thunk's place its code map to the thunk's node;
    *   - then the union log, in order: a lemma's instance walks its added side,
    *     the side of the newer root (an instance's union puts the lemma's left
    *     side first, so the log does not say which side was added, and the
    *     added root is made after the matched one), along the nodes the
    *     instance built, a node met taking `Rewritten(lemma, l)` for each
    *     location l of the matched root; a β step (`Justification.Beta(thunk)`)
    *     walks each code map of the thunk along the body, a node met taking
    *     `Inlined(c, a)` for each location c of the code's place and a of the
    *     application (nothing when the application has none: c alone would say
    *     the node is written at c, where its code is written with a variable or
    *     a binder more), and a residual thunk of the same code takes
    *     `Inlined(t, a)` for each location t of the thunk and its code maps;
    *     every other union gives nothing.
    *
    * A node an input located keeps its input's locations and takes none derived
    * (`firstLocated`); a node given nothing has its class's locations
    * (`locations`). The lemmas are given by their sides; an instance of a lemma
    * not given walks nothing.
    */
  def of[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      inputs: Vector[Input[C]],
      lemmas: Map[LemmaIdentifier, (Pattern[C], Pattern[C])]
  ): Provenance =
    val fromInputs = inputs.foldLeft(Provenance(HashMap.empty, HashMap.empty))(
      (provenance, input) =>
        inputPlaces(graph, List((input.instruction, input.map)), provenance)
    )
    graph.unions.foldLeft(fromInputs)((provenance, union) =>
      union.justification match
        case Justification.Lemma(lemma, _) =>
          lemmas.get(lemma).fold(provenance) { (left, right) =>
            val (added, addedRoot, matchedRoot) =
              if union.second > union.first then
                (right, union.second, union.first)
              else (left, union.first, union.second)
            val from =
              provenance.node(matchedRoot).map(Location.Rewritten(lemma, _))
            patternWalked(
              graph,
              List((added, addedRoot)),
              from,
              matchedRoot,
              provenance
            )
          }
        case Justification.Beta(thunk) =>
          betaWalked(graph, thunk, union.first, union.second, provenance)
        case _ => provenance
    )

  @tailrec
  private def inputPlaces[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      pending: List[(Configured[C], SourceMap)],
      provenance: Provenance
  ): Provenance =
    pending match
      case Nil                        => provenance
      case (instruction, map) :: rest =>
        graph.instructionNode(instruction) match
          case None       => inputPlaces(graph, rest, provenance)
          case Some(node) =>
            val located = provenance.withLocations(node, map.locations)
            // A node's code map is read for every thunk of its class with
            // that code, whatever its fillings: the code's map alone.
            val withCode = (graph.layer(node), map.code) match
              case (Thunk(code, _, _), Some(codeMap)) =>
                located.withCodeMap(node, SourceMap.codeAlone(code, codeMap))
              case _ => located
            val below =
              if map.bare || instruction.opaque then Nil
              else instruction.layer.children.toList.zip(map.children)
            inputPlaces(graph, below ++ rest, withCode)

  /** The added side walked along the nodes the instance built: the nodes
    * numbered above the matched root, which existed before the instance; the
    * side's other nodes were there before it and take nothing.
    */
  @tailrec
  private def patternWalked[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      pending: List[(Pattern[C], Int)],
      locations: Set[Location],
      matchedRoot: Int,
      provenance: Provenance
  ): Provenance =
    pending match
      case Nil                     => provenance
      case (pattern, node) :: rest =>
        val below = (pattern, graph.layer(node)) match
          case (
                Pattern.Apply(function, argument),
                Apply(functionNode, argumentNode)
              ) =>
            List((function, functionNode), (argument, argumentNode))
          case (Pattern.Choice(left, right), Choice(leftNode, rightNode)) =>
            List((left, leftNode), (right, rightNode))
          case (Pattern.Parallel(left, right), Parallel(leftNode, rightNode)) =>
            List((left, leftNode), (right, rightNode))
          case (Pattern.Thunk(_, _, fillings), Thunk(_, _, fillingNodes))
              if fillings.size == fillingNodes.size =>
            fillings.toList.zip(fillingNodes)
          case _ => Nil
        val walked = pattern match
          case Pattern.Metavariable(_) | Pattern.Closure(_) |
              Pattern.InstructionReference(_) =>
            provenance
          case _ if node <= matchedRoot => provenance
          case _ => provenance.firstLocated(node, locations)
        patternWalked(graph, below ++ rest, locations, matchedRoot, walked)

  private def betaWalked[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      thunk: Int,
      application: Int,
      body: Int,
      provenance: Provenance
  ): Provenance =
    val callSites = provenance.node(application)
    def inlined(callees: Set[Location]): Set[Location] =
      callees.flatMap(callee => callSites.map(Location.Inlined(callee, _)))
    graph.layer(thunk) match
      case Thunk(code, _, _) =>
        val maps = provenance.codeMaps.getOrElse(thunk, Vector.empty)
        graph.layer(body) match
          case Thunk(residualCode, _, _) if residualCode eq code =>
            maps.foldLeft(
              provenance.firstLocated(body, inlined(provenance.node(thunk)))
            )(_.withCodeMap(body, _))
          case _ =>
            maps.foldLeft(provenance)((walked, map) =>
              codeWalked(graph, List((code, map, body)), inlined, walked)
            )
      case _ => provenance

  @tailrec
  private def codeWalked[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      pending: List[(Code, SourceMap, Int)],
      inlined: Set[Location] => Set[Location],
      provenance: Provenance
  ): Provenance =
    pending match
      case Nil                       => provenance
      case (code, map, node) :: rest =>
        val sides = (code.layer, graph.layer(node)) match
          case (Apply(function, argument), Apply(functionNode, argumentNode)) =>
            Vector((function, functionNode), (argument, argumentNode))
          case (Choice(left, right), Choice(leftNode, rightNode)) =>
            Vector((left, leftNode), (right, rightNode))
          case (Parallel(left, right), Parallel(leftNode, rightNode)) =>
            Vector((left, leftNode), (right, rightNode))
          case _ => Vector.empty
        val below =
          if map.bare then Nil
          else
            sides
              .lazyZip(map.children)
              .map((side, sideMap) => (side._1, sideMap, side._2))
              .toList
        val walked = code.layer match
          case Slot(_)        => provenance
          case Thunk(_, _, _) =>
            val located = provenance.firstLocated(node, inlined(map.locations))
            (graph.layer(node), map.code) match
              case (Thunk(_, _, _), Some(innerMap)) =>
                located.withCodeMap(node, innerMap)
              case _ => located
          case _ => provenance.firstLocated(node, inlined(map.locations))
        codeWalked(graph, below ++ rest, inlined, walked)
