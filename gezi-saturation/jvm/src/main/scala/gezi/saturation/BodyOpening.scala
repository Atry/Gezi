package gezi.saturation

import gezi.egraph.EGraph
import gezi.egraph.Justification
import gezi.egraph.MadeNodes
import gezi.egraph.LiveNode
import gezi.ir.Pattern
import gezi.ir.Spine
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Slot, Thunk}
import gezi.ir.TailRecFolds
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Configured, NativeSpecializer}

/** A closure opened: its thunk node, its eigenvariables, one for each hole
  * in lambda order, each an opaque leaf with its node, and the node of its
  * body read at them.
  */
final case class Opening[C <: NativeSpecializer & Singleton](
    closure: Int,
    eigenvariables: Vector[(Configured[C], Int)],
    body: Int
)

/** How a round chooses the closures it opens: an option of the
  * saturation, not a part of what a program means. Both open only closures
  * that call a head (`BodyOpening.opened`); the second opens a subset of
  * the first's.
  */
enum OpeningCriterion[C <: NativeSpecializer & Singleton]:

  /** Every closure that calls a head: a name some enabled lemma's left side
    * applies, or such a name applied to fewer arguments than a left side
    * applies it to. The default.
    */
  case CallsAHead[C <: NativeSpecializer & Singleton]() extends OpeningCriterion[C]

  /** A closure that calls a head, as `CallsAHead` opens, and where some call
    * of a head at the head's own class has arguments that may match one of
    * the head's spines in a left side (`argumentPatterns`, each the
    * patterns of the arguments of one spine the head heads), argument by
    * argument for as many as both have: a metavariable or a closure
    * metavariable matches every argument; an argument that is a hole of the
    * closure itself, an eigenvariable once it is opened, is taken to match
    * no other pattern; an argument that is a filling matches when its class
    * has a member of the pattern's layer (for an instruction, holds the
    * instruction's node); any other argument, a hole of an inner closure or
    * a part of the code, may match, since what it is is known only once the
    * body is opened. A call whose head is a partial application of a head
    * may match, as is the let-bound case's head when the let binds no
    * filling. The criterion reads the graph's structure and the left sides'
    * syntax, no name's meaning and no lemma's.
    *
    * A closure it does not open is asked again after each first-order fixed
    * point, as every closure not yet opened is, so a filling's class that
    * gains a member of the pattern's layer in a later pass, as a list's class
    * gains a choice of filters, opens the closure then.
    *
    * FIXME (https://github.com/Atry/private-overlay/issues/2076): it may lose
    * instances the default adds, read from the code and not yet seen: the
    * criterion decides before the body is opened, and the body's own steps,
    * once it is, can give an argument's class the members a pattern needs.
    * The shapes: under the β rule, `λz. ((λw. w) z) + H c z` gives z's class
    * the application `(λw. w) z`, which `H a (f y)` would then match; under
    * an idempotence lemma `M + M = M`, `λz. (z + z) ∥ H c z` gives z's class
    * `z + z`, which `H a (b + c)` would match; and a lemma whose left side
    * heads no spine with a name matches in a body that only a call of
    * another head opened. So it is taken as a lossy option beside the
    * default. `OpeningCriterionLawTest` checks that its instances are never
    * more than the default's and records both counts on these shapes, equal
    * on every sample measured (2026-11-21).
    */
  case CallsAHeadWithMatchingArguments(argumentPatterns: Map[Configured[C], Vector[Vector[Pattern[C]]]])

/** Which `OpeningCriterion` a round's saturation opens closures by, as the
  * round's data chooses: the choice alone, the saturator building the
  * criterion from its round's enabled left sides.
  */
enum OpeningCriterionChoice:
  case CallsAHead, CallsAHeadWithMatchingArguments

/** The opening of closures' bodies and their write-back, so that lemmas
  * rewrite inside a lambda: a body opened is written back by reverse β on
  * the e-graph, with lemma instances, never rewritten in Scala.
  *
  * A closure is opened by reading its body at fresh eigenvariables, opaque
  * leaves that no library names and no pattern mentions, so that its body
  * becomes nodes of the graph and the lemmas match in it. Adding a term is
  * sound with no equation. A body is written back by the abstraction rule ξ, congruence
  * under λ: a spelling of the body's class with the eigenvariables
  * abstracted (`HigherOrderMatching.abstraction`) is a thunk united with the
  * closure. It is sound when the derivation of the spelling used no fact
  * about the eigenvariables, which holds when each eigenvariable's class
  * holds its leaf alone: a pattern sees an eigenvariable only through a
  * metavariable, so every lemma instance on the body holds for every value
  * of it, and a class that gained another member would say a fact about
  * it. A write-back whose eigenvariables fail this is not made.
  *
  * Which closures: every thunk node with a hole that the round's opening
  * criterion opens (`OpeningCriterion`), in node order, a class once; which
  * spelling: the caller's, an extraction's. Nothing here reads a
  * type or names a lemma or combinator (`CONTRIBUTING.md`, "Types live only
  * in the term").
  */
object BodyOpening:

  /** The classes under the roots: each root's class and, through every
    * member's children, the classes it reads; a class of `stops` is
    * neither in it nor read through.
    */
  def classesUnder[C <: NativeSpecializer & Singleton](graph: EGraph[C], roots: Iterable[Int], stops: Set[Int]): Set[Int] =
    @scala.annotation.tailrec
    def visited(pending: List[Int], seen: Set[Int]): Set[Int] = pending match
      case Nil                                         => seen
      case root :: rest if seen(root) || stops(root)   => visited(rest, seen)
      case root :: rest =>
        visited(graph.classMembers(root).flatMap(_.layer.children).toList ::: rest, seen + root)
    visited(roots.map(graph.root).toList, Set.empty)

  /** The graph with every closure of the scope's classes that calls a head
    * and whose class has none opened yet opened, and then, pass after pass,
    * every such closure under the bodies the last pass opened (`stops` not
    * read through), at most `count` in all, and the openings made, a body's
    * closures after the body. A
    * closure's code is read with its holes at the eigenvariables and its
    * other slots at its fillings, as the β rule reads it
    * (`HigherOrderMatching.bodyAdded`, which reads a code a compiled
    * program was not built with as well), and no application of the
    * closure is made:
    * the body's class holds the body's nodes alone, so that its spelling is
    * never the closure applied to the eigenvariables, whose write-back
    * would be the closure's η-expansion.
    */
  def opened[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      openings: Vector[Opening[C]],
      count: Int,
      scope: Set[Int],
      heads: Map[Configured[C], Int],
      stops: Set[Int],
      criterion: OpeningCriterion[C]
  )(using C): (EGraph[C], Vector[Opening[C]]) =
    val (once, made) = openedOnce(graph, openings, count, scope, heads, criterion)
    if made.isEmpty || made.size >= count then (once, made)
    else
      val (deeper, inner) =
        opened(once, openings ++ made, count - made.size, classesUnder(once, made.map(_.body), stops), heads, stops, criterion)
      (deeper, made ++ inner)

  /** One pass of `opened`'s: the closures of the scope's classes, without
    * those of the bodies the pass opens.
    *
    * A closure is opened when it has holes, is in the scope, is not yet opened, and the criterion opens it
    * (`OpeningCriterion`, which a round's saturator implementation chooses from the entry's data); the first
    * `count` of them in the order of the live nodes.
    */
  private def openedOnce[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      openings: Vector[Opening[C]],
      count: Int,
      scope: Set[Int],
      heads: Map[Configured[C], Int],
      criterion: OpeningCriterion[C]
  )(using C): (EGraph[C], Vector[Opening[C]]) =
    val openedRoots = openings.map(opening => graph.root(opening.closure)).toSet
    val headRoots = heads.toVector
      .flatMap((head, arity) => graph.instructionNode(head).map(node => graph.root(node) -> arity))
      .foldLeft(Map.empty[Int, Int]) { case (bounds, (root, arity)) =>
        bounds.updated(root, bounds.get(root).fold(arity)(_ max arity))
      }
    val argumentPatternsByRoot = criterion match
      case OpeningCriterion.CallsAHead()                                       => Map.empty[Int, Vector[Vector[Pattern[C]]]]
      case OpeningCriterion.CallsAHeadWithMatchingArguments(argumentPatterns) => patternsByRoot(graph, argumentPatterns)
    val closures = graph.liveNodes
      .collect { case LiveNode(node, root, thunk @ Thunk(_, holes, _)) if holes.nonEmpty => (node, root, thunk) }
      .filter((_, root, thunk) =>
        scope.contains(root) && !openedRoots.contains(root) && calls(graph, thunk, headRoots) && (criterion match
          case OpeningCriterion.CallsAHead() => true
          case OpeningCriterion.CallsAHeadWithMatchingArguments(_) =>
            matchingCalls(graph, thunk, headRoots, argumentPatternsByRoot)
        )
      )
      .distinctBy(_._2)
      .take(count)
    closures.foldLeft((graph, Vector.empty[Opening[C]])) { case ((current, made), (node, _, thunk)) =>
      val (withBody, opening) = openedAt(current, node, thunk)
      (withBody, made :+ opening)
    }

  /** The closure of the node, the thunk layer given, opened: an opaque
    * eigenvariable leaf for each hole, in lambda order, its text naming the
    * node and the position, and the thunk's code read at them, its fillings
    * at the slots they fill, as the body. The rounds' openings and a closure
    * unit's compilation (`gezi.narrowblocks.ClosureUnits`) open a closure
    * this one way.
    */
  def openedAt[C <: NativeSpecializer & Singleton](graph: EGraph[C], node: Int, thunk: Thunk[Int])(
      using specializer: C
  ): (EGraph[C], Opening[C]) =
    val (withLeaves, leaves) = thunk.holes.indices.foldLeft((graph, Vector.empty[(Configured[C], Int)])) {
      case ((partial, added), position) =>
        val leaf: Configured[C] = (specializer: C).opaque(s"eigenvariable $node $position")
        val (next, leafNode) = partial.layerAdded(NoinlineLeaf(leaf))
        (next, added :+ (leaf, leafNode))
    }
    val (withBody, body) = HigherOrderMatching.bodyAdded(
      withLeaves,
      thunk.code,
      Saturation.slotValues(thunk.holes, leaves.map(_._2), thunk.fillings)
    )
    (withBody, Opening(node, leaves, body))

  /** Whether the thunk's code applies, at the head of an application of
    * its own code (an inner thunk's code is its own thunk's), a filling
    * whose class is one of the heads' (a name some enabled lemma's left side
    * applies) or is a head applied to fewer arguments than the largest
    * number a left side applies it to, `headRoots` giving each head's class
    * that number: then the code's application continues a spine a left side
    * may match once the body is opened, as the index seeds a node under the
    * head of its spine. The filling's class is followed through the function
    * position of its applications only, and no further than the head's
    * number, past which no left side's spine has the class as a prefix. A
    * let-bound name is such a filling: `iterate`, bound to
    * `wren_fixpoint_by_value @ F`, fills the head of `λt. iterate k G t`.
    * The let may be unreduced in the code, `(λiterate. … iterate k G t …) s`
    * with the filling at the slot s, as the front end spells a closure whose
    * let binds a closed value: a filling at an
    * argument of a redex of the code, an application whose function the code
    * writes as a thunk, is read as the let-bound name it binds
    * (`LetBoundHeadOpeningLawTest`).
    */
  private def calls[C <: NativeSpecializer & Singleton](graph: EGraph[C], thunk: Thunk[Int], headRoots: Map[Int, Int]): Boolean =
    val environment = Saturation.slotValues(thunk.holes, thunk.holes.map(_ => -1), thunk.fillings)
    def headSlots(code: gezi.ir.Code): Vector[Int] = code.layer match
      case Slot(_) => Vector.empty
      case Apply(function, argument) =>
        def head(of: gezi.ir.Code): Option[Int] = of.layer match
          case Slot(slot)        => Some(slot)
          case Apply(inner, _)   => head(inner)
          case _                                        => None
        def redex(of: gezi.ir.Code): Boolean = of.layer match
          case Thunk(_, _, _)  => true
          case Apply(inner, _) => redex(inner)
          case _               => false
        val letBound = argument.layer match
          case Slot(slot) if redex(function) => Vector(slot)
          case _                             => Vector.empty
        head(function).toVector ++ letBound ++ headSlots(function) ++ headSlots(argument)
      case Parallel(left, right) => headSlots(left) ++ headSlots(right)
      case Choice(left, right)   => headSlots(left) ++ headSlots(right)
      case Thunk(_, _, fillings) => fillings.flatMap(headSlots)
    headSlots(thunk.code).exists(slot => environment(slot) >= 0 && headApplied(graph, headRoots, graph.root(environment(slot)), 0))

  /** Whether the class is a head, or a head applied to fewer arguments than
    * the largest number a left side applies it to, with `applications`
    * arguments applied already, followed through the function position of
    * its applications.
    */
  private def headApplied[C <: NativeSpecializer & Singleton](graph: EGraph[C], headRoots: Map[Int, Int], root: Int, applications: Int): Boolean =
    val deepest = headRoots.values.maxOption.getOrElse(0)
    headRoots.get(root).exists(applications < _) || (applications + 1 < deepest && graph.classMembers(root).exists(member =>
      member.layer match
        case Apply(function, _) => headApplied(graph, headRoots, graph.root(function), applications + 1)
        case _                  => false
    ))

  /** The argument patterns of each head's spines by the head's class. */
  private def patternsByRoot[C <: NativeSpecializer & Singleton](graph: EGraph[C], argumentPatterns: Map[Configured[C], Vector[Vector[Pattern[C]]]]): Map[Int, Vector[Vector[Pattern[C]]]] =
    argumentPatterns.toVector
      .flatMap((head, spines) => graph.instructionNode(head).map(node => graph.root(node) -> spines))
      .foldLeft(Map.empty[Int, Vector[Vector[Pattern[C]]]]) { case (byRoot, (root, spines)) =>
        byRoot.updated(root, byRoot.getOrElse(root, Vector.empty) ++ spines)
      }

  /** What a slot of a code stands for in `matchingCalls`. */
  private enum SlotValue:
    /** A filling, by its node. */
    case Filling(node: Int)
    /** A hole of the closure, an eigenvariable once it is opened. */
    case Eigenvariable
    /** A hole of an inner closure, or anything else known only once the body is opened. */
    case Unknown

  /** Whether the thunk's code, its inner thunks' codes included, holds a
    * call of a head whose arguments may match one of the head's spines
    * (`OpeningCriterion.CallsAHeadWithMatchingArguments`). The closure's
    * holes are eigenvariables; an inner thunk's holes are unknown, unless
    * the thunk is the function of a redex of the code, a let, whose
    * arguments then stand for its first holes.
    */
  private def matchingCalls[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      thunk: Thunk[Int],
      headRoots: Map[Int, Int],
      patterns: Map[Int, Vector[Vector[Pattern[C]]]]
  ): Boolean =
    def valueOf(code: gezi.ir.Code, environment: Vector[SlotValue]): SlotValue = code.layer match
      case Slot(slot) => environment(slot)
      case _          => SlotValue.Unknown
    def innerEnvironment(
        holes: Vector[gezi.ir.Hole],
        fillings: Vector[gezi.ir.Code],
        bound: Vector[SlotValue],
        environment: Vector[SlotValue]
    ): Vector[SlotValue] =
      slotValues(holes, holes.indices.map(position => bound.lift(position).getOrElse(SlotValue.Unknown)).toVector, fillings.map(valueOf(_, environment)))
    def classMayMatch(root: Int, pattern: Pattern[C]): Boolean = pattern.layer match
      case gezi.ir.InstructionReference(instruction) => graph.instructionNode(instruction).exists(node => graph.root(node) == root)
      case gezi.ir.Apply(_, _)     => graph.classMembers(root).exists(_.layer.isInstanceOf[Apply[?]])
      case gezi.ir.Parallel(_, _)  => graph.classMembers(root).exists(_.layer.isInstanceOf[Parallel[?]])
      case gezi.ir.Choice(_, _)    => graph.classMembers(root).exists(_.layer.isInstanceOf[Choice[?]])
      case gezi.ir.Thunk(_, _, _)  => graph.classMembers(root).exists(_.layer.isInstanceOf[Thunk[?]])
      case _                       => true
    def argumentMayMatch(pattern: Pattern[C], argument: gezi.ir.Code, environment: Vector[SlotValue]): Boolean = pattern match
      case Pattern.Metavariable(_) | Pattern.Closure(_) => true
      case _ =>
        valueOf(argument, environment) match
          case SlotValue.Eigenvariable => false
          case SlotValue.Unknown       => true
          case SlotValue.Filling(node) => classMayMatch(graph.root(node), pattern)
    def headCallMayMatch(head: gezi.ir.Code, arguments: Vector[gezi.ir.Code], environment: Vector[SlotValue]): Boolean =
      valueOf(head, environment) match
        case SlotValue.Filling(node) =>
          val root = graph.root(node)
          patterns.get(root) match
            case Some(spines) => spines.exists(spine => spine.zip(arguments).forall((pattern, argument) => argumentMayMatch(pattern, argument, environment)))
            case None         => headApplied(graph, headRoots, root, 0)
        case _ => false
    def walked(code: gezi.ir.Code, environment: Vector[SlotValue]): Boolean = code.layer match
      case Slot(_) => false
      case Apply(_, _) =>
        val (head, arguments) = Spine.of(code)
        val atHead = head.layer match
          case Thunk(inner, holes, fillings) =>
            fillings.exists(walked(_, environment)) ||
              walked(inner, innerEnvironment(holes, fillings, arguments.map(valueOf(_, environment)), environment))
          case Slot(_) => headCallMayMatch(head, arguments, environment)
          case _       => walked(head, environment)
        atHead || arguments.exists(walked(_, environment))
      case Parallel(left, right) => walked(left, environment) || walked(right, environment)
      case Choice(left, right)   => walked(left, environment) || walked(right, environment)
      case Thunk(inner, holes, fillings) =>
        fillings.exists(walked(_, environment)) || walked(inner, innerEnvironment(holes, fillings, Vector.empty, environment))
    walked(thunk.code, slotValues(thunk.holes, thunk.holes.map(_ => SlotValue.Eigenvariable), thunk.fillings.map(SlotValue.Filling(_))))

  /** The values of a code's slots in slot order, its holes' values then its
    * fillings' in the order `Saturation.slotValues` places them, for any
    * kind of value: the slots of the holes and of the fillings placed by
    * that function's numbering, read through the positions it gives.
    */
  private def slotValues[Value](holes: Vector[gezi.ir.Hole], holeValues: Vector[Value], fillingValues: Vector[Value]): Vector[Value] =
    val all = holeValues ++ fillingValues
    Saturation.slotValues(holes, holeValues.indices.toVector, fillingValues.indices.map(_ + holeValues.size).toVector).map(all)

  /** Whether each of the opening's eigenvariables is alone in its class.
    *
    * FIXME (2026-11-07): sound but too https://github.com/Atry/private-overlay/issues/1966
    * strict. A fact that holds for every value, matched at an eigenvariable
    * through a metavariable (a hint lemma X = X + (0 ∥ l), an η-expansion),
    * puts a second node into its class and blocks the write-back, though
    * such a fact holds for whatever value the eigenvariable stands for.
    * Candidate condition: no union joins the eigenvariable's class with a
    * class that does not depend on it through a metavariable.
    */
  def eigenvariablesFree[C <: NativeSpecializer & Singleton](graph: EGraph[C], opening: Opening[C]): Boolean =
    opening.eigenvariables.forall((_, leafNode) => graph.classMembers(leafNode).map(_.node) == Vector(leafNode))

  /** The graph with the body's spelling written back as a thunk united with
    * the closure, by the abstraction rule, when the eigenvariables are free;
    * the graph as it is otherwise. The eigenvariables of every opening, the
    * opening's own and those of the closures it is inside, are given with
    * their nodes, so that a spelling that holds one is added at its leaf.
    */
  def writtenBack[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      opening: Opening[C],
      spelling: Configured[C],
      eigenvariables: Map[Configured[C], Int]
  )(using C): EGraph[C] =
    if !eigenvariablesFree(graph, opening) then graph
    else
      val spellingNode = this.spellingNode(graph, spelling, eigenvariables)
      val thunk = HigherOrderMatching.abstraction(graph, spelling, opening.eigenvariables.map(_._1))
      val (added, node) = HigherOrderMatching.termAdded(graph, thunk, eigenvariables)
      added.unionWorked(
        opening.closure,
        node,
        Justification.Abstraction(opening.eigenvariables.map(_._2), opening.body, spellingNode),
        Option.when(node >= graph.nodeCount)(MadeNodes(graph.nodeCount, node))
      )

  /** The node of a body's spelling, found layer by layer, nothing added: a
    * spelling is an extraction of the body's class, every layer of it a
    * member's layer over classes of the graph (a native storage the
    * construction converted one of them to standing for that layer, its view),
    * and an eigenvariable its leaf's node. A spelling shares subterms, so each distinct subterm is
    * looked up once, the nodes found threaded through the walk: linear in
    * the spelling as a graph, not in the tree it unfolds to (5da66229d). A trampoline: a spelling is as deep as a body. Throws
    * `IllegalStateException` for a spelling with a layer the graph has no
    * node of.
    */
  private def spellingNode[C <: NativeSpecializer & Singleton](graph: EGraph[C], spelling: Configured[C], eigenvariables: Map[Configured[C], Int]): Int =
    def found(instruction: Configured[C], known: Map[Configured[C], Int]): TailRec[Map[Configured[C], Int]] =
      if known.contains(instruction) then done(known)
      else
        eigenvariables.get(instruction).orElse(graph.instructionNode(instruction)) match
          case Some(node) => done(known.updated(instruction, node))
          case None =>
            // A native storage with no node is one the write-back's construction
            // just converted from the layer the graph holds (`Store.construction`):
            // its one-layer view is that layer, over children the graph has nodes of, read with the capability the
            // graph's store holds (`Store.expanded`).
            val layer = graph.store.expanded(instruction)
            TailRecFolds.folded(layer.children.toVector, known)((current, child) => found(child, current))
              .map(after =>
                val node = graph
                  .layerNode(layer.map(after))
                  .getOrElse(throw IllegalStateException(s"the spelling $instruction of a body has no node in the graph"))
                after.updated(instruction, node)
              )
    found(spelling, Map.empty).result(spelling)
