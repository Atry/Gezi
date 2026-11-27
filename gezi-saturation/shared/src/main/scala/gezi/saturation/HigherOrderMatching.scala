package gezi.saturation

import gezi.egraph.EGraph
import gezi.egraph.Justification
import gezi.ir.BindingNormalForm
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.NonEmptyHoles
import gezi.ir.Pattern
import gezi.ir.Store
import gezi.ir.TermConstruction
import gezi.ir
import scala.annotation.tailrec
import gezi.ir.{Configured, NativeSpecializer}

/** A closed term over the graph: a class, an instruction to be added, or one
  * layer of the IR over closed terms, a thunk's code canonical as the front end
  * writes it (`gezi.frontend.Defunctionalization`).
  */
enum ClosedTerm[C <: NativeSpecializer & Singleton]:
  case Class[C <: NativeSpecializer & Singleton](root: Int)
      extends ClosedTerm[C]
  case InstructionTerm(instruction: Configured[C])
  case Apply(function: ClosedTerm[C], argument: ClosedTerm[C])
  case Parallel(left: ClosedTerm[C], right: ClosedTerm[C])
  case Choice(left: ClosedTerm[C], right: ClosedTerm[C])
  case Thunk(code: Code, holes: Vector[Hole], fillings: Vector[ClosedTerm[C]])

/** What a match of a lemma's left side by its higher-order occurrences writes
  * to the graph: each thunk the left side matched, united with the left side's
  * thunk under the bindings (`expansions`, each a beta expansion of the matched
  * thunk); and each thunk of the right side that applies a higher-order
  * metavariable, under the bindings, united with its beta normal form
  * (`normalizations`). The lemma's own instance, which unites the two sides, is
  * the first-order matching's, once the expansions are in the graph.
  */
final case class HigherOrderInstance[C <: NativeSpecializer & Singleton](
    expansions: Vector[(Int, ClosedTerm[C])],
    normalizations: Vector[(ClosedTerm[C], ClosedTerm[C])]
)

/** What determines the instance a match of a left side writes: the class it
  * matched at, the metavariables' values, which of them were solved by
  * abstraction, and the member node each of the left side's thunks matched (its
  * class in a canonical key, `HigherOrderMatching.canonical`).
  */
final case class MatchKey[C <: NativeSpecializer & Singleton](
    root: Int,
    bindings: Map[Int, ClosedTerm[C]],
    higherOrder: Set[Int],
    thunkClasses: Vector[(Pattern.Thunk[C], Int)]
)

/** The n-ary reverse beta that every lemma's left side carries (a lemma whose
  * occurrence the matching cannot find is a defect of the matching engine, to
  * be fixed there, not of the lemma), for the occurrences the first-order
  * matching of `gezi.ematching.indexing.Seeding` cannot find: a metavariable K
  * applied to arguments inside a thunk of the left side, `K @ a1 @ ... @ an`, K
  * bound nowhere before and every ai open (reading a binder of the side's
  * object lambdas) with no metavariable unbound. Such an occurrence matches
  * every term T as `(λy1 ... λyn. T[a1 := y1, ..., an := yn]) @ a1 @ ... @ an`,
  * an equation by beta, when the abstraction is closed: K's value is that
  * abstraction. An occurrence of ai in T is ai itself or, when ai is a lambda
  * `λz1 ... λzr. B`, an instance of B with the zj captured, read as
  * `ai @ e1 @ ... @ er`; it is replaced by `yi @ e1 @ ... @ er`.
  *
  * The left side is read against the graph's classes, and a thunk of the side
  * against a thunk node's code with its fillings' classes: a code is syntax and
  * is read structurally, a class through its members. No lambda tree is built:
  * a code is read under an environment of its slots, as the β rule reads it
  * (`Saturation.slotValues`).
  *
  * Which terms are abstracted is the left side's, never a type or a name a
  * caller lists (`CONTRIBUTING.md`, "Types live only in the term").
  *
  * This file is compiled for Scala.js as well, alone of `saturation`
  * (`saturation-js`), so that the trace player replays a backward higher-order
  * conversion with this matching
  * (`gezi.rewritetrace.Conversions.expansionSolutions`). It depends on `egraph`
  * and `ir` alone and uses no JVM-only API; a new dependency on another source
  * of `saturation` is added to `saturation-js`'s `unmanagedSources` with it.
  */
object HigherOrderMatching:

  /** The metavariables of the pattern applied to an argument or more inside a
    * thunk of it: the candidates for a higher-order occurrence. The eta-shaped
    * lambda `\x. M x` is none: it is read as the class of M holding a closure
    * state (`Pattern.Closure`), the first-order matching's.
    */
  def higherOrderMetavariables[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C]
  ): Set[Int] =
    patternSubterms(pattern).flatMap {
      case Pattern.Thunk(
            code,
            Vector(Hole.Bound(hole)),
            Vector(Pattern.Metavariable(_))
          ) if code.layer == ir.Apply(Code.Slot(1 - hole), Code.Slot(hole)) =>
        Set.empty
      case Pattern.Thunk(code, holes, fillings) =>
        val environment =
          fillingEnvironment(holes, fillings.map(PatternView.of))
        codeHeads(code).flatMap(slot =>
          environment.get(slot) match
            case Some(PatternView.Metavariable(index)) => Some(index)
            case _                                     => None
        )
      case _ => Set.empty
    }.toSet

  /** The instances of the left side's higher-order occurrences in the graph,
    * each matched at a class and holding a metavariable solved by abstraction,
    * with what the right side writes for them; a thunk whose code is the side's
    * own is left to the first-order matching.
    */
  def instances[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      left: Pattern[C],
      right: Pattern[C]
  ): Vector[HigherOrderInstance[C]] =
    unseenInstances(graph, left, right, Set.empty).map(_._2)

  /** The instances of `instances` whose match is not among `seen`, each with
    * its match, read over the graph's roots now. A match already written writes
    * nothing new (its terms are in the graph, its unions made), so a caller
    * that keeps the matches it wrote skips building their instances again, the
    * β normal forms included; the graph comes out the same. The matches kept
    * are a cost memo, not a fact about a class (`CONTRIBUTING.md`, "Tables",
    * kind 1). For the same reason the seen filter runs before `admitted`, which
    * rebuilds the terms under the solution's classes: a seen match writes
    * nothing whether or not it is admitted, so the order changes no output and
    * spares the rebuild for the matches of earlier rounds.
    */
  def unseenInstances[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      left: Pattern[C],
      right: Pattern[C],
      seen: Set[MatchKey[C]]
  ): Vector[(MatchKey[C], HigherOrderInstance[C])] =
    if higherOrderMetavariables(left).isEmpty then Vector.empty
    else Matching(graph).unseenInstances(left, right, seen)

  /** The match read over the graph's roots now, so that a match found before a
    * union and the same match found after it are one key.
    */
  def canonical[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      key: MatchKey[C]
  ): MatchKey[C] =
    def term(closed: ClosedTerm[C]): ClosedTerm[C] = closed match
      case ClosedTerm.Class(root) => ClosedTerm.Class[C](graph.root(root))
      case ClosedTerm.InstructionTerm(_)        => closed
      case ClosedTerm.Apply(function, argument) =>
        ClosedTerm.Apply(term(function), term(argument))
      case ClosedTerm.Parallel(left, right) =>
        ClosedTerm.Parallel(term(left), term(right))
      case ClosedTerm.Choice(left, right) =>
        ClosedTerm.Choice(term(left), term(right))
      case ClosedTerm.Thunk(code, holes, fillings) =>
        ClosedTerm.Thunk(code, holes, fillings.map(term))
    MatchKey(
      graph.root(key.root),
      key.bindings.view.mapValues(term).toMap,
      key.higherOrder,
      key.thunkClasses.map((thunk, root) => (thunk, graph.root(root)))
    )

  /** The graph with the instance written: every closed term added, each
    * expansion united with the member node it matched and each right side's
    * thunk with its normal form, by β conversion
    * (`Justification.BetaConversion`: more than one β step, which the proof
    * does not replay as one).
    */
  def written[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      instance: HigherOrderInstance[C]
  ): EGraph[C] =
    val expanded = instance.expansions.foldLeft(graph) {
      case (current, (member, term)) =>
        val (added, node) = termAdded(current, term, Map.empty)
        added.unionWorked(
          member,
          node,
          Justification.BetaConversion(member),
          None
        )
    }
    instance.normalizations.foldLeft(expanded) {
      case (current, (firstOrder, normal)) =>
        val (withFirst, firstNode) = termAdded(current, firstOrder, Map.empty)
        val (withNormal, normalNode) = termAdded(withFirst, normal, Map.empty)
        withNormal.unionWorked(
          firstNode,
          normalNode,
          Justification.BetaConversion(normalNode),
          None
        )
    }

  /** The graph with the closed term's node, made when new; an instruction that
    * holds an eigenvariable of `eigenvariables` (an opaque leaf the store
    * cannot expand, `BodyOpening`) is added layer by layer, the eigenvariable
    * being its node.
    */
  def termAdded[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      term: ClosedTerm[C],
      eigenvariables: Map[Configured[C], Int]
  ): (EGraph[C], Int) = term match
    case ClosedTerm.Class(root)                  => (graph, root)
    case ClosedTerm.InstructionTerm(instruction) =>
      eigenvariables.get(instruction) match
        case Some(node)                                        => (graph, node)
        case None if holds(instruction, eigenvariables.keySet) =>
          instruction.layer match
            case storage: ir.NativeStorage =>
              throw IllegalStateException(
                s"a storage holds no eigenvariable: $storage"
              )
            case ir.Apply(function, argument) =>
              termAdded(
                graph,
                ClosedTerm.Apply(
                  ClosedTerm.InstructionTerm(function),
                  ClosedTerm.InstructionTerm(argument)
                ),
                eigenvariables
              )
            case ir.Parallel(left, right) =>
              termAdded(
                graph,
                ClosedTerm.Parallel(
                  ClosedTerm.InstructionTerm(left),
                  ClosedTerm.InstructionTerm(right)
                ),
                eigenvariables
              )
            case ir.Choice(left, right) =>
              termAdded(
                graph,
                ClosedTerm.Choice(
                  ClosedTerm.InstructionTerm(left),
                  ClosedTerm.InstructionTerm(right)
                ),
                eigenvariables
              )
            case ir.Thunk(code, holes, fillings) =>
              termAdded(
                graph,
                ClosedTerm.Thunk(
                  code,
                  holes,
                  fillings.map(ClosedTerm.InstructionTerm(_))
                ),
                eigenvariables
              )
            case ir.UriNode(_) | ir.Opaque(_) =>
              throw IllegalStateException(
                s"the opaque $instruction has no layer"
              )
        case None => graph.instructionAdded(instruction)
    case ClosedTerm.Apply(function, argument) =>
      val (withFunction, functionNode) =
        termAdded(graph, function, eigenvariables)
      val (withArgument, argumentNode) =
        termAdded(withFunction, argument, eigenvariables)
      withArgument.layerAdded(ir.Apply(functionNode, argumentNode))
    case ClosedTerm.Parallel(left, right) =>
      val (withLeft, leftNode) = termAdded(graph, left, eigenvariables)
      val (withRight, rightNode) = termAdded(withLeft, right, eigenvariables)
      withRight.layerAdded(ir.Parallel(leftNode, rightNode))
    case ClosedTerm.Choice(left, right) =>
      val (withLeft, leftNode) = termAdded(graph, left, eigenvariables)
      val (withRight, rightNode) = termAdded(withLeft, right, eigenvariables)
      withRight.layerAdded(ir.Choice(leftNode, rightNode))
    case ClosedTerm.Thunk(code, holes, fillings) =>
      val (withFillings, fillingNodes) =
        termsAdded(graph, fillings, eigenvariables)
      withFillings.layerAdded(ir.Thunk(code, holes, fillingNodes))

  private def termsAdded[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      terms: Vector[ClosedTerm[C]],
      eigenvariables: Map[Configured[C], Int]
  ): (EGraph[C], Vector[Int]) =
    terms.foldLeft((graph, Vector.empty[Int])) {
      case ((current, nodes), term) =>
        val (next, node) = termAdded(current, term, eigenvariables)
        (next, nodes :+ node)
    }

  /** The graph with the code read at the slots' nodes and the node of the body,
    * layer by layer as the β rule reads a code
    * (`gezi.ematching.indexing.Indexing.codeBuilding`: children first, an inner
    * thunk's fillings read at the slots and its code kept, and an application
    * whose function the code writes as a thunk, a redex such as a let, marked
    * for the β rule to read). It reads any code, not only those a compiled
    * program was built with.
    *
    * It once left that mark out, so a body read here, the body of a thunk the
    * graph had respelled (`EGraph.layerMade`), kept its lets unreduced where
    * the compiled body reduced them. Measured 2026-11-16 on
    * `contest-entries-wren`'s calls_10000_hot/direct first point: a chain of
    * four β steps that main took was missing, and the extracted narrow-block
    * cost was 1,922 where main's was 166 with no closure opened.
    */
  def bodyAdded[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      code: Code,
      slotValues: Vector[Int]
  ): (EGraph[C], Int) = code.layer match
    case ir.Slot(index)               => (graph, slotValues(index))
    case ir.Apply(function, argument) =>
      val (withFunction, functionNode) = bodyAdded(graph, function, slotValues)
      val (withArgument, argumentNode) =
        bodyAdded(withFunction, argument, slotValues)
      val (withApplication, node) =
        withArgument.layerAdded(ir.Apply(functionNode, argumentNode))
      function.layer match
        case ir.Thunk(_, _, _) => (withApplication.applicationRead(node), node)
        case _                 => (withApplication, node)
    case ir.Parallel(left, right) =>
      val (withLeft, leftNode) = bodyAdded(graph, left, slotValues)
      val (withRight, rightNode) = bodyAdded(withLeft, right, slotValues)
      withRight.layerAdded(ir.Parallel(leftNode, rightNode))
    case ir.Choice(left, right) =>
      val (withLeft, leftNode) = bodyAdded(graph, left, slotValues)
      val (withRight, rightNode) = bodyAdded(withLeft, right, slotValues)
      withRight.layerAdded(ir.Choice(leftNode, rightNode))
    case ir.Thunk(inner, holes, fillings) =>
      val (withFillings, fillingNodes) =
        fillings.foldLeft((graph, Vector.empty[Int])) {
          case ((current, nodes), filling) =>
            val (next, node) = bodyAdded(current, filling, slotValues)
            (next, nodes :+ node)
        }
      withFillings.layerAdded(ir.Thunk(inner, holes, fillingNodes))

  /** Whether the instruction's spelling holds one of the leaves; a native
    * storage the e-graph keeps as a leaf holds none, its view not read.
    */
  private def holds[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      leaves: Set[Configured[C]]
  ): Boolean =
    leaves.contains(instruction) ||
      (!instruction.heldAsLeaf && instruction.layer.children.exists(
        holds(_, leaves)
      ))

  /** The thunk `λx1 ... λxn. B[v1 := x1, ..., vn := xn]` of the body B over the
    * leaves v1 to vn, in lambda order, spelled as the front end spells it: the
    * body's maximal subterms that hold no vi its fillings, a vi that B does not
    * read an ignored hole.
    */
  def abstraction[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      body: Configured[C],
      leaves: Vector[Configured[C]]
  ): ClosedTerm[C] =
    Matching(graph).abstraction(body, leaves)

  /** `abstraction` of a body read outside any graph, as an instruction built by
    * the construction: the emission reads the graph only for a class, and the
    * view of an instruction holds none, so an empty graph stands in for it.
    */
  def abstractedInstruction[C <: NativeSpecializer & Singleton](
      body: Configured[C],
      leaves: Vector[Configured[C]],
      construction: TermConstruction[C]
  ): Configured[C] =
    val graph = EGraph.empty(
      Store(Set.empty[Configured[C]], construction),
      Map.empty[Configured[C], Int],
      explained = false
    )
    closedBuilt(abstraction(graph, body, leaves), construction.specializer)

  /** A closed term that names no class, as a term built through the
    * specializer.
    */
  private def closedBuilt[C <: NativeSpecializer & Singleton](
      term: ClosedTerm[C],
      specializer: C
  ): Configured[C] =
    def built(closed: ClosedTerm[C]): Configured[C] =
      closedBuilt(closed, specializer)
    term match
      case ClosedTerm.InstructionTerm(instruction) => instruction
      case ClosedTerm.Apply(function, argument)    =>
        specializer.application(built(function), built(argument))
      case ClosedTerm.Parallel(left, right) =>
        specializer.parallel(built(left), built(right))
      case ClosedTerm.Choice(left, right) =>
        specializer.choice(built(left), built(right))
      case ClosedTerm.Thunk(code, holes, fillings) =>
        thunkTerm(specializer, code, holes, fillings.map(built))
      case ClosedTerm.Class(root) =>
        throw IllegalStateException(
          s"a term read outside a graph names the class $root"
        )

  /** The term of a thunk's code, holes and fillings: a thunk with holes, the
    * instance of the code when it has none (`NativeSpecializer.built` makes it
    * the same way).
    */
  private def thunkTerm[C <: NativeSpecializer & Singleton](
      specializer: C,
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[Configured[C]]
  ): Configured[C] =
    NonEmptyHoles.of(holes) match
      case Some(present) => specializer.thunk(code, present, fillings)
      case None          => specializer.instance(code, fillings)

  /** The instruction as the emission reads it: a leaf of `bound` its binder, a
    * subterm that holds none a closed term, any other its layer.
    */
  private def instructionView[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      bound: Map[Configured[C], Int]
  ): View[C] =
    bound.get(instruction) match
      case Some(binder)                              => View.Bound[C](binder)
      case None if !holds(instruction, bound.keySet) =>
        View.Term(ClosedTerm.InstructionTerm(instruction))
      case None =>
        instruction.layer match
          case ir.Apply(function, argument) =>
            View.Apply(
              instructionView(function, bound),
              instructionView(argument, bound)
            )
          case ir.Parallel(left, right) =>
            View.Parallel(
              instructionView(left, bound),
              instructionView(right, bound)
            )
          case ir.Choice(left, right) =>
            View.Choice(
              instructionView(left, bound),
              instructionView(right, bound)
            )
          case ir.Thunk(code, holes, fillings) =>
            View.Lambda(
              code,
              holes,
              fillingEnvironment(
                holes,
                fillings.map(instructionView(_, bound))
              ),
              inlined = false
            )
          case ir.UriNode(_) | ir.Opaque(_) =>
            throw IllegalStateException(s"the opaque $instruction has no layer")
          case storage: ir.NativeStorage =>
            throw IllegalStateException(s"a storage holds no binder: $storage")

  // ---- reading ----

  /** A term of the graph as the matching reads it: a binder of a lambda
    * entered, a class, one layer over terms, or a lambda whose holes are not
    * yet entered (a code, its holes, and its slots read so far). A lambda that
    * is `inlined` is a higher-order metavariable's value, read by beta where
    * the right side applies it.
    */
  private enum View[C <: NativeSpecializer & Singleton]:
    case Bound[C <: NativeSpecializer & Singleton](binder: Int) extends View[C]
    case Class[C <: NativeSpecializer & Singleton](root: Int) extends View[C]
    case Term(term: ClosedTerm[C])
    case Apply(function: View[C], argument: View[C])
    case Parallel(left: View[C], right: View[C])
    case Choice(left: View[C], right: View[C])
    case Lambda(
        code: Code,
        holes: Vector[Hole],
        environment: Map[Int, View[C]],
        inlined: Boolean
    )

  private object View:

    /** The code read under the environment of its slots. */
    def read[C <: NativeSpecializer & Singleton](
        code: Code,
        environment: Map[Int, View[C]]
    ): View[C] = code.layer match
      case ir.Slot(index) =>
        environment.getOrElse(
          index,
          throw IllegalStateException(s"the slot $index is not in $environment")
        )
      case ir.Apply(function, argument) =>
        View.Apply(read(function, environment), read(argument, environment))
      case ir.Parallel(left, right) =>
        View.Parallel(read(left, environment), read(right, environment))
      case ir.Choice(left, right) =>
        View.Choice(read(left, environment), read(right, environment))
      case ir.Thunk(inner, holes, fillings) =>
        View.Lambda(
          inner,
          holes,
          fillingEnvironment(holes, fillings.map(read(_, environment))),
          inlined = false
        )

    /** The lambda with its first hole entered by the value: the lambda of the
      * holes left, or its body when none is.
      */
    def entered[C <: NativeSpecializer & Singleton](
        lambda: View.Lambda[C],
        value: View[C]
    ): View[C] =
      val environment = lambda.holes.head match
        case Hole.Bound(slot) => lambda.environment.updated(slot, value)
        case Hole.Ignored     => lambda.environment
      if lambda.holes.size == 1 then read(lambda.code, environment)
      else lambda.copy(holes = lambda.holes.tail, environment = environment)

    /** The view of a closed term, a thunk inlined when asked. */
    def of[C <: NativeSpecializer & Singleton](
        term: ClosedTerm[C],
        inlined: Boolean
    ): View[C] = term match
      case ClosedTerm.Class(root)               => View.Class[C](root)
      case ClosedTerm.InstructionTerm(_)        => View.Term(term)
      case ClosedTerm.Apply(function, argument) =>
        View.Apply(of(function, false), of(argument, false))
      case ClosedTerm.Parallel(left, right) =>
        View.Parallel(of(left, false), of(right, false))
      case ClosedTerm.Choice(left, right) =>
        View.Choice(of(left, false), of(right, false))
      case ClosedTerm.Thunk(code, holes, fillings) =>
        View.Lambda(
          code,
          holes,
          fillingEnvironment(holes, fillings.map(of(_, false))),
          inlined
        )

  /** A side of a lemma as the matching reads it: its patterns, and the code of
    * a thunk of it read under the environment of its slots, a binder of the
    * side's object lambda entered as `Bound` and a binder of an abstracted
    * argument's lambda as `Capture`.
    */
  private enum PatternView[C <: NativeSpecializer & Singleton]:
    case Bound[C <: NativeSpecializer & Singleton](binder: Int)
        extends PatternView[C]
    case Capture[C <: NativeSpecializer & Singleton](index: Int)
        extends PatternView[C]
    case Metavariable[C <: NativeSpecializer & Singleton](index: Int)
        extends PatternView[C]
    case Closure[C <: NativeSpecializer & Singleton](index: Int)
        extends PatternView[C]
    case Reference(instruction: Configured[C])
    case Apply(function: PatternView[C], argument: PatternView[C])
    case Parallel(left: PatternView[C], right: PatternView[C])
    case Choice(left: PatternView[C], right: PatternView[C])
    case Lambda(
        code: Code,
        holes: Vector[Hole],
        environment: Map[Int, PatternView[C]],
        origin: Option[Pattern.Thunk[C]]
    )

  private object PatternView:

    def of[C <: NativeSpecializer & Singleton](
        pattern: Pattern[C]
    ): PatternView[C] = pattern match
      case Pattern.Metavariable(index) => PatternView.Metavariable[C](index)
      case Pattern.Closure(index)      => PatternView.Closure[C](index)
      case Pattern.InstructionReference(instruction) =>
        PatternView.Reference(instruction)
      case Pattern.Apply(function, argument) =>
        PatternView.Apply(of(function), of(argument))
      case Pattern.Parallel(left, right) =>
        PatternView.Parallel(of(left), of(right))
      case Pattern.Choice(left, right) =>
        PatternView.Choice(of(left), of(right))
      case thunk @ Pattern.Thunk(code, holes, fillings) =>
        PatternView.Lambda(
          code,
          holes,
          fillingEnvironment(holes, fillings.map(of)),
          Some(thunk)
        )

    def read[C <: NativeSpecializer & Singleton](
        code: Code,
        environment: Map[Int, PatternView[C]]
    ): PatternView[C] = code.layer match
      case ir.Slot(index) =>
        environment.getOrElse(
          index,
          throw IllegalStateException(s"the slot $index is not in $environment")
        )
      case ir.Apply(function, argument) =>
        PatternView.Apply(
          read(function, environment),
          read(argument, environment)
        )
      case ir.Parallel(left, right) =>
        PatternView.Parallel(read(left, environment), read(right, environment))
      case ir.Choice(left, right) =>
        PatternView.Choice(read(left, environment), read(right, environment))
      case ir.Thunk(inner, holes, fillings) =>
        PatternView.Lambda(
          inner,
          holes,
          fillingEnvironment(holes, fillings.map(read(_, environment))),
          None
        )

    def entered[C <: NativeSpecializer & Singleton](
        lambda: PatternView.Lambda[C],
        value: PatternView[C]
    ): PatternView[C] =
      val environment = lambda.holes.head match
        case Hole.Bound(slot) => lambda.environment.updated(slot, value)
        case Hole.Ignored     => lambda.environment
      if lambda.holes.size == 1 then read(lambda.code, environment)
      else
        lambda.copy(
          holes = lambda.holes.tail,
          environment = environment,
          origin = None
        )

  /** The slots of a thunk's code that are not holes, in slot order, each with
    * its filling.
    */
  private def fillingEnvironment[Value](
      holes: Vector[Hole],
      fillings: Vector[Value]
  ): Map[Int, Value] =
    val bound = holes.collect { case Hole.Bound(slot) => slot }.toSet
    val slots = (0 until bound.size + fillings.size).filterNot(bound.contains)
    require(
      slots.size == fillings.size,
      s"the fillings $fillings do not fill the slots of $holes"
    )
    slots.zip(fillings).toMap

  /** The slots at the head of an application spine of an argument or more in
    * the code. An inner thunk's own slots are not the code's, so a head inside
    * an inner thunk's code is read through the inner thunk's fillings: an inner
    * slot that is no hole and whose filling is a slot of the code (or a spine
    * headed by one) is that slot. Without this, a metavariable applied only
    * inside an inner lambda of a side, such as G in
    * `S^N^T^(N @ T @ … @ (P^(G @ (S @ P @ (S @ P @ T)))))`, was not found
    * higher-order, and its lemma matched only a target whose code equals the
    * side's, never a loop whose function a let's β writes into its body
    * (2026-11-07, the hot ladder's inlined site).
    */
  private def codeHeads(code: Code): Vector[Int] = code.layer match
    case ir.Slot(_)                   => Vector.empty
    case ir.Apply(function, argument) =>
      val head = spineHead(function)
      head.toVector ++ codeHeads(function) ++ codeHeads(argument)
    case ir.Parallel(left, right)         => codeHeads(left) ++ codeHeads(right)
    case ir.Choice(left, right)           => codeHeads(left) ++ codeHeads(right)
    case ir.Thunk(inner, holes, fillings) =>
      val filled = fillingEnvironment(holes, fillings)
      fillings.flatMap(codeHeads) ++ codeHeads(inner).flatMap(innerSlot =>
        filled.get(innerSlot).flatMap(spineHead)
      )

  private def spineHead(code: Code): Option[Int] =
    ir.Spine.of(code)._1.layer match
      case ir.Slot(index) => Some(index)
      case _              => None

  private def patternSubterms[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C]
  ): Vector[Pattern[C]] =
    pattern +: pattern.children.flatMap(patternSubterms)

  /** Whether the matching may bind metavariables (`Solving`) or only reads the
    * bindings made so far (`Frozen`, an occurrence of an argument).
    */
  private enum Mode:
    case Solving
    case Frozen

  /** The matching over one graph: every function that reads the graph's
    * classes, in the configuration `C` of the graph's native specializer, which
    * builds each term the matching writes.
    */
  private final class Matching[C <: NativeSpecializer & Singleton](
      graph: EGraph[C]
  ):

    private val specializer: C = graph.store.construction.specializer
    private given C = specializer

    private type ClosedTerm = gezi.saturation.ClosedTerm[C]
    private type View = HigherOrderMatching.View[C]
    private type PatternView = HigherOrderMatching.PatternView[C]
    private type Pattern = gezi.ir.Pattern[C]
    private type PatternThunk = gezi.ir.Pattern.Thunk[C]
    private type MatchKey = gezi.saturation.MatchKey[C]
    private type HigherOrderInstance = gezi.saturation.HigherOrderInstance[C]

    def unseenInstances(
        left: Pattern,
        right: Pattern,
        seen: Set[MatchKey]
    ): Vector[(MatchKey, HigherOrderInstance)] =
      val classRoots = graph.liveNodes.map(_.root).distinct
      classRoots
        .flatMap(root =>
          matched(
            PatternView.of(left),
            View.Class[C](root),
            State.initial,
            Mode.Solving
          )
            .filter(state => state.higherOrder.nonEmpty)
            .map(state =>
              (
                canonical(
                  graph,
                  MatchKey(
                    root,
                    state.bindings,
                    state.higherOrder,
                    state.thunkClasses
                  )
                ),
                state
              )
            )
            .filterNot((key, _) => seen.contains(key))
            .filter((_, state) => admitted(state))
            .map((key, state) => (key, instance(state, right)))
        )
        .distinctBy(_._1)

    def abstraction(
        body: Configured[C],
        leaves: Vector[Configured[C]]
    ): ClosedTerm =
      val binders = leaves.indices.toVector
      val bound = leaves.zip(binders).toMap
      chainEmitted(
        binders,
        instructionView(body, bound),
        None,
        binders.size
      ) match
        case Some((emitted, _)) if emitted.free.isEmpty => emitted.closedTerm
        case other                                      =>
          throw IllegalStateException(
            s"the abstraction of a closed body reads a binder around it: $other"
          )

    /** Whether the solution is one an expansion union may state: for each thunk
      * of the side matched at a member node and holding a higher-order
      * metavariable, the binding normal form of the thunk under the solution
      * (`BindingNormalForm.of`, the function a trace's conversions call) is the
      * member's term or its spelling
      * (`gezi.rewritetrace.Conversions.spelledAlike`).
      *
      * The abstraction reads a filling through any member of its class, and a
      * class may hold, beside the term matched, a redex of it that a lemma's
      * instance put there: under `λk. λa. (λx. λz. k x) a = λk. λa. λz. k a`
      * the class of `λw. I I` holds `(λx. λz. I x) I`, and the program
      * `(λx. λz. x (λw. I I)) I` was solved with
      * `k := λy. y ((λx. λz. I x) I)`. Its binding normal form keeps that
      * redex, since it reduces only the higher-order values' applications and
      * is not to be completed into full β, so the union of the member and the
      * expansion would equate two terms no conversion relates, and a trace
      * could not replay it (2026-11-16; RewriteTraceLawTest under HEDGEHOG_SEED
      * 73277739101918).
      *
      * Why dropping a solution S, matched at the member m, loses no class the
      * instances reach, when the premise below holds:
      *
      *   1. The matching also finds the solution S_m that reads every position
      *      under m through the node m's made layer holds there. Wherever S
      *      read a member n of a class, that class is the root of the node p
      *      m's layer holds at that position, and entering the class enumerates
      *      all its members (`View.memberNodes`), p among them.
      *   2. S and S_m differ only by nodes of one class put for each other:
      *      every value they bind names, at each position, a node of the same
      *      class. The instance builds the left side's thunks and the right
      *      side's normal forms as layers over the nodes the bindings name
      *      (`instance`, `normalForm`), and unites each with a class S and S_m
      *      share (m's, or the class of the built thunk). Layers over nodes of
      *      equal classes are congruent, so the two instances unite the same
      *      classes.
      *   3. Premise: S_m is admitted. Its abstraction takes m's own subterms
      *      out of m's term, and the binding normal form puts them back by
      *      reducing the applications of the higher-order values, so it gives
      *      m's term, or that term's spelling, whenever the abstraction took
      *      out no lambda that m's term applies. The premise fails for a
      *      solution that abstracts an applied lambda, k := λf. f C for the
      *      redex `(λw. x) C` of m's term (the shape left out at
      *      `RewriteTraceLawTest.higherOrderLemmas`'s FIXME): the normal form
      *      https://github.com/Atry/private-overlay/issues/1964 contracts that
      *      redex, S_m is not admitted, and this filter drops the match (a
      *      reading of the definition, not measured).
      *
      * FIXME (2026-11-16): under a lemma that applies its function
      * https://github.com/Atry/private-overlay/issues/1964 metavariable to a
      * lambda, this filter drops the match itself, not a duplicate of it, until
      * the matcher abstracts a lambda argument only where it occurs unapplied
      * (the fix recorded at that FIXME).
      * https://github.com/Atry/private-overlay/issues/1964
      */
    private def admitted(state: State): Boolean =
      val expanded = state.thunkClasses.filter((thunk, _) =>
        mentions(thunk, state.higherOrder)
      )
      expanded.isEmpty || {
        val terms = nodeTerms(
          state.bindings.values.flatMap(classNodes).toVector ++ expanded.map(
            _._2
          )
        )
        val bindings =
          state.bindings.view.mapValues(closedInstruction(_, terms)).toMap
        expanded.forall { (thunk, member) =>
          val normal = BindingNormalForm.of(thunk, bindings, state.higherOrder)
          val term = terms(member)
          Configured.same(normal, term) || Configured.same(
            normal,
            BindingNormalForm.spelled(term)
          )
        }
      }

    /** The nodes a closed term names. */
    private def classNodes(term: ClosedTerm): Vector[Int] = term match
      case ClosedTerm.Class(node)               => Vector(node)
      case ClosedTerm.InstructionTerm(_)        => Vector.empty
      case ClosedTerm.Apply(function, argument) =>
        classNodes(function) ++ classNodes(argument)
      case ClosedTerm.Parallel(left, right) =>
        classNodes(left) ++ classNodes(right)
      case ClosedTerm.Choice(left, right) =>
        classNodes(left) ++ classNodes(right)
      case ClosedTerm.Thunk(_, _, fillings) => fillings.flatMap(classNodes)

    /** A closed term as an instruction, each node its term. */
    private def closedInstruction(
        term: ClosedTerm,
        terms: Map[Int, Configured[C]]
    ): Configured[C] = term match
      case ClosedTerm.Class(node)                  => terms(node)
      case ClosedTerm.InstructionTerm(instruction) => instruction
      case ClosedTerm.Apply(function, argument)    =>
        specializer.application(
          closedInstruction(function, terms),
          closedInstruction(argument, terms)
        )
      case ClosedTerm.Parallel(left, right) =>
        specializer.parallel(
          closedInstruction(left, terms),
          closedInstruction(right, terms)
        )
      case ClosedTerm.Choice(left, right) =>
        specializer.choice(
          closedInstruction(left, terms),
          closedInstruction(right, terms)
        )
      case ClosedTerm.Thunk(code, holes, fillings) =>
        thunkTerm(
          specializer,
          code,
          holes,
          fillings.map(closedInstruction(_, terms))
        )

    /** The terms of the nodes and the nodes below them: each node's layer as it
      * was made over the terms of the nodes its maker passed, the term a proof
      * reads for it (`gezi.strategies.GraphProof`). A stack of visits, since a
      * term is as deep as a program.
      */
    private def nodeTerms(nodes: Vector[Int]): Map[Int, Configured[C]] =
      @tailrec
      def visited(
          stack: List[(Int, Boolean)],
          made: Map[Int, Configured[C]]
      ): Map[Int, Configured[C]] = stack match
        case Nil                                      => made
        case (node, _) :: rest if made.contains(node) => visited(rest, made)
        case (node, false) :: rest                    =>
          visited(
            graph.madeLayer(node).children.toList.map((_, false)) ++ ((
              node,
              true
            ) :: rest),
            made
          )
        case (node, true) :: rest =>
          val term =
            graph.store.construction.instruction(graph.madeLayer(node))(made)
          visited(rest, made.updated(node, term))
      visited(nodes.toList.map((_, false)), Map.empty)

    // ---- reading ----

    /** The views of a class's members that have a layer of the IR. */
    def members(root: Int): Vector[View] =
      memberNodes(root).map(_._2)

    /** The views of a class's members that have a layer of the IR, each with
      * its node, so that a union written for a match joins the member the match
      * read and not another member of its class: a step of the proof goes
      * between the terms it spells. A member's view is over the nodes it was
      * made over (`EGraph.madeLayer`), not over its children's classes' roots,
      * so that a closed subterm a solution takes from it is written as the node
      * the member holds: through a root, a class that also holds a redex of
      * that subterm (a lemma's instance united with it) was written as the
      * redex, and the expansion's term differed from the member's by more than
      * the conversion (RewriteTraceLawTest under HEDGEHOG_SEED 73277739101918;
      * 2026-11-16). Without explanation mode a node's made layer is its
      * signature over the roots at the time it was made: still the specific
      * nodes it was built over. Every comparison of classes goes through
      * `EGraph.root`. A class the round stops at shows its pattern views only
      * (`ConstantStorageStop`), as it does to the first-order matchers.
      */
    def memberNodes(node: Int): Vector[(Int, View)] =
      graph
        .classMembers(graph.root(node))
        .filterNot(member => ConstantStorageStop.hidden(graph, member.node))
        .flatMap(member =>
          ((graph.madeLayer(member.node) match
            case ir.Apply(function, argument) =>
              Some(View.Apply(View.Class[C](function), View.Class[C](argument)))
            case ir.Parallel(left, right) =>
              Some(View.Parallel(View.Class[C](left), View.Class[C](right)))
            case ir.Choice(left, right) =>
              Some(View.Choice(View.Class[C](left), View.Class[C](right)))
            case ir.Thunk(code, holes, fillings) =>
              Some(
                View.Lambda(
                  code,
                  holes,
                  fillingEnvironment(holes, fillings.map(View.Class[C](_))),
                  inlined = false
                )
              )
            case ir.NoinlineLeaf(_)      => None
            case view: ir.StorageView[?] =>
              throw IllegalStateException(
                s"a node's layer is never a storage's view: $view"
              )
          ): Option[View]).map(view => (member.node, view))
        )

    /** A match so far: the metavariables' values, those solved by abstraction,
      * the target binder each binder of the side's object lambdas stands for,
      * the captures of an argument's lambda, the next binder number free, and
      * the member node each thunk of the side was matched at.
      */
    private final case class State(
        bindings: Map[Int, ClosedTerm],
        higherOrder: Set[Int],
        correspondence: Map[Int, Int],
        captures: Map[Int, View],
        nextBinder: Int,
        thunkClasses: Vector[(PatternThunk, Int)]
    ):
      def fresh: (State, Int) = (copy(nextBinder = nextBinder + 1), nextBinder)

    private object State:
      val initial: State =
        State(Map.empty, Set.empty, Map.empty, Map.empty, 0, Vector.empty)

    /** The matches of the pattern at the target. */
    private def matched(
        pattern: PatternView,
        target: View,
        state: State,
        mode: Mode
    ): Vector[State] =
      pattern match
        case PatternView.Bound(binder) =>
          target match
            case View.Bound(targetBinder)
                if state.correspondence.get(binder).contains(targetBinder) =>
              Vector(state)
            case _ => Vector.empty
        case PatternView.Capture(index) =>
          state.captures.get(index) match
            case None =>
              Vector(
                state.copy(captures = state.captures.updated(index, target))
              )
            case Some(earlier) =>
              if same(earlier, target) then Vector(state) else Vector.empty
        case PatternView.Metavariable(index) =>
          valueMatched(index, target, state, mode)
        case PatternView.Closure(index) =>
          target match
            case View.Class(node)
                if !ConstantStorageStop.stopped(graph, node) && graph
                  .hasClosure(graph.root(node)) =>
              valueMatched(index, target, state, mode)
            case View.Lambda(_, _, _, _) =>
              valueMatched(index, target, state, mode)
            case _ => Vector.empty
        case PatternView.Reference(instruction) =>
          target match
            case View.Class(node)
                if graph
                  .instructionNode(instruction)
                  .exists(found =>
                    !ConstantStorageStop.hidden(graph, found) && graph
                      .root(found) == graph.root(node)
                  ) =>
              Vector(state)
            case _ => Vector.empty
        case application @ PatternView.Apply(function, argument) =>
          val (head, arguments) = patternSpine(application)
          head match
            case PatternView.Metavariable(index)
                if mode == Mode.Solving && !state.bindings.contains(index) &&
                  arguments.forall(argument =>
                    determined(argument, state) && open(argument)
                  ) =>
              solved(index, arguments, target, state).toVector
            case _ =>
              alternatives(target).flatMap {
                case View.Apply(targetFunction, targetArgument) =>
                  matched(function, targetFunction, state, mode).flatMap(
                    matched(argument, targetArgument, _, mode)
                  )
                case _ => Vector.empty
              }
        case PatternView.Parallel(left, right) =>
          alternatives(target).flatMap {
            case View.Parallel(targetLeft, targetRight) =>
              matched(left, targetLeft, state, mode).flatMap(
                matched(right, targetRight, _, mode)
              )
            case _ => Vector.empty
          }
        case PatternView.Choice(left, right) =>
          alternatives(target).flatMap {
            case View.Choice(targetLeft, targetRight) =>
              matched(left, targetLeft, state, mode).flatMap(
                matched(right, targetRight, _, mode)
              )
            case _ => Vector.empty
          }
        case lambda @ PatternView.Lambda(_, _, _, _) =>
          target match
            case View.Class(root) =>
              memberNodes(root).flatMap {
                case (member, targetLambda @ View.Lambda(_, _, _, _)) =>
                  lambda.origin match
                    case Some(origin)
                        if targetLambda.code == origin.code && targetLambda.holes == origin.holes =>
                      // The side's own code: the first-order matching finds it.
                      Vector.empty
                    case Some(origin) =>
                      lambdaMatched(lambda, targetLambda, state, mode)
                        .map(found =>
                          found.copy(thunkClasses =
                            found.thunkClasses :+ (origin, member)
                          )
                        )
                    case None =>
                      lambdaMatched(lambda, targetLambda, state, mode)
                case _ => Vector.empty
              }
            case targetLambda @ View.Lambda(_, _, _, _) =>
              lambdaMatched(lambda, targetLambda, state, mode)
            case _ => Vector.empty

    /** A lambda of the side against a lambda of the target: a binder entered on
      * each side, standing for each other, and the rest matched.
      */
    private def lambdaMatched(
        lambda: PatternView.Lambda[C],
        target: View.Lambda[C],
        state: State,
        mode: Mode
    ): Vector[State] =
      val (afterPattern, patternBinder) = state.fresh
      val (afterTarget, targetBinder) = afterPattern.fresh
      val entered = afterTarget.copy(correspondence =
        afterTarget.correspondence.updated(patternBinder, targetBinder)
      )
      matched(
        PatternView.entered(lambda, PatternView.Bound[C](patternBinder)),
        View.entered(target, View.Bound[C](targetBinder)),
        entered,
        mode
      )

    /** A metavariable read: its value when bound, which the target must equal;
      * bound to the target, which must be closed, otherwise.
      */
    private def valueMatched(
        index: Int,
        target: View,
        state: State,
        mode: Mode
    ): Vector[State] =
      (state.bindings.get(index), closedTerm(target)) match
        case (Some(value), Some(term)) =>
          if rooted(value) == rooted(term) then Vector(state) else Vector.empty
        case (None, Some(term)) if mode == Mode.Solving =>
          Vector(state.copy(bindings = state.bindings.updated(index, term)))
        case _ => Vector.empty

    /** The target, or the views of its class's members. */
    private def alternatives(target: View): Vector[View] = target match
      case View.Class(root) => members(root)
      case other            => Vector(other)

    private def patternSpine(
        pattern: PatternView
    ): (PatternView, Vector[PatternView]) = pattern match
      case PatternView.Apply(function, argument) =>
        val (head, arguments) = patternSpine(function)
        (head, arguments :+ argument)
      case other => (other, Vector.empty)

    /** The argument has no metavariable left unbound. */
    private def determined(argument: PatternView, state: State): Boolean =
      argument match
        case PatternView.Metavariable(index) => state.bindings.contains(index)
        case PatternView.Closure(index)      => state.bindings.contains(index)
        case PatternView.Apply(function, argument) =>
          determined(function, state) && determined(argument, state)
        case PatternView.Parallel(left, right) =>
          determined(left, state) && determined(right, state)
        case PatternView.Choice(left, right) =>
          determined(left, state) && determined(right, state)
        case PatternView.Lambda(_, _, environment, _) =>
          environment.values.forall(determined(_, state))
        case PatternView.Bound(_) | PatternView.Capture(_) |
            PatternView.Reference(_) =>
          true

    /** The argument reads a binder of the side's object lambdas. */
    private def open(argument: PatternView): Boolean = argument match
      case PatternView.Bound(_)                  => true
      case PatternView.Apply(function, argument) =>
        open(function) || open(argument)
      case PatternView.Parallel(left, right)        => open(left) || open(right)
      case PatternView.Choice(left, right)          => open(left) || open(right)
      case PatternView.Lambda(_, _, environment, _) =>
        environment.values.exists(open)
      case _ => false

    /** Two views of one term, compared by their structure. */
    private def same(left: View, right: View): Boolean = (left, right) match
      case (View.Bound(first), View.Bound(second)) => first == second
      case (View.Class(first), View.Class(second)) =>
        graph.root(first) == graph.root(second)
      case (View.Term(first), View.Term(second))    => first == second
      case (View.Apply(f1, a1), View.Apply(f2, a2)) =>
        same(f1, f2) && same(a1, a2)
      case (View.Parallel(l1, r1), View.Parallel(l2, r2)) =>
        same(l1, l2) && same(r1, r2)
      case (View.Choice(l1, r1), View.Choice(l2, r2)) =>
        same(l1, l2) && same(r1, r2)
      case (View.Lambda(c1, h1, e1, _), View.Lambda(c2, h2, e2, _)) =>
        c1 == c2 && h1 == h2 && e1.keySet == e2.keySet && e1.keySet.forall(
          slot => same(e1(slot), e2(slot))
        )
      case _ => false

    // ---- abstraction ----

    /** The arguments of a higher-order occurrence, the binders that stand for
      * them, and the match whose correspondence reads them.
      */
    private final case class Abstraction(
        arguments: Vector[PatternView],
        binders: Vector[Int],
        state: State
    )

    /** The metavariable solved at the target: the abstraction of the arguments'
      * occurrences, when it is closed.
      */
    private def solved(
        index: Int,
        arguments: Vector[PatternView],
        target: View,
        state: State
    ): Option[State] =
      val (afterBinders, binders) =
        arguments.foldLeft((state, Vector.empty[Int])) {
          case ((current, made), _) =>
            val (next, binder) = current.fresh
            (next, made :+ binder)
        }
      val abstraction = Abstraction(arguments, binders, afterBinders)
      chainEmitted(binders, target, Some(abstraction), afterBinders.nextBinder)
        .collect {
          case (emitted, nextBinder) if emitted.free.isEmpty =>
            afterBinders.copy(
              bindings =
                afterBinders.bindings.updated(index, emitted.closedTerm),
              higherOrder = afterBinders.higherOrder + index,
              nextBinder = nextBinder
            )
        }

    /** The argument whose occurrence the view is, and the views it captures, by
      * the first argument that matches.
      */
    private def occurrence(
        view: View,
        abstraction: Abstraction
    ): Option[(Int, Vector[View])] =
      abstraction.arguments.indices.foldLeft(
        Option.empty[(Int, Vector[View])]
      ) {
        case (None, position) =>
          argumentOccurrence(
            abstraction.arguments(position),
            view,
            abstraction.state
          ).map((position, _))
        case (found, _) => found
      }

    /** The captures of the argument's occurrence at the view: the instance of a
      * lambda's body with its binders captured, or the argument itself.
      */
    private def argumentOccurrence(
        argument: PatternView,
        view: View,
        state: State
    ): Option[Vector[View]] =
      val captured = argument match
        case lambda @ PatternView.Lambda(_, _, _, _)
            if lambda.holes.forall(_ != Hole.Ignored) =>
          val body = lambda.holes.indices.foldLeft(lambda: PatternView) {
            case (entered @ PatternView.Lambda(_, _, _, _), position) =>
              PatternView.entered(entered, PatternView.Capture[C](position))
            case (other, _) => other
          }
          matched(body, view, state.copy(captures = Map.empty), Mode.Frozen)
            .find(_.captures.size == lambda.holes.size)
            .map(found => lambda.holes.indices.toVector.map(found.captures))
        case _ => None
      captured.orElse(
        matched(argument, view, state, Mode.Frozen).headOption.map(_ =>
          Vector.empty
        )
      )

    // ---- emission ----

    /** What a slot of an emitted code reads: a binder, of the chain being
      * emitted or of one around it, or a maximal closed subterm.
      */
    private enum Source:
      case Bound(binder: Int)
      case Closed(term: ClosedTerm)

    /** The slots of a body being emitted, numbered by first occurrence in
      * preorder, as the front end numbers them.
      */
    private final case class Slots(
        sources: Vector[Source],
        numbers: Map[Source, Int]
    ):
      def slotOf(source: Source): (Int, Slots) =
        numbers.get(source) match
          case Some(slot) => (slot, this)
          case None       =>
            (
              sources.size,
              Slots(sources :+ source, numbers.updated(source, sources.size))
            )

    private object Slots:
      val empty: Slots = Slots(Vector.empty, Map.empty)

    /** An emitted chain: its code, its holes, and what its other slots read in
      * slot order, the binders around it (`free`) and the closed subterms.
      */
    private final case class Emitted(
        code: Code,
        holes: Vector[Hole],
        fillings: Vector[Source]
    ):
      def free: Vector[Int] = fillings.collect { case Source.Bound(binder) =>
        binder
      }

      /** The chain as a closed term; it reads no binder around it. */
      def closedTerm: ClosedTerm =
        ClosedTerm.Thunk(
          code,
          holes,
          fillings.map {
            case Source.Closed(term)  => term
            case Source.Bound(binder) =>
              throw IllegalStateException(
                s"a closed chain reads the binder $binder"
              )
          }
        )

    /** The chain of the binders given, then of every lambda at the head of the
      * body, emitted over the body; the abstraction's occurrences replaced
      * where it is given. Nothing when an occurrence's captures cannot be
      * emitted.
      */
    private def chainEmitted(
        binders: Vector[Int],
        body: View,
        abstraction: Option[Abstraction],
        nextBinder: Int
    ): Option[(Emitted, Int)] =
      entered(headReduced(body)) match
        case lambda @ View.Lambda(_, _, _, _)
            if abstraction.forall(occurrence(lambda, _).isEmpty) =>
          chainEmitted(
            binders :+ nextBinder,
            View.entered(lambda, View.Bound[C](nextBinder)),
            abstraction,
            nextBinder + 1
          )
        case reduced =>
          bodyEmitted(reduced, abstraction, Slots.empty, nextBinder).map {
            case (code, slots, after) =>
              val chain = binders.toSet
              val holes = binders.map(binder =>
                slots.numbers
                  .get(Source.Bound(binder))
                  .fold(Hole.Ignored)(Hole.Bound(_))
              )
              val fillings = slots.sources.filter {
                case Source.Bound(binder) => !chain.contains(binder)
                case Source.Closed(_)     => true
              }
              (Emitted(code, holes, fillings), after)
          }

    /** A chain's body that is a closed term whose layer is a thunk with holes,
      * as the lambda it is, so that the chain goes on into it: the front end
      * folds such a body into the chain, its binders before the thunk's holes
      * (`gezi.frontend.Defunctionalization`, `thunkInstruction`). The closed
      * term is an instruction, or a node of the graph, whose own layer is read,
      * its fillings the nodes that layer holds, so that the folded thunk's
      * fillings are the node's (the node's term, read by
      * `gezi.strategies.GraphProof`, is its layer over those nodes). Any other
      * view as it is.
      */
    private def entered(view: View): View = view match
      case View.Term(ClosedTerm.InstructionTerm(instruction))
          if !instruction.heldAsLeaf =>
        instruction.layer match
          case ir.Thunk(code, holes, fillings) if holes.nonEmpty =>
            View.Lambda(
              code,
              holes,
              fillingEnvironment(
                holes,
                fillings.map(filling =>
                  View.Term(ClosedTerm.InstructionTerm(filling))
                )
              ),
              inlined = false
            )
          case _ => view
      case View.Class(node) if !ConstantStorageStop.hidden(graph, node) =>
        graph.madeLayer(node) match
          case ir.Thunk(code, holes, fillings) if holes.nonEmpty =>
            View.Lambda(
              code,
              holes,
              fillingEnvironment(holes, fillings.map(View.Class[C](_))),
              inlined = false
            )
          case _ => view
      case other => other

    /** The view with every application of an inlined lambda at its head reduced
      * by beta. A lambda given as an argument to an inlined lambda is inlined
      * in turn, so that the redexes the substitution makes are reduced too, as
      * the instance of a higher-order pattern's right side is normalized
      * (hereditary substitution).
      *
      * FIXME (2026-11-04): nothing bounds the reduction; a right side whose
      * https://github.com/Atry/private-overlay/issues/1965 higher-order value
      * applies a lambda to itself, as `λy. y y` given `λx. x x`, does not end.
      * No lemma of the standard library has such a right side. Candidate fix: a
      * bound on the β steps of one normal form, the instance dropped when it is
      * reached.
      */
    private def headReduced(view: View): View = view match
      case View.Apply(_, _) =>
        val (head, arguments) = viewSpine(view)
        head match
          case lambda @ View.Lambda(_, _, _, _) if lambda.inlined =>
            val (reduced, left) =
              arguments.foldLeft((lambda: View, Vector.empty[View])) {
                case ((entered @ View.Lambda(_, _, _, _), rest), argument)
                    if rest.isEmpty =>
                  val inlinedArgument = argument match
                    case argumentLambda @ View.Lambda(_, _, _, _) =>
                      argumentLambda.copy(inlined = true)
                    case other => other
                  (View.entered(entered, inlinedArgument), rest)
                case ((other, rest), argument) => (other, rest :+ argument)
              }
            headReduced(left.foldLeft(reduced)(View.Apply(_, _)))
          case _ => view
      case other => other

    private def viewSpine(view: View): (View, Vector[View]) = view match
      case View.Apply(function, argument) =>
        val (head, arguments) = viewSpine(function)
        (head, arguments :+ argument)
      case other => (other, Vector.empty)

    /** The code of a subterm of a body, and the slots and the next binder after
      * it: an occurrence of the abstraction's argument the binder that stands
      * for it applied to the captures; a binder its slot; a maximal closed
      * subterm its slot; a lambda an inner chain whose fillings are slots of
      * the body.
      */
    private def bodyEmitted(
        view: View,
        abstraction: Option[Abstraction],
        slots: Slots,
        nextBinder: Int
    ): Option[(Code, Slots, Int)] =
      val reduced = headReduced(view)
      abstraction.flatMap(found =>
        occurrence(reduced, found).map((found, _))
      ) match
        case Some((found, (position, captures))) =>
          val (slot, afterHead) =
            slots.slotOf(Source.Bound(found.binders(position)))
          captures.foldLeft(Option((Code.Slot(slot), afterHead, nextBinder))) {
            case (Some((function, current, next)), capture) =>
              bodyEmitted(capture, abstraction, current, next).map {
                case (argument, after, afterNext) =>
                  (Code.Apply(function, argument), after, afterNext)
              }
            case (None, _) => None
          }
        case None =>
          reduced match
            case View.Bound(binder) =>
              val (slot, after) = slots.slotOf(Source.Bound(binder))
              Some((Code.Slot(slot), after, nextBinder))
            case closed if bindersRead(closed).isEmpty =>
              closedTerm(closed).map { term =>
                val (slot, after) = slots.slotOf(Source.Closed(term))
                (Code.Slot(slot), after, nextBinder)
              }
            case View.Apply(function, argument) =>
              for
                (functionCode, afterFunction, nextAfterFunction) <- bodyEmitted(
                  function,
                  abstraction,
                  slots,
                  nextBinder
                )
                (argumentCode, afterArgument, nextAfterArgument) <-
                  bodyEmitted(
                    argument,
                    abstraction,
                    afterFunction,
                    nextAfterFunction
                  )
              yield (
                Code.Apply(functionCode, argumentCode),
                afterArgument,
                nextAfterArgument
              )
            case View.Parallel(left, right) =>
              for
                (leftCode, afterLeft, nextAfterLeft) <- bodyEmitted(
                  left,
                  abstraction,
                  slots,
                  nextBinder
                )
                (rightCode, afterRight, nextAfterRight) <- bodyEmitted(
                  right,
                  abstraction,
                  afterLeft,
                  nextAfterLeft
                )
              yield (
                Code.Parallel(leftCode, rightCode),
                afterRight,
                nextAfterRight
              )
            case View.Choice(left, right) =>
              for
                (leftCode, afterLeft, nextAfterLeft) <- bodyEmitted(
                  left,
                  abstraction,
                  slots,
                  nextBinder
                )
                (rightCode, afterRight, nextAfterRight) <- bodyEmitted(
                  right,
                  abstraction,
                  afterLeft,
                  nextAfterLeft
                )
              yield (
                Code.Choice(leftCode, rightCode),
                afterRight,
                nextAfterRight
              )
            case lambda @ View.Lambda(_, _, _, _) =>
              chainEmitted(
                Vector(nextBinder),
                View.entered(lambda, View.Bound[C](nextBinder)),
                abstraction,
                nextBinder + 1
              )
                .map { case (inner, afterInner) =>
                  val (fillings, after) =
                    inner.fillings.foldLeft((Vector.empty[Code], slots)) {
                      case ((codes, current), source) =>
                        val (slot, next) = current.slotOf(source)
                        (codes :+ Code.Slot(slot), next)
                    }
                  (
                    Code.Thunk(inner.code, inner.holes, fillings),
                    after,
                    afterInner
                  )
                }
            case View.Class(root) =>
              val (slot, after) =
                slots.slotOf(Source.Closed(ClosedTerm.Class[C](root)))
              Some((Code.Slot(slot), after, nextBinder))
            case View.Term(term) =>
              val (slot, after) = slots.slotOf(Source.Closed(term))
              Some((Code.Slot(slot), after, nextBinder))

    /** The binders of lambdas around the view that it reads. A view that reads
      * none holds no occurrence of an abstraction, every argument being open.
      */
    private def bindersRead(view: View): Set[Int] = view match
      case View.Bound(binder)             => Set(binder)
      case View.Term(_)                   => Set.empty
      case View.Class(_)                  => Set.empty
      case View.Apply(function, argument) =>
        bindersRead(function) ++ bindersRead(argument)
      case View.Parallel(left, right) => bindersRead(left) ++ bindersRead(right)
      case View.Choice(left, right)   => bindersRead(left) ++ bindersRead(right)
      case View.Lambda(_, _, environment, _) =>
        environment.values.flatMap(bindersRead).toSet

    /** The closed term of a view that reads no binder. The binders a closed
      * lambda's chain enters are numbered from 0: the view reads no other.
      */
    private def closedTerm(view: View): Option[ClosedTerm] =
      if bindersRead(view).nonEmpty then None
      else
        view match
          case View.Class(root)               => Some(ClosedTerm.Class[C](root))
          case View.Term(term)                => Some(term)
          case View.Apply(function, argument) =>
            for
              functionTerm <- closedTerm(function)
              argumentTerm <- closedTerm(argument)
            yield ClosedTerm.Apply(functionTerm, argumentTerm)
          case View.Parallel(left, right) =>
            for
              leftTerm <- closedTerm(left)
              rightTerm <- closedTerm(right)
            yield ClosedTerm.Parallel(leftTerm, rightTerm)
          case View.Choice(left, right) =>
            for
              leftTerm <- closedTerm(left)
              rightTerm <- closedTerm(right)
            yield ClosedTerm.Choice(leftTerm, rightTerm)
          case lambda @ View.Lambda(_, _, _, _) =>
            chainEmitted(Vector.empty, lambda, None, 0).collect {
              case (emitted, _) if emitted.free.isEmpty => emitted.closedTerm
            }
          case View.Bound(_) => None

    // ---- instances ----

    /** What the match writes: the left side's thunks under the bindings, each
      * united with the class it matched in; and the right side's thunks that
      * apply a higher-order metavariable, each united with its beta normal
      * form.
      */
    private def instance(state: State, right: Pattern): HigherOrderInstance =
      val expansions = state.thunkClasses.collect {
        case (thunk, member) if mentions(thunk, state.higherOrder) =>
          (member, instantiated(thunk, state.bindings))
      }
      val normalizations = patternSubterms(right).collect {
        case thunk @ Pattern.Thunk(_, _, _)
            if mentions(thunk, state.higherOrder) =>
          (instantiated(thunk, state.bindings), normalForm(thunk, state))
      }
      HigherOrderInstance(expansions, normalizations)

    private def mentions(
        thunk: PatternThunk,
        metavariables: Set[Int]
    ): Boolean =
      thunk.fillings.exists(filling =>
        patternSubterms(filling).exists {
          case Pattern.Metavariable(index) => metavariables.contains(index)
          case _                           => false
        }
      )

    /** The pattern with its metavariables replaced by their values, a closed
      * term; a reference is the instruction it names.
      */
    private def instantiated(
        pattern: Pattern,
        bindings: Map[Int, ClosedTerm]
    ): ClosedTerm = pattern match
      case Pattern.Metavariable(index) =>
        bindings.getOrElse(
          index,
          throw IllegalStateException(s"the metavariable $index is unbound")
        )
      case Pattern.Closure(index) =>
        bindings.getOrElse(
          index,
          throw IllegalStateException(s"the metavariable $index is unbound")
        )
      case Pattern.InstructionReference(instruction) =>
        ClosedTerm.InstructionTerm(instruction)
      case Pattern.Apply(function, argument) =>
        ClosedTerm.Apply(
          instantiated(function, bindings),
          instantiated(argument, bindings)
        )
      case Pattern.Parallel(left, right) =>
        ClosedTerm.Parallel(
          instantiated(left, bindings),
          instantiated(right, bindings)
        )
      case Pattern.Choice(left, right) =>
        ClosedTerm.Choice(
          instantiated(left, bindings),
          instantiated(right, bindings)
        )
      case Pattern.Thunk(code, holes, fillings) =>
        ClosedTerm.Thunk(code, holes, fillings.map(instantiated(_, bindings)))

    /** The right side's thunk under the bindings with every application of a
      * higher-order metavariable's value reduced by beta, spelled as the front
      * end spells it: `gezi.ir.BindingNormalForm.of`, the one function the
      * trace's conversions call too, over the bindings as instructions
      * (`bindingInstruction`), each class that is no thunk with holes an opaque
      * placeholder read back as its class.
      */
    private def normalForm(thunk: PatternThunk, state: State): ClosedTerm =
      val converted =
        state.bindings.view.mapValues(bindingInstruction(_, Set.empty)).toMap
      val placeholders = converted.values
        .flatMap(_._2)
        .map(node => placeholder(node) -> node)
        .toMap
      closedTermOf(
        BindingNormalForm
          .of(thunk, converted.view.mapValues(_._1).toMap, state.higherOrder),
        placeholders
      )

    /** A closed term with each node it names replaced by its class's root: two
      * bindings of one metavariable are one value when they name the same
      * classes, whichever members (`View.memberNodes`).
      */
    private def rooted(term: ClosedTerm): ClosedTerm = term match
      case ClosedTerm.Class(node) => ClosedTerm.Class[C](graph.root(node))
      case ClosedTerm.InstructionTerm(_)        => term
      case ClosedTerm.Apply(function, argument) =>
        ClosedTerm.Apply(rooted(function), rooted(argument))
      case ClosedTerm.Parallel(left, right) =>
        ClosedTerm.Parallel(rooted(left), rooted(right))
      case ClosedTerm.Choice(left, right) =>
        ClosedTerm.Choice(rooted(left), rooted(right))
      case ClosedTerm.Thunk(code, holes, fillings) =>
        ClosedTerm.Thunk(code, holes, fillings.map(rooted))

    /** A binding as an instruction, with the nodes it stands in for: a node
      * made over a thunk with holes expanded to that thunk, over the nodes of
      * its fillings in turn, so that the normal form enters it as the trace's
      * conversions enter the same term (a higher-order value inlined, a chain's
      * body folded, d1ce63b27); any other node an opaque placeholder
      * (`placeholder`) read back as that node. The node is the one the solution
      * names, read through the layer it was made over, never its class's root
      * (`View.memberNodes`).
      */
    private def bindingInstruction(
        term: ClosedTerm,
        expanding: Set[Int]
    ): (Configured[C], Set[Int]) =
      def all(
          parts: Vector[ClosedTerm],
          below: Set[Int]
      ): (Vector[Configured[C]], Set[Int]) =
        parts.foldLeft((Vector.empty[Configured[C]], Set.empty[Int])) {
          case ((made, nodes), part) =>
            val (instruction, partNodes) = bindingInstruction(part, below)
            (made :+ instruction, nodes ++ partNodes)
        }
      term match
        case ClosedTerm.InstructionTerm(instruction) => (instruction, Set.empty)
        case ClosedTerm.Class(node)                  =>
          graph.madeLayer(node) match
            case ir.Thunk(code, holes, fillings)
                if holes.nonEmpty && !expanding.contains(node) =>
              val (made, nodes) =
                all(fillings.map(ClosedTerm.Class[C](_)), expanding + node)
              (thunkTerm(specializer, code, holes, made), nodes)
            case _ => (placeholder(node), Set(node))
        case ClosedTerm.Apply(function, argument) =>
          val (functionInstruction, functionNodes) =
            bindingInstruction(function, expanding)
          val (argumentInstruction, argumentNodes) =
            bindingInstruction(argument, expanding)
          (
            specializer.application(functionInstruction, argumentInstruction),
            functionNodes ++ argumentNodes
          )
        case ClosedTerm.Parallel(left, right) =>
          val (leftInstruction, leftNodes) = bindingInstruction(left, expanding)
          val (rightInstruction, rightNodes) =
            bindingInstruction(right, expanding)
          (
            specializer.parallel(leftInstruction, rightInstruction),
            leftNodes ++ rightNodes
          )
        case ClosedTerm.Choice(left, right) =>
          val (leftInstruction, leftNodes) = bindingInstruction(left, expanding)
          val (rightInstruction, rightNodes) =
            bindingInstruction(right, expanding)
          (
            specializer.choice(leftInstruction, rightInstruction),
            leftNodes ++ rightNodes
          )
        case ClosedTerm.Thunk(code, holes, fillings) =>
          val (made, nodes) = all(fillings, expanding)
          (thunkTerm(specializer, code, holes, made), nodes)

    /** The opaque instruction that stands for a node in a binding given to the
      * normal form, read back as that node (`closedTermOf`). It never reaches
      * the graph.
      */
    private def placeholder(node: Int): Configured[C] =
      specializer.opaque(s"binding normal form placeholder of node $node")

    /** The normal form as a closed term: a placeholder its class, a subterm
      * that holds none the instruction it is, any other one layer over closed
      * terms.
      */
    private def closedTermOf(
        instruction: Configured[C],
        placeholders: Map[Configured[C], Int]
    ): ClosedTerm =
      placeholders.get(instruction) match
        case Some(root) => ClosedTerm.Class[C](root)
        case None if !holds(instruction, placeholders.keySet) =>
          ClosedTerm.InstructionTerm(instruction)
        case None =>
          instruction.layer match
            case ir.Apply(function, argument) =>
              ClosedTerm.Apply(
                closedTermOf(function, placeholders),
                closedTermOf(argument, placeholders)
              )
            case ir.Parallel(left, right) =>
              ClosedTerm.Parallel(
                closedTermOf(left, placeholders),
                closedTermOf(right, placeholders)
              )
            case ir.Choice(left, right) =>
              ClosedTerm.Choice(
                closedTermOf(left, placeholders),
                closedTermOf(right, placeholders)
              )
            case ir.Thunk(code, holes, fillings) =>
              ClosedTerm.Thunk(
                code,
                holes,
                fillings.map(closedTermOf(_, placeholders))
              )
            case other =>
              throw IllegalStateException(
                s"a normal form holds a placeholder under a leaf: $other"
              )
