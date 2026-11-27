package com.yang_bo.gezi.rewritetrace

import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.TermOf
import com.yang_bo.gezi.ir.BindingNormalForm
import com.yang_bo.gezi.ir.Store
import com.yang_bo.gezi.ir.TermConstruction
import com.yang_bo.gezi.saturation.ClosedTerm
import com.yang_bo.gezi.saturation.HigherOrderMatching
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.Layer
import com.yang_bo.gezi.ir.NonEmptyHoles
import com.yang_bo.gezi.ir.Pattern
import com.yang_bo.gezi.ir.Spine
import com.yang_bo.gezi.ir.StorageAccess
import com.yang_bo.gezi.ir.StorageView
import com.yang_bo.gezi.ir.{Apply, Choice, Parallel, Slot, Thunk}
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** A side of a lemma's statement. */
enum LemmaSide:
  case Left, Right

/** A β conversion the e-graph made with no step of a proof yet
  * (`com.yang_bo.gezi.strategies.GraphProof`'s FIXME), named by what the replay computes it
  * from. Its equation is derivable by the β rule and the congruence under λ,
  * both rules of ⊢.
  *
  * `HigherOrder` is the higher-order matching's expansion and normalization
  * (`com.yang_bo.gezi.saturation.HigherOrderMatching.written`): the instance of the thunk
  * pattern at `occurrence` (preorder, `Conversions.thunkPatterns`) of the
  * lemma's side equals its normal form (`Conversions.normalForm`).
  *
  * `RootReverseBeta` is the higher-order saturator's root reverse β
  * (`com.yang_bo.gezi.strategies.HigherOrderSaturator`): a term equals the redex
  * `(λx1 … xn. T[G1 := x1, …]) G1 … Gn` over the names G1 to Gn the lemma's
  * left side applies its metavariable to (`Conversions.redex`).
  */
enum Conversion:
  case HigherOrder(lemma: Int, side: LemmaSide, occurrence: Int)
  case RootReverseBeta(lemma: Int)

/** The terms a conversion's equation relates, computed on the IR as the front
  * end spells them: a term is read as a HOAS term in which only the
  * applications the conversion contracts are reduced, and the front end
  * converts it (`Defunctionalization`), so that the spelling is the front
  * end's. The saturator builds the same terms on the e-graph; the writer of a
  * trace checks, step by step, that the two give one instruction
  * (`com.yang_bo.gezi.proofs.RewriteTrace.trace`), as the β rule's two implementations are
  * checked (`Statements.fill` and the saturator's β).
  */
object Conversions:

  /** The thunks of a side, in preorder: a thunk before the thunks under it. */
  def thunkPatterns[Term](
      side: StatementTerm[Term]
  ): Vector[StatementTerm[Term]] = side match
    case StatementTerm.Layered(layer @ Thunk(_, _, _)) =>
      side +: (layer: Layer[StatementTerm[Term]]).children
        .flatMap(thunkPatterns)
    case StatementTerm.Layered(layer) => layer.children.flatMap(thunkPatterns)
    case StatementTerm.Variable(_) | StatementTerm.Stored(_) => Vector.empty

  /** The thunk pattern of a higher-order conversion. Throws
    * `IllegalArgumentException` when the side has no thunk at the occurrence.
    */
  def pattern[Term](
      statement: Statement[Term],
      side: LemmaSide,
      occurrence: Int
  ): StatementTerm[Term] =
    thunkPatterns(sideOf(statement, side))
      .lift(occurrence)
      .getOrElse(
        throw IllegalArgumentException(
          s"the $side side has no thunk $occurrence"
        )
      )

  /** The side of a statement. */
  def sideOf[Term](
      statement: Statement[Term],
      side: LemmaSide
  ): StatementTerm[Term] = side match
    case LemmaSide.Left  => statement.left
    case LemmaSide.Right => statement.right

  /** The higher-order variables of a statement: those a thunk of the left side
    * applies, a variable filling a slot that heads an application in the
    * thunk's code, which the higher-order matching solves by abstraction
    * (`HigherOrderMatching.solved`, its `state.higherOrder`) and whose
    * applications its normal forms reduce. A variable applied only on the right
    * side is matched first-order, its value a leaf: counting it reduced the
    * right side's `a w`, which the saturator keeps, under
    * `λk. λa. (λx. λz. z (λw. k (x w))) a = λk. λa. λz. z (λw. k (a w))`.
    */
  def higherOrder[Term](statement: Statement[Term]): Set[String] =
    thunkPatterns(statement.left).flatMap {
      case StatementTerm.Layered(Thunk(code, holes, fillings)) =>
        val slots = Defunctionalization.slotValues(
          holes,
          holes.map(_ => None),
          fillings.map(Some(_))
        )
        headSlots(code).toVector
          .flatMap(slot => slots.lift(slot).flatten)
          .collect { case StatementTerm.Variable(name) => name }
      case _ => Vector.empty
    }.toSet

  /** The slots of the code that head an application, an inner thunk's head
    * slots read through its fillings back to the code's own.
    */
  private def headSlots(code: Code): Set[Int] = code.layer match
    case Slot(_)                   => Set.empty
    case Apply(function, argument) =>
      spineHead(function).toSet ++ headSlots(function) ++ headSlots(argument)
    case Parallel(left, right)         => headSlots(left) ++ headSlots(right)
    case Choice(left, right)           => headSlots(left) ++ headSlots(right)
    case Thunk(inner, holes, fillings) =>
      val innerSlots = Defunctionalization.slotValues(
        holes,
        holes.map(_ => None),
        fillings.map(Some(_))
      )
      fillings.flatMap(headSlots).toSet ++ headSlots(inner).flatMap(slot =>
        innerSlots
          .lift(slot)
          .flatten
          .flatMap(filling =>
            filling.layer match
              case Slot(outer) => Some(outer)
              case _           => None
          )
      )

  private def spineHead(code: Code): Option[Int] = Spine.of(code)._1.layer match
    case Slot(slot) => Some(slot)
    case _          => None

  /** The normal form of the thunk pattern under the bindings, as the
    * higher-order saturator computes it: `com.yang_bo.gezi.ir.BindingNormalForm.of`, the
    * one function both call, over the pattern with its variables numbered in
    * the order they first occur, in the trace's configuration. Throws
    * `IllegalArgumentException` for a variable with no binding and for a
    * pattern that is no thunk.
    */
  def normalForm[C <: NativeSpecializer & Singleton](
      pattern: StatementTerm[Configured[C]],
      bound: Map[String, Configured[C]],
      higherOrderVariables: Set[String]
  )(using C): Configured[C] =
    val names = Statements.variables(pattern).distinct
    val indices = names.zipWithIndex.toMap
    val thunk = patternOf(pattern, indices)
    thunk match
      case Pattern.Thunk(_, _, _) =>
        BindingNormalForm.of(
          thunk,
          names
            .map(name =>
              indices(name) -> bound.getOrElse(
                name,
                throw IllegalArgumentException(s"the conversion binds no $name")
              )
            )
            .toMap,
          higherOrderVariables.flatMap(indices.get)
        )
      case other =>
        throw IllegalArgumentException(
          s"a conversion's pattern is a thunk, not $other"
        )

  /** Whether a normal form (`normalForm`, spelled as the front end spells) is
    * the term up to that spelling: the term itself, or the term respelled
    * (`BindingNormalForm.spelled`). A step backward checks the term it replaces
    * this way: a node the saturator made by a β step may keep a closed lambda
    * inline as code where the front end makes it a slot, the same λ-term
    * spelled otherwise (`wren_own_loop_lifted` on the inlined hot points,
    * 2026-11-16, whose matched thunk keeps the body of x0's value `λa. …`
    * inline), so the equation checked, the term β-equal to the instance, holds
    * of it as of its spelling.
    */
  def spelledAlike[C <: NativeSpecializer & Singleton](
      normal: Configured[C],
      term: Configured[C]
  )(using C): Boolean =
    Configured.same(normal, term) || Configured.same(
      normal,
      BindingNormalForm.spelled(term)
    )

  /** The bindings that make the term, in the replay's spelling, the pattern's
    * instance in that spelling (`ReplaySpelling.side`). A lemma's side split
    * into its metavariables' fillings and the holes left is not always its own
    * spelling: `λk. λa. λz. k a` has the thunk
    * `thunk(apply(slot 0, slot 1), [ignored], [k, a])`, whose instance the
    * replay spells `thunk(slot 0, [ignored], [apply(k, a)])`.
    */
  def instanceBindings[C <: NativeSpecializer & Singleton](
      pattern: StatementTerm[Configured[C]],
      term: Configured[C]
  )(using
      C,
      StorageAccess
  ): Option[Map[String, Configured[C]]] =
    Statements.matchedBindings(ReplaySpelling.side(pattern), term)

  /** The pattern's instance under the bindings in the replay's spelling. */
  def instance[C <: NativeSpecializer & Singleton](
      pattern: StatementTerm[Configured[C]],
      bound: Map[String, Configured[C]]
  )(using C): Configured[C] =
    Statements.instance(ReplaySpelling.side(pattern), bound)

  /** `λx. term x` as the front end spells it, the term a closed filling: the
    * thunk a step backward of the defunctionalized η rule puts in place of the
    * term, computed so that the step writes no thunk: a step backward names its
    * place by a path in the term's tree, not by a thunk.
    */
  def etaExpanded[C <: NativeSpecializer & Singleton](
      term: Configured[C]
  )(using C): Configured[C] =
    Defunctionalization.thunkInstruction[C](
      Term.λ(variable => Term.closed(term)(variable)).deBruijnTerm(Map.empty)
    )

  /** The solutions of a thunk pattern of a lemma's left side on the term a step
    * backward replaces, its normal form: the bindings of each match of the
    * pattern at the term's class that the saturator's own higher-order matching
    * finds (`com.yang_bo.gezi.saturation.HigherOrderMatching`) on a graph of that term
    * alone, and whose binding normal form (`normalForm`) is the term up to its
    * spelling (`spelledAlike`). The matching solves a higher-order metavariable
    * by abstracting its arguments' occurrences out of the matched term, so the
    * term and the pattern determine a solution, and a step backward of a left
    * side's conversion writes no binding: a binding written in a command is
    * what a trace avoids. The matching runs in the player too, which is why
    * `egraph` and that file of `saturation` are built for Scala.js. The graph
    * files no noinline name (`Store`), as a trace names none, and builds
    * through the trace's configuration with no storage made one layer up from a
    * leaf (`TermConstruction.apply`): the graph only matches the term, adding
    * no lemma instance, so that nothing it would build is read.
    */
  def expansionSolutions[C <: NativeSpecializer & Singleton](
      pattern: StatementTerm[Configured[C]],
      replaced: Configured[C],
      higherOrderVariables: Set[String]
  )(using specializer: C): Vector[Map[String, Configured[C]]] =
    val names = Statements.variables(pattern).distinct
    val indices = names.zipWithIndex.toMap
    val thunk = patternOf(pattern, indices)
    def solutionsOn(term: Configured[C]): Vector[Map[String, Configured[C]]] =
      val (graph, node) =
        EGraph
          .empty(
            Store(Set.empty[Configured[C]], TermConstruction(specializer)),
            Map.empty,
            explained = false
          )
          .instructionAdded(term)
      val classTerms = graph.liveNodes
        .flatMap(live => graph.nodeInstruction(live.node).map(live.root -> _))
        .toMap
      def instructionOf(closed: ClosedTerm[C]): Configured[C] = closed match
        case ClosedTerm.Class(root) =>
          classTerms.getOrElse(
            graph.root(root),
            throw IllegalStateException(
              s"the class $root of a term's graph holds no term"
            )
          )
        case ClosedTerm.InstructionTerm(instruction) => instruction
        case ClosedTerm.Apply(function, argument)    =>
          specializer.application(
            instructionOf(function),
            instructionOf(argument)
          )
        case ClosedTerm.Choice(left, right) =>
          specializer.choice(instructionOf(left), instructionOf(right))
        case ClosedTerm.Parallel(left, right) =>
          specializer.parallel(instructionOf(left), instructionOf(right))
        case ClosedTerm.Thunk(code, holes, fillings) =>
          NonEmptyHoles.of(holes) match
            case Some(present) =>
              specializer.thunk(code, present, fillings.map(instructionOf))
            case None => specializer.instance(code, fillings.map(instructionOf))
      HigherOrderMatching
        .unseenInstances(graph, thunk, thunk, Set.empty)
        .collect {
          case (key, _) if graph.root(key.root) == graph.root(node) =>
            key.bindings
        }
        .map(bindings =>
          names
            .map(name =>
              name -> instructionOf(
                bindings.getOrElse(
                  indices(name),
                  throw IllegalStateException(
                    s"a match of $pattern binds no $name"
                  )
                )
              )
            )
            .toMap
        )
    val solutions = solutionsOn(replaced).filter(bound =>
      spelledAlike(normalForm(pattern, bound, higherOrderVariables), replaced)
    )
    // Distinct by the bindings' terms, compared as terms of the configuration.
    solutions.foldLeft(Vector.empty[Map[String, Configured[C]]])(
      (kept, bound) =>
        if kept.exists(earlier =>
            earlier.keySet == bound.keySet && earlier.forall((name, term) =>
              Configured.same(term, bound(name))
            )
          )
        then kept
        else kept :+ bound
    )

  /** The side as a pattern of the IR, each variable the metavariable of its
    * index.
    */
  private def patternOf[C <: NativeSpecializer & Singleton](
      term: StatementTerm[Configured[C]],
      indices: Map[String, Int]
  ): Pattern[C] =
    term match
      case StatementTerm.Variable(name) => Pattern.Metavariable(indices(name))
      case StatementTerm.Stored(stored) => Pattern.InstructionReference(stored)
      case StatementTerm.Layered(layer) =>
        layer match
          case Apply(function, argument) =>
            Pattern.Apply(
              patternOf(function, indices),
              patternOf(argument, indices)
            )
          case Parallel(left, right) =>
            Pattern.Parallel(
              patternOf(left, indices),
              patternOf(right, indices)
            )
          case Choice(left, right) =>
            Pattern.Choice(patternOf(left, indices), patternOf(right, indices))
          case Thunk(code, holes, fillings) =>
            Pattern.Thunk(code, holes, fillings.map(patternOf(_, indices)))
          case other =>
            throw IllegalStateException(
              s"a statement's layer is never a leaf or a storage's view: $other"
            )

  /** The names a lemma's left side applies its metavariable to, when the side
    * is a metavariable applied to closed terms, `m G1 … Gn`.
    */
  def names[Term](statement: Statement[Term]): Option[Vector[Term]] =
    def spine(
        term: StatementTerm[Term],
        arguments: List[Term]
    ): Option[Vector[Term]] = term match
      case StatementTerm.Layered(Apply(function, StatementTerm.Stored(name))) =>
        spine(function, name :: arguments)
      case StatementTerm.Variable(_) if arguments.nonEmpty =>
        Some(arguments.toVector)
      case _ => None
    spine(statement.left, Nil)

  /** The redex `(λx1 … xn. T[G1 := x1, …]) G1 … Gn` of a term T over the names,
    * its abstraction spelled as the front end spells the lambda.
    */
  def redex[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      names: Vector[Configured[C]]
  )(using specializer: C, access: StorageAccess): Configured[C] =
    names.foldLeft(abstraction(term, names))((function, argument) =>
      (specializer: C).application(function, argument)
    )

  /** Whether the term is an application to the names, in order, as every redex
    * over them is (`redex`): a check of the names alone, which a term that is
    * no redex fails before its abstraction is computed.
    */
  def appliedToNames[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      names: Vector[Configured[C]]
  )(using C): Boolean =
    @scala.annotation.tailrec
    def matched(at: Configured[C], rest: List[Configured[C]]): Boolean =
      rest match
        case Nil             => true
        case name :: earlier =>
          at.layer match
            case Apply(function, argument) =>
              Configured.same(argument, name) && matched(function, earlier)
            case _ => false
    matched(term, names.reverse.toList)

  /** The thunk `λx1 … xn. T[G1 := x1, …]` of a term T over the leaves G1 to Gn,
    * spelled as the front end spells the lambda: the abstraction of a root
    * reverse β, and the write-back of a body opened at eigenvariables (the
    * abstraction rule ξ).
    */
  def abstraction[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      leaves: Vector[Configured[C]]
  )(using C, StorageAccess): Configured[C] =
    def abstracted(
        bound: Map[Configured[C], com.yang_bo.gezi.frontend.Term],
        rest: Vector[Configured[C]]
    ): TermOf[Configured[C]] = rest match
      case leaf +: others =>
        Term.λ(variable => abstracted(bound.updated(leaf, variable), others))
      case _ => readBack(term, bound)
    Defunctionalization.thunkInstruction[C](
      abstracted(Map.empty, leaves).deBruijnTerm(Map.empty)
    )

  /** The eigenvariables a replay opens a thunk of `count` holes at, under
    * `depth` enclosing openings: opaque leaves no program holds, named by their
    * place, so that a writer and a replay agree on them.
    */
  def eigenvariables[C <: NativeSpecializer & Singleton](
      depth: Int,
      count: Int
  )(using specializer: C): Vector[Configured[C]] =
    Vector.tabulate(count)(position =>
      specializer.opaque(s"trace eigenvariable $depth $position")
    )

  /** The body of a thunk opened at the leaves, one for each of its first holes
    * in lambda order, as the defunctionalized β rule fills them: a bound hole's
    * leaf put among the fillings at its slot's place, an ignored hole's
    * dropped; with holes left, the thunk of those holes (the front end folds a
    * chain whose body is a thunk with holes into one thunk, so `λz. λx. x`
    * written back is one thunk of two holes), else its code read at the
    * fillings, built through the configuration (`NativeSpecializer.instance`).
    * Throws `IllegalArgumentException` for a term that is no thunk of at least
    * as many holes as leaves.
    */
  def opened[C <: NativeSpecializer & Singleton](
      thunk: Configured[C],
      leaves: Vector[Configured[C]]
  )(using specializer: C): Configured[C] =
    thunk.layer match
      case Thunk(code, holes, fillings)
          if holes.size >= leaves.size && leaves.nonEmpty =>
        val (rest, filled) = leaves.foldLeft((holes, fillings)) {
          case ((remaining, current), leaf) =>
            remaining match
              case Hole.Bound(slot) +: others =>
                (
                  others,
                  current.patch(
                    Defunctionalization.fillingPosition(others, slot),
                    Vector(leaf),
                    0
                  )
                )
              case Hole.Ignored +: others => (others, current)
              case _                      =>
                throw IllegalStateException(s"no hole is left for $leaf")
        }
        NonEmptyHoles.of(rest) match
          case Some(present) => specializer.thunk(code, present, filled)
          case None          => specializer.instance(code, filled)
      case other =>
        throw IllegalArgumentException(
          s"$other is no thunk of at least ${leaves.size} holes"
        )

  /** The term with each leaf of the map replaced, a subterm that holds none
    * kept as it is, each layer rebuilt through the configuration
    * (`Positions.built`). A leaf sits only where a term sits, never in a code.
    */
  def leavesReplaced[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      replaced: Map[Configured[C], Configured[C]]
  )(using
      C,
      StorageAccess
  ): Configured[C] =
    if replaced.isEmpty || !holds(term, replaced.keySet) then term
    else
      replaced.get(term) match
        case Some(leaf) => leaf
        case None       =>
          val layer = Positions.layerOf(term)
          Positions.built(
            layer,
            layer.children.map(leavesReplaced(_, replaced))
          )

  /** The term a redex of `redex` contracts to, its n applications of the
    * abstraction reduced, spelled as the front end spells it. Throws
    * `IllegalArgumentException` for a term that is not the abstraction applied
    * to n arguments.
    */
  def contracted[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      count: Int
  )(using C): Configured[C] =
    def spine(
        current: Configured[C],
        arguments: List[Configured[C]]
    ): (Configured[C], Vector[Configured[C]]) =
      if arguments.size == count then (current, arguments.toVector)
      else
        current.layer match
          case Apply(function, argument) =>
            spine(function, argument :: arguments)
          case _ =>
            throw IllegalArgumentException(
              s"$term is no abstraction applied to $count arguments"
            )
    val (abstraction, arguments) = spine(term, Nil)
    spelled(
      arguments.foldLeft(instructionValue(abstraction, inlined = true))(
        (function, argument) =>
          applied(function, Value.Syntax(Term.closed(argument)))
      )
    )

  /** The provenance of a root reverse β, from the term to its redex: each
    * filling of the redex's abstraction (a maximal subterm of the term that
    * holds no name, `filling i`) and each name (`name i`, from 0) where they
    * occur in the term and in the redex.
    */
  def redexProvenance[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      redex: Configured[C],
      count: Int
  )(using C, StorageAccess): Vector[Provenance] =
    val abstractionPosition = Vector.fill(count)(PositionSegment.Function)
    val abstraction = Positions.subterm(redex, abstractionPosition)
    val fillings = abstraction.layer match
      case Thunk(_, _, fillings) => fillings
      case other                 =>
        throw IllegalArgumentException(
          s"the redex's abstraction is no thunk: $other"
        )
    val fillingProvenance = fillings.zipWithIndex.map((filling, place) =>
      Provenance(
        s"filling$place",
        Positions.occurrences(term, filling),
        Vector(abstractionPosition :+ PositionSegment.Filling(place))
      )
    )
    val nameProvenance = (0 until count).toVector.map(place =>
      val position = Vector.fill(count - 1 - place)(
        PositionSegment.Function
      ) :+ PositionSegment.Argument
      Provenance(
        s"name$place",
        Positions.occurrences(term, Positions.subterm(redex, position)),
        Vector(position)
      )
    )
    fillingProvenance ++ nameProvenance

  /** The term of the instruction with each of the bound terms read as its HOAS
    * variable, a subterm that holds none of them a closed constant, a storage
    * that holds one read through its view.
    */
  private def readBack[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      bound: Map[Configured[C], com.yang_bo.gezi.frontend.Term]
  )(using
      C,
      StorageAccess
  ): TermOf[Configured[C]] =
    bound.get(term) match
      case Some(variable)                     => variable
      case None if !holds(term, bound.keySet) => Term.closed(term)
      case None                               =>
        Positions.layerOf(term) match
          case Apply(function, argument) =>
            readBack(function, bound)(readBack(argument, bound))
          case Choice(left, right) =>
            TermOf.Choice(readBack(left, bound), readBack(right, bound))
          case Parallel(left, right) =>
            TermOf.Parallel(readBack(left, bound), readBack(right, bound))
          case StorageView(value, criterion) =>
            TermOf.Parallel(readBack(value, bound), readBack(criterion, bound))
          case Thunk(code, holes, fillings) =>
            reified(
              lambda(
                code,
                holes,
                fillings.map(filling => Value.Syntax(readBack(filling, bound))),
                inlined = false
              )
            )

  /** Whether the term holds one of the leaves, not under an opaque term, a
    * storage read through its view.
    */
  def holds[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      names: Set[Configured[C]]
  )(using C, StorageAccess): Boolean =
    names.contains(term) || (!term.opaque && Positions
      .layerOf(term)
      .children
      .exists(holds(_, names)))

  /** A value of the reading: a lambda, which an application contracts when it
    * is inlined, or a term.
    */
  private enum Value[C <: NativeSpecializer & Singleton]:
    case Function(inlined: Boolean, body: Value[C] => Value[C])
    case Syntax(term: TermOf[Configured[C]])

  private def instructionValue[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      inlined: Boolean
  )(using C): Value[C] =
    if term.opaque then Value.Syntax(Term.closed(term))
    else
      term.layer match
        case Thunk(code, holes, fillings) =>
          lambda(
            code,
            holes,
            fillings.map(filling => Value.Syntax(Term.closed(filling))),
            inlined
          )
        case _ => Value.Syntax(Term.closed(term))

  /** The lambda of a thunk's code over its fillings' values, one function per
    * hole, the code read when the last hole is entered.
    */
  private def lambda[C <: NativeSpecializer & Singleton](
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[Value[C]],
      inlined: Boolean
  ): Value[C] =
    def entered(rest: Vector[Hole], slots: Vector[Option[Value[C]]]): Value[C] =
      rest match
        case hole +: others =>
          Value.Function(
            inlined,
            argument =>
              entered(
                others,
                hole match
                  case Hole.Bound(slot) => slots.updated(slot, Some(argument))
                  case Hole.Ignored     => slots
              )
          )
        case _ => read(code, slots)
    entered(
      holes,
      Defunctionalization.slotValues(
        holes,
        holes.map(_ => None),
        fillings.map(Some(_))
      )
    )

  private def read[C <: NativeSpecializer & Singleton](
      code: Code,
      slots: Vector[Option[Value[C]]]
  ): Value[C] = code.layer match
    case Slot(slot) =>
      slots
        .lift(slot)
        .flatten
        .getOrElse(
          throw IllegalArgumentException(s"the code reads the empty slot $slot")
        )
    case Apply(function, argument) =>
      applied(read(function, slots), read(argument, slots))
    case Choice(left, right) =>
      Value.Syntax(
        TermOf.Choice(reified(read(left, slots)), reified(read(right, slots)))
      )
    case Parallel(left, right) =>
      Value.Syntax(
        TermOf.Parallel(reified(read(left, slots)), reified(read(right, slots)))
      )
    case Thunk(inner, holes, fillings) =>
      lambda(inner, holes, fillings.map(read(_, slots)), inlined = false)

  /** The application: contracted when the function is an inlined lambda, a
    * lambda argument then inlined in turn; a term otherwise.
    */
  private def applied[C <: NativeSpecializer & Singleton](
      function: Value[C],
      argument: Value[C]
  ): Value[C] = function match
    case Value.Function(true, body) =>
      body(argument match
        case Value.Function(_, argumentBody) =>
          Value.Function(true, argumentBody)
        case syntax => syntax)
    case _ => Value.Syntax(reified(function)(reified(argument)))

  private def reified[C <: NativeSpecializer & Singleton](
      value: Value[C]
  ): TermOf[Configured[C]] = value match
    case Value.Function(_, body) =>
      Term.λ(variable => reified(body(Value.Syntax(variable))))
    case Value.Syntax(term) => term

  /** The value's term as the front end spells it, built through the
    * configuration.
    */
  private def spelled[C <: NativeSpecializer & Singleton](
      value: Value[C]
  )(using C): Configured[C] =
    Defunctionalization.thunkInstruction[C](
      reified(value).deBruijnTerm(Map.empty)
    )
