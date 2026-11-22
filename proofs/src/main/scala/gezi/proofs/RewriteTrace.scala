package gezi.proofs

import gezi.ir.Code
import gezi.ir.CodeLayer
import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.rewritetrace.Conversion
import gezi.rewritetrace.Conversions
import gezi.rewritetrace.Given
import gezi.rewritetrace.ThunkShape
import gezi.rewritetrace.ReplaySpelling
import gezi.rewritetrace.Spellings
import gezi.rewritetrace.Spine
import gezi.rewritetrace.LemmaSide
import gezi.rewritetrace.Positions
import gezi.rewritetrace.PositionSegment
import gezi.rewritetrace.Provenance
import gezi.rewritetrace.ProvedReason
import gezi.rewritetrace.RewriteDirection
import gezi.rewritetrace.Statement
import gezi.rewritetrace.StatementTerm
import gezi.rewritetrace.Statements
import gezi.rewritetrace.Trace
import gezi.rewritetrace.TraceCommand
import gezi.rewritetrace.TraceLemma
import gezi.rewritetrace.TraceValue
import gezi.rewritetrace.ValueSource
import gezi.rewritetrace.UnprovedKind
import scala.annotation.tailrec
import scala.collection.immutable.TreeMap
import gezi.ir.TailRecFolds
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Apply, Choice, Parallel, Slot, Thunk}

/** The proof of a round's equation `left = right` as the article writer
  * builds it, before it is written (`OpentheoryArticle.derivation`): its
  * tree, the expansion of its edges and paths, the store the article states
  * its axioms from, and the forest of the search's terms and unions it is
  * built from.
  */
final class ArticleDerivation private[proofs] (
    val left: Instruction,
    val right: Instruction,
    val proof: ArticleProof,
    expansion: ArticleProof => Option[ArticleProof],
    val store: ArticleStore,
    val forest: ProofForest
):

  /** The proof an edge or a path expands to, the one the article writes in
    * its place; none for any other proof.
    */
  def expanded(proof: ArticleProof): Option[ArticleProof] = expansion(proof)

/** Why a step holds: an instance of a lemma, by its identifier, one for
  * each direction and pair of sides (`gezi.standardlibrary.LemmaNamed`);
  * of a numbered equation; the defunctionalized β rule of a thunk, the
  * thunk of the redex and its argument; the equation of a thunk with no
  * hole and its code's body, the thunk; the defunctionalized η rule of an
  * eta-shaped thunk, the thunk; or the equation of a thunk with holes and
  * its spelling by the front end (`Statements.respell`), the thunk. A lemma
  * and an equation bind the variables of their statements by name in
  * `substitution`; the β, body, η and respelling equations bind theirs
  * through the thunk's fillings (`filling0`, `filling1`, and so
  * on) and the argument (`argument`). A step of a union with no proof
  * (`ArticleProof.Conversion`) instantiates no equation and binds nothing.
  * A step of the abstraction rule replaces a closure by the thunk its body
  * is written back to: the eigenvariables it opened the closure at, the
  * body it opened to, and the body's own steps, from the body to the
  * spelling written back (turned with the step).
  */
enum RewriteReason:
  case Lemma(lemma: LemmaIdentifier, substitution: Vector[(String, Instruction)])
  case Equation(number: Int, substitution: Vector[(String, Instruction)])
  case Fill(thunk: Instruction, argument: Instruction)
  case Body(thunk: Instruction)
  case Eta(thunk: Instruction)
  case Respell(thunk: Instruction)
  case Unproved(kind: UnprovedKind)
  case Abstraction(eigenvariables: Vector[Instruction], body: Instruction, steps: Vector[RewriteStep])

/** A rewrite of the whole term: the subterm at `position`, from the root,
  * replaced by `replacement`, by the equation of `reason` in `direction`,
  * with the provenance of the equation's variables.
  */
final case class RewriteStep(
    reason: RewriteReason,
    position: Vector[PositionSegment],
    direction: RewriteDirection,
    replacement: Instruction,
    provenance: Vector[Provenance]
)

/** A round: its input, its steps in order, and its output, which the steps
  * make of the input.
  */
final case class RewriteRound(input: Instruction, steps: Vector[RewriteStep], output: Instruction)

/** A step with the subterm it replaces, which turning the step needs. */
private final case class OrientedStep(step: RewriteStep, replaced: Instruction):

  def turned: OrientedStep =
    OrientedStep(
      step.copy(
        reason = OrientedStep.reasonTurned(step.reason),
        direction = step.direction.reversed,
        replacement = replaced,
        provenance = step.provenance.map(_.turned)
      ),
      step.replacement
    )

  def under(segment: PositionSegment): OrientedStep = copy(step = step.copy(position = segment +: step.position))

private object OrientedStep:

  /** The reason of a step turned: an abstraction's body steps turned and in
    * reverse order, from the body they made back to the body; any other as
    * it is.
    */
  def reasonTurned(reason: RewriteReason): RewriteReason = reason match
    case RewriteReason.Abstraction(eigenvariables, body, steps) =>
      val befores = steps.scanLeft(body)(RewriteTrace.applied)
      val oriented = steps.zip(befores).map((step, before) => OrientedStep(step, Positions.subterm(before, step.position)))
      RewriteReason.Abstraction(eigenvariables, befores.last, oriented.reverse.map(_.turned.step))
    case other => other

/** The proof of a round flattened into rewrites of the whole term: the tree
  * the article writer builds (`OpentheoryArticle.derivation`), its edges and
  * paths expanded as the writer expands them, read without matching again.
  *
  * {{{
  * Instance(a, σ)           one step: σ(left of a) replaced by σ(right of a), forward
  * Symmetry(p)              the steps of p in reverse order, each turned
  * Transitivity(p, q)       the steps of p, then those of q
  * Congruence(s, [p1 … pn]) the steps of each pi in turn, under the role of the i-th subterm
  * Reflexivity(t)           no step
  * Edge, Connection         the steps of the proof the writer expands it to
  * Unproved(k, a, b)        one step: a replaced by b, of no equation
  * Abstraction(a, b, e, m, p) one step: a replaced by b, carrying the steps of p from m
  * }}}
  *
  * From the round's input, the steps in order give its output (`applied`),
  * the law the tests check. `trace` keeps of each step what a replay cannot
  * compute (`gezi.rewritetrace.TraceCommand`). It names no lemma and no
  * combinator and holds no type: a step's reason is the equation the proof
  * instantiates, read from the proof.
  */
object RewriteTrace:

  /** The steps of the derivation's proof, from its left term to its right
    * term. Throws `OpentheoryArticleError` as the writer does on an edge it
    * cannot prove.
    */
  def of(derivation: ArticleDerivation): Vector[RewriteStep] =
    flattened(derivation, derivation.proof, Map.empty).result._1.map(_.step)

  /** The round of the derivation: its left term, its steps, its right term. */
  def round(derivation: ArticleDerivation): RewriteRound =
    RewriteRound(derivation.left, of(derivation), derivation.right)

  /** The lemmas the derivation's steps name, in the order they first name
    * them, by their identifiers: the lemmas its article imports. Its trace
    * (`trace`) names these and may name more, the lemmas of the unions its
    * values are made by, and keeps them by their sides.
    */
  def lemmas(derivation: ArticleDerivation): Vector[LemmaIdentifier] =
    plan(derivation, derivation.left, of(derivation)).flatMap(lemmasOf).distinct

  /** The trace of the derivation, one round from its left term, which a
    * replay is given (the trace holds no start): each step's command, the replacement, the provenance and the bindings of the
    * replaced side's variables left to the replay; the values the commands
    * name (`gezi.rewritetrace.TraceValue`); and the lemmas the commands
    * name, in the order they first name them, by their sides. Throws
    * `IllegalStateException` when a lemma's statement from its sides
    * (`Statements.lemma`) is not the strategy's encoding of it, which the
    * article states: a replay would then rewrite otherwise than the proof.
    */
  def trace(derivation: ArticleDerivation): Trace =
    val (commands, building) = built(derivation)
    val traced = building.lemmas.map(lemma =>
      val (left, right) = derivation.store.lemmaSides(lemma)
      val traceLemma = TraceLemma(left, right)
      if ArticleStore.sides(traceLemma.statement) != derivation.store.axiomStatement(Axiom.Lemma(lemma)) then
        throw IllegalStateException(s"the sides of $lemma state it otherwise than the strategy's encoding")
      traceLemma
    )
    Trace(traced, building.values, Vector(commands))

  /** The commands of the derivation's round and what they name. */
  private def built(derivation: ArticleDerivation): (Vector[TraceCommand], TraceBuilding) =
    val origins = ValueOrigins.of(derivation)
    plan(derivation, derivation.left, of(derivation)).foldLeft((Vector.empty[TraceCommand], TraceBuilding.empty)) {
      case ((made, building), planned) =>
        val (command, after) = commandOf(derivation, origins, building, planned, 0, Map.empty)
        (made :+ command, after)
    }

  /** A trace as it is written: the lemmas its commands name so far, each at
    * its place, in the order they are first named; its values made so far,
    * each node's term at its value's place (`valuePlaces`); the edges and
    * paths flattened so far; and the terms whose values are being made, to
    * refuse one made from itself.
    */
  private final case class TraceBuilding(
      lemmas: Vector[LemmaIdentifier],
      values: Vector[TraceValue],
      valuePlaces: Map[Instruction, Int],
      expansions: Expansions,
      making: Set[Instruction]
  ):

    /** The lemma's place, the lemma placed after the others if it has none. */
    def lemmaPlaced(lemma: LemmaIdentifier): (Int, TraceBuilding) =
      lemmas.indexOf(lemma) match
        case -1    => (lemmas.size, copy(lemmas = lemmas :+ lemma))
        case place => (place, this)

    /** The value's place, the value of the term placed after the others. */
    def valuePlaced(term: Instruction, value: TraceValue): (Int, TraceBuilding) =
      (values.size, copy(values = values :+ value, valuePlaces = valuePlaces.updated(term, values.size)))

  private object TraceBuilding:
    val empty: TraceBuilding = TraceBuilding(Vector.empty, Vector.empty, Map.empty, Map.empty, Set.empty)

  /** Where the terms of a derivation's proof come from: the position in the
    * round's start of each of its subterms, the first in preorder; the
    * unions that made a node, by that node's index in the forest
    * (`ProofUnion.built`); and the eigenvariables the proof's abstractions
    * open bodies at.
    */
  private final case class ValueOrigins(
      derivation: ArticleDerivation,
      startPaths: Map[Instruction, Vector[PositionSegment]],
      builtUnions: TreeMap[Int, ProofUnion],
      eigenvariables: Set[Instruction],
      madeParents: Map[Int, Vector[(Int, PositionSegment)]],
      startByTree: Map[Int, Instruction]
  ):

    /** The root of the node's tree in the proof's forest: two nodes are in
      * one tree when the unions make them equal.
      */
    def treeRoot(node: Int): Int =
      @tailrec
      def climbed(at: Int): Int = derivation.forest.parents.get(at) match
        case Some((parent, _)) => climbed(parent)
        case None              => at
      climbed(node)

    /** The union that made the node of the term, the term it built, the
      * union's other term, and the position of the term in the one built:
      * the union whose made nodes (`ProofUnion.made`) hold the node, found
      * by walking the built term through the nodes the union made. None for
      * a term of no node and for a node no union records making (an input,
      * a node a β conversion made).
      */
    def maker(term: Instruction): Option[(ProofUnion, Instruction, Instruction, Vector[PositionSegment])] =
      val forest = derivation.forest
      forest.indexes.get(term).flatMap(node =>
        builtUnions.minAfter(node).flatMap((_, union) =>
          union.made.filter(made => forest.index(made.first) <= node).flatMap(made =>
            val other = if made.last == union.second then union.first else union.second
            ValueOrigins.madePath(made.last, term, forest.index(made.first), forest).map(at => (union, made.last, other, at))
          )
        )
      )

  private object ValueOrigins:

    def of(derivation: ArticleDerivation): ValueOrigins =
      val forest = derivation.forest
      val builtUnions = forest.unions.foldLeft(TreeMap.empty[Int, ProofUnion])((found, union) =>
        union.built.fold(found)(built =>
          val node = forest.index(built)
          if found.contains(node) then found else found.updated(node, union)
        )
      )
      val eigenvariables = forest.unions.flatMap(_.justification match
        case Justification.Abstraction(opened, _, _) => opened
        case _                                       => Vector.empty
      ).toSet
      val startPaths = subtermPaths(derivation.left)
      // Each node's made layer is over the nodes of its children's terms: the parents of a node are the nodes whose
      // made layer holds it, with the role it has there.
      val madeParents = forest.nodes.zipWithIndex.foldLeft(Map.empty[Int, Vector[(Int, PositionSegment)]]) {
        case (found, (term, parent)) =>
          if term.opaque then found
          else
            val layer = term.layered
            layer.children.zip(Positions.roles(layer)).foldLeft(found) { case (current, (child, role)) =>
              forest.indexes.get(child).fold(current)(node => current.updated(node, current.getOrElse(node, Vector.empty) :+ (parent, role)))
            }
      }
      val origins = ValueOrigins(derivation, startPaths, builtUnions, eigenvariables, madeParents, Map.empty)
      // A subterm of the start in each tree of the forest, the first in preorder.
      val startByTree = startPaths.toVector.sortBy(_._2.size).foldLeft(Map.empty[Int, Instruction]) { case (found, (term, _)) =>
        forest.indexes.get(term).fold(found)(node =>
          val root = origins.treeRoot(node)
          if found.contains(root) then found else found.updated(root, term)
        )
      }
      origins.copy(startByTree = startByTree)

    /** The position of each subterm of the term, the first in preorder. A
      * loop over the positions pending: a term is as deep as a program.
      */
    private def subtermPaths(term: Instruction): Map[Instruction, Vector[PositionSegment]] =
      @tailrec
      def walked(
          pending: List[(Instruction, Vector[PositionSegment])],
          found: Map[Instruction, Vector[PositionSegment]]
      ): Map[Instruction, Vector[PositionSegment]] =
        pending match
          case Nil => found
          case (at, path) :: rest =>
            if found.contains(at) then walked(rest, found)
            else if at.opaque then walked(rest, found.updated(at, path))
            else
              val layer = at.layered
              val below = layer.children.zip(Positions.roles(layer)).map((child, role) => (child, path :+ role)).toList
              walked(below ++ rest, found.updated(at, path))
      walked(List((term, Vector.empty)), Map.empty)

    /** The position of the term in the term built, walking only the nodes
      * the step made, from the first of them on: a node older than the first
      * is one the step was given. A loop over the positions pending.
      */
    def madePath(built: Instruction, term: Instruction, first: Int, forest: ProofForest): Option[Vector[PositionSegment]] =
      @tailrec
      def walked(pending: List[(Instruction, Vector[PositionSegment])]): Option[Vector[PositionSegment]] =
        pending match
          case Nil => None
          case (at, path) :: rest =>
            if at == term then Some(path)
            else if at.opaque || forest.indexes.get(at).forall(_ < first) then walked(rest)
            else
              val layer = at.layered
              walked(layer.children.zip(Positions.roles(layer)).map((child, role) => (child, path :+ role)).toList ++ rest)
      walked(List((built, Vector.empty)))

  /** The value of the term, at its place among the building's values, made
    * if it is not yet, from the first origin that gives one: the term's
    * position in the round's start; the union that made its node
    * (`fromMaker`); a node whose made layer holds it (`fromParent`); a subterm
    * of the start the proof makes equal to it (`fromClassmate`). None for a
    * term that holds an eigenvariable, which no round's start holds, for one
    * no origin gives, and for one whose value would be made from itself.
    */
  private def valueOf(
      derivation: ArticleDerivation,
      origins: ValueOrigins,
      building: TraceBuilding,
      term: Instruction
  ): Option[(Int, TraceBuilding)] =
    building.valuePlaces.get(term) match
      case Some(place) => Some((place, building))
      case None if building.making.contains(term) || Conversions.holds(term, origins.eigenvariables) => None
      case None =>
        origins.startPaths.get(term) match
          case Some(path) =>
            ReplaySpelling.positions(derivation.left, path) match
              case Vector(spelledPath) =>
                Some(building.valuePlaced(term, TraceValue(ValueSource.RoundStart(0), Vector.empty, spelledPath)))
              case _ => None
          case None =>
            fromMaker(derivation, origins, building, term)
              .orElse(fromRedex(derivation, origins, building, term))
              .orElse(fromParent(derivation, origins, building, term))
              .orElse(fromClassmate(derivation, origins, building, term))

  /** The value of the term made from the union that made its node
    * (`ValueOrigins.maker`): the commands of the union replayed from its
    * other term, whose value is made first, and the term's position in the
    * term the union built.
    */
  private def fromMaker(
      derivation: ArticleDerivation,
      origins: ValueOrigins,
      building: TraceBuilding,
      term: Instruction
  ): Option[(Int, TraceBuilding)] =
    origins.maker(term).flatMap((union, built, other, at) =>
      valueOf(derivation, origins, building.copy(making = building.making + term), other).flatMap((source, afterSource) =>
        ReplaySpelling.positions(built, at) match
          case Vector(spelledAt) =>
            val edge = ArticleProof.Edge(union.index)
            val oriented = if built == union.second then edge else ArticleProof.Symmetry(edge)
            val (steps, expansions) = flattened(derivation, oriented, afterSource.expansions).result
            val (commands, afterCommands) = plan(derivation, other, steps.map(_.step))
              .foldLeft((Vector.empty[TraceCommand], afterSource.copy(expansions = expansions))) {
                case ((made, current), planned) =>
                  val (command, after) = commandOf(derivation, origins, current, planned, 0, Map.empty)
                  (made :+ command, after)
              }
            Some(
              afterCommands
                .copy(making = afterCommands.making - term)
                .valuePlaced(term, TraceValue(ValueSource.Value(source), commands, spelledAt))
            )
          // The replay's spelling drops or copies the term (`ReplaySpelling.positions`).
          case _ => None
      )
    )

  /** The value of the term as the redex of a root reverse β of a subterm of
    * the start the proof makes equal to it, over the names a lemma's left
    * side applies a metavariable to (`Conversions.redex`): the conversion
    * from that subterm, as the strategy that added the redex as an input made
    * it (`gezi.strategies.HigherOrderSaturator`'s root case). Its
    * abstraction is no term the start holds, and the path of unions between
    * the two crosses the β rule backward, which needs that abstraction.
    */
  private def fromRedex(
      derivation: ArticleDerivation,
      origins: ValueOrigins,
      building: TraceBuilding,
      term: Instruction
  ): Option[(Int, TraceBuilding)] =
    derivation.forest.indexes.get(term).flatMap(node => origins.startByTree.get(origins.treeRoot(node))).filterNot(_ == term).flatMap(
      classmate =>
        val spelledTerm = ReplaySpelling.term(term)
        val spelledClassmate = ReplaySpelling.term(classmate)
        derivation.store.encodedLemmas
          .find(lemma =>
            val (left, right) = derivation.store.lemmaSides(lemma)
            Conversions.names(TraceLemma(left, right).statement).exists(names =>
              Conversions.appliedToNames(spelledTerm, names) && (Conversions.redex(spelledClassmate, names) eq spelledTerm)
            )
          )
          .flatMap(lemma =>
            valueOf(derivation, origins, building.copy(making = building.making + term), classmate).map((source, afterSource) =>
              val converted = Converted(lemma, Conversion.RootReverseBeta(_), Vector.empty, RewriteDirection.Forward, Vector.empty)
              val (command, afterCommand) = commandOf(derivation, origins, afterSource, Planned.Converted(converted), 0, Map.empty)
              afterCommand
                .copy(making = afterCommand.making - term)
                .valuePlaced(term, TraceValue(ValueSource.Value(source), Vector(command), Vector.empty))
            )
          )
    )

  /** The value of the term from a node whose made layer holds it, whose value
    * is made first, and the term's position in that node's term: a node no
    * union records making, made with a larger term that has a value (a
    * reverse β redex a strategy adds as an input, say).
    */
  private def fromParent(
      derivation: ArticleDerivation,
      origins: ValueOrigins,
      building: TraceBuilding,
      term: Instruction
  ): Option[(Int, TraceBuilding)] =
    @tailrec
    def first(parents: List[(Int, PositionSegment)]): Option[(Int, TraceBuilding)] = parents match
      case Nil => None
      case (parent, role) :: rest =>
        val parentTerm = derivation.forest.nodes(parent)
        val made =
          valueOf(derivation, origins, building.copy(making = building.making + term), parentTerm).flatMap((place, after) =>
            ReplaySpelling.positions(parentTerm, Vector(role)) match
              case Vector(spelled) =>
                Some(after.copy(making = after.making - term).valuePlaced(term, TraceValue(ValueSource.Value(place), Vector.empty, spelled)))
              case _ => None
          )
        made match
          case Some(_) => made
          case None    => first(rest)
    derivation.forest.indexes.get(term).fold(None)(node => first(origins.madeParents.getOrElse(node, Vector.empty).toList))

  /** The value of the term from a subterm of the start the proof makes equal
    * to it: the steps of the path between them in the forest
    * (`ArticleProof.Connection`) replayed from the start's subterm. A term a
    * round adds as an input, which no union made and no larger term holds.
    */
  private def fromClassmate(
      derivation: ArticleDerivation,
      origins: ValueOrigins,
      building: TraceBuilding,
      term: Instruction
  ): Option[(Int, TraceBuilding)] =
    derivation.forest.indexes.get(term).flatMap(node => origins.startByTree.get(origins.treeRoot(node))).filterNot(_ == term).flatMap(
      classmate =>
        valueOf(derivation, origins, building.copy(making = building.making + term), classmate).map((source, afterSource) =>
          val (steps, expansions) = flattened(derivation, ArticleProof.Connection(classmate, term), afterSource.expansions).result
          val (commands, afterCommands) = plan(derivation, classmate, steps.map(_.step))
            .foldLeft((Vector.empty[TraceCommand], afterSource.copy(expansions = expansions))) { case ((made, current), planned) =>
              val (command, after) = commandOf(derivation, origins, current, planned, 0, Map.empty)
              (made :+ command, after)
            }
          afterCommands
            .copy(making = afterCommands.making - term)
            .valuePlaced(term, TraceValue(ValueSource.Value(source), commands, Vector.empty))
        )
    )

  /** A step as the trace will keep it, before the lemmas have their places:
    * a proved step; a β conversion with no proof, as the conversion of a
    * lemma it instantiates; or the abstraction rule, as the steps of the body
    * it opened.
    */
  private enum Planned:
    case Proved(step: RewriteStep)
    case Converted(found: RewriteTrace.Converted)
    case Abstracted(position: Vector[PositionSegment], eigenvariables: Vector[Instruction], steps: Vector[Planned])

  /** The plan of the steps from the term, in the replay's spelling
    * (`ReplaySpelling`), the spelling the replay works in: a step whose
    * replaced subterm and replacement have one spelling, a respelling
    * (`Axiom.Respell`) above all, has no command, since the replay holds its
    * two sides as one term; every other step keeps its reason, its position
    * translated into the spelled term (`ReplaySpelling.positions`), and the β
    * rule's step of a thunk's last hole is joined to the body step beside it
    * (`betaJoined`). Two steps side by side that are an identity together in
    * that spelling have no command either (`detoursDropped`). Throws
    * `IllegalStateException` when no conversion computes a β conversion's
    * step, when a step's subterm is at other than one position of the
    * spelled term, and when the replay of an abstraction would open or write
    * back another term than the proof's (the body the closure opens to is
    * not the body's spelling the steps start from, or the body they make
    * written back is not the thunk): the trace would replay otherwise than
    * the proof.
    */
  private def plan(derivation: ArticleDerivation, start: Instruction, steps: Vector[RewriteStep]): Vector[Planned] =
    val joined = betaJoined(steps)
    // The term before each step is kept as a spine (`Spine`): a step rebuilds only the path to its position and
    // interns only the subterm it reads. A step costs the depth of
    // its position (`subterm`, `replaced`, `spelledPositions`: one child taken and one `Vector.updated` per segment; a
    // node turns from settled to rebuilt once, `Layer.map` over its children), plus the size of the subterm it replaces
    // and of its replacement not yet spelled (`materialized` interns the rebuilt nodes in that subterm only; the
    // spellings, `Spellings`, keep each term's spelling), plus the size of the code of each kind of thunk the
    // flattening meets for the first time. A layer the step only passes through is not hashed.
    val (spelled, _, _) = joined.foldLeft((Vector.empty[SpelledStep], Spine.Settled(start): Spine, Spellings.empty)) {
      case ((found, before, known), step) =>
        val replaced = Spine.materialized(Spine.subterm(before, step.position))
        // The replay works in the replay's spelling (`ReplaySpelling`): a step that is an identity there (a
        // respelling) has no command, and every other step's position is the position of its subterm in that
        // spelling of the term.
        val (spelledReplaced, afterReplaced) = known.term(replaced)
        val (spelledReplacement, afterReplacement) = afterReplaced.term(step.replacement)
        val (kept, knownAfter) =
          if spelledReplaced == spelledReplacement then (None, afterReplacement)
          else
            val (positions, knownAfter) = Spine.spelledPositions(before, step.position, afterReplacement)
            val position = positions match
              case Vector(only) => only
              case _ =>
                throw IllegalStateException(
                  s"the subterm at ${step.position} is at ${positions.size} positions of the term's replay spelling"
                )
            (Some(SpelledStep(step.copy(position = position), replaced, spelledReplaced, spelledReplacement)), knownAfter)
        (found ++ kept, Spine.replaced(before, step.position, step.replacement), knownAfter)
    }
    detoursDropped(spelled).map(kept =>
      planned(derivation, kept.step, kept.replaced, kept.spelledReplaced, kept.spelledReplacement)
    )

  /** A step that is no identity in the replay's spelling: the step with its
    * position in that spelling, the subterm it replaces, and its two sides in
    * that spelling.
    */
  private final case class SpelledStep(
      step: RewriteStep,
      replaced: Instruction,
      spelledReplaced: Instruction,
      spelledReplacement: Instruction
  )

  /** The steps without each two side by side at one position of which the
    * second puts back, in the replay's spelling, the subterm the first
    * replaced: together they are an identity in that spelling, as a
    * respelling alone is, and the replay holds the term before them as the
    * term after them. Dropping a pair may put two others side by side, which
    * are dropped in turn. Measured 2026-11-16 on the entry `wren`'s
    * inlined_calls_10000_hot/direct first point: 4 pairs of a higher-order
    * conversion forward and backward, the backward one writing a binding of
    * about 420,000 characters, 1.77 million of the trace's 3.5 million.
    */
  private def detoursDropped(steps: Vector[SpelledStep]): Vector[SpelledStep] =
    steps
      .foldLeft(List.empty[SpelledStep]) { (kept, step) =>
        kept match
          case last :: earlier
              if last.step.position == step.step.position && (last.spelledReplaced eq step.spelledReplacement) &&
                (last.spelledReplacement eq step.spelledReplaced) =>
            earlier
          case _ => step :: kept
      }
      .reverse
      .toVector

  /** The steps with each step of the β rule that fills a thunk's one hole
    * joined to the step of the body equation that reads the thunk with no
    * hole it leaves, at the same position: forward, the β step then the body
    * step; backward, the body step then the β step. The joined step is the β
    * rule's, its replacement the pair's (`Statements.betaBody`), so that no
    * command writes the thunk with no hole, which the front end never spells.
    * Throws `IllegalStateException` for a β step of one hole with no body
    * step beside it: the replay, which reads the body at once, would replay
    * otherwise than the proof.
    */
  private def betaJoined(steps: Vector[RewriteStep]): Vector[RewriteStep] =
    def lastHole(step: RewriteStep): Boolean = step.reason match
      case RewriteReason.Fill(Instruction.Thunk(_, Vector(_), _), _) => true
      case _                                                         => false
    def body(step: RewriteStep): Boolean = step.reason match
      case RewriteReason.Body(_) => true
      case _                     => false
    @tailrec
    def joined(rest: List[RewriteStep], made: Vector[RewriteStep]): Vector[RewriteStep] = rest match
      case first :: second :: after
          if lastHole(first) && body(second) && first.position == second.position &&
            first.direction == RewriteDirection.Forward && second.direction == RewriteDirection.Forward =>
        joined(after, made :+ first.copy(replacement = second.replacement))
      case first :: second :: after
          if body(first) && lastHole(second) && first.position == second.position &&
            first.direction == RewriteDirection.Backward && second.direction == RewriteDirection.Backward =>
        joined(after, made :+ second)
      case first :: _ if lastHole(first) =>
        throw IllegalStateException(s"the β step of one hole at ${first.position} has no body step beside it")
      case first :: after => joined(after, made :+ first)
      case Nil            => made
    joined(steps.toList, Vector.empty)

  /** The plan of a step that is no identity in the replay's spelling, its
    * position already in that spelling.
    */
  private def planned(
      derivation: ArticleDerivation,
      step: RewriteStep,
      replaced: Instruction,
      spelledReplaced: Instruction,
      spelledReplacement: Instruction
  ): Planned =
    step.reason match
      case RewriteReason.Unproved(kind) =>
        etaStep(step, spelledReplaced, spelledReplacement).filter(_ => kind == UnprovedKind.BetaConversion) match
          case Some(eta) => Planned.Proved(eta)
          case None =>
            Planned.Converted(conversion(derivation, kind, step.copy(replacement = spelledReplacement), spelledReplaced))
      case RewriteReason.Abstraction(eigenvariables, body, inner) =>
        val opened = Conversions.opened(replaced, eigenvariables)
        if !(opened eq body) then
          throw IllegalStateException(s"the closure $replaced opens to $opened, not to the body $body its steps start from")
        val made = inner.foldLeft(body)(applied)
        val written = Conversions.abstraction(made, eigenvariables)
        // FIXME (2026-11-14): a step backward of the abstraction rule puts https://github.com/Atry/private-overlay/issues/1980
        // back a closure, and the replay writes the body back as the front
        // end spells the lambda; a closure the front end does not spell so
        // (a residual thunk of a β step, a written-back thunk's own
        // closure) has no command, and the trace throws here. Candidate
        // fix: the replay of a step backward puts back the closure the
        // step forward opened, kept by the replay, not written. Writing
        // the closure in the command does not work: every term the text
        // holds must read back through the front end as itself
        // (`TraceText.readBack`), and a closure the front end does not
        // spell reads back as another instruction (tried 2026-11-16,
        // 67066478d, reverted). Now the e-graph makes every thunk
        // with holes, a residual's closure included, in the front end's
        // spelling (`EGraph.layerMade`; ExplanationRespellingLawTest), so
        // a closure of the graph is no longer such a closure. Measured
        // 2026-11-16 on 200 seeded write-back rounds with residual closures
        // (the shapes of a scratch search, `(λw. λz. (λk. λl. k) w z) C`
        // among them): 92 abstraction steps, all forward, every closure in
        // the front end's spelling, every trace written. No round has taken
        // a step backward, so the case stays unwitnessed; a witness comes
        // first.
        if !(written eq step.replacement) then
          throw IllegalStateException(
            s"the body ${spelled(made)} written back is ${spelled(written)} (${written.layer}), " +
              s"not the thunk ${spelled(step.replacement)} (${step.replacement.layer}), ${step.direction}; " +
              s"${inner.size} steps from ${spelled(body)}, eigenvariables $eigenvariables, " +
              s"the thunk opens to ${scala.util.Try(spelled(Conversions.opened(step.replacement, eigenvariables)))}; " +
              s"steps ${inner.map(inner => (inner.reason.getClass.getSimpleName, inner.position, inner.direction, spelled(inner.replacement)))}"
          )
        Planned.Abstracted(step.position, eigenvariables, plan(derivation, body, inner))
      case _ => Planned.Proved(step)

  /** The text of a term for a message, its opaque leaves as they are. */
  private def spelled(term: Instruction): String =
    scala.util.Try(gezi.frontend.Lambdalattice.closedText(term)).getOrElse(term.toString)

  /** Where two codes differ, for a message: every minimal differing pair,
    * found by descending into each differing child of two codes of one shape,
    * at most `limit` of them, each with its path of child indices (an
    * application's function 0 and argument 1, a choice's or a parallel's
    * sides 0 and 1, a thunk's code 0 and its fillings from 1).
    */
  private def codeDifferences(left: Code, right: Code, path: Vector[Int], limit: Int): Vector[(Vector[Int], CodeLayer[Code], CodeLayer[Code])] =
    if left == right || limit <= 0 then Vector.empty
    else
      val (leftParts, rightParts) = (codeParts(left.layer), codeParts(right.layer))
      if codeShape(left.layer) != codeShape(right.layer) || leftParts.size != rightParts.size then
        Vector((path, left.layer, right.layer))
      else
        leftParts.zip(rightParts).zipWithIndex.foldLeft(Vector.empty[(Vector[Int], CodeLayer[Code], CodeLayer[Code])]) {
          case (found, ((own, other), index)) =>
            found ++ codeDifferences(own, other, path :+ index, limit - found.size)
        }

  private def codeParts(layer: CodeLayer[Code]): Vector[Code] = layer match
    case Slot(_)                         => Vector.empty
    case Apply(function, argument)       => Vector(function, argument)
    case Parallel(leftSide, rightSide)   => Vector(leftSide, rightSide)
    case Choice(leftSide, rightSide)     => Vector(leftSide, rightSide)
    case Thunk(code, _, fillings)        => code +: fillings

  /** A code as text, for a message: a slot `s<index>`, an application in
    * parentheses, a choice `+`, a parallel `∥`, and an inner thunk
    * `λ<holes>[<fillings>]. <code>`.
    */
  private def codeText(code: Code): String = codeLayerText(code.layer)

  private def codeLayerText(layer: CodeLayer[Code]): String = layer match
    case Slot(index)               => s"s$index"
    case Apply(function, argument) => s"(${codeText(function)} ${codeText(argument)})"
    case Parallel(left, right)     => s"(${codeText(left)} ∥ ${codeText(right)})"
    case Choice(left, right)       => s"(${codeText(right)} + ${codeText(left)})"
    case Thunk(inner, holes, fillings) =>
      s"λ${holes.mkString(",")}[${fillings.map(codeText).mkString(", ")}]. ${codeText(inner)}"

  private def codeShape(layer: CodeLayer[Code]): String = layer match
    case Thunk(_, holes, fillings) => s"thunk $holes ${fillings.size}"
    case Slot(index)               => s"slot $index"
    case Apply(_, _)               => "apply"
    case Parallel(_, _)            => "parallel"
    case Choice(_, _)              => "choice"

  /** The layer of a term for a message, or the term itself when it is opaque. */
  private def layerShown(term: Instruction): String =
    if term.opaque then term.toString else term.layer.toString

  /** Where two terms first differ, for a message: below the position, the
    * outermost pair of subterms that are not one layer over equal children
    * with exactly one child differing; the position and the two subterms.
    */
  /** The step of the defunctionalized η rule that a β conversion with no
    * proof is: the replaced term and the replacement differ at one position
    * only, where one is the η-shaped thunk `λx. f x` over the other, f. A
    * higher-order conversion backward that only η-expands a filling has a
    * replaced term that does not determine its binding (K := f and
    * K := λx. f x have one normal form), while the η rule's step needs none
    * (the reading of the entry `wren`'s inlined hot point, 2026-11-17). None for any other
    * pair.
    */
  private def etaStep(step: RewriteStep, replaced: Instruction, replacement: Instruction): Option[RewriteStep] =
    val (at, from, to) = difference(replaced, replacement, Vector.empty)
    def etaOver(thunk: Instruction, filling: Instruction): Boolean = thunk.layer match
      case Thunk(code, holes, Vector(only)) => Statements.etaShaped(code, holes) && (only eq filling)
      case _                                => false
    val elsewhereEqual = Positions.replaced(replaced, at, to) eq replacement
    val bare = Vector(Vector.empty[PositionSegment])
    val underThunk = Vector(Vector(PositionSegment.Filling(0)))
    if !elsewhereEqual then None
    else if etaOver(to, from) then
      Some(RewriteStep(RewriteReason.Eta(to), step.position ++ at, RewriteDirection.Backward, to, Vector(Provenance("filling0", bare, underThunk))))
    else if etaOver(from, to) then
      Some(RewriteStep(RewriteReason.Eta(from), step.position ++ at, RewriteDirection.Forward, to, Vector(Provenance("filling0", underThunk, bare))))
    else None

  private def difference(
      left: Instruction,
      right: Instruction,
      position: Vector[PositionSegment]
  ): (Vector[PositionSegment], Instruction, Instruction) =
    if left.opaque || right.opaque then (position, left, right)
    else
      val (leftLayer, rightLayer) = (left.layered, right.layered)
      val differing = leftLayer.children
        .zip(rightLayer.children)
        .zip(Positions.roles(leftLayer))
        .filter { case ((leftChild, rightChild), _) => leftChild != rightChild }
      differing match
        case Vector(((leftChild, rightChild), role)) if leftLayer.map(_ => ()) == rightLayer.map(_ => ()) =>
          difference(leftChild, rightChild, position :+ role)
        case _ => (position, left, right)

  private def lemmasOf(planned: Planned): Vector[LemmaIdentifier] = planned match
    case Planned.Proved(RewriteStep(RewriteReason.Lemma(lemma, _), _, _, _, _)) => Vector(lemma)
    case Planned.Proved(_)                                                       => Vector.empty
    case Planned.Converted(found)                                                => Vector(found.lemma)
    case Planned.Abstracted(_, _, steps)                                         => steps.flatMap(lemmasOf)

  /** The command of a planned step under `depth` openings, each
    * eigenvariable of an enclosing opening renamed to the replay's
    * (`Conversions.eigenvariables`) in every term it writes, and the building
    * with the lemmas and the values it names. A term the command gives is
    * named by its value (`valueOf`), or written where it holds an
    * eigenvariable or has no value (`gezi.rewritetrace.Given`, its
    * FIXME). https://github.com/Atry/private-overlay/issues/1980
    */
  private def commandOf(
      derivation: ArticleDerivation,
      origins: ValueOrigins,
      building: TraceBuilding,
      planned: Planned,
      depth: Int,
      renamed: Map[Instruction, Instruction]
  ): (TraceCommand, TraceBuilding) =
    def giving(current: TraceBuilding, term: Instruction): (Given, TraceBuilding) =
      val named =
        if renamed.nonEmpty && Conversions.holds(term, renamed.keySet) then None
        else valueOf(derivation, origins, current, term)
      named match
        case Some((place, after)) => (Given.Value(place), after)
        case None                 => (Given.Written(Conversions.leavesReplaced(ReplaySpelling.term(term), renamed)), current)
    def bindingsGiven(current: TraceBuilding, bindings: Vector[(Int, Instruction)]): (Vector[(Int, Given)], TraceBuilding) =
      bindings.foldLeft((Vector.empty[(Int, Given)], current)) { case ((made, before), (place, term)) =>
        val (named, after) = giving(before, term)
        (made :+ (place, named), after)
      }
    // The thunk of a step backward of the β rule, the body equation or the η rule (`ThunkShape`): the replay reads
    // only the code and holes of its spelling, its fillings being the equation's variables. The step's own thunk is
    // often no node of the proof: the β rule of a function of several arguments fills one hole at a time, and the
    // e-graph makes no node for the thunks between (`Saturation.betaWorked` extends the closure state). So a thunk of
    // the proof with the code names the code, and the holes are written.
    def thunkGiven(current: TraceBuilding, thunk: Option[Instruction]): (Option[ThunkShape], TraceBuilding) =
      // The first of the candidates that has a value, tried in order; a loop, since thousands of a program's
      // thunks may share a code and have none.
      @tailrec
      def firstValue(candidates: Vector[Instruction]): Option[(Int, TraceBuilding)] =
        candidates.headOption match
          case None => None
          case Some(candidate) =>
            valueOf(derivation, origins, current, candidate) match
              case found @ Some(_) => found
              case None            => firstValue(candidates.tail)
      thunk.fold((None, current))(term =>
        val spelling = ReplaySpelling.term(term)
        spelling.layer match
          case Thunk(code, holes, _) =>
            val sameCode = derivation.forest.thunks.toVector.collect { case ((found, _), nodes) if found == code => nodes }.flatten
            val named =
              if renamed.nonEmpty && Conversions.holds(term, renamed.keySet) then None
              else firstValue((Vector(term, spelling) ++ sameCode).distinct)
            named match
              case Some((place, after)) => (Some(ThunkShape(Given.Value(place), holes)), after)
              case None =>
                giving(current, term) match { case (named, after) => (Some(ThunkShape(named, holes)), after) }
          case other => throw IllegalStateException(s"the thunk of a step is no thunk: $other")
      )
    planned match
      case Planned.Proved(step) =>
        val (reason, bindings) = proved(derivation, step)
        val (reasonGiven, afterReason) = reason match
          case ReasonDraft.Lemma(lemma)      => building.lemmaPlaced(lemma) match { case (place, after) => (ProvedReason.Lemma(place), after) }
          case ReasonDraft.Equation(number)  => (ProvedReason.Equation(number), building)
          case ReasonDraft.Fill(thunk)       => thunkGiven(building, thunk) match { case (named, after) => (ProvedReason.Fill(named), after) }
          case ReasonDraft.Body(thunk)       => thunkGiven(building, thunk) match { case (named, after) => (ProvedReason.Body(named), after) }
          case ReasonDraft.Eta(thunk)        => thunkGiven(building, thunk) match { case (named, after) => (ProvedReason.Eta(named), after) }
        val (bindingsNamed, afterBindings) = bindingsGiven(afterReason, bindings)
        (TraceCommand.Rewrite(reasonGiven, step.position, step.direction, bindingsNamed), afterBindings)
      case Planned.Converted(found) =>
        val (place, afterLemma) = building.lemmaPlaced(found.lemma)
        val (bindingsNamed, afterBindings) = bindingsGiven(afterLemma, found.bindings)
        (TraceCommand.Convert(found.conversion(place), found.position, found.direction, bindingsNamed), afterBindings)
      case Planned.Abstracted(position, eigenvariables, steps) =>
        val inner = renamed ++ eigenvariables.zip(Conversions.eigenvariables(depth, eigenvariables.size))
        val (commands, after) = steps.foldLeft((Vector.empty[TraceCommand], building)) { case ((made, current), step) =>
          val (command, next) = commandOf(derivation, origins, current, step, depth + 1, inner)
          (made :+ command, next)
        }
        (TraceCommand.Abstraction(position, eigenvariables.size, commands), after)

  /** The reason of a proved step's command before the trace places its
    * lemma and gives its thunk (`commandOf`).
    */
  private enum ReasonDraft:
    case Lemma(lemma: LemmaIdentifier)
    case Equation(number: Int)
    case Fill(thunk: Option[Instruction])
    case Body(thunk: Option[Instruction])
    case Eta(thunk: Option[Instruction])

  /** A step of no proof as a conversion of a lemma (`Conversion`), its
    * place in the trace's lemmas not yet known.
    */
  private final case class Converted(
      lemma: LemmaIdentifier,
      conversion: Int => Conversion,
      position: Vector[PositionSegment],
      direction: RewriteDirection,
      bindings: Vector[(Int, Instruction)]
  )

  /** The conversion a step of no proof instantiates: the first, over the
    * strategy's lemmas in order and each lemma's conversions, whose equation
    * computes the step's replacement from its replaced subterm, forward or
    * backward. Throws `IllegalStateException` when none does.
    */
  private def conversion(
      derivation: ArticleDerivation,
      kind: UnprovedKind,
      step: RewriteStep,
      replaced: Instruction
  ): Converted = kind match
    // FIXME (2026-11-13): the abstraction rule of a body written back has https://github.com/Atry/private-overlay/issues/2046
    // no command yet, so a round whose proof crosses one has no trace. Candidate
    // fix: a nested
    // command that opens the thunk at its position with eigenvariables,
    // replays the body's commands and writes the body back as the front end
    // spells the lambda; its certificate needs extensionality (Lean
    // `Derivable.extensional`, 40b55dd8a).
    case UnprovedKind.Abstraction =>
      throw IllegalStateException(s"the abstraction rule at ${step.position} has no command of the trace")
    case UnprovedKind.BetaConversion =>
      derivation.store.encodedLemmas.to(LazyList)
        .flatMap(lemma => conversions(derivation, lemma, step.position, replaced, step.replacement))
        .headOption
        .getOrElse {
          val (at, from, to) = difference(replaced, step.replacement, Vector.empty)
          throw IllegalStateException(
            s"no conversion of a lemma takes $replaced to ${step.replacement} at ${step.position}, " +
              s"${step.direction}; they first differ at $at: ${layerShown(from)} against ${layerShown(to)}, " +
              s"spelled ${spelled(from)} against ${spelled(to)}; the higher-order conversions tried: " +
              attempts(derivation, replaced, step.replacement).mkString(" | ")
          )
        }

  private def conversions(
      derivation: ArticleDerivation,
      lemma: LemmaIdentifier,
      position: Vector[PositionSegment],
      replaced: Instruction,
      replacement: Instruction
  ): LazyList[Converted] =
    val (left, right) = derivation.store.lemmaSides(lemma)
    val statement = TraceLemma(left, right).statement
    val higherOrderVariables = Conversions.higherOrder(statement)
    val higherOrder = LemmaSide.values.to(LazyList).flatMap(side =>
      Conversions.thunkPatterns(Conversions.sideOf(statement, side)).zipWithIndex.to(LazyList).flatMap((pattern, occurrence) =>
        val conversion = (place: Int) => Conversion.HigherOrder(place, side, occurrence)
        val forward = Conversions
          .instanceBindings(pattern, replaced)
          .filter(bound => Conversions.normalForm(pattern, bound, higherOrderVariables) eq replacement)
          .map(_ => Converted(lemma, conversion, position, RewriteDirection.Forward, Vector.empty))
        // A left side's conversion backward writes no binding: the replay
        // solves the pattern on the replaced term (`Conversions.expansionSolutions`),
        // so the candidate stands only where that solution is the one and
        // gives this replacement.
        val backward = Conversions
          .instanceBindings(pattern, replacement)
          .filter(bound => Conversions.spelledAlike(Conversions.normalForm(pattern, bound, higherOrderVariables), replaced))
          .filter(_ =>
            side match
              case LemmaSide.Left =>
                Conversions
                  .expansionSolutions(pattern, replaced, higherOrderVariables)
                  .map(Conversions.instance(pattern, _)) == Vector(replacement)
              case LemmaSide.Right => true
          )
          .map(bound =>
            Converted(
              lemma,
              conversion,
              position,
              RewriteDirection.Backward,
              side match
                case LemmaSide.Left  => Vector.empty
                case LemmaSide.Right => Statements.variables(pattern).distinct.zipWithIndex.map((name, place) => (place, bound(name)))
            )
          )
        forward.to(LazyList) ++ backward.to(LazyList)
      )
    )
    val rootReversed = Conversions.names(statement).to(LazyList).flatMap(names =>
      val conversion = (place: Int) => Conversion.RootReverseBeta(place)
      // A redex is applied to the names (`Conversions.appliedToNames`), checked before the abstraction of the
      // whole other side is computed: on the entry `solo`'s repeated_library_hotspots calls_1000 point that
      // abstraction, made for each step of no proof and each lemma, was half the flattening.
      Option.when(Conversions.appliedToNames(replacement, names) && (Conversions.redex(replaced, names) eq replacement))(
        Converted(lemma, conversion, position, RewriteDirection.Forward, Vector.empty)
      ).to(LazyList) ++ Option.when(Conversions.appliedToNames(replaced, names) && (Conversions.redex(replacement, names) eq replaced))(
        Converted(lemma, conversion, position, RewriteDirection.Backward, Vector.empty)
      ).to(LazyList)
    )
    higherOrder ++ rootReversed

  /** For a message: each higher-order conversion `conversions` tries, by
    * lemma, side and occurrence, and why it does not take the replaced
    * subterm to the replacement either way: the thunk pattern matches
    * neither, or its normal form differs from the other side, with the
    * higher-order variables' values and where they first differ
    * (`difference`).
    */
  private def attempts(derivation: ArticleDerivation, replaced: Instruction, replacement: Instruction): Vector[String] =
    def tried(
        pattern: StatementTerm,
        higherOrderVariables: Set[String],
        from: Instruction,
        to: Instruction,
        direction: RewriteDirection
    ): String =
      Statements.matchedBindings(pattern, from) match
        case None => "no match"
        case Some(bound) =>
          val normal = Conversions.normalForm(pattern, bound, higherOrderVariables)
          val converts = direction match
            case RewriteDirection.Forward  => normal eq to
            case RewriteDirection.Backward => Conversions.spelledAlike(normal, to)
          if converts then "converts"
          else
            val (at, mine, theirs) = difference(normal, to, Vector.empty)
            val codes = (mine.opaque, theirs.opaque) match
              case (false, false) =>
                (mine.layer, theirs.layer) match
                  case (Thunk(ownCode, _, _), Thunk(otherCode, _, _)) =>
                    val found = codeDifferences(ownCode, otherCode, Vector.empty, 6)
                    s"; the codes differ at ${found.size} minimal places (at most 6 shown): " +
                      found.map((path, ownPart, otherPart) =>
                        s"at $path ${codeLayerText(ownPart)} against ${codeLayerText(otherPart)}"
                      ).mkString("; ")
                  case _ => ""
              case _ => ""
            val higherOrderValues = bound.toVector
              .filter((name, _) => higherOrderVariables.contains(name))
              .map((name, value) => s"$name := ${layerShown(value)}")
              .mkString(", ")
            s"matches with $higherOrderValues; its normal form differs at $at: ${layerShown(mine)} against " +
              s"${layerShown(theirs)}$codes"
    derivation.store.encodedLemmas.flatMap { lemma =>
      val (left, right) = derivation.store.lemmaSides(lemma)
      val statement = TraceLemma(left, right).statement
      val higherOrderVariables = Conversions.higherOrder(statement)
      LemmaSide.values.toVector.flatMap(side =>
        Conversions.thunkPatterns(Conversions.sideOf(statement, side)).zipWithIndex.map((pattern, occurrence) =>
          s"$lemma $side $occurrence: forward " +
            s"${tried(pattern, higherOrderVariables, replaced, replacement, RewriteDirection.Forward)}; " +
            s"backward ${tried(pattern, higherOrderVariables, replacement, replaced, RewriteDirection.Backward)}"
        )
      )
    }

  private def proved(derivation: ArticleDerivation, step: RewriteStep): (ReasonDraft, Vector[(Int, Instruction)]) =
    def backward(thunk: Instruction): Option[Instruction] = Option.when(step.direction == RewriteDirection.Backward)(thunk)
    val reason = step.reason match
      case RewriteReason.Lemma(lemma, _)     => ReasonDraft.Lemma(lemma)
      case RewriteReason.Equation(number, _) => ReasonDraft.Equation(number)
      case RewriteReason.Fill(thunk, _)      => ReasonDraft.Fill(backward(thunk))
      case RewriteReason.Body(thunk)         => ReasonDraft.Body(backward(thunk))
      // A step backward whose thunk is the front end's `λx. f x` writes none:
      // the replay spells it over the replaced f (`Conversions.etaExpanded`).
      case RewriteReason.Eta(thunk) =>
        val canonical = thunk.layer match
          case Thunk(code, holes, Vector(filling)) =>
            Conversions.etaExpanded(filling).layer match
              case Thunk(canonicalCode, canonicalHoles, _) => canonicalCode == code && canonicalHoles == holes
              case _                                     => false
          case _ => false
        ReasonDraft.Eta(if canonical then None else backward(thunk))
      case RewriteReason.Respell(_) =>
        throw IllegalArgumentException("a respelling is an identity in the replay's spelling and has no command (ReplaySpelling)")
      case RewriteReason.Unproved(kind)      => throw IllegalArgumentException(s"a step of $kind has no proof")
      case RewriteReason.Abstraction(_, _, _) => throw IllegalArgumentException("the abstraction rule has no proof")
    // The β rule of a thunk's one hole is replayed together with the body equation that follows it (`plan`).
    val equation = step.reason match
      case RewriteReason.Fill(Instruction.Thunk(code, holes @ Vector(_), _), _) => Statements.betaBody(code, holes)
      case _                                                                     => statement(derivation, step.reason)
    val (replacedSide, _) = equation.oriented(step.direction)
    val held = Statements.variables(replacedSide).toSet
    val bound = this.bound(step.reason)
    val bindings = equation.variables.zipWithIndex.collect {
      case (name, place) if !held.contains(name) =>
        (place, bound.getOrElse(name, throw IllegalStateException(s"the step binds no $name")))
    }
    (reason, bindings)

  /** The steps an edge or a path expanded to, each expansion flattened once:
    * a union's edge recurs in the paths that cross it.
    */
  private type Expansions = Map[ArticleProof, Vector[OrientedStep]]

  private def flattened(
      derivation: ArticleDerivation,
      proof: ArticleProof,
      expansions: Expansions
  ): TailRec[(Vector[OrientedStep], Expansions)] = proof match
    case ArticleProof.Reflexivity(_) => done((Vector.empty, expansions))
    case ArticleProof.Symmetry(inner) =>
      tailcall(flattened(derivation, inner, expansions)).map((steps, after) => (steps.reverse.map(_.turned), after))
    case ArticleProof.Transitivity(first, second) =>
      for
        (firstSteps, afterFirst) <- tailcall(flattened(derivation, first, expansions))
        (secondSteps, afterSecond) <- tailcall(flattened(derivation, second, afterFirst))
      yield (firstSteps ++ secondSteps, afterSecond)
    case ArticleProof.Congruence(shape, proofs) =>
      TailRecFolds.folded(proofs.zip(roles(shape, proofs.size)).toVector, (Vector.empty[OrientedStep], expansions)) {
        case ((steps, current), (inner, role)) =>
          flattened(derivation, inner, current).map((innerSteps, after) =>
            (steps ++ innerSteps.map(_.under(role)), after)
          )
      }
    case ArticleProof.Instance(axiom, substitution) =>
      done((Vector(instanceStep(derivation, axiom, substitution)), expansions))
    case ArticleProof.Conversion(first, second, _) =>
      val step = RewriteStep(
        RewriteReason.Unproved(UnprovedKind.BetaConversion),
        Vector.empty,
        RewriteDirection.Forward,
        second,
        Vector.empty
      )
      done((Vector(OrientedStep(step, first)), expansions))
    case ArticleProof.Abstraction(first, second, eigenvariables, body, proof) =>
      tailcall(flattened(derivation, proof, expansions)).map((inner, after) =>
        val made = inner.map(_.step).foldLeft(body)(applied)
        val spelling = Conversions.opened(second, eigenvariables)
        if !(made eq spelling) then
          throw IllegalStateException(
            s"the ${inner.size} steps of the body ${spelled(body)} make ${spelled(made)}, not its spelling ${spelled(spelling)}"
          )
        val step = RewriteStep(
          RewriteReason.Abstraction(eigenvariables, body, inner.map(_.step)),
          Vector.empty,
          RewriteDirection.Forward,
          second,
          Vector.empty
        )
        (Vector(OrientedStep(step, first)), after)
      )
    case ArticleProof.Edge(_) | ArticleProof.Connection(_, _) =>
      expansions.get(proof) match
        case Some(steps) => done((steps, expansions))
        case None =>
          val expansion = derivation
            .expanded(proof)
            .getOrElse(throw IllegalStateException(s"the writer does not expand $proof"))
          tailcall(flattened(derivation, expansion, expansions)).map((steps, after) =>
            (steps, after.updated(proof, steps))
          )

  /** The role of each child of a layer of the shape, in child order. */
  private def roles(shape: LayerShape, children: Int): Vector[PositionSegment] = shape match
    case LayerShape.Thunk(_, _)                  => Vector.tabulate(children)(PositionSegment.Filling(_))
    case LayerShape.Apply                        => Vector(PositionSegment.Function, PositionSegment.Argument)
    case LayerShape.Choice | LayerShape.Parallel => Vector(PositionSegment.Left, PositionSegment.Right)

  /** The step of an instance of an axiom of the import set. */
  private def instanceStep(
      derivation: ArticleDerivation,
      axiom: Axiom,
      substitution: Vector[(String, ArticleTerm)]
  ): OrientedStep =
    val (left, right) = derivation.store.axiomStatement(axiom)
    val equation = Statement(ArticleStore.statementTerm(left), ArticleStore.statementTerm(right))
    val bindings = substitution.map((name, term) => (name, instructionOf(term)))
    val bound = bindings.toMap
    def fillings(count: Int): Vector[Instruction] = Vector.tabulate(count)(place => boundVariable(bound, s"filling$place"))
    val reason = axiom match
      case Axiom.SetEquation(number) => RewriteReason.Equation(number, bindings)
      case Axiom.Lemma(lemma)        => RewriteReason.Lemma(lemma, bindings)
      case Axiom.Fill(code, holes) =>
        RewriteReason.Fill(
          Instruction.Thunk(code, holes, fillings(derivation.store.thunkArity(code, holes))),
          boundVariable(bound, "argument")
        )
      case Axiom.Body(code) =>
        RewriteReason.Body(Instruction.Thunk(code, Vector.empty, fillings(derivation.store.thunkArity(code, Vector.empty))))
      case Axiom.Eta(code, holes) => RewriteReason.Eta(Instruction.Thunk(code, holes, fillings(1)))
      case Axiom.Respell(code, holes) =>
        RewriteReason.Respell(Instruction.Thunk(code, holes, fillings(derivation.store.thunkArity(code, holes))))
      case Axiom.Conversion(_, _) =>
        throw IllegalStateException(s"a conversion equation is no instance of a proof: the trace converts by replay")
    OrientedStep(
      RewriteStep(
        reason,
        Vector.empty,
        RewriteDirection.Forward,
        Statements.instance(equation.right, bound),
        equation.provenance
      ),
      Statements.instance(equation.left, bound)
    )

  private def boundVariable(bound: Map[String, Instruction], name: String): Instruction =
    bound.getOrElse(name, throw IllegalStateException(s"the instance binds no $name"))

  /** The closed instruction of a term over instructions. Throws
    * `IllegalArgumentException` for a variable and for an equation.
    */
  def instructionOf(term: ArticleTerm): Instruction = Statements.instance(ArticleStore.statementTerm(term), Map.empty)

  /** The axiom of the import set a reason instantiates. */
  def axiom(reason: RewriteReason): Axiom = reason match
    case RewriteReason.Lemma(lemma, _)                            => Axiom.Lemma(lemma)
    case RewriteReason.Equation(number, _)                        => Axiom.SetEquation(number)
    case RewriteReason.Fill(Instruction.Thunk(code, holes, _), _) => Axiom.Fill(code, holes)
    case RewriteReason.Body(Instruction.Thunk(code, _, _))        => Axiom.Body(code)
    case RewriteReason.Eta(Instruction.Thunk(code, holes, _))     => Axiom.Eta(code, holes)
    case RewriteReason.Respell(Instruction.Thunk(code, holes, _)) => Axiom.Respell(code, holes)
    case other => throw IllegalArgumentException(s"the reason $other holds no thunk")

  /** The statement of the axiom a reason instantiates, as the article states
    * it.
    */
  def statement(derivation: ArticleDerivation, reason: RewriteReason): Statement =
    val (left, right) = derivation.store.axiomStatement(axiom(reason))
    Statement(ArticleStore.statementTerm(left), ArticleStore.statementTerm(right))

  /** The variables a reason binds, by name. */
  def bound(reason: RewriteReason): Map[String, Instruction] =
    def fillingsBound(thunk: Instruction): Map[String, Instruction] = thunk match
      case Instruction.Thunk(_, _, fillings) =>
        fillings.zipWithIndex.map((filling, place) => (s"filling$place", filling)).toMap
      case other => throw IllegalArgumentException(s"$other is no thunk")
    reason match
      case RewriteReason.Lemma(_, substitution)    => substitution.toMap
      case RewriteReason.Equation(_, substitution) => substitution.toMap
      case RewriteReason.Fill(thunk, argument)     => fillingsBound(thunk).updated("argument", argument)
      case RewriteReason.Body(thunk)               => fillingsBound(thunk)
      case RewriteReason.Eta(thunk)                => fillingsBound(thunk)
      case RewriteReason.Respell(thunk)            => fillingsBound(thunk)
      case RewriteReason.Unproved(_)               => Map.empty
      case RewriteReason.Abstraction(_, _, _)      => Map.empty

  /** The term after the step. */
  def applied(term: Instruction, step: RewriteStep): Instruction = Positions.replaced(term, step.position, step.replacement)
