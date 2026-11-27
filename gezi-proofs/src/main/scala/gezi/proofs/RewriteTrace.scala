package gezi.proofs

import gezi.ir.Code
import gezi.ir.CodeLayer
import gezi.ir.Hole
import gezi.ir.LemmaIdentifier
import gezi.ir.NonEmptyHoles
import gezi.ir.StorageAccess
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
import gezi.ir.{Configured, NativeSpecializer}

/** The proof of a round's equation `left = right` as the article writer builds
  * it, before it is written (`OpentheoryArticle.derivation`): its tree, the
  * expansion of its edges and paths, the store the article states its axioms
  * from, and the forest of the search's nodes and unions it is built from; with
  * the configuration of the round's terms and the capability to read a
  * storage's view, under which the trace reads the article's terms back
  * (`term`): each built layer by layer through the configuration, so that the
  * term of a storage's view node is the storage again.
  */
final class ArticleDerivation[
    C <: NativeSpecializer & Singleton
] private[proofs] (
    val specializer: C,
    val left: Configured[C],
    val right: Configured[C],
    val proof: ArticleProof,
    expansion: ArticleProof => Option[ArticleProof],
    val store: ArticleStore[C],
    val forest: ProofForest[C]
)(using val access: StorageAccess):

  private given C = specializer

  /** The proof an edge or a path expands to, the one the article writes in its
    * place; none for any other proof.
    */
  def expanded(proof: ArticleProof): Option[ArticleProof] = expansion(proof)

  /** The term of each term of the article, by its place: a layer's built over
    * its children's, placed before it (`ProofTerms`).
    */
  private lazy val readBack: Vector[Configured[C]] =
    (0 until store.terms.size).foldLeft(Vector.empty[Configured[C]])(
      (made, place) =>
        made :+ (store.terms.key(TermId(place)) match
          case TermKey.Leaf(leaf)            => leaf
          case TermKey.Stored(storage, _, _) => storage
          case TermKey.Layered(layer)        =>
            Positions
              .built(layer, layer.children.map(child => made(child.index))))
    )

  /** The term of a term of the article in the round's configuration. */
  def term(of: TermId): Configured[C] = readBack(of.index)

  /** The term of a node. */
  def nodeTerm(node: Int): Configured[C] = term(store.terms.nodeTerm(node))

  /** Each term of a node to the first node whose term it is: two nodes may read
    * back as one term (a storage's view node and the storage).
    */
  private lazy val nodesOfTerms: Map[Configured[C], Int] =
    (0 until store.terms.nodeCount).foldLeft(Map.empty[Configured[C], Int])(
      (found, node) =>
        val read = nodeTerm(node)
        if found.contains(read) then found else found.updated(read, node)
    )

  /** The first node whose term the term is; none for a term no node has. */
  def nodeOf(read: Configured[C]): Option[Int] = nodesOfTerms.get(read)

/** Why a step holds: an instance of a lemma, by its identifier, one for each
  * direction and pair of sides (`gezi.standardlibrary.LemmaNamed`); of a
  * numbered equation; the defunctionalized β rule of a thunk, the thunk's code,
  * holes and fillings and the argument; the equation of a thunk with no hole
  * and its code's body, the code and the fillings; the defunctionalized η rule
  * of an eta-shaped thunk, its code, holes and filling; or the equation of a
  * thunk with holes and its spelling by the front end (`Statements.respell`),
  * its code, holes and fillings. No reason holds a thunk as a term: a thunk of
  * no hole is no term. A lemma and an equation bind the variables of their
  * statements by name in `substitution`; the β, body, η and respelling
  * equations bind theirs through the thunk's fillings (`filling0`, `filling1`,
  * and so on) and the argument (`argument`). A step of a union with no proof
  * (`ArticleProof.Conversion`) instantiates no equation and binds nothing. A
  * step of the abstraction rule replaces a closure by the thunk its body is
  * written back to: the eigenvariables it opened the closure at, the body it
  * opened to, and the body's own steps, from the body to the spelling written
  * back (turned with the step).
  */
enum RewriteReason[C <: NativeSpecializer & Singleton]:
  case Lemma(
      lemma: LemmaIdentifier,
      substitution: Vector[(String, Configured[C])]
  )

  /** A native's fold: `application` equals the storage `result`, the native's
    * trusted obligation (`Axiom.Native`). The article imports it as an axiom;
    * the trace writes the replacement as a native value
    * (`TraceCommand.Native`), a step of no equation, in either direction.
    */
  case Native(native: String, application: Configured[C], result: Configured[C])
  case Equation(number: Int, substitution: Vector[(String, Configured[C])])
  case Fill(
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[Configured[C]],
      argument: Configured[C]
  )
  case Body(code: Code, fillings: Vector[Configured[C]])
  case Eta(code: Code, holes: Vector[Hole], fillings: Vector[Configured[C]])
  case Respell(code: Code, holes: Vector[Hole], fillings: Vector[Configured[C]])
  case Unproved(kind: UnprovedKind)
  case Abstraction(
      eigenvariables: Vector[Configured[C]],
      body: Configured[C],
      steps: Vector[RewriteStep[C]]
  )

/** A rewrite of the whole term: the subterm at `position`, from the root,
  * replaced by `replacement`, by the equation of `reason` in `direction`, with
  * the provenance of the equation's variables.
  */
final case class RewriteStep[C <: NativeSpecializer & Singleton](
    reason: RewriteReason[C],
    position: Vector[PositionSegment],
    direction: RewriteDirection,
    replacement: Configured[C],
    provenance: Vector[Provenance]
)

/** A round: its input, its steps in order, and its output, which the steps make
  * of the input.
  */
final case class RewriteRound[C <: NativeSpecializer & Singleton](
    input: Configured[C],
    steps: Vector[RewriteStep[C]],
    output: Configured[C]
)

/** A side of a step as the article's proof gives it: a term, or the thunk of a
  * code with no hole over its fillings, which is no term and stands only
  * between the β rule's step that fills a thunk's last hole and the body
  * equation's step that reads it, the two joined into one step before any term
  * is made of it (`OrientedStep.joined`).
  */
private enum StepTerm[C <: NativeSpecializer & Singleton]:
  case Term(term: Configured[C])
  case Holeless(code: Code, fillings: Vector[Configured[C]])

/** A step of the proof as it is flattened, a side of which may be the thunk of
  * no hole (`StepTerm`).
  */
private final case class FlatStep[C <: NativeSpecializer & Singleton](
    reason: RewriteReason[C],
    position: Vector[PositionSegment],
    direction: RewriteDirection,
    replacement: StepTerm[C],
    provenance: Vector[Provenance]
)

/** A step with the subterm it replaces, which turning the step needs. */
private final case class OrientedStep[C <: NativeSpecializer & Singleton](
    step: FlatStep[C],
    replaced: StepTerm[C]
):

  def turned(using C, StorageAccess): OrientedStep[C] =
    OrientedStep(
      step.copy(
        reason = OrientedStep.reasonTurned(step.reason),
        direction = step.direction.reversed,
        replacement = replaced,
        provenance = step.provenance.map(_.turned)
      ),
      step.replacement
    )

  def under(segment: PositionSegment): OrientedStep[C] =
    copy(step = step.copy(position = segment +: step.position))

private object OrientedStep:

  /** The step of a rewrite of the whole term, with the subterm it replaces. */
  def of[C <: NativeSpecializer & Singleton](
      step: RewriteStep[C],
      replaced: Configured[C]
  ): OrientedStep[C] =
    OrientedStep(
      FlatStep(
        step.reason,
        step.position,
        step.direction,
        StepTerm.Term(step.replacement),
        step.provenance
      ),
      StepTerm.Term(replaced)
    )

  /** The steps of a flattened proof as rewrites of the whole term, each step of
    * the β rule that fills a thunk's one hole joined to the step of the body
    * equation that reads the thunk with no hole it leaves, at the same
    * position: forward, the β step then the body step; backward, the body step
    * then the β step. The joined step is the β rule's, its replacement the
    * pair's (`Statements.betaBody`), so that the thunk with no hole, which is
    * no term, is never made, and no command writes it. Throws
    * `IllegalStateException` for a β step of one hole with no body step beside
    * it, and for a side of no hole left once the pairs are joined: the replay,
    * which reads the body at once, would replay otherwise than the proof.
    */
  def joined[C <: NativeSpecializer & Singleton](
      steps: Vector[OrientedStep[C]]
  ): Vector[RewriteStep[C]] =
    def lastHole(step: FlatStep[C]): Boolean = step.reason match
      case RewriteReason.Fill(_, Vector(_), _, _) => true
      case _                                      => false
    def body(step: FlatStep[C]): Boolean = step.reason match
      case RewriteReason.Body(_, _) => true
      case _                        => false
    def rewrite(step: FlatStep[C]): RewriteStep[C] = step.replacement match
      case StepTerm.Term(term) =>
        RewriteStep(
          step.reason,
          step.position,
          step.direction,
          term,
          step.provenance
        )
      case StepTerm.Holeless(code, _) =>
        throw IllegalStateException(
          s"a step at ${step.position} puts the thunk of the code $code with no hole, which no step reads"
        )
    @tailrec
    def joinedFrom(
        rest: List[FlatStep[C]],
        made: Vector[RewriteStep[C]]
    ): Vector[RewriteStep[C]] = rest match
      case first :: second :: after
          if lastHole(first) && body(
            second
          ) && first.position == second.position &&
            first.direction == RewriteDirection.Forward && second.direction == RewriteDirection.Forward =>
        joinedFrom(
          after,
          made :+ rewrite(first.copy(replacement = second.replacement))
        )
      case first :: second :: after
          if body(first) && lastHole(
            second
          ) && first.position == second.position &&
            first.direction == RewriteDirection.Backward && second.direction == RewriteDirection.Backward =>
        joinedFrom(after, made :+ rewrite(second))
      case first :: _ if lastHole(first) =>
        throw IllegalStateException(
          s"the β step of one hole at ${first.position} has no body step beside it"
        )
      case first :: _ if body(first) =>
        throw IllegalStateException(
          s"the body step at ${first.position} reads a thunk of no hole that no β step beside it left"
        )
      case first :: after => joinedFrom(after, made :+ rewrite(first))
      case Nil            => made
    joinedFrom(steps.map(_.step).toList, Vector.empty)

  /** The reason of a step turned: an abstraction's body steps turned and in
    * reverse order, from the body they made back to the body; any other as it
    * is.
    */
  def reasonTurned[C <: NativeSpecializer & Singleton](
      reason: RewriteReason[C]
  )(using C, StorageAccess): RewriteReason[C] = reason match
    case RewriteReason.Abstraction(eigenvariables, body, steps) =>
      val befores = steps.scanLeft(body)(RewriteTrace.applied)
      val oriented = steps
        .zip(befores)
        .map((step, before) =>
          OrientedStep.of(step, Positions.subterm(before, step.position))
        )
      RewriteReason.Abstraction(
        eigenvariables,
        befores.last,
        joined(oriented.reverse.map(_.turned))
      )
    case other => other

/** The proof of a round flattened into rewrites of the whole term: the tree the
  * article writer builds (`OpentheoryArticle.derivation`), its edges and paths
  * expanded as the writer expands them, read without matching again.
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
  * From the round's input, the steps in order give its output (`applied`), the
  * law the tests check. `trace` keeps of each step what a replay cannot compute
  * (`gezi.rewritetrace.TraceCommand`). It names no lemma and no combinator and
  * holds no type: a step's reason is the equation the proof instantiates, read
  * from the proof.
  */
object RewriteTrace:

  /** The steps of the derivation's proof, from its left term to its right term,
    * each step of the β rule that fills a thunk's last hole joined to the body
    * equation's step beside it (`joined`). Throws `OpentheoryArticleError` as
    * the writer does on an edge it cannot prove.
    */
  def of[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C]
  ): Vector[RewriteStep[C]] =
    given C = derivation.specializer
    given StorageAccess = derivation.access
    OrientedStep.joined(
      flattened(derivation, derivation.proof, Map.empty).result._1
    )

  /** The round of the derivation: its left term, its steps, its right term. */
  def round[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C]
  ): RewriteRound[C] =
    RewriteRound(derivation.left, of(derivation), derivation.right)

  /** The lemmas the derivation's steps name, in the order they first name them,
    * by their identifiers: the lemmas its article imports. Its trace (`trace`)
    * names these and may name more, the lemmas of the unions its values are
    * made by, and keeps them by their sides.
    */
  def lemmas[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C]
  ): Vector[LemmaIdentifier] =
    given C = derivation.specializer
    given StorageAccess = derivation.access
    plan(derivation, derivation.left, of(derivation)).flatMap(lemmasOf).distinct

  /** The trace of the derivation, one round from its left term, which a replay
    * is given (the trace holds no start): each step's command, the replacement,
    * the provenance and the bindings of the replaced side's variables left to
    * the replay; the values the commands name (`gezi.rewritetrace.TraceValue`);
    * and the lemmas the commands name, in the order they first name them, by
    * their sides. Throws `IllegalStateException` when a lemma's statement from
    * its sides (`Statements.lemma`) is not the strategy's encoding of it, which
    * the article states: a replay would then rewrite otherwise than the proof.
    */
  def trace[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C]
  ): Trace[C] =
    given C = derivation.specializer
    given StorageAccess = derivation.access
    val (commands, building) = built(derivation)
    val traced = building.lemmas.map(lemma =>
      val (left, right) = derivation.store.lemmaSides(lemma)
      val traceLemma = TraceLemma(left, right)
      if derivation.store.lemmaStatementSides(
          traceLemma.statement
        ) != derivation.store.axiomStatement(Axiom.Lemma(lemma))
      then
        throw IllegalStateException(
          s"the sides of $lemma state it otherwise than the strategy's encoding"
        )
      traceLemma
    )
    Trace(traced, building.values, Vector(commands))

  /** The commands of the derivation's round and what they name. */
  private def built[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C]
  )(using
      C,
      StorageAccess
  ): (Vector[TraceCommand[C]], TraceBuilding[C]) =
    val origins = ValueOrigins.of(derivation)
    plan(derivation, derivation.left, of(derivation)).foldLeft(
      (Vector.empty[TraceCommand[C]], TraceBuilding.empty[C])
    ) { case ((made, building), planned) =>
      val (command, after) =
        commandOf(derivation, origins, building, planned, 0, Map.empty)
      (made :+ command, after)
    }

  /** A trace as it is written: the lemmas its commands name so far, each at its
    * place, in the order they are first named; its values made so far, each
    * node's term at its value's place (`valuePlaces`); the edges and paths
    * flattened so far; and the terms whose values are being made, to refuse one
    * made from itself.
    */
  private final case class TraceBuilding[C <: NativeSpecializer & Singleton](
      lemmas: Vector[LemmaIdentifier],
      values: Vector[TraceValue[C]],
      valuePlaces: Map[Configured[C], Int],
      expansions: Expansions[C],
      making: Set[Configured[C]]
  ):

    /** The lemma's place, the lemma placed after the others if it has none. */
    def lemmaPlaced(lemma: LemmaIdentifier): (Int, TraceBuilding[C]) =
      lemmas.indexOf(lemma) match
        case -1    => (lemmas.size, copy(lemmas = lemmas :+ lemma))
        case place => (place, this)

    /** The value's place, the value of the term placed after the others. */
    def valuePlaced(
        term: Configured[C],
        value: TraceValue[C]
    ): (Int, TraceBuilding[C]) =
      (
        values.size,
        copy(
          values = values :+ value,
          valuePlaces = valuePlaces.updated(term, values.size)
        )
      )

  private object TraceBuilding:
    def empty[C <: NativeSpecializer & Singleton]: TraceBuilding[C] =
      TraceBuilding(Vector.empty, Vector.empty, Map.empty, Map.empty, Set.empty)

  /** Where the terms of a derivation's proof come from: the position in the
    * round's start of each of its subterms, the first in preorder; the unions
    * that made a node, by that node (`ProofUnion.built`); and the
    * eigenvariables the proof's abstractions open bodies at.
    */
  private final case class ValueOrigins[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      startPaths: Map[Configured[C], Vector[PositionSegment]],
      builtUnions: TreeMap[Int, ProofUnion],
      eigenvariables: Set[Configured[C]],
      madeParents: Map[Int, Vector[(Int, PositionSegment)]],
      startByTree: Map[Int, Configured[C]]
  ):

    /** The root of the node's tree in the proof's forest: two nodes are in one
      * tree when the unions make them equal.
      */
    def treeRoot(node: Int): Int =
      @tailrec
      def climbed(at: Int): Int = derivation.forest.parents.get(at) match
        case Some((parent, _)) => climbed(parent)
        case None              => at
      climbed(node)

    /** The union that made the node of the term, the term it built, the union's
      * other term, and the position of the term in the one built: the union
      * whose made nodes (`ProofUnion.made`) hold the node, found by walking the
      * built term through the nodes the union made. None for a term of no node
      * and for a node no union records making (an input, a node a β conversion
      * made).
      */
    def maker(term: Configured[C])(using
        C,
        StorageAccess
    ): Option[
      (ProofUnion, Configured[C], Configured[C], Vector[PositionSegment])
    ] =
      derivation
        .nodeOf(term)
        .flatMap(node =>
          builtUnions
            .minAfter(node)
            .flatMap((_, union) =>
              union.made
                .filter(made => made.first <= node)
                .flatMap(made =>
                  val other = if made.last == union.second then union.first
                  else union.second
                  ValueOrigins
                    .madePath(
                      derivation.nodeTerm(made.last),
                      term,
                      made.first,
                      derivation
                    )
                    .map(at =>
                      (
                        union,
                        derivation.nodeTerm(made.last),
                        derivation.nodeTerm(other),
                        at
                      )
                    )
                )
            )
        )

  private object ValueOrigins:

    def of[C <: NativeSpecializer & Singleton](
        derivation: ArticleDerivation[C]
    )(using C, StorageAccess): ValueOrigins[C] =
      val forest = derivation.forest
      val terms = derivation.store.terms
      val builtUnions =
        forest.unions.foldLeft(TreeMap.empty[Int, ProofUnion])((found, union) =>
          union.built.fold(found)(node =>
            if found.contains(node) then found else found.updated(node, union)
          )
        )
      val eigenvariables = forest.unions
        .flatMap(_.justification match
          case Justification.Abstraction(opened, _, _) =>
            opened.map(derivation.nodeTerm)
          case _ => Vector.empty)
        .toSet
      val startPaths = subtermPaths(derivation.left)
      // Each node's made layer is over the nodes of its children's terms: the parents of a node are the nodes whose
      // made layer holds it, with the role it has there.
      val madeParents = (0 until terms.nodeCount).foldLeft(
        Map.empty[Int, Vector[(Int, PositionSegment)]]
      ) { (found, parent) =>
        terms.key(terms.nodeTerm(parent)) match
          case TermKey.Layered(layer) =>
            layer.children.zip(Positions.roles(layer)).foldLeft(found) {
              case (current, (child, role)) =>
                terms
                  .node(child)
                  .fold(current)(node =>
                    current.updated(
                      node,
                      current.getOrElse(node, Vector.empty) :+ (parent, role)
                    )
                  )
            }
          case _ => found
      }
      val origins = ValueOrigins(
        derivation,
        startPaths,
        builtUnions,
        eigenvariables,
        madeParents,
        Map.empty
      )
      // A subterm of the start in each tree of the forest, the first in preorder.
      val startByTree = startPaths.toVector
        .sortBy(_._2.size)
        .foldLeft(Map.empty[Int, Configured[C]]) { case (found, (term, _)) =>
          derivation
            .nodeOf(term)
            .fold(found)(node =>
              val root = origins.treeRoot(node)
              if found.contains(root) then found else found.updated(root, term)
            )
        }
      origins.copy(startByTree = startByTree)

    /** The position of each subterm of the term, the first in preorder. A loop
      * over the positions pending: a term is as deep as a program.
      */
    private def subtermPaths[C <: NativeSpecializer & Singleton](
        term: Configured[C]
    )(using C, StorageAccess): Map[Configured[C], Vector[PositionSegment]] =
      @tailrec
      def walked(
          pending: List[(Configured[C], Vector[PositionSegment])],
          found: Map[Configured[C], Vector[PositionSegment]]
      ): Map[Configured[C], Vector[PositionSegment]] =
        pending match
          case Nil                => found
          case (at, path) :: rest =>
            if found.contains(at) then walked(rest, found)
            else if at.opaque then walked(rest, found.updated(at, path))
            else
              val layer = Positions.layerOf(at)
              val below = layer.children
                .zip(Positions.roles(layer))
                .map((child, role) => (child, path :+ role))
                .toList
              walked(below ++ rest, found.updated(at, path))
      walked(List((term, Vector.empty)), Map.empty)

    /** The position of the term in the term built, walking only the nodes the
      * step made, from the first of them on: a node older than the first is one
      * the step was given. A loop over the positions pending.
      */
    def madePath[C <: NativeSpecializer & Singleton](
        built: Configured[C],
        term: Configured[C],
        first: Int,
        derivation: ArticleDerivation[C]
    )(using C, StorageAccess): Option[Vector[PositionSegment]] =
      @tailrec
      def walked(
          pending: List[(Configured[C], Vector[PositionSegment])]
      ): Option[Vector[PositionSegment]] =
        pending match
          case Nil                => None
          case (at, path) :: rest =>
            if Configured.same(at, term) then Some(path)
            else if at.opaque || derivation.nodeOf(at).forall(_ < first) then
              walked(rest)
            else
              val layer = Positions.layerOf(at)
              walked(
                layer.children
                  .zip(Positions.roles(layer))
                  .map((child, role) => (child, path :+ role))
                  .toList ++ rest
              )
      walked(List((built, Vector.empty)))

  /** The value of the term, at its place among the building's values, made if
    * it is not yet, from the first origin that gives one: the term's position
    * in the round's start; the union that made its node (`fromMaker`); a node
    * whose made layer holds it (`fromParent`); a subterm of the start the proof
    * makes equal to it (`fromClassmate`). None for a term that holds an
    * eigenvariable, which no round's start holds, for one no origin gives, and
    * for one whose value would be made from itself.
    */
  private def valueOf[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      origins: ValueOrigins[C],
      building: TraceBuilding[C],
      term: Configured[C]
  )(using C, StorageAccess): Option[(Int, TraceBuilding[C])] =
    building.valuePlaces.get(term) match
      case Some(place) => Some((place, building))
      case None
          if building.making.contains(term) || Conversions.holds(
            term,
            origins.eigenvariables
          ) =>
        None
      case None =>
        origins.startPaths.get(term) match
          case Some(path) =>
            ReplaySpelling.positions(derivation.left, path) match
              case Vector(spelledPath) =>
                Some(
                  building.valuePlaced(
                    term,
                    TraceValue(
                      ValueSource.RoundStart(0),
                      Vector.empty,
                      spelledPath
                    )
                  )
                )
              case _ => None
          case None =>
            fromMaker(derivation, origins, building, term)
              .orElse(fromRedex(derivation, origins, building, term))
              .orElse(fromParent(derivation, origins, building, term))
              .orElse(fromClassmate(derivation, origins, building, term))

  /** The value of the term made from the union that made its node
    * (`ValueOrigins.maker`): the commands of the union replayed from its other
    * term, whose value is made first, and the term's position in the term the
    * union built.
    */
  private def fromMaker[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      origins: ValueOrigins[C],
      building: TraceBuilding[C],
      term: Configured[C]
  )(using C, StorageAccess): Option[(Int, TraceBuilding[C])] =
    origins
      .maker(term)
      .flatMap((union, built, other, at) =>
        valueOf(
          derivation,
          origins,
          building.copy(making = building.making + term),
          other
        ).flatMap((source, afterSource) =>
          ReplaySpelling.positions(built, at) match
            case Vector(spelledAt) =>
              val edge = ArticleProof.Edge(union.index)
              val oriented =
                if Configured.same(built, derivation.nodeTerm(union.second))
                then edge
                else ArticleProof.Symmetry(edge)
              val (steps, expansions) =
                flattened(derivation, oriented, afterSource.expansions).result
              val (commands, afterCommands) =
                plan(derivation, other, OrientedStep.joined(steps))
                  .foldLeft(
                    (
                      Vector.empty[TraceCommand[C]],
                      afterSource.copy(expansions = expansions)
                    )
                  ) { case ((made, current), planned) =>
                    val (command, after) = commandOf(
                      derivation,
                      origins,
                      current,
                      planned,
                      0,
                      Map.empty
                    )
                    (made :+ command, after)
                  }
              Some(
                afterCommands
                  .copy(making = afterCommands.making - term)
                  .valuePlaced(
                    term,
                    TraceValue(ValueSource.Value(source), commands, spelledAt)
                  )
              )
            // The replay's spelling drops or copies the term (`ReplaySpelling.positions`).
            case _ => None
        )
      )

  /** The value of the term as the redex of a root reverse β of a subterm of the
    * start the proof makes equal to it, over the names a lemma's left side
    * applies a metavariable to (`Conversions.redex`): the conversion from that
    * subterm, as the strategy that added the redex as an input made it
    * (`gezi.strategies.HigherOrderSaturator`'s root case). Its abstraction is
    * no term the start holds, and the path of unions between the two crosses
    * the β rule backward, which needs that abstraction.
    */
  private def fromRedex[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      origins: ValueOrigins[C],
      building: TraceBuilding[C],
      term: Configured[C]
  )(using C, StorageAccess): Option[(Int, TraceBuilding[C])] =
    derivation
      .nodeOf(term)
      .flatMap(node => origins.startByTree.get(origins.treeRoot(node)))
      .filterNot(Configured.same(_, term))
      .flatMap(classmate =>
        val spelledTerm = ReplaySpelling.term(term)
        val spelledClassmate = ReplaySpelling.term(classmate)
        derivation.store.encodedLemmas
          .find(lemma =>
            val (left, right) = derivation.store.lemmaSides(lemma)
            Conversions
              .names(TraceLemma(left, right).statement)
              .exists(names =>
                Conversions.appliedToNames(spelledTerm, names) && Configured
                  .same(Conversions.redex(spelledClassmate, names), spelledTerm)
              )
          )
          .flatMap(lemma =>
            valueOf(
              derivation,
              origins,
              building.copy(making = building.making + term),
              classmate
            ).map((source, afterSource) =>
              val converted = Converted[C](
                lemma,
                Conversion.RootReverseBeta(_),
                Vector.empty,
                RewriteDirection.Forward,
                Vector.empty
              )
              val (command, afterCommand) = commandOf(
                derivation,
                origins,
                afterSource,
                Planned.Converted(converted),
                0,
                Map.empty
              )
              afterCommand
                .copy(making = afterCommand.making - term)
                .valuePlaced(
                  term,
                  TraceValue(
                    ValueSource.Value(source),
                    Vector(command),
                    Vector.empty
                  )
                )
            )
          )
      )

  /** The value of the term from a node whose made layer holds it, whose value
    * is made first, and the term's position in that node's term: a node no
    * union records making, made with a larger term that has a value (a reverse
    * β redex a strategy adds as an input, say).
    */
  private def fromParent[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      origins: ValueOrigins[C],
      building: TraceBuilding[C],
      term: Configured[C]
  )(using C, StorageAccess): Option[(Int, TraceBuilding[C])] =
    @tailrec
    def first(
        parents: List[(Int, PositionSegment)]
    ): Option[(Int, TraceBuilding[C])] = parents match
      case Nil                    => None
      case (parent, role) :: rest =>
        val parentTerm = derivation.nodeTerm(parent)
        val made =
          valueOf(
            derivation,
            origins,
            building.copy(making = building.making + term),
            parentTerm
          ).flatMap((place, after) =>
            ReplaySpelling.positions(parentTerm, Vector(role)) match
              case Vector(spelled) =>
                Some(
                  after
                    .copy(making = after.making - term)
                    .valuePlaced(
                      term,
                      TraceValue(
                        ValueSource.Value(place),
                        Vector.empty,
                        spelled
                      )
                    )
                )
              case _ => None
          )
        made match
          case Some(_) => made
          case None    => first(rest)
    derivation
      .nodeOf(term)
      .fold(None)(node =>
        first(origins.madeParents.getOrElse(node, Vector.empty).toList)
      )

  /** The value of the term from a subterm of the start the proof makes equal to
    * it: the steps of the path between them in the forest
    * (`ArticleProof.Connection`) replayed from the start's subterm. A term a
    * round adds as an input, which no union made and no larger term holds.
    */
  private def fromClassmate[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      origins: ValueOrigins[C],
      building: TraceBuilding[C],
      term: Configured[C]
  )(using C, StorageAccess): Option[(Int, TraceBuilding[C])] =
    derivation
      .nodeOf(term)
      .flatMap(node =>
        origins.startByTree.get(origins.treeRoot(node)).map(_ -> node)
      )
      .flatMap((classmate, node) =>
        derivation
          .nodeOf(classmate)
          .filterNot(_ == node)
          .flatMap(classmateNode =>
            valueOf(
              derivation,
              origins,
              building.copy(making = building.making + term),
              classmate
            ).map((source, afterSource) =>
              val connection = ArticleProof.Connection(
                derivation.store.terms.nodeTerm(classmateNode),
                derivation.store.terms.nodeTerm(node)
              )
              val (steps, expansions) =
                flattened(derivation, connection, afterSource.expansions).result
              val (commands, afterCommands) =
                plan(derivation, classmate, OrientedStep.joined(steps))
                  .foldLeft(
                    (
                      Vector.empty[TraceCommand[C]],
                      afterSource.copy(expansions = expansions)
                    )
                  ) { case ((made, current), planned) =>
                    val (command, after) = commandOf(
                      derivation,
                      origins,
                      current,
                      planned,
                      0,
                      Map.empty
                    )
                    (made :+ command, after)
                  }
              afterCommands
                .copy(making = afterCommands.making - term)
                .valuePlaced(
                  term,
                  TraceValue(ValueSource.Value(source), commands, Vector.empty)
                )
            )
          )
      )

  /** A step as the trace will keep it, before the lemmas have their places: a
    * proved step; a β conversion with no proof, as the conversion of a lemma it
    * instantiates; or the abstraction rule, as the steps of the body it opened.
    */
  private enum Planned[C <: NativeSpecializer & Singleton]:
    case Proved(step: RewriteStep[C])
    case Native(position: Vector[PositionSegment], value: Configured[C])
    case Converted(found: RewriteTrace.Converted[C])
    case Abstracted(
        position: Vector[PositionSegment],
        eigenvariables: Vector[Configured[C]],
        steps: Vector[Planned[C]]
    )

  /** The plan of the steps from the term, in the replay's spelling
    * (`ReplaySpelling`), the spelling the replay works in: a step whose
    * replaced subterm and replacement have one spelling, a respelling
    * (`Axiom.Respell`) above all, has no command, since the replay holds its
    * two sides as one term; every other step keeps its reason, its position
    * translated into the spelled term (`ReplaySpelling.positions`); the β
    * rule's step of a thunk's last hole is already joined to the body step
    * beside it (`joined`). Two steps side by side that are an identity together
    * in that spelling have no command either (`detoursDropped`). Throws
    * `IllegalStateException` when no conversion computes a β conversion's step,
    * when a step's subterm is at other than one position of the spelled term,
    * and when the replay of an abstraction would open or write back another
    * term than the proof's (the body the closure opens to is not the body's
    * spelling the steps start from, or the body they make written back is not
    * the thunk): the trace would replay otherwise than the proof.
    */
  private def plan[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      start: Configured[C],
      steps: Vector[RewriteStep[C]]
  )(using C, StorageAccess): Vector[Planned[C]] =
    // The term before each step is kept as a spine (`Spine`): a step rebuilds only the path to its position and
    // builds only the subterm it reads. A step costs the depth of
    // its position (`subterm`, `replaced`, `spelledPositions`: one child taken and one `Vector.updated` per segment; a
    // node turns from settled to rebuilt once, `Layer.map` over its children), plus the size of the subterm it replaces
    // and of its replacement not yet spelled (`materialized` builds the rebuilt nodes in that subterm only; the
    // spellings, `Spellings`, keep each term's spelling), plus the size of the code of each kind of thunk the
    // flattening meets for the first time. A layer the step only passes through is not hashed.
    val (spelled, _, _) = steps.foldLeft(
      (
        Vector.empty[SpelledStep[C]],
        Spine.Settled(start): Spine[C],
        Spellings.empty[C]
      )
    ) { case ((found, before, known), step) =>
      val replaced = Spine.materialized(Spine.subterm(before, step.position))
      // The replay works in the replay's spelling (`ReplaySpelling`): a step that is an identity there (a
      // respelling) has no command, and every other step's position is the position of its subterm in that
      // spelling of the term.
      val (spelledReplaced, afterReplaced) = known.term(replaced)
      val (spelledReplacement, afterReplacement) =
        afterReplaced.term(step.replacement)
      val (kept, knownAfter) =
        if Configured.same(spelledReplaced, spelledReplacement) then
          (None, afterReplacement)
        else
          val (positions, knownAfter) =
            Spine.spelledPositions(before, step.position, afterReplacement)
          val position = positions match
            case Vector(only) => only
            case _            =>
              throw IllegalStateException(
                s"the subterm at ${step.position} is at ${positions.size} positions of the term's replay spelling"
              )
          (
            Some(
              SpelledStep(
                step.copy(position = position),
                replaced,
                spelledReplaced,
                spelledReplacement
              )
            ),
            knownAfter
          )
      (
        found ++ kept,
        Spine.replaced(before, step.position, step.replacement),
        knownAfter
      )
    }
    detoursDropped(spelled).map(kept =>
      planned(
        derivation,
        kept.step,
        kept.replaced,
        kept.spelledReplaced,
        kept.spelledReplacement
      )
    )

  /** A step that is no identity in the replay's spelling: the step with its
    * position in that spelling, the subterm it replaces, and its two sides in
    * that spelling.
    */
  private final case class SpelledStep[C <: NativeSpecializer & Singleton](
      step: RewriteStep[C],
      replaced: Configured[C],
      spelledReplaced: Configured[C],
      spelledReplacement: Configured[C]
  )

  /** The steps without each two side by side at one position of which the
    * second puts back, in the replay's spelling, the subterm the first
    * replaced: together they are an identity in that spelling, as a respelling
    * alone is, and the replay holds the term before them as the term after
    * them. Dropping a pair may put two others side by side, which are dropped
    * in turn. Measured 2026-11-16 on the entry `wren`'s
    * inlined_calls_10000_hot/direct first point: 4 pairs of a higher-order
    * conversion forward and backward, the backward one writing a binding of
    * about 420,000 characters, 1.77 million of the trace's 3.5 million.
    */
  private def detoursDropped[C <: NativeSpecializer & Singleton](
      steps: Vector[SpelledStep[C]]
  )(using C): Vector[SpelledStep[C]] =
    steps
      .foldLeft(List.empty[SpelledStep[C]]) { (kept, step) =>
        kept match
          case last :: earlier
              if last.step.position == step.step.position && Configured.same(
                last.spelledReplaced,
                step.spelledReplacement
              ) &&
                Configured.same(
                  last.spelledReplacement,
                  step.spelledReplaced
                ) =>
            earlier
          case _ => step :: kept
      }
      .reverse
      .toVector

  /** The plan of a step that is no identity in the replay's spelling, its
    * position already in that spelling.
    */
  private def planned[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      step: RewriteStep[C],
      replaced: Configured[C],
      spelledReplaced: Configured[C],
      spelledReplacement: Configured[C]
  )(using C, StorageAccess): Planned[C] =
    step.reason match
      case RewriteReason.Unproved(kind) =>
        etaStep(step, spelledReplaced, spelledReplacement).filter(_ =>
          kind == UnprovedKind.BetaConversion
        ) match
          case Some(eta) => Planned.Proved(eta)
          case None      =>
            Planned.Converted(
              conversion(
                derivation,
                kind,
                step.copy(replacement = spelledReplacement),
                spelledReplaced
              )
            )
      case RewriteReason.Abstraction(eigenvariables, body, inner) =>
        val opened = Conversions.opened(replaced, eigenvariables)
        if !Configured.same(opened, body) then
          throw IllegalStateException(
            s"the closure $replaced opens to $opened, not to the body $body its steps start from"
          )
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
        if !Configured.same(written, step.replacement) then
          throw IllegalStateException(
            s"the body ${spelled(made)} written back is ${spelled(written)} (${layerShown(written)}), " +
              s"not the thunk ${spelled(step.replacement)} (${layerShown(step.replacement)}), ${step.direction}; " +
              s"${inner.size} steps from ${spelled(body)}, eigenvariables $eigenvariables, " +
              s"the thunk opens to ${scala.util.Try(spelled(Conversions.opened(step.replacement, eigenvariables)))}; " +
              s"steps ${inner.map(inner =>
                  (inner.reason.getClass.getSimpleName, inner.position, inner.direction, spelled(inner.replacement))
                )}"
          )
        Planned.Abstracted(
          step.position,
          eigenvariables,
          plan(derivation, body, inner)
        )
      case RewriteReason.Native(_, _, _) =>
        Planned.Native(step.position, spelledReplacement)
      case _ => Planned.Proved(step)

  /** The text of a term for a message, a storage written as its view. */
  private def spelled[C <: NativeSpecializer & Singleton](
      term: Configured[C]
  )(using C, StorageAccess): String =
    scala.util
      .Try(gezi.frontend.Lambdalattice.closedTextViewed(term))
      .getOrElse(term.toString)

  /** Where two codes differ, for a message: every minimal differing pair, found
    * by descending into each differing child of two codes of one shape, at most
    * `limit` of them, each with its path of child indices (an application's
    * function 0 and argument 1, a choice's or a parallel's sides 0 and 1, a
    * thunk's code 0 and its fillings from 1).
    */
  private def codeDifferences(
      left: Code,
      right: Code,
      path: Vector[Int],
      limit: Int
  ): Vector[(Vector[Int], CodeLayer[Code], CodeLayer[Code])] =
    if left == right || limit <= 0 then Vector.empty
    else
      val (leftParts, rightParts) =
        (codeParts(left.layer), codeParts(right.layer))
      if codeShape(left.layer) != codeShape(
          right.layer
        ) || leftParts.size != rightParts.size
      then Vector((path, left.layer, right.layer))
      else
        leftParts
          .zip(rightParts)
          .zipWithIndex
          .foldLeft(
            Vector.empty[(Vector[Int], CodeLayer[Code], CodeLayer[Code])]
          ) { case (found, ((own, other), index)) =>
            found ++ codeDifferences(
              own,
              other,
              path :+ index,
              limit - found.size
            )
          }

  private def codeParts(layer: CodeLayer[Code]): Vector[Code] = layer match
    case Slot(_)                       => Vector.empty
    case Apply(function, argument)     => Vector(function, argument)
    case Parallel(leftSide, rightSide) => Vector(leftSide, rightSide)
    case Choice(leftSide, rightSide)   => Vector(leftSide, rightSide)
    case Thunk(code, _, fillings)      => code +: fillings

  /** A code as text, for a message: a slot `s<index>`, an application in
    * parentheses, a choice `+`, a parallel `∥`, and an inner thunk
    * `λ<holes>[<fillings>]. <code>`.
    */
  private def codeText(code: Code): String = codeLayerText(code.layer)

  private def codeLayerText(layer: CodeLayer[Code]): String = layer match
    case Slot(index)               => s"s$index"
    case Apply(function, argument) =>
      s"(${codeText(function)} ${codeText(argument)})"
    case Parallel(left, right) => s"(${codeText(left)} ∥ ${codeText(right)})"
    case Choice(left, right)   => s"(${codeText(right)} + ${codeText(left)})"
    case Thunk(inner, holes, fillings) =>
      s"λ${holes.mkString(",")}[${fillings.map(codeText).mkString(", ")}]. ${codeText(inner)}"

  private def codeShape(layer: CodeLayer[Code]): String = layer match
    case Thunk(_, holes, fillings) => s"thunk $holes ${fillings.size}"
    case Slot(index)               => s"slot $index"
    case Apply(_, _)               => "apply"
    case Parallel(_, _)            => "parallel"
    case Choice(_, _)              => "choice"

  /** The layer of a term for a message, or the term itself when it is opaque.
    */
  private def layerShown[C <: NativeSpecializer & Singleton](
      term: Configured[C]
  )(using C): String =
    if term.opaque then term.toString else term.layer.toString

  /** The step of the defunctionalized η rule that a β conversion with no proof
    * is: the replaced term and the replacement differ at one position only,
    * where one is the η-shaped thunk `λx. f x` over the other, f. A
    * higher-order conversion backward that only η-expands a filling has a
    * replaced term that does not determine its binding (K := f and K := λx. f x
    * have one normal form), while the η rule's step needs none (the reading of
    * the entry `wren`'s inlined hot point, 2026-11-17). None for any other
    * pair.
    */
  private def etaStep[C <: NativeSpecializer & Singleton](
      step: RewriteStep[C],
      replaced: Configured[C],
      replacement: Configured[C]
  )(using
      C,
      StorageAccess
  ): Option[RewriteStep[C]] =
    val (at, from, to) = difference(replaced, replacement, Vector.empty)
    def etaOver(
        thunk: Configured[C],
        filling: Configured[C]
    ): Option[RewriteReason[C]] = thunk.layer match
      case Thunk(code, holes, fillings @ Vector(only))
          if Statements
            .etaShaped(code, holes) && Configured.same(only, filling) =>
        Some(RewriteReason.Eta(code, holes, fillings))
      case _ => None
    val elsewhereEqual =
      Configured.same(Positions.replaced(replaced, at, to), replacement)
    val bare = Vector(Vector.empty[PositionSegment])
    val underThunk = Vector(Vector(PositionSegment.Filling(0)))
    if !elsewhereEqual then None
    else
      etaOver(to, from)
        .map(reason =>
          RewriteStep(
            reason,
            step.position ++ at,
            RewriteDirection.Backward,
            to,
            Vector(Provenance("filling0", bare, underThunk))
          )
        )
        .orElse(
          etaOver(from, to).map(reason =>
            RewriteStep(
              reason,
              step.position ++ at,
              RewriteDirection.Forward,
              to,
              Vector(Provenance("filling0", underThunk, bare))
            )
          )
        )

  private def difference[C <: NativeSpecializer & Singleton](
      left: Configured[C],
      right: Configured[C],
      position: Vector[PositionSegment]
  )(using
      C,
      StorageAccess
  ): (Vector[PositionSegment], Configured[C], Configured[C]) =
    if left.opaque || right.opaque then (position, left, right)
    else
      val (leftLayer, rightLayer) =
        (Positions.layerOf(left), Positions.layerOf(right))
      val differing = leftLayer.children
        .zip(rightLayer.children)
        .zip(Positions.roles(leftLayer))
        .filter { case ((leftChild, rightChild), _) =>
          !Configured.same(leftChild, rightChild)
        }
      differing match
        case Vector(((leftChild, rightChild), role))
            if LayerShape.of(leftLayer) == LayerShape.of(
              rightLayer
            ) && leftLayer.children.size == rightLayer.children.size =>
          difference(leftChild, rightChild, position :+ role)
        case _ => (position, left, right)

  private def lemmasOf[C <: NativeSpecializer & Singleton](
      planned: Planned[C]
  ): Vector[LemmaIdentifier] = planned match
    case Planned.Proved(
          RewriteStep(RewriteReason.Lemma(lemma, _), _, _, _, _)
        ) =>
      Vector(lemma)
    case Planned.Proved(_)               => Vector.empty
    case Planned.Native(_, _)            => Vector.empty
    case Planned.Converted(found)        => Vector(found.lemma)
    case Planned.Abstracted(_, _, steps) => steps.flatMap(lemmasOf)

  /** The command of a planned step under `depth` openings, each eigenvariable
    * of an enclosing opening renamed to the replay's
    * (`Conversions.eigenvariables`) in every term it writes, and the building
    * with the lemmas and the values it names. A term the command gives is named
    * by its value (`valueOf`), or written where it holds an eigenvariable or
    * has no value (`gezi.rewritetrace.Given`, its FIXME).
    * https://github.com/Atry/private-overlay/issues/1980
    */
  private def commandOf[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      origins: ValueOrigins[C],
      building: TraceBuilding[C],
      planned: Planned[C],
      depth: Int,
      renamed: Map[Configured[C], Configured[C]]
  )(using
      specializer: C,
      access: StorageAccess
  ): (TraceCommand[C], TraceBuilding[C]) =
    def giving(
        current: TraceBuilding[C],
        term: Configured[C]
    ): (Given[C], TraceBuilding[C]) =
      val named =
        if renamed.nonEmpty && Conversions.holds(term, renamed.keySet) then None
        else valueOf(derivation, origins, current, term)
      named match
        case Some((place, after)) => (Given.Value(place), after)
        case None                 =>
          (
            Given.Written(
              Conversions.leavesReplaced(ReplaySpelling.term(term), renamed)
            ),
            current
          )
    def bindingsGiven(
        current: TraceBuilding[C],
        bindings: Vector[(Int, Configured[C])]
    ): (Vector[(Int, Given[C])], TraceBuilding[C]) =
      bindings.foldLeft((Vector.empty[(Int, Given[C])], current)) {
        case ((made, before), (place, term)) =>
          val (named, after) = giving(before, term)
          (made :+ (place, named), after)
      }
    // The thunk of a step backward of the β rule or the η rule (`ThunkShape`): the replay reads only the code and
    // holes of its spelling, its fillings being the equation's variables. The step's own thunk is often no node of the
    // proof: the β rule of a function of several arguments fills one hole at a time, and the e-graph makes no node for
    // the thunks between (`Saturation.betaWorked` extends the closure state). So a thunk of the proof with the code
    // names the code, and the holes are written.
    def thunkGiven(
        current: TraceBuilding[C],
        thunk: Option[Configured[C]]
    ): (Option[ThunkShape[C]], TraceBuilding[C]) =
      // The first of the candidates that has a value, tried in order; a loop, since thousands of a program's
      // thunks may share a code and have none.
      @tailrec
      def firstValue(
          candidates: Vector[Configured[C]]
      ): Option[(Int, TraceBuilding[C])] =
        candidates.headOption match
          case None            => None
          case Some(candidate) =>
            valueOf(derivation, origins, current, candidate) match
              case found @ Some(_) => found
              case None            => firstValue(candidates.tail)
      thunk.fold((None, current))(term =>
        val spelling = ReplaySpelling.term(term)
        spelling.layer match
          case Thunk(code, holes, _) =>
            val sameCode = derivation.forest.thunks.toVector
              .collect { case ((found, _), nodes) if found == code => nodes }
              .flatten
              .map(derivation.term)
            val candidates = (Vector(term, spelling) ++ sameCode)
              .foldLeft(Vector.empty[Configured[C]])((kept, candidate) =>
                if kept.exists(Configured.same(_, candidate)) then kept
                else kept :+ candidate
              )
            val named =
              if renamed.nonEmpty && Conversions.holds(term, renamed.keySet)
              then None
              else firstValue(candidates)
            named match
              case Some((place, after)) =>
                (Some(ThunkShape(Given.Value(place), holes)), after)
              case None =>
                giving(current, term) match {
                  case (named, after) => (Some(ThunkShape(named, holes)), after)
                }
          case other =>
            throw IllegalStateException(
              s"the thunk of a step is no thunk: $other"
            )
      )
    planned match
      case Planned.Proved(step) =>
        val (reason, bindings) = proved(derivation, step)
        val (reasonGiven, afterReason) = reason match
          case ReasonDraft.Lemma(lemma) =>
            building.lemmaPlaced(lemma) match {
              case (place, after) => (ProvedReason.Lemma[C](place), after)
            }
          case ReasonDraft.Equation(number) =>
            (ProvedReason.Equation[C](number), building)
          case ReasonDraft.Fill(thunk) =>
            thunkGiven(building, thunk) match {
              case (named, after) => (ProvedReason.Fill(named), after)
            }
          case ReasonDraft.Eta(thunk) =>
            thunkGiven(building, thunk) match {
              case (named, after) => (ProvedReason.Eta(named), after)
            }
        val (bindingsNamed, afterBindings) =
          bindingsGiven(afterReason, bindings)
        (
          TraceCommand.Rewrite(
            reasonGiven,
            step.position,
            step.direction,
            bindingsNamed
          ),
          afterBindings
        )
      case Planned.Native(position, value) =>
        (TraceCommand.Native(position, value), building)
      case Planned.Converted(found) =>
        val (place, afterLemma) = building.lemmaPlaced(found.lemma)
        val (bindingsNamed, afterBindings) =
          bindingsGiven(afterLemma, found.bindings)
        (
          TraceCommand.Convert(
            found.conversion(place),
            found.position,
            found.direction,
            bindingsNamed
          ),
          afterBindings
        )
      case Planned.Abstracted(position, eigenvariables, steps) =>
        val inner = renamed ++ eigenvariables.zip(
          Conversions.eigenvariables(depth, eigenvariables.size)
        )
        val (commands, after) =
          steps.foldLeft((Vector.empty[TraceCommand[C]], building)) {
            case ((made, current), step) =>
              val (command, next) =
                commandOf(derivation, origins, current, step, depth + 1, inner)
              (made :+ command, next)
          }
        (
          TraceCommand.Abstraction(position, eigenvariables.size, commands),
          after
        )

  /** The reason of a proved step's command before the trace places its lemma
    * and gives its thunk (`commandOf`): a step backward of the β rule or the η
    * rule its thunk, built through the configuration. A body step has none: it
    * is joined to its β step (`OrientedStep.joined`).
    */
  private enum ReasonDraft[C <: NativeSpecializer & Singleton]:
    case Lemma(lemma: LemmaIdentifier)
    case Equation(number: Int)
    case Fill(thunk: Option[Configured[C]])
    case Eta(thunk: Option[Configured[C]])

  /** A step of no proof as a conversion of a lemma (`Conversion`), its place in
    * the trace's lemmas not yet known.
    */
  private final case class Converted[C <: NativeSpecializer & Singleton](
      lemma: LemmaIdentifier,
      conversion: Int => Conversion,
      position: Vector[PositionSegment],
      direction: RewriteDirection,
      bindings: Vector[(Int, Configured[C])]
  )

  /** The conversion a step of no proof instantiates: the first, over the
    * strategy's lemmas in order and each lemma's conversions, whose equation
    * computes the step's replacement from its replaced subterm, forward or
    * backward. Throws `IllegalStateException` when none does.
    */
  private def conversion[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      kind: UnprovedKind,
      step: RewriteStep[C],
      replaced: Configured[C]
  )(using C, StorageAccess): Converted[C] = kind match
    // FIXME (2026-11-13): the abstraction rule of a body written back has https://github.com/Atry/private-overlay/issues/2046
    // no command yet, so a round whose proof crosses one has no trace. Candidate
    // fix: a nested
    // command that opens the thunk at its position with eigenvariables,
    // replays the body's commands and writes the body back as the front end
    // spells the lambda; its certificate needs extensionality (Lean
    // `Derivable.extensional`, 40b55dd8a).
    case UnprovedKind.Abstraction =>
      throw IllegalStateException(
        s"the abstraction rule at ${step.position} has no command of the trace"
      )
    case UnprovedKind.BetaConversion =>
      derivation.store.encodedLemmas
        .to(LazyList)
        .flatMap(lemma =>
          conversions(
            derivation,
            lemma,
            step.position,
            replaced,
            step.replacement
          )
        )
        .headOption
        .getOrElse {
          val (at, from, to) =
            difference(replaced, step.replacement, Vector.empty)
          throw IllegalStateException(
            s"no conversion of a lemma takes $replaced to ${step.replacement} at ${step.position}, " +
              s"${step.direction}; they first differ at $at: ${layerShown(from)} against ${layerShown(to)}, " +
              s"spelled ${spelled(from)} against ${spelled(to)}; the higher-order conversions tried: " +
              attempts(derivation, replaced, step.replacement).mkString(" | ")
          )
        }

  private def conversions[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      lemma: LemmaIdentifier,
      position: Vector[PositionSegment],
      replaced: Configured[C],
      replacement: Configured[C]
  )(using C, StorageAccess): LazyList[Converted[C]] =
    val (left, right) = derivation.store.lemmaSides(lemma)
    val statement = TraceLemma(left, right).statement
    val higherOrderVariables = Conversions.higherOrder(statement)
    val higherOrder = LemmaSide.values
      .to(LazyList)
      .flatMap(side =>
        Conversions
          .thunkPatterns(Conversions.sideOf(statement, side))
          .zipWithIndex
          .to(LazyList)
          .flatMap((pattern, occurrence) =>
            val conversion =
              (place: Int) => Conversion.HigherOrder(place, side, occurrence)
            val forward = Conversions
              .instanceBindings(pattern, replaced)
              .filter(bound =>
                Configured.same(
                  Conversions.normalForm(pattern, bound, higherOrderVariables),
                  replacement
                )
              )
              .map(_ =>
                Converted[C](
                  lemma,
                  conversion,
                  position,
                  RewriteDirection.Forward,
                  Vector.empty
                )
              )
            // A left side's conversion backward writes no binding: the replay
            // solves the pattern on the replaced term (`Conversions.expansionSolutions`),
            // so the candidate stands only where that solution is the one and
            // gives this replacement.
            val backward = Conversions
              .instanceBindings(pattern, replacement)
              .filter(bound =>
                Conversions.spelledAlike(
                  Conversions.normalForm(pattern, bound, higherOrderVariables),
                  replaced
                )
              )
              .filter(_ =>
                side match
                  case LemmaSide.Left =>
                    Conversions
                      .expansionSolutions(
                        pattern,
                        replaced,
                        higherOrderVariables
                      )
                      .map(Conversions.instance(pattern, _)) match
                      case Vector(only) => Configured.same(only, replacement)
                      case _            => false
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
                    case LemmaSide.Right =>
                      Statements
                        .variables(pattern)
                        .distinct
                        .zipWithIndex
                        .map((name, place) => (place, bound(name)))
                )
              )
            forward.to(LazyList) ++ backward.to(LazyList)
          )
      )
    val rootReversed = Conversions
      .names(statement)
      .to(LazyList)
      .flatMap(names =>
        val conversion = (place: Int) => Conversion.RootReverseBeta(place)
        // A redex is applied to the names (`Conversions.appliedToNames`), checked before the abstraction of the
        // whole other side is computed: on the entry `solo`'s repeated_library_hotspots calls_1000 point that
        // abstraction, made for each step of no proof and each lemma, was half the flattening.
        Option
          .when(
            Conversions.appliedToNames(replacement, names) && Configured
              .same(Conversions.redex(replaced, names), replacement)
          )(
            Converted[C](
              lemma,
              conversion,
              position,
              RewriteDirection.Forward,
              Vector.empty
            )
          )
          .to(LazyList) ++ Option
          .when(
            Conversions.appliedToNames(replaced, names) && Configured
              .same(Conversions.redex(replacement, names), replaced)
          )(
            Converted[C](
              lemma,
              conversion,
              position,
              RewriteDirection.Backward,
              Vector.empty
            )
          )
          .to(LazyList)
      )
    higherOrder ++ rootReversed

  /** For a message: each higher-order conversion `conversions` tries, by lemma,
    * side and occurrence, and why it does not take the replaced subterm to the
    * replacement either way: the thunk pattern matches neither, or its normal
    * form differs from the other side, with the higher-order variables' values
    * and where they first differ (`difference`).
    */
  private def attempts[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      replaced: Configured[C],
      replacement: Configured[C]
  )(using C, StorageAccess): Vector[String] =
    def tried(
        pattern: StatementTerm[Configured[C]],
        higherOrderVariables: Set[String],
        from: Configured[C],
        to: Configured[C],
        direction: RewriteDirection
    ): String =
      Statements.matchedBindings(pattern, from) match
        case None        => "no match"
        case Some(bound) =>
          val normal =
            Conversions.normalForm(pattern, bound, higherOrderVariables)
          val converts = direction match
            case RewriteDirection.Forward  => Configured.same(normal, to)
            case RewriteDirection.Backward =>
              Conversions.spelledAlike(normal, to)
          if converts then "converts"
          else
            val (at, mine, theirs) = difference(normal, to, Vector.empty)
            val codes = (mine.opaque, theirs.opaque) match
              case (false, false) =>
                (mine.layer, theirs.layer) match
                  case (Thunk(ownCode, _, _), Thunk(otherCode, _, _)) =>
                    val found =
                      codeDifferences(ownCode, otherCode, Vector.empty, 6)
                    s"; the codes differ at ${found.size} minimal places (at most 6 shown): " +
                      found
                        .map((path, ownPart, otherPart) =>
                          s"at $path ${codeLayerText(ownPart)} against ${codeLayerText(otherPart)}"
                        )
                        .mkString("; ")
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
        Conversions
          .thunkPatterns(Conversions.sideOf(statement, side))
          .zipWithIndex
          .map((pattern, occurrence) =>
            s"$lemma $side $occurrence: forward " +
              s"${tried(pattern, higherOrderVariables, replaced, replacement, RewriteDirection.Forward)}; " +
              s"backward ${tried(pattern, higherOrderVariables, replacement, replaced, RewriteDirection.Backward)}"
          )
      )
    }

  private def proved[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      step: RewriteStep[C]
  )(using
      specializer: C,
      access: StorageAccess
  ): (ReasonDraft[C], Vector[(Int, Configured[C])]) =
    // The thunk of a step backward, built through the configuration: a thunk of the β rule and of the η rule has holes.
    def backward(
        code: Code,
        holes: Vector[Hole],
        fillings: Vector[Configured[C]]
    ): Option[Configured[C]] =
      Option.when(step.direction == RewriteDirection.Backward)(
        specializer.thunk(
          code,
          NonEmptyHoles
            .of(holes)
            .getOrElse(
              throw IllegalStateException(
                s"a thunk of the code $code with no hole is no term"
              )
            ),
          fillings
        )
      )
    val reason: ReasonDraft[C] = step.reason match
      case RewriteReason.Lemma(lemma, _)     => ReasonDraft.Lemma(lemma)
      case RewriteReason.Equation(number, _) => ReasonDraft.Equation(number)
      case RewriteReason.Fill(code, holes, fillings, _) =>
        ReasonDraft.Fill(backward(code, holes, fillings))
      case RewriteReason.Body(code, _) =>
        throw IllegalStateException(
          s"the body step of the code $code is joined to its β step and has no command of its own"
        )
      // A step backward whose thunk is the front end's `λx. f x` writes none:
      // the replay spells it over the replaced f (`Conversions.etaExpanded`).
      case RewriteReason.Eta(code, holes, fillings) =>
        val canonical = fillings match
          case Vector(filling) =>
            Conversions.etaExpanded(filling).layer match
              case Thunk(canonicalCode, canonicalHoles, _) =>
                canonicalCode == code && canonicalHoles == holes
              case _ => false
          case _ => false
        ReasonDraft.Eta(if canonical then None
        else backward(code, holes, fillings))
      case RewriteReason.Respell(_, _, _) =>
        throw IllegalArgumentException(
          "a respelling is an identity in the replay's spelling and has no command (ReplaySpelling)"
        )
      case RewriteReason.Unproved(kind) =>
        throw IllegalArgumentException(s"a step of $kind has no proof")
      case RewriteReason.Abstraction(_, _, _) =>
        throw IllegalArgumentException("the abstraction rule has no proof")
      case RewriteReason.Native(native, _, _) =>
        throw IllegalArgumentException(
          s"the fold of the native $native is planned as a native value (`Planned.Native`), not proved"
        )
    // The β rule of a thunk's one hole is replayed together with the body equation that follows it (`joined`).
    val equation: Statement[Any] = step.reason match
      case RewriteReason.Fill(code, holes @ Vector(_), _, _) =>
        Statements.betaBody(code, holes)
      case _ => statement(derivation, step.reason)
    val (replacedSide, _) = equation.oriented(step.direction)
    val held = Statements.variables(replacedSide).toSet
    val bound = this.bound(step.reason)
    val bindings = equation.variables.zipWithIndex.collect {
      case (name, place) if !held.contains(name) =>
        (
          place,
          bound.getOrElse(
            name,
            throw IllegalStateException(s"the step binds no $name")
          )
        )
    }
    (reason, bindings)

  /** The steps an edge or a path expanded to, each expansion flattened once: a
    * union's edge recurs in the paths that cross it.
    */
  private type Expansions[C <: NativeSpecializer & Singleton] =
    Map[ArticleProof, Vector[OrientedStep[C]]]

  private def flattened[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      proof: ArticleProof,
      expansions: Expansions[C]
  )(using C, StorageAccess): TailRec[(Vector[OrientedStep[C]], Expansions[C])] =
    proof match
      case ArticleProof.Reflexivity(_)  => done((Vector.empty, expansions))
      case ArticleProof.Symmetry(inner) =>
        tailcall(flattened(derivation, inner, expansions)).map((steps, after) =>
          (steps.reverse.map(_.turned), after)
        )
      case ArticleProof.Transitivity(first, second) =>
        for
          (firstSteps, afterFirst) <- tailcall(
            flattened(derivation, first, expansions)
          )
          (secondSteps, afterSecond) <- tailcall(
            flattened(derivation, second, afterFirst)
          )
        yield (firstSteps ++ secondSteps, afterSecond)
      case ArticleProof.Congruence(shape, proofs) =>
        TailRecFolds.folded(
          proofs.zip(roles(shape, proofs.size)).toVector,
          (Vector.empty[OrientedStep[C]], expansions)
        ) { case ((steps, current), (inner, role)) =>
          flattened(derivation, inner, current).map((innerSteps, after) =>
            (steps ++ innerSteps.map(_.under(role)), after)
          )
        }
      case ArticleProof.Instance(axiom, substitution) =>
        done(
          (Vector(instanceStep(derivation, axiom, substitution)), expansions)
        )
      case ArticleProof.Conversion(first, second, _) =>
        val step = RewriteStep[C](
          RewriteReason.Unproved(UnprovedKind.BetaConversion),
          Vector.empty,
          RewriteDirection.Forward,
          derivation.term(second),
          Vector.empty
        )
        done(
          (Vector(OrientedStep.of(step, derivation.term(first))), expansions)
        )
      case ArticleProof.Abstraction(
            first,
            second,
            eigenvariableTerms,
            bodyTerm,
            proof
          ) =>
        tailcall(flattened(derivation, proof, expansions)).map((inner, after) =>
          val eigenvariables = eigenvariableTerms.map(derivation.term)
          val body = derivation.term(bodyTerm)
          val innerSteps = OrientedStep.joined(inner)
          val made = innerSteps.foldLeft(body)(applied)
          val spelling =
            Conversions.opened(derivation.term(second), eigenvariables)
          if !Configured.same(made, spelling) then
            throw IllegalStateException(
              s"the ${inner.size} steps of the body ${spelled(body)} make ${spelled(made)}, not its spelling ${spelled(spelling)}"
            )
          val step = RewriteStep(
            RewriteReason.Abstraction(eigenvariables, body, innerSteps),
            Vector.empty,
            RewriteDirection.Forward,
            derivation.term(second),
            Vector.empty
          )
          (Vector(OrientedStep.of(step, derivation.term(first))), after)
        )
      case ArticleProof.Edge(_) | ArticleProof.Connection(_, _) =>
        expansions.get(proof) match
          case Some(steps) => done((steps, expansions))
          case None        =>
            val expansion = derivation
              .expanded(proof)
              .getOrElse(
                throw IllegalStateException(
                  s"the writer does not expand $proof"
                )
              )
            tailcall(flattened(derivation, expansion, expansions)).map(
              (steps, after) => (steps, after.updated(proof, steps))
            )

  /** The role of each child of a layer of the shape, in child order. */
  private def roles(shape: LayerShape, children: Int): Vector[PositionSegment] =
    shape match
      case LayerShape.Thunk(_, _) =>
        Vector.tabulate(children)(PositionSegment.Filling(_))
      case LayerShape.Apply =>
        Vector(PositionSegment.Function, PositionSegment.Argument)
      case LayerShape.Choice | LayerShape.Parallel =>
        Vector(PositionSegment.Left, PositionSegment.Right)

  /** The step of an instance of an axiom of the import set, its two sides read
    * back in the round's configuration (`ArticleDerivation.term`): the thunk of
    * no hole, the right side of the β rule into the last hole and the left side
    * of the body equation, as data (`StepTerm.Holeless`), never as a term.
    */
  private def instanceStep[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      axiom: Axiom,
      substitution: Vector[(String, ArticleTerm)]
  )(using C, StorageAccess): OrientedStep[C] =
    val (left, right) = derivation.store.axiomStatement(axiom)
    val bindings =
      substitution.map((name, term) => (name, instructionOf(derivation, term)))
    val bound = bindings.toMap
    def fillings(count: Int): Vector[Configured[C]] =
      Vector.tabulate(count)(place => boundVariable(bound, s"filling$place"))
    val reason: RewriteReason[C] = axiom match
      case Axiom.Native(native, application, result) =>
        RewriteReason.Native(
          native,
          instructionOf(derivation, application),
          derivation.term(result)
        )
      case Axiom.SetEquation(number) => RewriteReason.Equation(number, bindings)
      case Axiom.Lemma(lemma)        => RewriteReason.Lemma(lemma, bindings)
      case Axiom.Fill(code, holes)   =>
        RewriteReason.Fill(
          code,
          holes,
          fillings(derivation.store.thunkArity(code, holes)),
          boundVariable(bound, "argument")
        )
      case Axiom.Body(code) =>
        RewriteReason.Body(
          code,
          fillings(derivation.store.thunkArity(code, Vector.empty))
        )
      case Axiom.Eta(code, holes) => RewriteReason.Eta(code, holes, fillings(1))
      case Axiom.Respell(code, holes) =>
        RewriteReason.Respell(
          code,
          holes,
          fillings(derivation.store.thunkArity(code, holes))
        )
      case Axiom.Conversion(_, _) =>
        throw IllegalStateException(
          s"a conversion equation is no instance of a proof: the trace converts by replay"
        )
    val equation =
      Statement(sideRead(derivation, left), sideRead(derivation, right))
    OrientedStep(
      FlatStep(
        reason,
        Vector.empty,
        RewriteDirection.Forward,
        stepTerm(equation.right, bound),
        equation.provenance
      ),
      stepTerm(equation.left, bound)
    )

  /** A side of an equation of an article as a side of a statement over the
    * round's terms.
    */
  private def sideRead[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      side: ArticleTerm
  ): StatementTerm[Configured[C]] =
    statementOver(ArticleStore.statementTerm(side), derivation.term)

  /** The side with each term it holds mapped. A trampoline: a side is as deep
    * as a program.
    */
  private def statementOver[From, To](
      side: StatementTerm[From],
      mapped: From => To
  ): StatementTerm[To] =
    def over(term: StatementTerm[From]): TailRec[StatementTerm[To]] = term match
      case StatementTerm.Variable(name) => done(StatementTerm.Variable(name))
      case StatementTerm.Stored(held)   =>
        done(StatementTerm.Stored(mapped(held)))
      case StatementTerm.Layered(layer) =>
        ArticleStore
          .traversed(layer.children)(child => tailcall(over(child)))
          .map(children => StatementTerm.Layered(layer.over(children)))
    over(side).result

  /** The side instantiated under the bindings: the thunk of a code with no hole
    * as data (`StepTerm.Holeless`), any other side its term built through the
    * configuration.
    */
  private def stepTerm[C <: NativeSpecializer & Singleton](
      side: StatementTerm[Configured[C]],
      bound: Map[String, Configured[C]]
  )(using
      C
  ): StepTerm[C] = side match
    case StatementTerm.Layered(Thunk(code, Vector(), fillings)) =>
      StepTerm.Holeless(code, fillings.map(Statements.instance(_, bound)))
    case other => StepTerm.Term(Statements.instance(other, bound))

  private def boundVariable[C <: NativeSpecializer & Singleton](
      bound: Map[String, Configured[C]],
      name: String
  ): Configured[C] =
    bound.getOrElse(
      name,
      throw IllegalStateException(s"the instance binds no $name")
    )

  /** The closed term of a term of an article over the article's terms, in the
    * round's configuration. Throws `IllegalArgumentException` for a variable,
    * for an equation and for a thunk of no hole, which is no term.
    */
  def instructionOf[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      term: ArticleTerm
  )(using C): Configured[C] =
    Statements.instance(sideRead(derivation, term), Map.empty)

  /** The axiom of the import set a reason instantiates. Throws
    * `IllegalArgumentException` for a native's fold, whose axiom states the
    * article's terms, and for a reason of no axiom.
    */
  def axiom[C <: NativeSpecializer & Singleton](
      reason: RewriteReason[C]
  ): Axiom = reason match
    case RewriteReason.Lemma(lemma, _)         => Axiom.Lemma(lemma)
    case RewriteReason.Equation(number, _)     => Axiom.SetEquation(number)
    case RewriteReason.Fill(code, holes, _, _) => Axiom.Fill(code, holes)
    case RewriteReason.Body(code, _)           => Axiom.Body(code)
    case RewriteReason.Eta(code, holes, _)     => Axiom.Eta(code, holes)
    case RewriteReason.Respell(code, holes, _) => Axiom.Respell(code, holes)
    case other                                 =>
      throw IllegalArgumentException(
        s"the reason $other states no axiom of a step"
      )

  /** The statement of the axiom a reason instantiates, as the article states
    * it, over the article's terms.
    */
  def statement[C <: NativeSpecializer & Singleton](
      derivation: ArticleDerivation[C],
      reason: RewriteReason[C]
  ): Statement[TermId] =
    val (left, right) = derivation.store.axiomStatement(axiom(reason))
    Statement(
      ArticleStore.statementTerm(left),
      ArticleStore.statementTerm(right)
    )

  /** The variables a reason binds, by name. */
  def bound[C <: NativeSpecializer & Singleton](
      reason: RewriteReason[C]
  ): Map[String, Configured[C]] =
    def fillingsBound(
        fillings: Vector[Configured[C]]
    ): Map[String, Configured[C]] =
      fillings.zipWithIndex
        .map((filling, place) => (s"filling$place", filling))
        .toMap
    reason match
      case RewriteReason.Lemma(_, substitution)         => substitution.toMap
      case RewriteReason.Equation(_, substitution)      => substitution.toMap
      case RewriteReason.Fill(_, _, fillings, argument) =>
        fillingsBound(fillings).updated("argument", argument)
      case RewriteReason.Body(_, fillings)       => fillingsBound(fillings)
      case RewriteReason.Eta(_, _, fillings)     => fillingsBound(fillings)
      case RewriteReason.Respell(_, _, fillings) => fillingsBound(fillings)
      case RewriteReason.Unproved(_)             => Map.empty
      case RewriteReason.Abstraction(_, _, _)    => Map.empty
      case RewriteReason.Native(_, _, _)         => Map.empty

  /** The term after the step. */
  def applied[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      step: RewriteStep[C]
  )(using C, StorageAccess): Configured[C] =
    Positions.replaced(term, step.position, step.replacement)
