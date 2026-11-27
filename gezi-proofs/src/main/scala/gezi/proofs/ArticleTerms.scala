package gezi.proofs

import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.ir.NotTerm
import gezi.rewritetrace.UnprovedKind
import gezi.ir

/** A term an article writes: a term of the article's `ProofTerms`; a
  * variable of type term, named; a layer over terms; or the equation of two
  * terms. A layer holds its code by identifier; no layer is a noinline leaf.
  */
enum ArticleTerm:
  case Stored(term: TermId)
  case Variable(name: String)
  case Layered(layer: Layer[ArticleTerm])
  case Equation(left: ArticleTerm, right: ArticleTerm)

object ArticleTerm:
  /** A term an article writes is no IR term. */
  given NotTerm[ArticleTerm] = NotTerm.granted

/** A pattern the matcher reads: a metavariable; a term of the article; a lambda pattern
  * `\x. M x` of the metavariable `index` (the eta-shaped thunk pattern
  * `thunk(apply(slot(F), slot(H)), [H], [metavariable(Index)])`, F not H),
  * with its thunk layer; or one layer over
  * patterns. Only a lemma's side has lambda patterns: the Prolog writer's
  * `lambda_pattern/2` matched a thunk whose code is written out as a tree,
  * which a lemma's pattern holds, and never one whose code is an instruction, which
  * the body of a closure read as a pattern holds (`code_body_pattern/2`), so
  * a body's eta-shaped thunk is matched as a layer.
  */
enum MatchPattern:
  case Metavariable(index: Int)
  case Reference(term: TermId)
  case Lambda(index: Int, thunk: Layer[MatchPattern])
  case Layered(layer: Layer[MatchPattern])

  /** The metavariables the pattern mentions. */
  def mentions: Vector[Int] = this match
    case Metavariable(index) => Vector(index)
    case Reference(_)        => Vector.empty
    case Lambda(_, thunk)    => thunk.children.flatMap(_.mentions)
    case Layered(layer)      => layer.children.flatMap(_.mentions)

object MatchPattern:
  /** A pattern is no IR term. */
  given NotTerm[MatchPattern] = NotTerm.granted

/** The constructor of a layer with its atoms: a thunk's code and holes. */
enum LayerShape:
  case Thunk(code: Code, holes: Vector[Hole])
  case Apply
  case Choice
  case Parallel

/** The shapes of layers. */
object LayerShape:

  /** The shape of the layer. Throws `IllegalArgumentException` for a
    * noinline leaf, which is no term of an article.
    */
  def of(layer: Layer[Any]): LayerShape = layer match
    case ir.Thunk(code, holes, _) => Thunk(code, holes)
    case ir.Apply(_, _)           => Apply
    case ir.Choice(_, _)          => Choice
    case ir.Parallel(_, _)        => Parallel
    // A storage's view `v ∥ T` is the parallel the storage stands for.
    case ir.StorageView(_, _)     => Parallel
    case ir.NoinlineLeaf(instruction) =>
      throw IllegalArgumentException(s"a noinline leaf $instruction is no layer of an article")

  /** The layer of the shape over the children, which are as many as the
    * shape has.
    */
  def layer[Child](shape: LayerShape, children: Vector[Child])(using NotTerm[Child]): Layer[Child] =
    (shape, children) match
      case (Thunk(code, holes), _)                 => ir.Thunk(code, holes, children)
      case (Apply, Vector(function, argument))     => ir.Apply(function, argument)
      case (Choice, Vector(left, right))           => ir.Choice(left, right)
      case (Parallel, Vector(left, right))         => ir.Parallel(left, right)
      case _ =>
        throw IllegalArgumentException(s"the shape $shape has no layer over ${children.size} children")

/** An equation of the import set. */
enum Axiom:

  /** One of the numbered equations (1) to (6) and (8) to (10)
    * (`ArticleStore.setEquation`).
    */
  case SetEquation(number: Int)

  /** The statement of a lemma, its metavariables the variables
    * metavariable0, metavariable1, and so on.
    */
  case Lemma(lemma: LemmaIdentifier)

  /** The defunctionalized β rule of the thunk constant of the code and the
    * holes, one hole at least: its first hole filled by `argument`.
    */
  case Fill(code: Code, holes: Vector[Hole])

  /** The thunk constant of the code with no hole equals the code's body over
    * its fillings.
    */
  case Body(code: Code)

  /** The defunctionalized η rule of an eta-shaped thunk constant. */
  case Eta(code: Code, holes: Vector[Hole])

  /** The thunk constant of the code and the holes, one hole at least, equals
    * its spelling by the front end (`gezi.rewritetrace.Statements.respell`).
    */
  case Respell(code: Code, holes: Vector[Hole])

  /** The closed term `redex` of a union the e-graph made by β conversion
    * (`gezi.egraph.Justification.BetaConversion`) reduces to the closed
    * term `reduct`: an equation the checker decides by a search for the β
    * steps that reduce its left side to its right (Lean
    * `EndToEnd.conversionChecked`).
    * It has no variable, so each union states its own.
    */
  case Conversion(redex: TermId, reduct: TermId)

  /** The application `application`, a define bound to the native named
    * applied to storages, a term over terms of the article, equals the
    * storage `result` of the native's value
    * on them. It rests on two sources: the native's obligation
    * `native = define`, which its binding states on unfiltered values and
    * which is trusted; and the unique spelling's pattern theorem
    * `C ȳ ∥ T ≃_O C ȳ` (`docs/design/gezi-set-equations-proofs.md`, section
    * 23, a theorem of Definition 14 with no derivation in ⊢), at each
    * argument and at the result, under the premise the fold requires
    * (`UniqueSpellingPremise`). It has no variable, so each fold states its
    * own.
    */
  case Native(native: String, application: ArticleTerm, result: TermId)

/** A proof of an equation of terms, before it is written. */
enum ArticleProof:
  case Reflexivity(term: ArticleTerm)
  case Symmetry(proof: ArticleProof)
  case Transitivity(first: ArticleProof, second: ArticleProof)

  /** One layer of the shape over the proofs of its children. */
  case Congruence(shape: LayerShape, proofs: Vector[ArticleProof])

  /** The equation of the import set, its variables substituted by name. */
  case Instance(axiom: Axiom, substitution: Vector[(String, ArticleTerm)])

  /** The two terms the union names are equal. */
  case Edge(union: Int)

  /** The path between the nodes of two terms in the forest (`ProofForest.node`). */
  case Connection(first: TermId, second: TermId)

  /** The two terms of a union by β conversion are equal, `reduct` the one
    * of them the other reduces to: the trace keeps it as a step that
    * converts, and the writer imports the reduction as its conversion
    * equation (`Axiom.Conversion`), turned where `reduct` is `first`.
    */
  case Conversion(first: TermId, second: TermId, reduct: TermId)

  /** The closure `first` equals the thunk `second` written back by the
    * abstraction rule ξ from the closure's body opened at the eigenvariables,
    * `body`, equal by `proof` to the spelling `second` opens to: a step the
    * trace keeps over the body's steps and the writer refuses.
    */
  case Abstraction(
      first: TermId,
      second: TermId,
      eigenvariables: Vector[TermId],
      body: TermId,
      proof: ArticleProof
  )

/** The constructors of proofs that drop reflexivity, as the Prolog writer's
  * do.
  */
object ArticleProof:

  def transitivity(first: ArticleProof, second: ArticleProof): ArticleProof =
    (first, second) match
      case (Reflexivity(_), _) => second
      case (_, Reflexivity(_)) => first
      case _                   => Transitivity(first, second)

  def symmetry(proof: ArticleProof): ArticleProof = proof match
    case Reflexivity(_)   => proof
    case Symmetry(inner)  => inner
    case _                => Symmetry(proof)

  def connection(first: TermId, second: TermId): ArticleProof =
    if first == second then Reflexivity(ArticleTerm.Stored(first))
    else Connection(first, second)

  /** One layer over the proofs of its children: a layer over reflexive
    * proofs is reflexive.
    */
  def congruence(shape: LayerShape, proofs: Vector[ArticleProof]): ArticleProof =
    val terms = proofs.collect { case Reflexivity(term) => term }
    if terms.size == proofs.size then
      Reflexivity(ArticleTerm.Layered(LayerShape.layer(shape, terms)))
    else Congruence(shape, proofs)

/** A constant of the article's HOL terms. */
enum HolSymbol:
  case Apply
  case Choice
  case Parallel
  case Equality
  case Thunk(code: Code, holes: Vector[Hole])

/** A type of the article: `LambdaJit.term`, `bool`, a function type, or one
  * of the types of a thunk constant's defining term (`ThunkDefinitions`):
  * `LambdaJit.number`, `LambdaJit.code`, `LambdaJit.codes`,
  * `LambdaJit.hole` and `LambdaJit.holes`.
  *
  * Stack-safe: a thunk constant's type nests one function type per filling,
  * thousands deep, so
  * a function type computes its hash code once, when it is made, from its
  * parts' (made before it), and compares by a loop over the pairs of parts
  * still to compare; neither recurses on the depth of a type.
  */
sealed abstract class HolType extends Product with Serializable

/** The types of the article. */
object HolType:
  case object Term extends HolType
  case object Bool extends HolType

  final case class Function(argument: HolType, result: HolType) extends HolType:
    override val hashCode: Int = scala.util.hashing.MurmurHash3.productHash(this)
    override def equals(other: Any): Boolean = other match
      case that: HolType => equal(List((this, that)))
      case _             => false

  case object Number extends HolType
  case object Code extends HolType
  case object Codes extends HolType
  case object Hole extends HolType
  case object Holes extends HolType

  /** Whether the two types of each pair are equal: the same object, or two
    * function types of one hash code whose arguments and results are equal.
    */
  @scala.annotation.tailrec
  private def equal(pending: List[(HolType, HolType)]): Boolean = pending match
    case Nil => true
    case (first, second) :: rest =>
      if first eq second then equal(rest)
      else
        (first, second) match
          case (Function(firstArgument, firstResult), Function(secondArgument, secondResult)) =>
            if first.hashCode != second.hashCode then false
            else equal((firstArgument, secondArgument) :: (firstResult, secondResult) :: rest)
          case _ => false

/** A type operator of the article. */
enum TypeOperator:
  case Term
  case Bool
  case Function
  case Number
  case Code
  case Codes
  case Hole
  case Holes

/** A HOL term as an article builds it, without the dictionary: a constant
  * or a variable, its name the components of its namespace and then its
  * local name, unescaped, with its type; or an application.
  */
enum HolTerm:
  case Constant(name: Vector[String], typeTerm: HolTypeTerm)
  case Variable(name: Vector[String], typeTerm: HolTypeTerm)
  case Application(function: HolTerm, argument: HolTerm)

/** A HOL type as an article builds it: a type operator, named, applied to
  * types.
  *
  * Stack-safe, as `HolType` is: the hash code is computed once, when the
  * type is made, from its parts' (made before it), and equality is a loop
  * over the pairs of types still to compare.
  */
final case class HolTypeTerm(name: Vector[String], arguments: Vector[HolTypeTerm]):
  override val hashCode: Int = scala.util.hashing.MurmurHash3.productHash(this)
  override def equals(other: Any): Boolean = other match
    case that: HolTypeTerm => HolTypeTerm.equal(List((this, that)))
    case _                 => false

/** The equality of HOL types. */
object HolTypeTerm:

  /** Whether the two types of each pair are equal: the same object, or one
    * hash code, one name and arguments equal in order.
    */
  @scala.annotation.tailrec
  private def equal(pending: List[(HolTypeTerm, HolTypeTerm)]): Boolean = pending match
    case Nil => true
    case (first, second) :: rest =>
      if first eq second then equal(rest)
      else if first.hashCode != second.hashCode || first.name != second.name ||
        first.arguments.size != second.arguments.size
      then false
      else equal(first.arguments.zip(second.arguments).toList ++ rest)

/** Why the writer refused a proof or a lemma, the Prolog writer's
  * `opentheory_article_error(Reason)`.
  */
enum ArticleErrorReason:
  case NotAProofOfOneEquation(equations: Int)
  case UnionsOutOfOrder(expected: Int, found: Int)
  case NotANode(term: TermId)
  /** A union that names a number that is no node of the proof. */
  case NotANodeNumber(node: Int)
  case UnionWithinAClass(union: Int)
  case SidesNotJoined(leftAt: TermId, rightAt: TermId)
  case CongruenceNotProved(union: Int, first: TermId, second: TermId)
  case BindingsDiffer(union: Int, lemma: LemmaIdentifier, bindings: Int, arity: Int)
  case LemmaBindingNotRecorded(union: Int, lemma: LemmaIdentifier)
  case BetaNotProved(union: Int, application: TermId, body: TermId)
  case NotAJustification(union: Int, justification: Justification)
  /** The union replaced a closure unit by its compilation's artifact, whose
    * proof the writer does not have.
    */
  case CompiledUnitNotProved(union: Int, function: TermId)

  /** A pattern view's union whose first node is no `s ∥ T′` over the
    * storage `s` of its second, or whose storage's view is no parallel.
    */
  case PatternViewNotProved(union: Int, view: TermId, storage: TermId)

  /** A storage view's union whose two nodes' terms are not both parallels. */
  case StorageViewNotProved(union: Int, storage: TermId, view: TermId)
  case UnboundMetavariable(index: Int)
  case InstanceNotMatched(union: Int, pattern: MatchPattern, node: TermId)
  case NotALemma(lemma: LemmaIdentifier)
  case NoEncoding(lemma: LemmaIdentifier)
  case ClosureInEncoding(lemma: LemmaIdentifier, index: Int)
  case AxiomPoppedBeforeUse(axiom: Axiom)
  case SideNotMatched(node: TermId)
  case NotConnected(first: TermId, second: TermId)
  case FillingsDiffer(code: Code, holes: Vector[Hole], fillings: Int)
  case MoreHolesThanSlots(code: Code, holes: Vector[Hole])
  case Unproved(kind: UnprovedKind, first: TermId, second: TermId)

/** The writer's refusal. */
final case class OpentheoryArticleError(reason: ArticleErrorReason)
    extends RuntimeException(s"OpenTheory article: $reason")
