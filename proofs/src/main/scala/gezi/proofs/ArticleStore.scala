package gezi.proofs

import gezi.standardlibrary.StandardLibraryIndex
import gezi.ir.BindingNormalForm
import gezi.ir.CodeLayer
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.ir.Pattern
import gezi.lemmaencoding.EncodedLemma
import gezi.rewritetrace.Statement
import gezi.rewritetrace.StatementTerm
import gezi.rewritetrace.Statements
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Apply, Choice, Parallel, Slot, Thunk}
import gezi.ir.{Configured, NativeSpecializer}

/** What an article reads of the terms of a proof and of the library: the layers
  * of the article's terms (`ProofTerms`), the codes the thunks carry, the lemma
  * sides of the library's index (the Prolog writer read `lemma_sides/4` of the
  * index and the one hash_consing store), and the lemmas as the strategy
  * encoded them into patterns (`gezi.lemmaencoding.EncodedLemma`), by which the
  * article states and matches a lemma. The index gives a lemma its two closed
  * terms only; how they become patterns is the strategy's encoding (a pattern's
  * arity belongs to the encoding, not to the framework), which the caller hands
  * over as data. A lambda pattern of an encoding is the eta-shaped thunk
  * pattern; no side holds a `Pattern.Closure`. It names no lemma and no
  * combinator and holds no type.
  *
  * KEYS. The key of a term is the value a term is written under: a layer whose
  * children are keys that are all terms of the article is that term, when the
  * article has it (`ProofTerms.existing`), so that one term has one key, as the
  * Prolog writer interned such a layer into its store; a layer the article has
  * no term of stays a layer, equal to every other key of it.
  */
final class ArticleStore[C <: NativeSpecializer & Singleton](
    index: StandardLibraryIndex[C],
    lemmas: Vector[EncodedLemma[C]],
    val terms: ProofTerms[C]
):

  /** The configuration of the proof's terms. */
  def specializer: C = index.specializer

  private given C = index.specializer

  private val encodings: Map[LemmaIdentifier, EncodedLemma[C]] =
    lemmas.map(lemma => lemma.lemma -> lemma).toMap

  /** The name of a lemma in the library's index, the one its Lean statement
    * `LambdaJit.Exported.Statement.«Name»` bears (`LeanStatements`); none for a
    * lemma the index names nowhere, such as a test's.
    */
  def lemmaName(lemma: LemmaIdentifier): Option[String] =
    index.lemmaNames.collectFirst {
      case gezi.standardlibrary.LemmaNamed(`lemma`, name) => name
    }

  /** The layer of a term of the article (`ProofTerms.layer`): a storage's its
    * view. Throws `IllegalStateException` for an opaque term.
    */
  def layer(term: TermId): Layer[TermId] = terms.layer(term)

  /** The code of an identifier. */
  def code(identifier: Code): CodeLayer[Code] = identifier.layer

  /** The number of fillings of a thunk of the code with the holes: the code's
    * slots that are no hole (`Statements.thunkArity`). Throws
    * `OpentheoryArticleError` with `MoreHolesThanSlots` when it would be
    * negative.
    */
  def thunkArity(code: Code, holes: Vector[Hole]): Int =
    val arity = Statements.highestSlot(code) + 1 - holes.count {
      case Hole.Bound(_) => true
      case Hole.Ignored  => false
    }
    if arity < 0 then
      throw OpentheoryArticleError(
        ArticleErrorReason.MoreHolesThanSlots(code, holes)
      )
    arity

  /** A thunk of the code with the holes has a defunctionalized η rule equation
    * (`Statements.etaShaped`).
    */
  def etaShaped(code: Code, holes: Vector[Hole]): Boolean =
    Statements.etaShaped(code, holes)

  /** The holes, after `thunkArity` has checked that a thunk of the code can
    * have them, so that a refusal is the article's error.
    */
  private def arityChecked(code: Code, holes: Vector[Hole]): Vector[Hole] =
    val _ = thunkArity(code, holes)
    holes

  /** The lemmas the strategy encoded, in its order. */
  def encodedLemmas: Vector[LemmaIdentifier] = lemmas.map(_.lemma)

  /** The two closed sides of a lemma of the index. Throws
    * `OpentheoryArticleError` with `NotALemma` when the index holds none.
    */
  def lemmaSides(lemma: LemmaIdentifier): (Configured[C], Configured[C]) =
    val sides = index
      .sides(lemma)
      .getOrElse(
        throw OpentheoryArticleError(ArticleErrorReason.NotALemma(lemma))
      )
    (sides.left, sides.right)

  /** The number of the lemma's metavariables and the patterns of its two sides,
    * read from the strategy's encoding of the lemma. Throws
    * `OpentheoryArticleError` with `NotALemma` when the index holds no sides
    * for it, with `NoEncoding` when the strategy gave no encoding of it, and
    * with `ClosureInEncoding` when a side of the encoding holds a closure
    * pattern.
    */
  def lemmaPatterns(lemma: LemmaIdentifier): (Int, MatchPattern, MatchPattern) =
    if index.sides(lemma).isEmpty then
      throw OpentheoryArticleError(ArticleErrorReason.NotALemma(lemma))
    val encoding =
      encodings.getOrElse(
        lemma,
        throw OpentheoryArticleError(ArticleErrorReason.NoEncoding(lemma))
      )
    (
      encoding.metavariables,
      lemmaPattern(lemma, encoding.left),
      lemmaPattern(lemma, encoding.right)
    )

  private def lemmaPattern(
      lemma: LemmaIdentifier,
      pattern: Pattern[C]
  ): MatchPattern =
    pattern match
      case Pattern.Thunk(
            code,
            holes,
            Vector(Pattern.Metavariable(metavariable))
          ) if etaShaped(code, holes) =>
        MatchPattern.Lambda(metavariable, lemmaPatternLayer(lemma, pattern))
      case Pattern.Metavariable(index) => MatchPattern.Metavariable(index)
      case Pattern.InstructionReference(instruction) =>
        MatchPattern.Reference(terms.of(instruction))
      case Pattern.Closure(index) =>
        throw OpentheoryArticleError(
          ArticleErrorReason.ClosureInEncoding(lemma, index)
        )
      case _ => MatchPattern.Layered(lemmaPatternLayer(lemma, pattern))

  private def lemmaPatternLayer(
      lemma: LemmaIdentifier,
      pattern: Pattern[C]
  ): Layer[MatchPattern] = pattern match
    case Pattern.Apply(function, argument) =>
      Apply(lemmaPattern(lemma, function), lemmaPattern(lemma, argument))
    case Pattern.Parallel(left, right) =>
      Parallel(lemmaPattern(lemma, left), lemmaPattern(lemma, right))
    case Pattern.Choice(left, right) =>
      Choice(lemmaPattern(lemma, left), lemmaPattern(lemma, right))
    case Pattern.Thunk(code, holes, fillings) =>
      Thunk(code, holes, fillings.map(lemmaPattern(lemma, _)))
    case _ => throw IllegalArgumentException(s"$pattern is no layer")

  /** The layer of a term of the article as a pattern over its children. */
  def storedPattern(term: TermId): Layer[MatchPattern] =
    layer(term).map(MatchPattern.Reference(_))

  /** The body of a code as a pattern, its slot i the metavariable i, an inner
    * thunk's fillings its codes.
    */
  def codeBodyPattern(identifier: Code): MatchPattern = code(identifier) match
    case Slot(index)               => MatchPattern.Metavariable(index)
    case Apply(function, argument) =>
      MatchPattern.Layered(
        Apply(codeBodyPattern(function), codeBodyPattern(argument))
      )
    case Parallel(left, right) =>
      MatchPattern.Layered(
        Parallel(codeBodyPattern(left), codeBodyPattern(right))
      )
    case Choice(left, right) =>
      MatchPattern.Layered(
        Choice(codeBodyPattern(left), codeBodyPattern(right))
      )
    case Thunk(inner, holes, fillings) =>
      MatchPattern.Layered(Thunk(inner, holes, fillings.map(codeBodyPattern)))

  /** The term of a pattern, its metavariable i the element i of the leaves.
    * Throws `OpentheoryArticleError` with `UnboundMetavariable` for a
    * metavariable with no leaf.
    */
  def patternTerm(
      pattern: MatchPattern,
      leaves: Vector[Option[ArticleTerm]]
  ): ArticleTerm = pattern match
    case MatchPattern.Metavariable(index) =>
      ArticleStore.leafBound(leaves, index)
    case MatchPattern.Reference(term)  => ArticleTerm.Stored(term)
    case MatchPattern.Lambda(_, thunk) =>
      ArticleTerm.Layered(thunk.map(patternTerm(_, leaves)))
    case MatchPattern.Layered(layer) =>
      ArticleTerm.Layered(layer.map(patternTerm(_, leaves)))

  /** The key of a term (the class comment, KEYS). A trampoline: a term is as
    * deep as a program.
    */
  def key(term: ArticleTerm): ArticleTerm = keyed(term).result

  private def keyed(term: ArticleTerm): TailRec[ArticleTerm] = term match
    case ArticleTerm.Stored(_) | ArticleTerm.Variable(_) => done(term)
    case ArticleTerm.Equation(left, right)               =>
      for
        leftKey <- tailcall(keyed(left))
        rightKey <- tailcall(keyed(right))
      yield ArticleTerm.Equation(leftKey, rightKey)
    case ArticleTerm.Layered(layer) =>
      ArticleStore
        .traversed(layer.children)(child => tailcall(keyed(child)))
        .map { children =>
          val keyedLayer = LayerShape.layer(LayerShape.of(layer), children)
          val stored = children.collect { case ArticleTerm.Stored(child) =>
            child
          }
          Option
            .when(stored.size == children.size)(
              LayerShape.layer(LayerShape.of(layer), stored)
            )
            .flatMap(terms.existing) match
            case Some(existing) => ArticleTerm.Stored(existing)
            case None           => ArticleTerm.Layered(keyedLayer)
        }

  /** The layer of a key that is one, a term's its own; a variable and an
    * equation have none.
    */
  def keyLayer(key: ArticleTerm): Option[Layer[ArticleTerm]] = key match
    case ArticleTerm.Stored(term) =>
      Some(layer(term).map(ArticleTerm.Stored(_)))
    case ArticleTerm.Layered(layer)                           => Some(layer)
    case ArticleTerm.Variable(_) | ArticleTerm.Equation(_, _) => None

  /** The two sides of an equation of the import set, terms over variables: a
    * lemma as the strategy's encoding states it, every other equation as
    * `gezi.rewritetrace.Statements` states it.
    */
  def axiomStatement(axiom: Axiom): (ArticleTerm, ArticleTerm) = axiom match
    case Axiom.SetEquation(number) => ArticleStore.setEquation(number)
    case Axiom.Lemma(lemma)        =>
      val (arity, left, right) = lemmaPatterns(lemma)
      val leaves =
        ArticleStore.numberedVariables("metavariable", arity).map(Some(_))
      (patternTerm(left, leaves), patternTerm(right, leaves))
    case Axiom.Fill(code, holes) =>
      ArticleStore.sides(Statements.fill(code, arityChecked(code, holes)))
    case Axiom.Body(code) =>
      val _ = arityChecked(code, Vector.empty)
      ArticleStore.sides(Statements.body(code))
    case Axiom.Eta(code, holes) =>
      ArticleStore.sides(Statements.eta(code, holes))
    case Axiom.Respell(code, holes) =>
      ArticleStore.sides(Statements.respell(code, arityChecked(code, holes)))
    case Axiom.Conversion(first, second) =>
      (ArticleTerm.Stored(first), ArticleTerm.Stored(second))
    case Axiom.Native(_, application, result) =>
      (application, ArticleTerm.Stored(result))

  /** The two sides of a lemma's statement from its sides
    * (`gezi.rewritetrace.Statements.lemma`) as terms of the article, each
    * instruction of the statement its term.
    */
  def lemmaStatementSides(
      statement: Statement[Configured[C]]
  ): (ArticleTerm, ArticleTerm) =
    ArticleStore.sidesOver(statement, terms.of)

  /** The front end's spelling of a thunk of the code with the holes, its
    * fillings codes over the slots of the thunk's fillings
    * (`BindingNormalForm.respelled`), or none when the thunk is its own
    * spelling.
    */
  def respelled(
      code: Code,
      holes: Vector[Hole]
  ): Option[(Code, Vector[Hole], Vector[Code])] =
    BindingNormalForm.respelled(code, holes, thunkArity(code, holes))

/** The import set's numbered equations and the naming of variables. */
object ArticleStore:

  /** The store of an article over the nodes of the layers
    * (`StrategyProof.layers`) and the references: the terms of the nodes, of
    * the references, of the constants of the lemmas' encodings and, when a
    * storage's view can be read, of the lemmas' sides (`ProofTerms.of`).
    */
  def of[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      lemmas: Vector[EncodedLemma[C]],
      layers: Vector[gezi.ir.LayerWith[Int, Configured[C]]],
      references: Vector[Configured[C]],
      access: Option[gezi.ir.StorageAccess]
  ): ArticleStore[C] =
    given C = index.specializer
    val patternConstants =
      lemmas.flatMap(lemma => constants(lemma.left) ++ constants(lemma.right))
    val sides =
      if access.isEmpty then Vector.empty
      else
        lemmas.flatMap(lemma =>
          index
            .sides(lemma.lemma)
            .toVector
            .flatMap(found => Vector(found.left, found.right))
        )
    ArticleStore(
      index,
      lemmas,
      ProofTerms.of(layers, references ++ patternConstants ++ sides, access)
    )

  /** The instructions of a pattern's `InstructionReference`s, in preorder. A
    * loop over the patterns pending.
    */
  private def constants[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C]
  ): Vector[Configured[C]] =
    @scala.annotation.tailrec
    def collected(
        pending: List[Pattern[C]],
        found: Vector[Configured[C]]
    ): Vector[Configured[C]] = pending match
      case Nil          => found
      case next :: rest =>
        next match
          case Pattern.InstructionReference(instruction) =>
            collected(rest, found :+ instruction)
          case _ => collected(next.children.toList ++ rest, found)
    collected(List(pattern), Vector.empty)

  /** The results of the step on each item, in order, as a trampoline. */
  def traversed[Item, Result](items: Vector[Item])(
      step: Item => TailRec[Result]
  ): TailRec[Vector[Result]] =
    def from(index: Int, results: Vector[Result]): TailRec[Vector[Result]] =
      if index >= items.size then done(results)
      else
        tailcall(step(items(index))).flatMap(result =>
          from(index + 1, results :+ result)
        )
    from(0, Vector.empty)

  /** The leaf of the metavariable. Throws `OpentheoryArticleError` with
    * `UnboundMetavariable` when there is none.
    */
  def leafBound[Leaf](leaves: Vector[Option[Leaf]], index: Int): Leaf =
    leaves
      .lift(index)
      .flatten
      .getOrElse(
        throw OpentheoryArticleError(
          ArticleErrorReason.UnboundMetavariable(index)
        )
      )

  /** The variables `stem0`, `stem1`, ..., as many as the count. */
  def numberedVariables(stem: String, count: Int): Vector[ArticleTerm] =
    Vector.tabulate(count)(index => ArticleTerm.Variable(s"$stem$index"))

  /** The numbers of the numbered equations an article imports, in the order
    * written: (1) to (6) and (8) to (10). (7), the unit law 0 + M = M, is none
    * of them: the calculus is to have no 0, and no derivation uses it.
    */
  val importedSetEquations: Vector[Int] = Vector(1, 2, 3, 4, 5, 6, 8, 9, 10)

  /** The numbered equation (`Statements.setEquation`). */
  def setEquation(number: Int): (ArticleTerm, ArticleTerm) = sides(
    Statements.setEquation(number)
  )

  /** The two sides of a statement that holds no term as terms of an article. */
  def sides(statement: Statement[Nothing]): (ArticleTerm, ArticleTerm) =
    sidesOver[Nothing](statement, nothing => nothing)

  /** The two sides of a statement as terms of an article, each term it holds
    * the article's term `stored` gives.
    */
  def sidesOver[Term](
      statement: Statement[Term],
      stored: Term => TermId
  ): (ArticleTerm, ArticleTerm) =
    (articleTerm(statement.left, stored), articleTerm(statement.right, stored))

  /** A side of a statement as a term of an article. A trampoline: a body is as
    * deep as a program.
    */
  def articleTerm[Term](
      term: StatementTerm[Term],
      stored: Term => TermId
  ): ArticleTerm = articleTermMade(term, stored).result

  private def articleTermMade[Term](
      term: StatementTerm[Term],
      stored: Term => TermId
  ): TailRec[ArticleTerm] = term match
    case StatementTerm.Variable(name) => done(ArticleTerm.Variable(name))
    case StatementTerm.Stored(held)   => done(ArticleTerm.Stored(stored(held)))
    case StatementTerm.Layered(layer) =>
      traversed(layer.children)(child =>
        tailcall(articleTermMade(child, stored))
      ).map(children =>
        ArticleTerm.Layered(LayerShape.layer(LayerShape.of(layer), children))
      )

  /** A side of an equation of an article as a side of a statement. Throws
    * `IllegalArgumentException` for an equation, which is no side. A
    * trampoline.
    */
  def statementTerm(term: ArticleTerm): StatementTerm[TermId] =
    statementTermMade(term).result

  private def statementTermMade(
      term: ArticleTerm
  ): TailRec[StatementTerm[TermId]] = term match
    case ArticleTerm.Variable(name) => done(StatementTerm.Variable(name))
    case ArticleTerm.Stored(held)   => done(StatementTerm.Stored(held))
    case ArticleTerm.Equation(_, _) =>
      throw IllegalArgumentException(s"$term is no side of an equation")
    case ArticleTerm.Layered(layer) =>
      traversed(layer.children)(child => tailcall(statementTermMade(child)))
        .map(children =>
          StatementTerm.Layered(
            LayerShape.layer(LayerShape.of(layer), children)
          )
        )
