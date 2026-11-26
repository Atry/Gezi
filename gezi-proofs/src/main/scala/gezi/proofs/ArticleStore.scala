package gezi.proofs

import gezi.standardlibrary.StandardLibraryIndex
import gezi.ir.BindingNormalForm
import gezi.ir.CodeLayer
import gezi.ir.Code
import gezi.ir.Instruction
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

/** What an article reads of the IR and of the library: the layers and codes
  * the instructions carry, the lemma sides of the library's index (the Prolog
  * writer read `lemma_sides/4` of the index and the one hash_consing store),
  * and the lemmas as the strategy encoded them into patterns
  * (`gezi.lemmaencoding.EncodedLemma`), by which the article states and
  * matches a lemma. The index gives a lemma its two closed terms only; how
  * they become patterns is the strategy's encoding (a pattern's arity
  * belongs to the encoding, not to the framework), which the caller hands
  * over as data. A lambda pattern of an
  * encoding is the eta-shaped thunk pattern; no side holds a
  * `Pattern.Closure`.
  * It names no lemma and no combinator and holds no type.
  *
  * KEYS. The key of a term is the value a term is written under: a layer
  * whose children are keys that are all instructions is the instruction of that
  * layer, interned, so that one term has one key, as the Prolog writer
  * interned such a layer into its store.
  */
final class ArticleStore(index: StandardLibraryIndex, lemmas: Vector[EncodedLemma]):

  private val encodings: Map[LemmaIdentifier, EncodedLemma] = lemmas.map(lemma => lemma.lemma -> lemma).toMap

  /** The name of a lemma in the library's index, the one its Lean statement
    * `LambdaJit.Exported.Statement.«Name»` bears (`LeanStatements`); none
    * for a lemma the index names nowhere, such as a test's.
    */
  def lemmaName(lemma: LemmaIdentifier): Option[String] =
    index.lemmaNames.collectFirst { case gezi.standardlibrary.LemmaNamed(`lemma`, name) => name }

  /** The layer of a term instruction. Throws `IllegalStateException` for an
    * opaque instruction.
    *
    * FIXME: a URI node is opaque, so any proof whose terms hold one https://github.com/Atry/private-overlay/issues/1978
    * has no article: the writer throws here, and the evaluation phase writes
    * none for such a proof (`OpentheoryArticle.uriFree`, whose FIXME has the
    * candidate).
    */
  def layer(instruction: Instruction): Layer[Instruction] = instruction.layered

  /** The code of an identifier. */
  def code(identifier: Code): CodeLayer[Code] = identifier.layer

  /** The number of fillings of a thunk of the code with the holes: the
    * code's slots that are no hole (`Statements.thunkArity`). Throws
    * `OpentheoryArticleError` with `MoreHolesThanSlots` when it would be
    * negative.
    */
  def thunkArity(code: Code, holes: Vector[Hole]): Int =
    val arity = Statements.highestSlot(code) + 1 - holes.count(_.isInstanceOf[Hole.Bound])
    if arity < 0 then throw OpentheoryArticleError(ArticleErrorReason.MoreHolesThanSlots(code, holes))
    arity

  /** A thunk of the code with the holes has a defunctionalized η rule
    * equation (`Statements.etaShaped`).
    */
  def etaShaped(code: Code, holes: Vector[Hole]): Boolean = Statements.etaShaped(code, holes)

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
  def lemmaSides(lemma: LemmaIdentifier): (Instruction, Instruction) =
    val sides = index.sides(lemma).getOrElse(throw OpentheoryArticleError(ArticleErrorReason.NotALemma(lemma)))
    (sides.left, sides.right)

  /** The number of the lemma's metavariables and the patterns of its two
    * sides, read from the strategy's encoding of the lemma. Throws
    * `OpentheoryArticleError` with `NotALemma` when the index holds no sides
    * for it, with `NoEncoding` when the strategy gave no encoding of it, and
    * with `ClosureInEncoding` when a side of the encoding holds a closure
    * pattern.
    */
  def lemmaPatterns(lemma: LemmaIdentifier): (Int, MatchPattern, MatchPattern) =
    if index.sides(lemma).isEmpty then throw OpentheoryArticleError(ArticleErrorReason.NotALemma(lemma))
    val encoding =
      encodings.getOrElse(lemma, throw OpentheoryArticleError(ArticleErrorReason.NoEncoding(lemma)))
    (encoding.metavariables, lemmaPattern(lemma, encoding.left), lemmaPattern(lemma, encoding.right))

  private def lemmaPattern(lemma: LemmaIdentifier, pattern: Pattern): MatchPattern =
    pattern match
      case Pattern.Thunk(code, holes, Vector(Pattern.Metavariable(metavariable))) if etaShaped(code, holes) =>
        MatchPattern.Lambda(metavariable, lemmaPatternLayer(lemma, pattern))
      case Pattern.Metavariable(index)          => MatchPattern.Metavariable(index)
      case Pattern.InstructionReference(instruction) => MatchPattern.Reference(instruction)
      case Pattern.Closure(index) =>
        throw OpentheoryArticleError(ArticleErrorReason.ClosureInEncoding(lemma, index))
      case _ => MatchPattern.Layered(lemmaPatternLayer(lemma, pattern))

  private def lemmaPatternLayer(lemma: LemmaIdentifier, pattern: Pattern): Layer[MatchPattern] = pattern match
    case Pattern.Apply(function, argument) =>
      Apply(lemmaPattern(lemma, function), lemmaPattern(lemma, argument))
    case Pattern.Parallel(left, right) => Parallel(lemmaPattern(lemma, left), lemmaPattern(lemma, right))
    case Pattern.Choice(left, right)   => Choice(lemmaPattern(lemma, left), lemmaPattern(lemma, right))
    case Pattern.Thunk(code, holes, fillings) =>
      Thunk(code, holes, fillings.map(lemmaPattern(lemma, _)))
    case Pattern.Metavariable(_) | Pattern.InstructionReference(_) | Pattern.Closure(_) =>
      throw IllegalArgumentException(s"$pattern is no layer")

  /** The stored layer of an instruction as a pattern over its children. */
  def storedPattern(instruction: Instruction): Layer[MatchPattern] =
    layer(instruction).map(MatchPattern.Reference(_))

  /** The body of a code as a pattern, its slot i the metavariable i, an
    * inner thunk's fillings its codes.
    */
  def codeBodyPattern(identifier: Code): MatchPattern = code(identifier) match
    case Slot(index) => MatchPattern.Metavariable(index)
    case Apply(function, argument) =>
      MatchPattern.Layered(Apply(codeBodyPattern(function), codeBodyPattern(argument)))
    case Parallel(left, right) =>
      MatchPattern.Layered(Parallel(codeBodyPattern(left), codeBodyPattern(right)))
    case Choice(left, right) =>
      MatchPattern.Layered(Choice(codeBodyPattern(left), codeBodyPattern(right)))
    case Thunk(inner, holes, fillings) =>
      MatchPattern.Layered(Thunk(inner, holes, fillings.map(codeBodyPattern)))

  /** The term of a pattern, its metavariable i the element i of the leaves.
    * Throws `OpentheoryArticleError` with `UnboundMetavariable` for a
    * metavariable with no leaf.
    */
  def patternTerm(pattern: MatchPattern, leaves: Vector[Option[ArticleTerm]]): ArticleTerm = pattern match
    case MatchPattern.Metavariable(index) => ArticleStore.leafBound(leaves, index)
    case MatchPattern.Reference(instruction)   => ArticleTerm.Stored(instruction)
    case MatchPattern.Lambda(_, thunk)    => ArticleTerm.Layered(thunk.map(patternTerm(_, leaves)))
    case MatchPattern.Layered(layer)      => ArticleTerm.Layered(layer.map(patternTerm(_, leaves)))

  /** The key of a term (the class comment, KEYS). A trampoline: a term is as
    * deep as a program.
    */
  def key(term: ArticleTerm): ArticleTerm = keyed(term).result

  private def keyed(term: ArticleTerm): TailRec[ArticleTerm] = term match
    case ArticleTerm.Stored(_) | ArticleTerm.Variable(_) => done(term)
    case ArticleTerm.Equation(left, right) =>
      for
        leftKey <- tailcall(keyed(left))
        rightKey <- tailcall(keyed(right))
      yield ArticleTerm.Equation(leftKey, rightKey)
    case ArticleTerm.Layered(layer) =>
      ArticleStore.traversed(layer.children)(child => tailcall(keyed(child))).map { children =>
        val keyedLayer = LayerShape.layer(LayerShape.of(layer), children)
        val instructions = children.collect { case ArticleTerm.Stored(instruction) => instruction }
        val overInstructions = Option.when(instructions.size == children.size)(LayerShape.layer(LayerShape.of(layer), instructions))
        overInstructions match
          case Some(interned) => ArticleTerm.Stored(Instruction(interned))
          case None           => ArticleTerm.Layered(keyedLayer)
      }

  /** The layer of a key that is one, an instruction's its own; a
    * variable and an equation have none.
    */
  def keyLayer(key: ArticleTerm): Option[Layer[ArticleTerm]] = key match
    case ArticleTerm.Stored(instruction) => Some(layer(instruction).map(ArticleTerm.Stored(_)))
    case ArticleTerm.Layered(layer) => Some(layer)
    case ArticleTerm.Variable(_) | ArticleTerm.Equation(_, _) => None

  /** The two sides of an equation of the import set, terms over variables:
    * a lemma as the strategy's encoding states it, every other equation as
    * `gezi.rewritetrace.Statements` states it.
    */
  def axiomStatement(axiom: Axiom): (ArticleTerm, ArticleTerm) = axiom match
    case Axiom.SetEquation(number) => ArticleStore.setEquation(number)
    case Axiom.Lemma(lemma) =>
      val (arity, left, right) = lemmaPatterns(lemma)
      val leaves = ArticleStore.numberedVariables("metavariable", arity).map(Some(_))
      (patternTerm(left, leaves), patternTerm(right, leaves))
    case Axiom.Fill(code, holes) => ArticleStore.sides(Statements.fill(code, arityChecked(code, holes)))
    case Axiom.Body(code) =>
      val _ = arityChecked(code, Vector.empty)
      ArticleStore.sides(Statements.body(code))
    case Axiom.Eta(code, holes) => ArticleStore.sides(Statements.eta(code, holes))
    case Axiom.Respell(code, holes) => ArticleStore.sides(Statements.respell(code, arityChecked(code, holes)))
    case Axiom.Conversion(first, second) => (ArticleTerm.Stored(first), ArticleTerm.Stored(second))

  /** The front end's spelling of a thunk of the code with the holes, its
    * fillings the placeholders (`BindingNormalForm.respelled`), or none when
    * the thunk is its own spelling.
    */
  def respelled(code: Code, holes: Vector[Hole]): Option[(Code, Vector[Hole], Vector[Instruction])] =
    BindingNormalForm.respelled(code, holes, thunkArity(code, holes))

/** The import set's numbered equations and the naming of variables. */
object ArticleStore:

  /** The results of the step on each item, in order, as a trampoline. */
  def traversed[Item, Result](items: Vector[Item])(step: Item => TailRec[Result]): TailRec[Vector[Result]] =
    def from(index: Int, results: Vector[Result]): TailRec[Vector[Result]] =
      if index >= items.size then done(results)
      else tailcall(step(items(index))).flatMap(result => from(index + 1, results :+ result))
    from(0, Vector.empty)

  /** The leaf of the metavariable. Throws `OpentheoryArticleError` with
    * `UnboundMetavariable` when there is none.
    */
  def leafBound[Leaf](leaves: Vector[Option[Leaf]], index: Int): Leaf =
    leaves.lift(index).flatten.getOrElse(throw OpentheoryArticleError(ArticleErrorReason.UnboundMetavariable(index)))

  /** The variables `stem0`, `stem1`, ..., as many as the count. */
  def numberedVariables(stem: String, count: Int): Vector[ArticleTerm] =
    Vector.tabulate(count)(index => ArticleTerm.Variable(s"$stem$index"))

  /** The numbers of the numbered equations an article imports, in the order
    * written: (1) to (6) and (8) to (10). (7), the
    * unit law 0 + M = M, is none of them: the calculus is to have no 0, and
    * no derivation uses it.
    */
  val importedSetEquations: Vector[Int] = Vector(1, 2, 3, 4, 5, 6, 8, 9, 10)

  /** The numbered equation (`Statements.setEquation`). */
  def setEquation(number: Int): (ArticleTerm, ArticleTerm) = sides(Statements.setEquation(number))

  /** The two sides of a statement as terms of an article. */
  def sides(statement: Statement): (ArticleTerm, ArticleTerm) =
    (articleTerm(statement.left), articleTerm(statement.right))

  /** A side of a statement as a term of an article. A trampoline: a body is
    * as deep as a program.
    */
  def articleTerm(term: StatementTerm): ArticleTerm = articleTermMade(term).result

  private def articleTermMade(term: StatementTerm): TailRec[ArticleTerm] = term match
    case StatementTerm.Variable(name) => done(ArticleTerm.Variable(name))
    case StatementTerm.Stored(instruction) => done(ArticleTerm.Stored(instruction))
    case StatementTerm.Layered(layer) =>
      traversed(layer.children)(child => tailcall(articleTermMade(child))).map(children =>
        ArticleTerm.Layered(LayerShape.layer(LayerShape.of(layer), children))
      )

  /** A side of an equation of an article as a side of a statement. Throws
    * `IllegalArgumentException` for an equation, which is no side. A
    * trampoline.
    */
  def statementTerm(term: ArticleTerm): StatementTerm = statementTermMade(term).result

  private def statementTermMade(term: ArticleTerm): TailRec[StatementTerm] = term match
    case ArticleTerm.Variable(name) => done(StatementTerm.Variable(name))
    case ArticleTerm.Stored(instruction) => done(StatementTerm.Stored(instruction))
    case ArticleTerm.Equation(_, _) => throw IllegalArgumentException(s"$term is no side of an equation")
    case ArticleTerm.Layered(layer) =>
      traversed(layer.children)(child => tailcall(statementTermMade(child))).map(children =>
        StatementTerm.Layered(LayerShape.layer(LayerShape.of(layer), children))
      )
