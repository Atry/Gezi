package gezi.proofs

import gezi.rewritetrace.UnprovedKind
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import gezi.standardlibrary.StandardLibraryIndex
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.lemmaencoding.EncodedLemma
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Slot, Thunk}
import gezi.ir.{Configured, NativeSpecializer}

/** A search strategy's proof as an OpenTheory article: the equation of two
  * terms, derived from the unions. The port of
  * `gezi/prolog/gezi/opentheory_article.pl`, the writer of the proof's trace,
  * which is an OpenTheory article; the article is the same text, byte for byte,
  * as the Prolog writer's for the same proof.
  *
  * Given the proof of a search strategy that joins the two terms `left` and
  * `right`, a `StrategyProof` of one equation `(leftAt, rightAt)`, `text`
  * writes an article in the OpenTheory article format, version 6
  * (https://www.gilith.com/opentheory/article.html). Reading the article gives
  * an import set, the theorems of its `axiom` commands, and one exported
  * theorem, the equation of the two terms; the article is a derivation of the
  * exported theorem from the import set. The proof is the strategy's and the
  * writer reads nothing else of it: no e-graph and no state of a search. The
  * search records its unions only when a round asks for the proof, an option
  * off by default, and the article is written once, after the search.
  *
  * WHAT IT DECIDES: nothing about the object language. Each union of the proof
  * is a step the search took, a lemma instance or a congruence, and the writer
  * writes the HOL proof of that step. It names no lemma and no combinator,
  * holds no type, and reads from the library's index only the sides of the
  * lemma a union names.
  *
  * THE ENCODING. The IR after defunctionalization has no binder, so its terms
  * are first-order HOL terms of one type:
  *
  * {{{
  * the type        LambdaJit.term, a nullary type operator, referenced and
  *                 not defined; equality is the constant = at type
  *                 term -> term -> bool, bool the type operator bool
  * apply(F, A)     LambdaJit.apply F A, term -> term -> term
  * choice(L, R)    LambdaJit.choice L R, term -> term -> term
  * parallel(L, R)  LambdaJit.parallel L R, term -> term -> term
  * thunk(Code, Holes, Fillings)
  *                 the thunk constant of (Code, Holes) applied, by HOL
  *                 application, to the encodings of the fillings in slot
  *                 order; its type has one argument per filling
  * }}}
  *
  * The operators are named after prior work's: + is the choice, ∥ the parallel,
  * 0 the empty choice. A library name is no constant: it labels the instruction
  * of its layer, so its encoding is its layer's, and there is no delta. The
  * thunk constant of (Code, Holes) is named `LambdaJit.thunk.N`, N the order in
  * which the article first writes it, from 0, and its code and holes are not in
  * its name: the article defines it, before its first use, by `defineConst` as
  * the first-order term `LambdaJit.Code.thunkOf C H`, `C` the code and `H` the
  * holes over the constants of `ThunkDefinitions`, and pops the definitional
  * theorem, which no step uses. Successor, `\n.\z.\s. s n`, with no filling, is
  * the constant defined as
  * `thunkOf (Code.apply (Code.slot zero) (Code.slot (successor zero)))` applied
  * to the holes 1, ignored and 0.
  *
  * THE IMPORT SET, every `axiom` with an empty list of hypotheses and free
  * variables of type term: the nine numbered equations (1) to (6) and (8) to
  * (10) (`CONTRIBUTING.md`, "Terms"), over the variables M, N, P, A and B,
  * first ((7), the unit law 0 + M = M, is not written: the calculus is to have
  * no 0, and no derivation uses it); the statement of every lemma that a union
  * on the derivation names, its metavariables the variables metavariable0,
  * metavariable1, ..., the outermost binder first, written where the derivation
  * first uses it; and for every thunk constant that occurs in the article, its
  * defunctionalized β rule equation: with holes [H | Hs] and fillings filling0,
  * ..., `LambdaJit.apply (c filling0 ...) argument` equals the constant of
  * (Code, Hs) applied to the fillings with the argument at the place of H's
  * slot (an ignored hole drops the argument); with no hole, `c filling0 ...`
  * equals the code's body with slot i read as filling_i. And its
  * defunctionalized η rule equation when the code is `apply(slot(F), slot(H))`
  * and the holes are [H] with F other than H: `c filling0` equals filling0. An
  * equation the derivation uses is written where it is first used; the others
  * after the derivation, until every constant they mention has its own.
  *
  * THE DERIVATION. The unions of the proof form a forest over its terms
  * (`ProofForest`); the proof that two nodes are equal is the path between them
  * in the forest (the proof forest of R. Nieuwenhuis and A. Oliveras,
  * Proof-producing congruence closure, RTA 2005; egg's explanations, O. Flatt
  * et al., Small proofs from congruence closure, FMCAD 2022), its edges chained
  * with `trans` and turned with `sym`, and an edge is proved by its
  * justification (`ProofMatching`). A side of an instance and the node a union
  * names need not be one spelling; the writer finds the proof by matching the
  * side against the node's class as the class stood when the union was made, so
  * the proof of union I uses only unions below I, and every proof is finite.
  * The two terms the article joins are matched in the same way, against the
  * classes of `leftAt` and `rightAt` at the end. Within a class the node named
  * is tried first, then the others in the order of the proof's terms, so the
  * article is the same in every process.
  *
  * SHARING. Every type, constant, term and theorem is built once; one used
  * again is stored with `def`, reused with `ref`, and removed by its last use
  * with `remove`, so that the dictionary is empty at the end, and one used once
  * is not stored. The dictionary's keys are numbered in the order things are
  * first written. An article uses only the commands version, typeOp, opType,
  * const, constTerm, var, varTerm, appTerm, refl, sym, trans, appThm, subst,
  * axiom, thm, defineConst, def, ref, remove, pop, nil and cons, besides
  * numbers and names.
  *
  * THE STATEMENTS AS TERMS. `lemmaStatementEncoded` gives the two sides of the
  * equation an article imports for a lemma as HOL terms, built by the functions
  * that write them, so that `LeanStatements` writes into Lean exactly the
  * statement an article imports.
  */
object OpentheoryArticle:

  /** Whether no term of the proof holds a URI node, which the writer cannot
    * write (`ArticleStore.layer`).
    *
    * FIXME: the evaluation phase writes no article for a proof whose
    * https://github.com/Atry/private-overlay/issues/1978 terms hold a URI node.
    * Measured 2026-11-17, `ArticleDestination.Written` on the direct point of
    * each repeated family (seed 20261116): no proof held one, every point
    * writing its article, under the fixture entry (13 families), the entry
    * `solo` (21) and the entry `wren` (2, and its two hot points); other
    * families and entries are unmeasured. Candidate: write a URI node as a term
    * variable named by its URI, as an eigenvariable is (`opaqueVariable`);
    * lemma and congruence steps over it then hold at every valuation, but a β
    * conversion over it needs a check at every valuation, a substitution lemma
    * of ≃_O under the interpretation that `LambdaJit.RoundCertificate` does not
    * have yet.
    */
  def uriFree[C <: NativeSpecializer & Singleton](
      proof: StrategyProof[C]
  )(using C): Boolean = !proof.layers.exists {
    case NoinlineLeaf(leaf) => holdsUri(leaf)
    case _                  => false
  }

  /** Whether the writer cannot write a β conversion: its terms hold a URI node.
    */
  private[proofs] def conversionUnwritable[C <: NativeSpecializer & Singleton](
      terms: ProofTerms[C],
      first: TermId,
      second: TermId
  )(using C): Boolean =
    terms.holdsUriUnder(first) || terms.holdsUriUnder(second)

  /** Whether a term is a URI node or holds one among its layers' children.
    * Iterative: a body is as deep as a program. A storage is a leaf of its
    * term's layer, and the e-graph keeps no URI node under one.
    */
  private def holdsUri[C <: NativeSpecializer & Singleton](term: Configured[C])(
      using C
  ): Boolean =
    @annotation.tailrec
    def searched(
        pending: List[Configured[C]],
        visited: Set[Configured[C]]
    ): Boolean = pending match
      case Nil                                    => false
      case next :: rest if visited.contains(next) => searched(rest, visited)
      case next :: _ if next.uri.isDefined        => true
      case next :: rest if next.opaque => searched(rest, visited + next)
      case next :: rest                =>
        searched(next.layer.children.toList ++ rest, visited + next)
    searched(List(term), Set.empty)

  /** The article of the equation `left = right`. `left` and `right` are the
    * closed IR instructions a search joined, and `proof` its proof of their
    * equation alone, `leftAt` and `rightAt` the terms whose classes the two are
    * matched against. The index holds the library's lemmas, and the proof the
    * search's encodings of them into patterns. Throws `OpentheoryArticleError`
    * when the proof is no proof of one equation, when it names a term twice or
    * a union names no term of it, when `leftAt` and `rightAt` are not joined by
    * its unions, and on a union whose step the writer cannot write.
    */
  def text[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      left: Configured[C],
      right: Configured[C],
      proof: StrategyProof[C]
  )(using gezi.ir.StorageAccess)(using C): String =
    val prepared = Prepared.of(index, left, right, proof)
    val lines = ArticleWriter(prepared.store, prepared.forest)
      .articleLines(
        prepared.left,
        prepared.right,
        prepared.leftAt,
        prepared.rightAt
      )
    dictionarySettled(lines).map(_ + "\n").mkString

  /** What the writer reads of a proof of one equation: the store over the
    * proof's nodes and the two terms, the forest, the two terms and the terms
    * of the nodes whose classes they are matched against. Throws
    * `OpentheoryArticleError` when the proof is no proof of one equation and
    * when the two nodes are not joined by its unions.
    */
  private final case class Prepared[C <: NativeSpecializer & Singleton](
      store: ArticleStore[C],
      forest: ProofForest[C],
      left: TermId,
      right: TermId,
      leftAt: TermId,
      rightAt: TermId
  )

  private object Prepared:
    def of[C <: NativeSpecializer & Singleton](
        index: StandardLibraryIndex[C],
        left: Configured[C],
        right: Configured[C],
        proof: StrategyProof[C]
    )(using access: gezi.ir.StorageAccess)(using C): Prepared[C] =
      val equation = proof.equations match
        case Vector(only) => only
        case other        =>
          throw OpentheoryArticleError(
            ArticleErrorReason.NotAProofOfOneEquation(other.size)
          )
      val store = ArticleStore.of(
        index,
        proof.lemmas,
        proof.layers,
        Vector(left, right),
        Some(access)
      )
      val forest = ProofForest.of(proof, store.terms)
      val leftAt = store.terms.nodeTerm(equation.leftAt)
      val rightAt = store.terms.nodeTerm(equation.rightAt)
      if forest.pathSteps(leftAt, rightAt).isEmpty then
        throw OpentheoryArticleError(
          ArticleErrorReason.SidesNotJoined(leftAt, rightAt)
        )
      Prepared(
        store,
        forest,
        store.terms.of(left),
        store.terms.of(right),
        leftAt,
        rightAt
      )

  /** Writes the article of `text` to the file, replacing it, in UTF-8. */
  def written[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      left: Configured[C],
      right: Configured[C],
      proof: StrategyProof[C],
      file: Path
  )(using gezi.ir.StorageAccess)(using C): Unit =
    Files.writeString(
      file,
      text(index, left, right, proof),
      StandardCharsets.UTF_8
    )

  /** The derivation `text` writes for the same arguments: the proof tree of
    * `left = right` before it is written, with the expansion of its edges and
    * paths, built by the same functions as the article
    * (`ArticleWriter.roundProof`, `ArticleWriter.proofExpanded`), so that
    * `RewriteTrace` flattens the proof the article derives. Throws as `text`
    * does before it writes.
    */
  def derivation[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      left: Configured[C],
      right: Configured[C],
      proof: StrategyProof[C]
  )(using gezi.ir.StorageAccess)(using specializer: C): ArticleDerivation[C] =
    val prepared = Prepared.of(index, left, right, proof)
    val writer = ArticleWriter(prepared.store, prepared.forest)
    ArticleDerivation(
      specializer,
      left,
      right,
      writer.roundProof(
        prepared.left,
        prepared.right,
        prepared.leftAt,
        prepared.rightAt
      ),
      writer.proofExpanded,
      prepared.store,
      prepared.forest
    )

  /** The two sides of the equation that an article imports for the lemma, the
    * HOL terms that the writer builds for the lemma's `axiom` command, built by
    * the same functions from the lemma's encoding among `lemmas`, without the
    * dictionary, with the thunks of their thunk constants, numbered from 0 in
    * this statement, the left side first. Throws `OpentheoryArticleError` as
    * the writer does on that lemma: with `NotALemma`, `NoEncoding` or
    * `ClosureInEncoding`.
    */
  def lemmaStatementEncoded[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      lemmas: Vector[EncodedLemma[C]],
      lemma: LemmaIdentifier
  )(using access: gezi.ir.StorageAccess): ThunkDefinitions.NamedTerms =
    val store =
      ArticleStore.of(index, lemmas, Vector.empty, Vector.empty, Some(access))
    val (left, right) = store.axiomStatement(Axiom.Lemma(lemma))
    Encoding(store).termsEncoded(Vector(left, right))

  /** The HOL term by which an article writes a closed instruction, built by the
    * functions that write it, with the thunks of its thunk constants, numbered
    * from 0 in this term.
    */
  def termEncoded[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      instruction: Configured[C]
  ): ThunkDefinitions.NamedTerms =
    val store = ArticleStore.of(
      index,
      Vector.empty,
      Vector.empty,
      Vector(instruction),
      None
    )
    Encoding(store).termsEncoded(
      Vector(ArticleTerm.Stored(store.terms.of(instruction)))
    )

  /** The defining term of a thunk constant, `LambdaJit.Code.thunkOf C H`, as a
    * HOL term with every type in it: what an article's `defineConst` defines
    * the constant by, for a text that stands alone.
    */
  def definingTermEncoded[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      code: Code,
      holes: Vector[Hole]
  ): HolTerm =
    val store =
      ArticleStore.of(index, Vector.empty, Vector.empty, Vector.empty, None)
    val encoding = Encoding(store)
    ThunkDefinitions.definingTerm(
      code,
      holes,
      store.thunkArity(code, holes),
      encoding.typeEncoded
    )

  /** A name of one component as the article writes it, quoted
    * (`ArticleState.name`).
    */
  private[proofs] def quotedName(name: String): String =
    "\"" + name.flatMap(character =>
      if character == '.' || character == '"' || character == '\\' then
        s"\\$character"
      else character.toString
    ) + "\""

  /** The lines of an article with the last `ref` of each stored object turned
    * into `remove`, and the number and `def` of an object that no `ref` reads
    * dropped, so that the dictionary is empty at the end. Each command leaves
    * the stack as it was: `def` only peeks, and `remove` pushes what `ref`
    * pushes. A number line followed by `def` or `ref` is a key; the writer
    * writes no other number but the version.
    */
  private def dictionarySettled(lines: Vector[String]): Vector[String] =
    val items = itemized(lines.toList, Vector.empty)
    val lastReferences = items.zipWithIndex.collect {
      case (DictionaryItem.Key(number, "ref"), position) =>
        (number, position)
    }.toMap
    items.zipWithIndex.flatMap {
      case (DictionaryItem.Line(line), _)         => Vector(line)
      case (DictionaryItem.Key(number, "def"), _) =>
        if lastReferences.contains(number) then Vector(number.toString, "def")
        else Vector.empty
      case (DictionaryItem.Key(number, _), position) =>
        if lastReferences(number) == position then
          Vector(number.toString, "remove")
        else Vector(number.toString, "ref")
    }

  private enum DictionaryItem:
    case Line(line: String)
    case Key(number: Int, operation: String)

  @scala.annotation.tailrec
  private def itemized(
      lines: List[String],
      items: Vector[DictionaryItem]
  ): Vector[DictionaryItem] =
    lines match
      case Nil => items
      case line :: (operation @ ("def" | "ref")) :: rest
          if line.nonEmpty && line.forall(_.isDigit) =>
        itemized(rest, items :+ DictionaryItem.Key(line.toInt, operation))
      case line :: rest => itemized(rest, items :+ DictionaryItem.Line(line))

/** A key of the article's dictionary. */
private enum DictionaryKey:
  case Term(key: ArticleTerm)
  case VariableObject(name: String)
  case Symbol(symbol: HolSymbol)
  case Type(holType: HolType)
  case Operator(operator: TypeOperator)
  case ReflexivityTheorem(key: ArticleTerm)
  case SymbolReflexivityTheorem(symbol: HolSymbol)
  case ProofTheorem(proof: ArticleProof)
  case AxiomTheorem(axiom: Axiom)
  case DefinitionConstantTerm(constant: DefinitionConstant)
  case DefinitionPartTerm(part: DefinitionPart)

/** How a key's term is written, one HOL layer:
  *
  * {{{
  * Variable(name)              the term variable of type term
  * Applied(symbol, arguments)  the constant of the symbol applied, by HOL
  *                             application, to the terms of the arguments
  * AliasSymbol(symbol)         the constant alone: a thunk with no
  *                             filling is its constant
  * }}}
  */
private enum TermEncoding:
  case Variable(name: String)
  case Applied(symbol: HolSymbol, arguments: Vector[ArticleTerm])
  case AliasSymbol(symbol: HolSymbol)

/** The encoding of terms, names and types, the one place that says how a term
  * is written (the Prolog writer's `key_encoding/2`, `symbol_name/2`,
  * `symbol_type/2` and `code_spelling/2`).
  *
  * The link from a source program to the reading of the Lean end-to-end theorem
  * needs the reading `read` of gezi/lean/LambdaJit/Interpretation.lean, applied
  * to the article term this writer writes for an IR term, to be
  * `Readback.readback` of that IR term. Module Encoding of the Lean package
  * defines this writer's encoding of a finite term, `encoding` below with the
  * types of `symbolType` and each thunk constant named by the signature of the
  * article's definitions, as `Encoding.encode`, undefined where this writer
  * throws, and proves that the reading of the encoding of a finite term is its
  * readback, as partial functions (`Encoding.readEncode`), on a signature whose
  * names are distinct (`Encoding.signatureWellFormed`).
  *
  * FIXME (link (ii) of https://github.com/Atry/private-overlay/issues/1561,
  * D6): that this writer computes Lean's `Encoding.encode` is not proved, and
  * is tested on the seven fixpoint runs only. The test
  * `OpentheoryArticleFixpointRunsTest.theWriterEncodesAsLeanEncodesOnTheFixpointRuns`
  * compares `termEncoded` of each run's two sides with `encode` of their finite
  * terms under the signature of the writer's thunk constants, byte for byte,
  * and the Lean module FixpointRunFixtures checks with the kernel that each of
  * those runs' articles exports the pair of `encode` of its sides under the
  * article's signature. An article of any other run has no check that its
  * exported sides are Lean's encodings of the IR terms it was asked to join.
  * Candidate fixes: the comparison of `termEncoded` with `encode` on generated
  * IR terms, as `DefunctionalizationAgreementTest` compares the front end with
  * Lean; or the two IR terms written beside every article as Lean finite terms,
  * as for the fixpoint runs.
  */
private final class Encoding[C <: NativeSpecializer & Singleton](
    store: ArticleStore[C]
):

  private given C = store.specializer

  /** How the term of a key is written: a choice is `LambdaJit.choice` applied
    * to its two sides, and an equation the constant `=` applied to its sides.
    */
  def encoding(key: ArticleTerm): TermEncoding = key match
    case ArticleTerm.Variable(name)        => TermEncoding.Variable(name)
    case ArticleTerm.Equation(left, right) =>
      TermEncoding.Applied(HolSymbol.Equality, Vector(left, right))
    case ArticleTerm.Stored(term) =>
      store.terms.opaqueName(term) match
        case Some(name) => TermEncoding.Variable(name)
        case None       => layered(key)
    case ArticleTerm.Layered(_) => layered(key)

  private def layered(key: ArticleTerm): TermEncoding =
    store.keyLayer(key) match
      case Some(layer) => layerEncoding(layer)
      case None => throw IllegalArgumentException(s"$key is no key of a term")

  private def layerEncoding(layer: Layer[ArticleTerm]): TermEncoding =
    layer match
      case Thunk(code, holes, Vector()) =>
        TermEncoding.AliasSymbol(HolSymbol.Thunk(code, holes))
      case Thunk(code, holes, fillings) =>
        if store.thunkArity(code, holes) != fillings.size then
          throw OpentheoryArticleError(
            ArticleErrorReason.FillingsDiffer(code, holes, fillings.size)
          )
        TermEncoding.Applied(HolSymbol.Thunk(code, holes), fillings)
      case Apply(function, argument) =>
        TermEncoding.Applied(HolSymbol.Apply, Vector(function, argument))
      case Parallel(left, right) =>
        TermEncoding.Applied(HolSymbol.Parallel, Vector(left, right))
      // A storage's view `v ∥ T` is the parallel the storage stands for.
      case gezi.ir.StorageView(value, criterion) =>
        TermEncoding.Applied(HolSymbol.Parallel, Vector(value, criterion))
      case Choice(left, right) =>
        TermEncoding.Applied(HolSymbol.Choice, Vector(left, right))
      case NoinlineLeaf(leaf) =>
        throw IllegalArgumentException(
          s"a noinline leaf $leaf is no term of an article"
        )

  /** The name of a fixed symbol's constant, its components. A thunk constant
    * has no name of its own: its name is its number among the thunk constants
    * of the article or the statement (`ThunkDefinitions.name`), which the
    * caller holds, and asking for it here throws.
    */
  def symbolName(symbol: HolSymbol): Vector[String] = symbol match
    case HolSymbol.Apply              => Vector("LambdaJit", "apply")
    case HolSymbol.Choice             => Vector("LambdaJit", "choice")
    case HolSymbol.Parallel           => Vector("LambdaJit", "parallel")
    case HolSymbol.Equality           => Vector("=")
    case HolSymbol.Thunk(code, holes) =>
      throw IllegalArgumentException(
        s"the thunk constant of $code with $holes is named by its number"
      )

  /** The type of a symbol's constant. */
  def symbolType(symbol: HolSymbol): HolType = symbol match
    case HolSymbol.Apply | HolSymbol.Choice | HolSymbol.Parallel =>
      HolType.Function(
        HolType.Term,
        HolType.Function(HolType.Term, HolType.Term)
      )
    case HolSymbol.Equality =>
      HolType.Function(
        HolType.Term,
        HolType.Function(HolType.Term, HolType.Bool)
      )
    case HolSymbol.Thunk(code, holes) =>
      ThunkDefinitions.thunkType(store.thunkArity(code, holes))

  /** The operator of a type and its argument types. */
  def typeOperator(holType: HolType): (TypeOperator, Vector[HolType]) =
    holType match
      case HolType.Term => (TypeOperator.Term, Vector.empty)
      case HolType.Bool => (TypeOperator.Bool, Vector.empty)
      case HolType.Function(argument, result) =>
        (TypeOperator.Function, Vector(argument, result))
      case HolType.Number => (TypeOperator.Number, Vector.empty)
      case HolType.Code   => (TypeOperator.Code, Vector.empty)
      case HolType.Codes  => (TypeOperator.Codes, Vector.empty)
      case HolType.Hole   => (TypeOperator.Hole, Vector.empty)
      case HolType.Holes  => (TypeOperator.Holes, Vector.empty)

  /** The name of a type operator, its components. */
  def operatorName(operator: TypeOperator): Vector[String] = operator match
    case TypeOperator.Term     => Vector("LambdaJit", "term")
    case TypeOperator.Bool     => Vector("bool")
    case TypeOperator.Function => Vector("->")
    case TypeOperator.Number   => Vector("LambdaJit", "number")
    case TypeOperator.Code     => Vector("LambdaJit", "code")
    case TypeOperator.Codes    => Vector("LambdaJit", "codes")
    case TypeOperator.Hole     => Vector("LambdaJit", "hole")
    case TypeOperator.Holes    => Vector("LambdaJit", "holes")

  /** The HOL terms of terms, built as the writer writes them, with the thunks
    * their thunk constants stand for: the thunk constants are numbered from 0
    * in the order they first occur, the terms in order and each term head
    * first, as an article numbers them. A trampoline: a term is as deep as a
    * program.
    */
  def termsEncoded(terms: Vector[ArticleTerm]): ThunkDefinitions.NamedTerms =
    val (encoded, (numbering, _)) =
      terms.foldLeft(
        (
          Vector.empty[HolTerm],
          (ThunkDefinitions.Numbering.empty, Map.empty[ArticleTerm, HolTerm])
        )
      ) { case ((before, (numbering, encodedKeys)), term) =>
        val (holTerm, next) =
          keyEncoded(store.key(term), numbering, encodedKeys).result
        (before :+ holTerm, next)
      }
    ThunkDefinitions.NamedTerms(encoded, numbering.entries)

  /** The HOL term of a key and the numbering and the keys encoded after it. A
    * key met again is the HOL term it was encoded to the first time, the same
    * object (`encodedKeys`), so that the term is as large as the program as a
    * graph and not as a tree: without it, a program whose IR shares subterms
    * was encoded once for every path to each, 26,476,705 characters of
    * `HolTermText.text` for a program whose exchange line is 7,699 (MEASURED
    * 2026-11-20, a point of
    * `repeated_library_longest_common_subsequences_small`). The numbering is
    * the same as without it: a key's thunk constants were numbered when it was
    * first encoded.
    */
  private def keyEncoded(
      key: ArticleTerm,
      numbering: ThunkDefinitions.Numbering,
      encodedKeys: Map[ArticleTerm, HolTerm]
  ): TailRec[
    (HolTerm, (ThunkDefinitions.Numbering, Map[ArticleTerm, HolTerm]))
  ] = encodedKeys.get(key) match
    case Some(encoded) => done((encoded, (numbering, encodedKeys)))
    case None          =>
      val encodedKey = encoding(key) match
        case TermEncoding.AliasSymbol(symbol) =>
          val (holTerm, next) = symbolEncoded(symbol, numbering)
          done((holTerm, (next, encodedKeys)))
        case TermEncoding.Variable(name) =>
          done(
            (
              HolTerm.Variable(Vector(name), typeEncoded(HolType.Term)),
              (numbering, encodedKeys)
            )
          )
        case TermEncoding.Applied(symbol, arguments) =>
          val (head, afterHead) = symbolEncoded(symbol, numbering)
          argumentsEncoded(head, arguments.toList, afterHead, encodedKeys)
      encodedKey.map { case (holTerm, (next, keys)) =>
        (holTerm, (next, keys.updated(key, holTerm)))
      }

  private def argumentsEncoded(
      head: HolTerm,
      arguments: List[ArticleTerm],
      numbering: ThunkDefinitions.Numbering,
      encodedKeys: Map[ArticleTerm, HolTerm]
  ): TailRec[
    (HolTerm, (ThunkDefinitions.Numbering, Map[ArticleTerm, HolTerm]))
  ] = arguments match
    case Nil              => done((head, (numbering, encodedKeys)))
    case argument :: rest =>
      tailcall(keyEncoded(store.key(argument), numbering, encodedKeys))
        .flatMap { case (encoded, (next, keys)) =>
          tailcall(
            argumentsEncoded(
              HolTerm.Application(head, encoded),
              rest,
              next,
              keys
            )
          )
        }

  /** The constant of a symbol, a thunk constant numbered by `numbering`. */
  private def symbolEncoded(
      symbol: HolSymbol,
      numbering: ThunkDefinitions.Numbering
  ): (HolTerm, ThunkDefinitions.Numbering) = symbol match
    case HolSymbol.Thunk(code, holes) =>
      val (number, next) = numbering.numbered(code, holes)
      (
        HolTerm.Constant(
          ThunkDefinitions.name(number),
          typeEncoded(symbolType(symbol))
        ),
        next
      )
    case _ =>
      (
        HolTerm.Constant(symbolName(symbol), typeEncoded(symbolType(symbol))),
        numbering
      )

  /** The HOL type term of a type. A trampoline: a thunk constant's type nests
    * one function type per filling.
    */
  def typeEncoded(holType: HolType): HolTypeTerm = typeTermBuilt(holType).result

  private def typeTermBuilt(holType: HolType): TailRec[HolTypeTerm] =
    val (operator, arguments) = typeOperator(holType)
    ArticleStore
      .traversed(arguments)(argument => tailcall(typeTermBuilt(argument)))
      .map(HolTypeTerm(operatorName(operator), _))

/** Whether an equation of the import set is written and its theorem kept in the
  * dictionary, or written and popped.
  */
private enum AxiomUse:
  case Kept
  case Popped

/** The article being written: its lines so far, the dictionary from each key to
  * its number, the next number, the thunk constants in the order they occurred,
  * how many of them have their import equations written, and the equations of
  * the import set written.
  */
private final case class ArticleState(
    lines: Vector[String],
    dictionary: Map[DictionaryKey, Int],
    nextNumber: Int,
    constants: Vector[(Code, Vector[Hole])],
    closed: Int,
    axioms: Map[Axiom, AxiomUse]
):
  def line(command: String): ArticleState = copy(lines = lines :+ command)

  def number(value: Int): ArticleState = line(value.toString)

  /** The object of a key in the dictionary pushed by `ref`, or nothing when the
    * dictionary does not hold the key.
    */
  def referenced(key: DictionaryKey): Option[ArticleState] =
    dictionary.get(key).map(number(_).line("ref"))

  /** The object on top of the stack stored by `def` under the next number,
    * which the key maps to.
    */
  def defined(key: DictionaryKey): ArticleState =
    copy(
      lines = lines :+ nextNumber.toString :+ "def",
      dictionary = dictionary.updated(key, nextNumber),
      nextNumber = nextNumber + 1
    )

  def aliased(key: DictionaryKey, existing: DictionaryKey): ArticleState =
    copy(dictionary = dictionary.updated(key, dictionary(existing)))

  /** A name, its namespace components and its local name joined by dots, each
    * component's dots, quotes and backslashes escaped by a backslash.
    */
  def name(components: Vector[String]): ArticleState =
    val escaped = components.map(
      _.flatMap(character =>
        if character == '.' || character == '"' || character == '\\' then
          s"\\$character"
        else character.toString
      )
    )
    line("\"" + escaped.mkString(".") + "\"")

  def conses(count: Int): ArticleState =
    (0 until count).foldLeft(this)((state, _) => state.line("cons"))

/** The writing of one article: every function takes the state and returns the
  * state after it, as a trampoline where it recurses on proofs and terms.
  */
private final class ArticleWriter[C <: NativeSpecializer & Singleton](
    store: ArticleStore[C],
    forest: ProofForest[C]
):

  private given C = store.specializer

  private val matching = ProofMatching(store, forest)
  private val encoding = Encoding(store)

  /** The version, the numbered equations (1) to (6) and (8) to (10)
    * (`ArticleStore.importedSetEquations`), the derivation of the equation, the
    * remaining equations of the import set, and the exported theorem, before
    * the dictionary is settled.
    */
  def articleLines(
      left: TermId,
      right: TermId,
      leftNode: TermId,
      rightNode: TermId
  ): Vector[String] =
    val start =
      ArticleState(Vector.empty, Map.empty, 0, Vector.empty, 0, Map.empty)
        .number(6)
        .line("version")
    val afterEquations =
      ArticleStore.importedSetEquations.foldLeft(start)((state, number) =>
        axiomTheoremWritten(state, Axiom.SetEquation(number)).result.line("pop")
      )
    val proof = roundProof(left, right, leftNode, rightNode)
    val proposition = store.key(
      ArticleTerm.Equation(ArticleTerm.Stored(left), ArticleTerm.Stored(right))
    )
    (for
      proved <- proofWritten(afterEquations, proof)
      stated <- keyTermWritten(proved, proposition)
      closed <- closureWritten(stated.line("pop"))
      exported <- keyTermWritten(closed.line("nil"), proposition)
    yield exported.line("thm")).result.lines

  /** The proof of `left = right` the article derives: `left` matched against
    * the class of `leftNode`, the path from `leftNode` to `rightNode`, and
    * `right` matched against the class of `rightNode`, turned. Its edges and
    * paths expand by `proofExpanded`.
    */
  def roundProof(
      left: TermId,
      right: TermId,
      leftNode: TermId,
      rightNode: TermId
  ): ArticleProof =
    val leftProof = sideProof(left, leftNode)
    val rightProof = sideProof(right, rightNode)
    ArticleProof.transitivity(
      leftProof,
      ArticleProof.transitivity(
        ArticleProof.connection(leftNode, rightNode),
        ArticleProof.symmetry(rightProof)
      )
    )

  private def sideProof(side: TermId, node: TermId): ArticleProof =
    matching
      .matchedProof(
        MatchPattern.Reference(side),
        Vector.empty,
        node,
        forest.finalTime
      )
      .getOrElse(
        throw OpentheoryArticleError(ArticleErrorReason.SideNotMatched(node))
      )

  /** The import equations of every thunk constant that occurred and has none
    * yet, in the order they occurred, until the equations written mention no
    * new constant.
    */
  private def closureWritten(state: ArticleState): TailRec[ArticleState] =
    if state.closed >= state.constants.size then done(state)
    else
      val (code, holes) = state.constants(state.closed)
      val main =
        if holes.nonEmpty then Axiom.Fill(code, holes) else Axiom.Body(code)
      for
        afterMain <- axiomEnsured(state, main)
        afterEta <-
          if store.etaShaped(code, holes) then
            axiomEnsured(afterMain, Axiom.Eta(code, holes))
          else done(afterMain)
        next <- tailcall(
          closureWritten(afterEta.copy(closed = afterEta.closed + 1))
        )
      yield next

  /** An equation of the import set that no step uses, written and popped unless
    * written already.
    */
  private def axiomEnsured(
      state: ArticleState,
      axiom: Axiom
  ): TailRec[ArticleState] =
    if state.axioms.contains(axiom) then done(state)
    else
      axiomStatementWritten(state, axiom).map(written =>
        written
          .line("axiom")
          .line("pop")
          .copy(axioms = written.axioms.updated(axiom, AxiomUse.Popped))
      )

  /** The theorem of an equation of the import set pushed, its axiom written and
    * kept on first use.
    */
  private def axiomTheoremWritten(
      state: ArticleState,
      axiom: Axiom
  ): TailRec[ArticleState] =
    val key = DictionaryKey.AxiomTheorem(axiom)
    state.referenced(key) match
      case Some(referenced) => done(referenced)
      case None             =>
        if state.axioms.get(axiom).contains(AxiomUse.Popped) then
          throw OpentheoryArticleError(
            ArticleErrorReason.AxiomPoppedBeforeUse(axiom)
          )
        axiomStatementWritten(state, axiom).map { written =>
          // A comment that names the library lemma an import is the statement
          // of, which readers skip: a round certificate reads it to name the
          // lemma's Lean statement (`RoundCertificates`).
          // A comment before a β conversion's `axiom`, so that a round
          // certificate checks it at the valuation of the scope it is written
          // in, where its terms may hold eigenvariables; and before a lemma's,
          // naming its library statement, or `# schema` for a lemma the index
          // names nowhere, whose instances a round certificate checks one by
          // one (`LambdaJit.RoundCertificate.schemaInstance`).
          val named = axiom match
            case Axiom.Lemma(lemma) =>
              written.line(
                store
                  .lemmaName(lemma)
                  .fold("# schema")(name => s"# lemma $name")
              )
            case Axiom.Conversion(_, _)     => written.line("# conversion")
            case Axiom.Native(native, _, _) =>
              written.line(
                s"# native $native, with the unique spelling's pattern theorem (docs/design/gezi-set-equations-proofs.md, section 23)"
              )
            case _ => written
          named
            .line("axiom")
            .defined(key)
            .copy(axioms = named.axioms.updated(axiom, AxiomUse.Kept))
        }

  private def axiomStatementWritten(
      state: ArticleState,
      axiom: Axiom
  ): TailRec[ArticleState] =
    val (left, right) = store.axiomStatement(axiom)
    tailcall(
      keyTermWritten(
        state.line("nil"),
        store.key(ArticleTerm.Equation(left, right))
      )
    )

  private def proofKey(proof: ArticleProof): DictionaryKey = proof match
    case ArticleProof.Reflexivity(term) =>
      DictionaryKey.ReflexivityTheorem(store.key(term))
    case _ => DictionaryKey.ProofTheorem(proof)

  /** The theorem of a proof pushed, built once: a proof is stored under its own
    * term, reflexivity under its term's key, and a union or a path under the
    * key of the proof it expands to.
    */
  private def proofWritten(
      state: ArticleState,
      proof: ArticleProof
  ): TailRec[ArticleState] =
    val key = proofKey(proof)
    state.referenced(key) match
      case Some(referenced) => done(referenced)
      case None             =>
        proofExpanded(proof) match
          case Some(expanded) =>
            tailcall(proofWritten(state, expanded)).map(
              _.aliased(key, proofKey(expanded))
            )
          case None => tailcall(proofBuilt(state, proof)).map(_.defined(key))

  /** The proof of a union's step, or the path between two nodes. */
  def proofExpanded(proof: ArticleProof): Option[ArticleProof] = proof match
    case ArticleProof.Edge(union) => Some(matching.edgeProof(union))
    case ArticleProof.Connection(first, second) =>
      Some(pathProof(first, second))
    case _ => None

  /** The unions of the path between two nodes chained, each turned where the
    * path runs from its second node to its first.
    */
  private def pathProof(first: TermId, second: TermId): ArticleProof =
    val steps = forest
      .pathSteps(first, second)
      .getOrElse(
        throw OpentheoryArticleError(
          ArticleErrorReason.NotConnected(first, second)
        )
      )
    val proofs = steps.map(step =>
      if forest.union(step.union).first == step.from then
        ArticleProof.Edge(step.union)
      else ArticleProof.Symmetry(ArticleProof.Edge(step.union))
    )
    proofs.init.foldRight(proofs.last)(ArticleProof.Transitivity(_, _))

  private def proofBuilt(
      state: ArticleState,
      proof: ArticleProof
  ): TailRec[ArticleState] = proof match
    case ArticleProof.Reflexivity(term) =>
      keyTermWritten(state, store.key(term)).map(_.line("refl"))
    case ArticleProof.Symmetry(inner) =>
      tailcall(proofWritten(state, inner)).map(_.line("sym"))
    case ArticleProof.Transitivity(first, second) =>
      for
        afterFirst <- tailcall(proofWritten(state, first))
        afterSecond <- tailcall(proofWritten(afterFirst, second))
      yield afterSecond.line("trans")
    case ArticleProof.Congruence(shape, proofs) =>
      congruenceWritten(state, shape, proofs)
    case ArticleProof.Instance(axiom, substitution) =>
      if substitution.isEmpty then axiomTheoremWritten(state, axiom)
      else
        for
          substituted <- substitutionWritten(state, substitution)
          axiomWritten <- axiomTheoremWritten(substituted, axiom)
        yield axiomWritten.line("subst")
    case ArticleProof.Edge(_) | ArticleProof.Connection(_, _) =>
      throw IllegalStateException(s"the proof $proof expands and is not built")
    case ArticleProof.Conversion(first, second, _)
        if OpentheoryArticle.conversionUnwritable(store.terms, first, second) =>
      throw OpentheoryArticleError(
        ArticleErrorReason.Unproved(UnprovedKind.BetaConversion, first, second)
      )
    case ArticleProof.Conversion(first, second, reduct) =>
      if reduct == second then
        axiomTheoremWritten(state, Axiom.Conversion(first, second))
      else
        assert(
          reduct == first,
          s"the reduct $reduct of a conversion is neither of its terms"
        )
        axiomTheoremWritten(state, Axiom.Conversion(second, first))
          .map(_.line("sym"))
    // The abstraction rule ξ, which no command of the article's logic is:
    // the theorem of the opened bodies, between comments that name the
    // eigenvariables, popped, then the closures' equation as an import,
    // which a round certificate proves from the popped theorem
    // (`LambdaJit.RoundCertificate.abstracted`) and the Lean reader refuses.
    // The import is no axiom theorem of the dictionary, so that the comments
    // always precede an `axiom`.
    case ArticleProof.Abstraction(first, second, eigenvariables, _, inner) =>
      val names = eigenvariables.map(eigenvariable =>
        store.terms
          .opaqueName(eigenvariable)
          .getOrElse(
            throw IllegalStateException(
              s"the eigenvariable $eigenvariable is no opaque term"
            )
          )
      )
      val opened = state.line(
        s"# abstraction begin ${names.map(OpentheoryArticle.quotedName).mkString(" ")}"
      )
      for
        body <- tailcall(proofWritten(opened, inner))
        closures <- tailcall(
          keyTermWritten(
            body.line("# abstraction end").line("pop").line("nil"),
            store.key(
              ArticleTerm
                .Equation(ArticleTerm.Stored(first), ArticleTerm.Stored(second))
            )
          )
        )
      yield closures.line("axiom")

  /** `refl` of the layer's constant, then `appThm` with each child's theorem in
    * argument order.
    */
  private def congruenceWritten(
      state: ArticleState,
      shape: LayerShape,
      proofs: Vector[ArticleProof]
  ): TailRec[ArticleState] =
    val symbol = shape match
      case LayerShape.Thunk(code, holes) => HolSymbol.Thunk(code, holes)
      case LayerShape.Apply              => HolSymbol.Apply
      case LayerShape.Parallel           => HolSymbol.Parallel
      case LayerShape.Choice             => HolSymbol.Choice
    sequenced(symbolReflexivityWritten(state, symbol), proofs.toList)(
      (current, proof) =>
        tailcall(proofWritten(current, proof)).map(_.line("appThm"))
    )

  private def symbolReflexivityWritten(
      state: ArticleState,
      symbol: HolSymbol
  ): ArticleState =
    val key = DictionaryKey.SymbolReflexivityTheorem(symbol)
    state
      .referenced(key)
      .getOrElse(symbolWritten(state, symbol).line("refl").defined(key))

  /** The argument of `subst`: no type substitution and one `[variable, term]`
    * pair per binding.
    */
  private def substitutionWritten(
      state: ArticleState,
      substitution: Vector[(String, ArticleTerm)]
  ): TailRec[ArticleState] =
    sequenced(state.line("nil"), substitution.toList) {
      case (current, (name, term)) =>
        tailcall(
          keyTermWritten(variableObjectWritten(current, name), store.key(term))
        )
          .map(_.line("nil").conses(2))
    }.map(_.line("nil").conses(substitution.size).line("nil").conses(2))

  /** The term of a key pushed, built once, as `Encoding.encoding` encodes it; a
    * key whose term is another key's term is stored under that key's number.
    */
  private def keyTermWritten(
      state: ArticleState,
      key: ArticleTerm
  ): TailRec[ArticleState] =
    val dictionaryKey = DictionaryKey.Term(key)
    state.referenced(dictionaryKey) match
      case Some(referenced) => done(referenced)
      case None             =>
        encoding.encoding(key) match
          case TermEncoding.AliasSymbol(symbol) =>
            done(
              symbolWritten(state, symbol)
                .aliased(dictionaryKey, DictionaryKey.Symbol(symbol))
            )
          case TermEncoding.Variable(name) =>
            done(
              variableObjectWritten(state, name)
                .line("varTerm")
                .defined(dictionaryKey)
            )
          case TermEncoding.Applied(symbol, arguments) =>
            sequenced(symbolWritten(state, symbol), arguments.toList)(
              (current, argument) =>
                tailcall(keyTermWritten(current, store.key(argument)))
                  .map(_.line("appTerm"))
            ).map(_.defined(dictionaryKey))

  private def variableObjectWritten(
      state: ArticleState,
      name: String
  ): ArticleState =
    val key = DictionaryKey.VariableObject(name)
    state
      .referenced(key)
      .getOrElse(
        typeWritten(state.name(Vector(name)), HolType.Term)
          .line("var")
          .defined(key)
      )

  /** The term of a HOL constant pushed: the name, `const`, its type,
    * `constTerm`. A thunk constant, the first time it occurs, takes the next
    * number, `LambdaJit.thunk.N`, and is defined by `defineConst` as its
    * defining term (`ThunkDefinitions`): the name, the defining term,
    * `defineConst`, and `pop` of the definitional theorem, which no step uses,
    * leaving the constant for `constTerm`.
    */
  private def symbolWritten(
      state: ArticleState,
      symbol: HolSymbol
  ): ArticleState =
    val key = DictionaryKey.Symbol(symbol)
    state.referenced(key).getOrElse {
      val constantPushed = symbol match
        case HolSymbol.Thunk(code, holes) =>
          val named = state.name(ThunkDefinitions.name(state.constants.size))
          val defining =
            DefinitionPart.Defining(code, holes, store.thunkArity(code, holes))
          val defined = definitionPartWritten(named, defining).result
            .line("defineConst")
            .line("pop")
          defined.copy(constants = defined.constants :+ (code, holes))
        case _ => state.name(encoding.symbolName(symbol)).line("const")
      typeWritten(constantPushed, encoding.symbolType(symbol))
        .line("constTerm")
        .defined(key)
    }

  /** A part of a thunk constant's defining term pushed, built once: its head
    * constant, then each part it is applied to with `appTerm`. A trampoline: a
    * code is as deep as a body, and a number is unary.
    */
  private def definitionPartWritten(
      state: ArticleState,
      part: DefinitionPart
  ): TailRec[ArticleState] =
    val key = DictionaryKey.DefinitionPartTerm(part)
    state.referenced(key) match
      case Some(referenced) => done(referenced)
      case None             =>
        val (constant, arguments) = ThunkDefinitions.layer(part)
        sequenced(definitionConstantWritten(state, constant), arguments.toList)(
          (current, argument) =>
            tailcall(definitionPartWritten(current, argument)).map(
              _.line("appTerm")
            )
        ).map(_.defined(key))

  /** The term of a constant of a defining term pushed, built once. */
  private def definitionConstantWritten(
      state: ArticleState,
      constant: DefinitionConstant
  ): ArticleState =
    val key = DictionaryKey.DefinitionConstantTerm(constant)
    state
      .referenced(key)
      .getOrElse(
        typeWritten(
          state.name(ThunkDefinitions.constantName(constant)).line("const"),
          ThunkDefinitions.constantType(constant)
        )
          .line("constTerm")
          .defined(key)
      )

  /** A type pushed, built once: its operator, each argument type, the list of
    * them and `opType`. A trampoline: a thunk constant's type nests one
    * function type per filling.
    */
  private def typeWritten(state: ArticleState, holType: HolType): ArticleState =
    typeWrittenTrampolined(state, holType).result

  private def typeWrittenTrampolined(
      state: ArticleState,
      holType: HolType
  ): TailRec[ArticleState] =
    val key = DictionaryKey.Type(holType)
    state.referenced(key) match
      case Some(referenced) => done(referenced)
      case None             =>
        val (operator, arguments) = encoding.typeOperator(holType)
        val afterOperator = operatorWritten(state, operator, arguments)
        sequenced(afterOperator, arguments.toList)((current, argument) =>
          tailcall(typeWrittenTrampolined(current, argument))
        ).map(_.line("nil").conses(arguments.size).line("opType").defined(key))

  /** A type operator pushed. An operator applied to arguments is stored in the
    * dictionary, since it makes many types; one applied to none makes one type,
    * which `typeWritten` stores, so it is written once without being stored.
    */
  private def operatorWritten(
      state: ArticleState,
      operator: TypeOperator,
      arguments: Vector[HolType]
  ): ArticleState =
    def objectWritten(current: ArticleState) =
      current.name(encoding.operatorName(operator)).line("typeOp")
    if arguments.isEmpty then objectWritten(state)
    else
      val key = DictionaryKey.Operator(operator)
      state.referenced(key).getOrElse(objectWritten(state).defined(key))

  private def sequenced[Item](state: ArticleState, items: List[Item])(
      step: (ArticleState, Item) => TailRec[ArticleState]
  ): TailRec[ArticleState] = items match
    case Nil          => done(state)
    case item :: rest =>
      tailcall(step(state, item)).flatMap(next =>
        tailcall(sequenced(next, rest)(step))
      )
