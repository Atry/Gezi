package gezi.proofs

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import gezi.standardlibrary.LemmaNamed
import gezi.standardlibrary.LemmaProof
import gezi.standardlibrary.ProofCitations
import gezi.standardlibrary.StandardLibrary
import gezi.ir.Code
import gezi.ir.CodeLayer
import gezi.ir.Hole
import gezi.ir.LemmaIdentifier
import gezi.ir.NativeSpecializer
import gezi.ir.StorageAccess
import gezi.standardlibrary.StandardLibraryIndex
import gezi.lemmaencoding.EncodedLemma
import scala.jdk.StreamConverters.*
import gezi.ir
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.tailcall

/** Why the export refused a library, the Prolog export's
  * `lean_statements_error(Reason)`.
  */
enum LeanStatementsErrorReason:
  case NotAWord(word: String)
  case NoDeclaration(name: String)
  case ControlCharacter(code: Int)
  case UnwritableProof(name: String, proof: String)
  case NotAName(components: Vector[String])

/** The export's refusal. */
final case class LeanStatementsError(reason: LeanStatementsErrorReason)
    extends RuntimeException(s"Lean statements: $reason")

/** One lemma of the export: its name, the HOL terms of its import with the
  * thunks of their thunk constants (numbered from 0 in the statement),
  * and its proof metadata, the fifth field of its lemma tuple in the
  * knowledge.
  */
private final case class LemmaStatement(
    name: String,
    left: HolTerm,
    right: HolTerm,
    definitions: Vector[(Code, Vector[Hole])],
    proof: LemmaProof
)

/** The library's lemma statements as a Lean module, the port of
  * `gezi/prolog/gezi/lean_statements.pl`: the export of the library's lemma
  * statements in the form the end-to-end theorem takes (Lean module `EndToEnd`). `text` writes a Lean module,
  * generated and not edited, that imports `LambdaJit.LemmaSoundness` and
  * declares, in the
  * namespace `LambdaJit.Exported`, for every lemma name of the index of the
  * compiled library, in the order of the index (`names`):
  *
  *   - `Statement.«Name»`, the lemma's statement, an `EndToEnd.Statement`:
  *     the two sides of the equation that an OpenTheory article imports for
  *     the lemma, as `Article.Term` values (Lean module `Article`), with the
  *     signature of their thunk constants, numbered from 0 in the statement
  *     so that a statement does not change when another lemma is added. The sides are the HOL
  *     terms of `OpentheoryArticle.lemmaStatementEncoded`, built by the
  *     functions that write the article's `axiom` command, so that
  *     `EndToEnd.importChecked` recognises the article's import of the
  *     statement, its thunk constants numbered otherwise, by `agree` under
  *     the two signatures.
  *   - `«Name»`, the statement's soundness,
  *     `EndToEnd.Statement.Sound`. The command `lemma_soundness` of
  *     the Lean module `LemmaSoundness` declares it as a theorem proved by
  *     the hand-written proof `LambdaJit.LibraryLemmaProofs.«Name»`
  *     when the Lean module `LibraryLemmaProofs` holds one whose type is
  *     definitionally equal to it; otherwise as a theorem proved by the first
  *     of six decisions of the Lean module `StatementNormalisation` that the
  *     kernel evaluates to `true` on the statement. When none applies it
  *     declares a named axiom. Whether a lemma is a theorem is so the
  *     environment and the kernel's evaluation, not a list of names here: a
  *     lemma that can be proved is a theorem, not an axiom. The module writes one docstring per lemma,
  *     which cites the lemma's proof, the fifth field of its lemma tuple in
  *     the knowledge (`LemmaProof`), its content as it is: a munit suite, a
  *     Markdown link to the document of a proof on paper, or a TeX citation
  *     (`proofCitation`). The command adds a paragraph that
  *     says which proof or decision proved the theorem, or, for an axiom, a
  *     FIXME that says none did (the generated text that
  *     lean_statements.pl:56, :204 and :315 described, carried here).
  *
  * and then `lemmas`, the list of every statement, and `lemmasSound`, its
  * soundness: the lemma list of `EndToEnd.endToEndOfChecked`. `soundNil` and
  * `soundCons` give the soundness of a shorter list, so that a theorem that
  * uses some of the lemmas depends on the axioms of those of them that are
  * axioms only.
  *
  * It reads the index's declarations and lemma sides and the strategies'
  * encodings of the lemmas into patterns (`EncodedLemma`), the latter two
  * through `lemmaStatementEncoded`, and, for the docstrings, the proof of
  * each lemma tuple of the knowledge files, which it copies into the text
  * and does not interpret beyond naming its kind. It holds no type and no
  * rule.
  *
  * The text names this export as its writer (`header`); the committed Lean
  * module `NativeRouteLibraryStatements` is its output.
  *
  * FIXME (2026-10-07, 2026-10-08; carried from lean_statements.pl:72): a https://github.com/Atry/private-overlay/issues/1981
  * lemma that has no hand-written proof in the Lean module
  * LibraryLemmaProofs and that none of the six decisions proves stays a
  * named axiom. Of the 36 lemmas of prelude, guard_laws, parallel_types,
  * filtered_recursion_naturals, lattice_types and contracts none does
  * (`LeanStatementsTest`, `expectedKindCounts`, the reading of 2026-11-19):
  * 2 are instances of the numbered equations (8) and (9), 14 are proved by
  * the decision of absorbed members, 4 by the normaliser, 4 by leftmost
  * outermost contraction and 12 by hand. Of the 89 lemmas of the native
  * route's modules native_types, native_arithmetic, hindley_milner_unions,
  * native_arithmetic_unions, occurrence_erasure, closure_application and
  * prolog_backend_shapes, none does either (`LeanStatementsNativeRouteTest`,
  * `expectedKinds`, which pins the decision of each, the reading of
  * 2026-11-21): 1 is an instance of the numbered equation (6), 3 are proved
  * by the normal form within the long fuel and 85 by the decision of
  * absorbed members. The lemmas of the other knowledge modules have not been exported
  * to Lean by any test, and a hand-written proof covers only the statement it
  * copies: a lemma added to these modules, or a change of the encoding, can
  * make an axiom or, for a copied statement, a build error, until a proof is
  * written.
  */
object LeanStatements:

  /** The name of every lemma of the index that has sides, in the order of
    * the index: the names of the soundness declarations that `text` writes.
    * A lemma knows no knowledge file, so its name alone names its statement.
    */
  def names(library: StandardLibrary): Vector[String] =
    library.index.lemmaNames.collect {
      case LemmaNamed(lemma, name) if library.index.sides(lemma).isDefined => name
    }

  /** The Lean module of the statements of the library, each named after its
    * lemma. `repository` is the monorepo's root, against which the Markdown
    * link of every `md` proof is checked (`ProofCitations.citationsChecked`,
    * which throws `StandardLibraryMalformed` with `BrokenCitation`). `index`
    * is the library's index in the configuration of the articles (an
    * entry's, the library crossed into its facts), and `lemmas` are the search
    * strategies' encodings of the lemmas into patterns in that configuration,
    * from which a statement is built as an article builds its import, a
    * storage written as its view. Throws `LeanStatementsError`, and
    * `OpentheoryArticleError` as the article writer does on a lemma.
    */
  def text[C <: NativeSpecializer & Singleton](
      library: StandardLibrary,
      index: StandardLibraryIndex[C],
      lemmas: Vector[EncodedLemma[C]],
      repository: Path
  )(using StorageAccess): String =
    selectedText(library, index, lemmas, repository, names(library))

  /** The module of `text` with the statements of the lemmas `lemmaNames`
    * only, in that order: what a round certificate imports of an entry's
    * library (`gezi.contest.entry.generic.EntryArticleVerification`),
    * so that Lean elaborates the soundness of those lemmas only. Throws as `text` does, and `LeanStatementsError`
    * with `NoDeclaration` for a name that is no lemma of the library.
    */
  def selectedText[C <: NativeSpecializer & Singleton](
      library: StandardLibrary,
      index: StandardLibraryIndex[C],
      lemmas: Vector[EncodedLemma[C]],
      repository: Path,
      lemmaNames: Vector[String]
  )(using StorageAccess): String =
    lemmaNames.foreach(checkedWord)
    val statements = lemmaNames.map(lemmaStatement(library, index, lemmas, _))
    ProofCitations.citationsChecked(statements.map(statement => statement.name -> statement.proof).toMap, repository)
    val shared = sharedTerms(statements.flatMap(statement => Vector(statement.left, statement.right)))
    header +
      "namespace Statement\n\n" +
      sharedText(shared) +
      statements.map(statementText(_, shared.names)).mkString +
      "end Statement\n\n" +
      statements.map(soundnessText).mkString +
      lemmasText(statements) +
      "end LambdaJit.Exported\n"

  /** Writes the module of `text` to the file, replacing it, in UTF-8. */
  def written[C <: NativeSpecializer & Singleton](
      library: StandardLibrary,
      index: StandardLibraryIndex[C],
      lemmas: Vector[EncodedLemma[C]],
      repository: Path,
      file: Path
  )(using StorageAccess): Unit =
    Files.writeString(file, text(library, index, lemmas, repository), StandardCharsets.UTF_8)

  /** A Lean string literal of the text: its quotes and backslashes escaped.
    * Throws `LeanStatementsError` with `ControlCharacter` for a control
    * character.
    */
  def stringLiteral(text: String): String =
    "\"" + text.codePoints.toScala(Vector).map { code =>
      if code == '"' then "\\\""
      else if code == '\\' then "\\\\"
      else if code >= 32 && code != 127 then String(Character.toChars(code))
      else throw LeanStatementsError(LeanStatementsErrorReason.ControlCharacter(code))
    }.mkString + "\""

  private def lemmaStatement[C <: NativeSpecializer & Singleton](
      library: StandardLibrary,
      index: StandardLibraryIndex[C],
      lemmas: Vector[EncodedLemma[C]],
      name: String
  )(using StorageAccess): LemmaStatement =
    val lemma = library.index.lemmaNames.collectFirst {
      case LemmaNamed(lemma, `name`) if library.index.sides(lemma).isDefined => lemma
    }.getOrElse(throw LeanStatementsError(LeanStatementsErrorReason.NoDeclaration(name)))
    val named = OpentheoryArticle.lemmaStatementEncoded(index, lemmas, lemma)
    val Vector(left, right) = named.terms: @unchecked
    val proof = library
      .lemmaProof(name)
      .getOrElse(throw LeanStatementsError(LeanStatementsErrorReason.NoDeclaration(name)))
    LemmaStatement(name, left, right, named.definitions, proof)

  /** A lemma name is a word Lean reads between guillemets and
    * inside a docstring: lower-case letters, digits and underscores.
    */
  private def checkedWord(word: String): Unit =
    if !isWord(word) then throw LeanStatementsError(LeanStatementsErrorReason.NotAWord(word))

  private def isWord(word: String): Boolean =
    word.nonEmpty && word.forall(character =>
      (character >= 'a' && character <= 'z') || (character >= '0' && character <= '9') || character == '_'
    )

  private val header: String =
    """import LambdaJit.LemmaSoundness
      |
      |/-!
      |# The library's lemma statements
      |
      |Written by `LeanStatements.text` of
      |`gezi/proofs/src/main/scala/gezi/proofs/LeanStatements.scala` from the index of a
      |compiled library (docs/design/gezi-lean-verification.md D5); generated, not edited. For each
      |lemma, `Statement.«Name»` is the two sides of the equation that an OpenTheory article written by
      |`gezi/proofs/src/main/scala/gezi/proofs/OpentheoryArticle.scala` imports for it, built by
      |the writer's own encoding, with the signature of their thunk constants, numbered from 0 in the
      |statement (D7.1), so that `EndToEnd.importChecked` recognises the import under the article's
      |signature; and `«Name»` is the statement's soundness, declared by the command
      |`lemma_soundness` (module `LemmaSoundness`): a theorem from the hand-written proof of module
      |`LibraryLemmaProofs` of the same name, or from the first decision of module
      |`StatementNormalisation` that the kernel evaluates to `true` on the statement, and a named axiom
      |when there is none. Each docstring cites the lemma's proof and says what proved the theorem; an
      |axiom's says, under a FIXME, that nothing did. `lemmas` lists
      |every statement and `lemmasSound` proves them sound from the theorems and the axioms: the lemma
      |list of `EndToEnd.endToEndOfChecked`. A theorem that uses some lemmas only builds its list with
      |`soundCons` and `soundNil`, and depends on the axioms of those of them that are axioms only.
      |-/
      |
      |namespace LambdaJit.Exported
      |
      |open LambdaJit.EndToEnd (Statement)
      |
      |-- A marker's code in R7's spelling (https://github.com/Atry/private-overlay/issues/1509, T4), a partial
      |-- function of a literal applied to the literal's bits, nests about 105 applications in a signature; at
      |-- Lean's default of 512 the statements' elaboration reached the maximum recursion depth (measured
      |-- 2026-11-19, SelectedStatementsCertificateTest), at 1024 it builds.
      |set_option maxRecDepth 1024
      |
      |/-- Every statement of the empty list is sound. -/
      |theorem soundNil : ∀ lemma ∈ ([] : List Statement), lemma.Sound :=
      |  fun _ member => nomatch member
      |
      |/-- Every statement of `first :: rest` is sound when `first` is and every statement of `rest`
      |is. -/
      |theorem soundCons {first : Statement} {rest : List Statement} (firstSound : first.Sound)
      |    (restSound : ∀ lemma ∈ rest, lemma.Sound) : ∀ lemma ∈ first :: rest, lemma.Sound := by
      |  intro lemma member
      |  cases member with
      |  | head => exact firstSound
      |  | tail _ member => exact restSound lemma member
      |
      |""".stripMargin

  /** The terms of the statements' sides that occur more than once, each
    * named by a definition of its own (`Shared.term<n>`), in an order in which
    * every definition names only those before it.
    *
    * In the markers' spelling as tags, `(λ"$t". M) "$t"`, every occurrence of a marker carries its function, a partial
    * function of a literal applied to the literal's bits, about 105 nested
    * applications, and a finite term spells every occurrence out: the
    * native route's 89 statements were 192,203 lines written in full against
    * 18,981 in the spelling before it (measured 2026-11-19). A definition
    * stands for its term by δ, so a statement means what it meant.
    */
  private final case class SharedTerms(names: Map[HolTerm, String], definitions: Vector[(String, HolTerm)])

  /** `SharedTerms` of the sides: a constant or an application met more than
    * once, counted where the walk meets it, a term below one met before
    * not counted again.
    */
  private def sharedTerms(sides: Vector[HolTerm]): SharedTerms =
    def counted(term: HolTerm, counts: Map[HolTerm, Int]): Map[HolTerm, Int] =
      val seen = counts.getOrElse(term, 0)
      val bumped = counts.updated(term, seen + 1)
      if seen > 0 then bumped
      else
        term match
          case HolTerm.Application(function, argument) => counted(argument, counted(function, bumped))
          case HolTerm.Constant(_, _) | HolTerm.Variable(_, _) => bumped
    val counts = sides.foldLeft(Map.empty[HolTerm, Int])((counts, side) => counted(side, counts))
    def repeated(term: HolTerm): Boolean = term match
      case HolTerm.Variable(_, _) => false
      case _                      => counts.getOrElse(term, 0) > 1
    def defined(term: HolTerm, done: SharedTerms): SharedTerms =
      if done.names.contains(term) then done
      else
        val below = term match
          case HolTerm.Application(function, argument) => defined(argument, defined(function, done))
          case HolTerm.Constant(_, _) | HolTerm.Variable(_, _) => done
        if repeated(term) then
          val name = s"Shared.term${below.definitions.size}"
          SharedTerms(below.names.updated(term, name), below.definitions :+ (name -> term))
        else below
    sides.foldLeft(SharedTerms(Map.empty, Vector.empty))((done, side) => defined(side, done))

  /** The definitions of the shared terms, in the namespace `Shared`. */
  private def sharedText(shared: SharedTerms): String =
    if shared.definitions.isEmpty then ""
    else
      "namespace Shared\n\n" +
        shared.definitions.map { (name, term) =>
          s"def ${name.stripPrefix("Shared.")} : Article.Term :=\n  " + termText(term, 2, shared.names) + "\n\n"
        }.mkString +
        "end Shared\n\n"

  /** The definition of a lemma's statement. */
  private def statementText(statement: LemmaStatement, shared: Map[HolTerm, String]): String =
    val LemmaStatement(name, left, right, definitions, _) = statement
    val signature = definitions.zipWithIndex.map { case ((code, holes), number) =>
      s"(${nameText(ThunkDefinitions.name(number))}, ${codeText(code)}, ${holesText(holes)})"
    }
    s"/-- The statement of the lemma `$name`:\n" +
      "the two sides of the equation that an article imports for it, with the signature of their\n" +
      "thunk constants. -/\n" +
      s"def «$name» : EndToEnd.Statement :=\n" +
      "  { signature := [" + signature.mkString(",\n      ") + "],\n" +
      "    left := (" + sideText(left, shared) + "),\n" +
      "    right := (" + sideText(right, shared) + ") }\n\n"

  /** A side of a statement: its shared term's name, or the term. */
  private def sideText(term: HolTerm, shared: Map[HolTerm, String]): String =
    shared.getOrElse(term, termText(term, 6, shared))

  /** A code as a Lean `Code` value, as deep as the code: a marker's code in
    * its spelling as a tag nests about 105 applications, for which the module raises
    * `maxRecDepth` (`header`).
    */
  private def codeText(code: Code): String = code.layer match
    case ir.Slot(index)          => s"(.slot $index)"
    case ir.Apply(left, right)    => s"(.apply ${codeText(left)} ${codeText(right)})"
    case ir.Choice(left, right)   => s"(.choice ${codeText(left)} ${codeText(right)})"
    case ir.Parallel(left, right) => s"(.parallel ${codeText(left)} ${codeText(right)})"
    case ir.Thunk(inner, holes, fillings) =>
      s"(.thunk ${codeText(inner)} ${holesText(holes)} [${fillings.map(codeText).mkString(", ")}])"

  /** Holes as a Lean list of `Hole` values. */
  private def holesText(holes: Vector[Hole]): String =
    holes.map {
      case Hole.Bound(slot) => s".slot $slot"
      case Hole.Ignored     => ".ignored"
    }.mkString("[", ", ", "]")

  /** A HOL term as a Lean `Article.Term`, without its outer parentheses; an
    * application's two operands are on lines of their own, indented below
    * it.
    */
  private def termText(term: HolTerm, indentation: Int, shared: Map[HolTerm, String]): String = term match
    case HolTerm.Application(function, argument) =>
      val inner = indentation + 2
      ".application\n" + operandText(function, inner, shared) + "\n" + operandText(argument, inner, shared)
    case HolTerm.Constant(name, typeTerm) => s".constant ${nameText(name)} ${typeText(typeTerm)}"
    case HolTerm.Variable(name, typeTerm) => s".termVariable ${nameText(name)} ${typeText(typeTerm)}"

  /** An operand: the name of its shared term, or the term in parentheses. */
  private def operandText(term: HolTerm, indentation: Int, shared: Map[HolTerm, String]): String =
    " " * indentation + shared.get(term).getOrElse("(" + termText(term, indentation, shared) + ")")

  /** A HOL type as a Lean `Article.LogicType`, built as a trampoline: a
    * thunk constant's type nests one function type per filling.
    */
  private def typeText(typeTerm: HolTypeTerm): String = typeTextBuilt(typeTerm).result

  private def typeTextBuilt(typeTerm: HolTypeTerm): TailRec[String] =
    ArticleStore
      .traversed(typeTerm.arguments)(argument => tailcall(typeTextBuilt(argument)))
      .map(arguments => s"(.operator ${nameText(typeTerm.name)} [${arguments.mkString(", ")}])")

  /** A name, its namespace's components and its local name, as a Lean
    * `Article.Name`.
    */
  private def nameText(components: Vector[String]): String = components match
    case namespace :+ local => s"⟨[${namespace.map(stringLiteral).mkString(", ")}], ${stringLiteral(local)}⟩"
    case _                  => throw LeanStatementsError(LeanStatementsErrorReason.NotAName(components))

  /** The command that declares a statement's soundness, with its docstring:
    * what the soundness says and the lemma's proof. The command adds the
    * paragraph that says what proved the theorem, or, for an axiom, the
    * FIXME that says none did.
    */
  private def soundnessText(statement: LemmaStatement): String =
    val LemmaStatement(name, _, _, _, proof) = statement
    val citation = proofCitation(name, proof)
    s"lemma_soundness «$name» of Statement.«$name»\n" +
      s"/-- The lemma `$name` is sound:\n" +
      "the two sides of its statement are contextually equivalent (≃_O of DdLP96's Definition 14)\n" +
      "under every valuation of its metavariables.\n\n" +
      s"The proof its declaration cites: $citation -/\n\n"

  /** The words that cite a lemma's proof (`LemmaProof`), its content as it
    * is after the name of its kind: a munit suite, a Markdown link (which
    * `text` has checked against the repository) or a TeX citation. A
    * content that holds `/-` or `-/`, which would open or close a Lean
    * comment inside the docstring, throws `UnwritableProof`.
    */
  private def proofCitation(name: String, proof: LemmaProof): String =
    val content = proof.content
    if content.contains("/-") || content.contains("-/") then
      throw LeanStatementsError(LeanStatementsErrorReason.UnwritableProof(name, content))
    proof match
      case LemmaProof.Munit(suite)    => s"the munit suite\n`$suite`."
      case LemmaProof.Markdown(link)  => s"the Markdown link\n$link."
      case LemmaProof.Tex(citation)   => s"the TeX citation\n`$citation`."

  /** The list of every statement and its soundness, one `soundCons` per
    * statement.
    */
  private def lemmasText(statements: Vector[LemmaStatement]): String =
    val joined = statements.map(statement => s"Statement.«${statement.name}»").mkString(",\n    ")
    "/-- The statements of every lemma of the library, in the order of the index: the lemma list of\n" +
      "`EndToEnd.endToEndOfChecked`. -/\n" +
      "def lemmas : List EndToEnd.Statement :=\n" +
      s"  [$joined]\n\n" +
      "/-- Every statement of `lemmas` is sound, by the soundness declarations; `#print axioms` lists\n" +
      "those of them that are named axioms for a theorem that uses this. -/\n" +
      "theorem lemmasSound : ∀ lemma ∈ lemmas, lemma.Sound :=\n" +
      statements.map(statement => s"  soundCons «${statement.name}» <|\n").mkString +
      "  soundNil\n\n"
