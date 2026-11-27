package gezi.proofs

import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls
import scala.util.control.TailCalls.tailcall

/** A name of an article: its namespace components and its local name. */
final case class ReplayName(namespace: Vector[String], local: String)

/** A type of an article's higher order logic.
  *
  * Stack-safe: a thunk constant's type nests one function type per filling,
  * thousands deep, so an operator type computes its hash code once, when it is
  * made, from its parts' (made before it), and compares by a loop over the
  * pairs of types still to compare.
  */
sealed abstract class ReplayType extends Product with Serializable

/** The types of an article's higher order logic. */
object ReplayType:
  final case class Variable(name: ReplayName) extends ReplayType

  final case class Operator(name: ReplayName, arguments: Vector[ReplayType])
      extends ReplayType:
    override val hashCode: Int =
      scala.util.hashing.MurmurHash3.productHash(this)
    override def equals(other: Any): Boolean = other match
      case that: ReplayType => equal(List((this, that)))
      case _                => false

  /** Whether the two types of each pair are equal: the same object, two
    * variables of one name, or two operators of one hash code and one name
    * whose arguments are equal in order.
    */
  @scala.annotation.tailrec
  private def equal(pending: List[(ReplayType, ReplayType)]): Boolean =
    pending match
      case Nil                     => true
      case (first, second) :: rest =>
        if first eq second then equal(rest)
        else
          (first, second) match
            case (Variable(firstName), Variable(secondName)) =>
              firstName == secondName && equal(rest)
            case (
                  firstOperator @ Operator(firstName, firstArguments),
                  secondOperator @ Operator(secondName, secondArguments)
                ) =>
              if firstOperator.hashCode != secondOperator.hashCode || firstName != secondName ||
                firstArguments.size != secondArguments.size
              then false
              else equal(firstArguments.zip(secondArguments).toList ++ rest)
            case _ => false

/** A term of an article's higher order logic. */
enum ReplayTerm:
  case Variable(name: ReplayName, replayType: ReplayType)
  case Constant(name: ReplayName, replayType: ReplayType)
  case Application(function: ReplayTerm, argument: ReplayTerm)

/** A term with the index of its Lean data (`LambdaJit.Article.Term`) in the
  * export.
  */
final case class ExportedTerm(term: ReplayTerm, data: Int)

/** An object of the article's virtual machine, as the certificate replays it:
  * each type, variable and term carries the index of its Lean data, and each
  * theorem the index of its proof, an expression of type
  * `EquationSound signature left right`.
  */
enum ReplayObject:
  case Number(value: BigInt)
  case Name(name: ReplayName)
  case Items(items: Vector[ReplayObject])
  case TypeOperator(name: ReplayName)
  case ConstantName(name: ReplayName)
  case TypeObject(replayType: ReplayType, data: Int)
  case VariableObject(name: ReplayName, replayType: ReplayType, data: Int)
  case TermObject(term: ExportedTerm)
  case Theorem(
      left: ExportedTerm,
      right: ExportedTerm,
      proof: Int,
      validity: ReplayValidity
  )
  case Definition(name: ReplayName)

  /** The import of a lemma the article names no library statement of (`#
    * schema`): no theorem until `subst` instantiates it
    * (`LambdaJit.RoundCertificate.schemaInstance`).
    */
  case Schema(left: ExportedTerm, right: ExportedTerm)

/** A scope of eigenvariables, the innermost first, each a term variable by its
  * name and type, with the index of its Lean data, a `List (Name × LogicType)`
  * (`LambdaJit.RoundCertificate.scopeValuation`).
  */
final case class ReplayScope(
    eigenvariables: Vector[(ReplayName, ReplayType)],
    data: Int
)

/** Where a theorem's proof holds: at every valuation, a proof of
  * `EquationSound signature left right`; or at the valuation of a scope, a
  * proof of `ScopedSound signature scope left right`.
  */
enum ReplayValidity:
  case Everywhere
  case Scoped(scope: ReplayScope)

/** An abstraction step whose body is being replayed: the scope the body is
  * proved in, the scope around the step, and the Lean data of the step's
  * eigenvariables in lambda order, the outermost first.
  */
final case class ReplayAbstraction(
    inner: ReplayScope,
    outer: ReplayScope,
    eigenvariables: Int
)

/** The state of the replay: the export written so far, the stack (its top
  * first), the dictionary, the constants `defineConst` defined (each a pair of
  * the name's data and the term's data, in order), the theorems `thm` exported,
  * the library lemma the comment before the next `axiom` names, whether that
  * comment marks the next `axiom` as a β conversion, the abstraction steps
  * whose bodies are being replayed (the innermost first), whether the next
  * `pop` pops an abstraction step's body, and the body popped, with its step,
  * that the next `axiom` concludes from.
  */
final case class ReplayState(
    leanExport: LeanExport,
    stack: List[ReplayObject],
    dictionary: Map[BigInt, ReplayObject],
    definitions: Vector[Int],
    exported: Vector[ReplayObject.Theorem],
    namedLemma: Option[String],
    schema: Boolean,
    conversion: Boolean,
    abstractions: List[ReplayAbstraction],
    closing: Boolean,
    closed: Option[(ReplayObject.Theorem, ReplayAbstraction)]
)

/** The certificate of an article: a declaration of Lean's export format whose
  * type is `EquationSound signature left right` for the article's exported
  * equation, and whose value is the article's proof, each inference a theorem
  * of `LambdaJit.RoundCertificate` applied to explicit arguments. The article's
  * commands are replayed as Lean's reader runs them (`LambdaJit.Article.step`),
  * so the terms are the reader's; but no reader runs in the checker: the
  * signature is the definition `signatureOf definitions` over the article's
  * definitions as data, and each import is accepted by the checker evaluating
  * `importChecked`.
  *
  * This writer is not trusted: a certificate it writes wrong is one the checker
  * rejects. It throws `IllegalArgumentException` on an article it cannot
  * replay.
  *
  * The theorem is Definition 14's: `EquationSound` is contextual equivalence
  * ≃_O, in which the correctness of every rewrite is proved; ⊢ and the other
  * semantics are means to prove it. The check is prior work's tools,
  * lean4export and nanoda (`CertificateChecks`), not a bridge of our own, so
  * that the trusted base is that prior work and the few lines of the build that
  * call it. An article's `axiom` command is an import, not an axiom: axioms are
  * used in the lemmas a rewrite calls, and the rewrite's trace calls none. A
  * trace is checked either as Lean source or as Lean's export format, one or
  * the other; the export is written, as the prototype's readings favoured.
  */
object RoundCertificates:

  private val certificate = "LambdaJit.RoundCertificate"

  /** The export continuing `leanExport` with the definition
    * `<namespace>.signature` and the theorem `<namespace>.round`, the
    * certificate of the one theorem `article` exports. An import of a library
    * lemma, which the article writer marks with the comment `# lemma <Name>`,
    * is accepted under the list of that one statement,
    * `[LambdaJit.Exported.Statement.«Name»]`, sound by the lemma's own
    * soundness `LambdaJit.Exported.«Name»`, so that the certificate depends on
    * the lemmas it uses only; any other import under the empty list.
    */
  def written(
      leanExport: LeanExport,
      article: String,
      namespace: String
  ): LeanExport =
    val signatureName = s"$namespace.signature"
    val replayed = article.linesIterator
      .filterNot(line =>
        line.isEmpty || (line.startsWith("#") && !replayedComments
          .exists(line.startsWith))
      )
      .foldLeft(
        ReplayState(
          leanExport,
          Nil,
          Map.empty,
          Vector.empty,
          Vector.empty,
          None,
          false,
          false,
          Nil,
          false,
          None
        )
      )((state, line) => stepped(state, line, signatureName))
    if replayed.abstractions.nonEmpty || replayed.closing || replayed.closed.nonEmpty
    then
      throw IllegalArgumentException(
        "the article ends inside an abstraction step"
      )
    val theorem = replayed.exported match
      case Vector(only) => only
      case theorems     =>
        throw IllegalArgumentException(
          s"the article exports ${theorems.size} theorems, not one"
        )
    val (withDefinitions, definitions) =
      listData(replayed.leanExport, nameTermPairType, replayed.definitions)
    val (withSignatureValue, signatureValue) =
      withDefinitions.constantApplied(
        "LambdaJit.Interpretation.signatureOf",
        0,
        Vector(definitions)
      )
    val (withSignatureType, signatureType) =
      withSignatureValue.constant("LambdaJit.Interpretation.Signature", 0)
    val withSignature =
      withSignatureType.definition(signatureName, signatureType, signatureValue)
    val (withSignatureConstant, signature) =
      withSignature.constant(signatureName, 0)
    val (withType, roundType) = withSignatureConstant.constantApplied(
      "LambdaJit.EndToEnd.EquationSound",
      0,
      Vector(signature, theorem.left.data, theorem.right.data)
    )
    withType.theorem(s"$namespace.round", roundType, theorem.proof)

  /** The library lemmas `article` imports, by the names its comments
    * `# lemma <Name>` give, each once, in the order of their first import.
    */
  def lemmaNames(article: String): Vector[String] =
    article.linesIterator
      .filter(_.startsWith(lemmaComment))
      .map(_.stripPrefix(lemmaComment))
      .toVector
      .distinct

  /** The modules lean4export imports to write the closure of certificates whose
    * articles import the library lemmas `lemmaNames`: this writer's steps, and,
    * when a lemma is imported, `statements`, a module of the library's
    * statements as `LeanStatements.text` writes it.
    */
  def closureModules(
      lemmaNames: Vector[String],
      statements: String
  ): Vector[String] =
    if lemmaNames.isEmpty then Vector(certificate)
    else Vector(certificate, statements)

  /** The module of the native route's library statements, the package's
    * `LambdaJit/NativeRouteLibraryStatements.lean`.
    */
  val nativeRouteStatements: String = "LambdaJit.NativeRouteLibraryStatements"

  /** The constants such certificates name, as lean4export's command line spells
    * them (a lemma's name between guillemets): lean4export writes each with the
    * constants it depends on, which a checker reads before the certificates
    * (`LeanExport.continuing`).
    */
  def closureConstants(lemmaNames: Vector[String]): Vector[String] =
    val steps = Vector(
      "reflexive",
      "symmetric",
      "transitive",
      "congruence",
      "instantiated",
      "imported",
      "noLemmasSound",
      "specialized",
      "unscoped",
      "scopedSymmetric",
      "scopedTransitive",
      "scopedCongruence",
      "scopedConversion",
      "abstracted",
      "schemaInstance"
    )
      .map(step => s"$certificate.$step")
    val data = Vector(
      "LambdaJit.Interpretation.signatureOf",
      "LambdaJit.Interpretation.Signature",
      "LambdaJit.EndToEnd.EquationSound",
      "LambdaJit.EndToEnd.Statement",
      "LambdaJit.Article.Name.mk",
      "LambdaJit.Article.LogicType.operator",
      "LambdaJit.Article.LogicType.typeVariable",
      "LambdaJit.Article.Term.constant",
      "LambdaJit.Article.Term.termVariable",
      "LambdaJit.Article.Term.application",
      "List.nil",
      "List.cons",
      "Prod",
      "Prod.mk",
      "Bool",
      "Bool.true",
      "Eq.refl",
      "String"
    )
    val lemmas =
      if lemmaNames.isEmpty then Vector.empty
      else
        Vector("LambdaJit.Exported.soundCons", "LambdaJit.Exported.soundNil") ++
          lemmaNames.flatMap(name =>
            Vector(
              s"LambdaJit.Exported.Statement.«$name»",
              s"LambdaJit.Exported.«$name»"
            )
          )
    steps ++ data ++ lemmas

  private val lemmaComment = "# lemma "

  private val conversionComment = "# conversion"

  private val schemaComment = "# schema"

  private val abstractionBegin = "# abstraction begin"

  private val abstractionEnd = "# abstraction end"

  /** The comments the replay reads: the article writer's marks for a round
    * certificate (`OpentheoryArticle`); every other comment is skipped.
    */
  private val replayedComments = Vector(
    lemmaComment,
    conversionComment,
    schemaComment,
    abstractionBegin,
    abstractionEnd
  )

  /** The type of the term variables that write eigenvariables, the article
    * writer's type of IR terms (`HolType.Term`).
    */
  private val eigenvariableType =
    ReplayType.Operator(ReplayName(Vector("LambdaJit"), "term"), Vector.empty)

  private val nameTermPairType = "pairOfNameAndTerm"

  private def stepped(
      state: ReplayState,
      line: String,
      signatureName: String
  ): ReplayState =
    if line.startsWith(lemmaComment) then
      state.copy(namedLemma = Some(line.stripPrefix(lemmaComment)))
    else if line == conversionComment then state.copy(conversion = true)
    else if line == schemaComment then state.copy(schema = true)
    else if line.startsWith(abstractionBegin) then
      abstractionOpened(state, line.stripPrefix(abstractionBegin))
    else if line == abstractionEnd then state.copy(closing = true)
    else if line.startsWith("\"") then
      push(state, ReplayObject.Name(parsedName(line)))
    else if line.headOption.exists(character =>
        character == '-' || character.isDigit
      )
    then push(state, ReplayObject.Number(BigInt(line)))
    else
      line match
        case "version" => state.copy(stack = state.stack.drop(1))
        case "typeOp"  =>
          state.stack match
            case ReplayObject.Name(name) :: rest =>
              state.copy(stack = ReplayObject.TypeOperator(name) :: rest)
            case _ => rejected("typeOp", state)
        case "opType" =>
          state.stack match
            case ReplayObject.Items(items) :: ReplayObject.TypeOperator(
                  name
                ) :: rest =>
              val arguments = items.map {
                case ReplayObject.TypeObject(replayType, data) =>
                  (replayType, data)
                case other =>
                  throw IllegalArgumentException(
                    s"opType: the list holds $other"
                  )
              }
              val (withName, nameData) = nameDatum(state.leanExport, name)
              val (withArguments, argumentsData) = listData(
                withName,
                "LambdaJit.Article.LogicType",
                arguments.map(_._2)
              )
              val (withType, data) =
                withArguments.constantApplied(
                  "LambdaJit.Article.LogicType.operator",
                  0,
                  Vector(nameData, argumentsData)
                )
              state.copy(
                leanExport = withType,
                stack = ReplayObject.TypeObject(
                  ReplayType.Operator(name, arguments.map(_._1)),
                  data
                ) :: rest
              )
            case _ => rejected("opType", state)
        case "const" =>
          state.stack match
            case ReplayObject.Name(name) :: rest =>
              state.copy(stack = ReplayObject.ConstantName(name) :: rest)
            case _ => rejected("const", state)
        case "constTerm" =>
          state.stack match
            case ReplayObject.TypeObject(replayType, typeData) :: ReplayObject
                  .ConstantName(name) :: rest =>
              val (withName, nameData) = nameDatum(state.leanExport, name)
              val (withTerm, data) =
                withName.constantApplied(
                  "LambdaJit.Article.Term.constant",
                  0,
                  Vector(nameData, typeData)
                )
              state.copy(
                leanExport = withTerm,
                stack = ReplayObject.TermObject(
                  ExportedTerm(ReplayTerm.Constant(name, replayType), data)
                ) :: rest
              )
            case _ => rejected("constTerm", state)
        case "var" =>
          state.stack match
            case ReplayObject.TypeObject(replayType, typeData) :: ReplayObject
                  .Name(name) :: rest =>
              val (withName, nameData) = nameDatum(state.leanExport, name)
              val (withVariable, data) =
                withName.constantApplied(
                  "LambdaJit.Article.Term.termVariable",
                  0,
                  Vector(nameData, typeData)
                )
              state.copy(
                leanExport = withVariable,
                stack =
                  ReplayObject.VariableObject(name, replayType, data) :: rest
              )
            case _ => rejected("var", state)
        case "varTerm" =>
          state.stack match
            case ReplayObject.VariableObject(name, replayType, data) :: rest =>
              state.copy(stack =
                ReplayObject.TermObject(
                  ExportedTerm(ReplayTerm.Variable(name, replayType), data)
                ) :: rest
              )
            case _ => rejected("varTerm", state)
        case "appTerm" =>
          state.stack match
            case ReplayObject.TermObject(argument) :: ReplayObject.TermObject(
                  function
                ) :: rest =>
              val (withApplication, applied) =
                application(state.leanExport, function, argument)
              state.copy(
                leanExport = withApplication,
                stack = ReplayObject.TermObject(applied) :: rest
              )
            case _ => rejected("appTerm", state)
        case "refl" =>
          state.stack match
            case ReplayObject.TermObject(term) :: rest =>
              val (signed, signature) =
                state.leanExport.constant(signatureName, 0)
              val (withProof, proof) =
                signed.constantApplied(
                  s"$certificate.reflexive",
                  0,
                  Vector(signature, term.data)
                )
              state.copy(
                leanExport = withProof,
                stack = ReplayObject.Theorem(
                  term,
                  term,
                  proof,
                  ReplayValidity.Everywhere
                ) :: rest
              )
            case _ => rejected("refl", state)
        case "sym" =>
          state.stack match
            case ReplayObject.Theorem(left, right, inner, validity) :: rest =>
              val (signed, signature) =
                state.leanExport.constant(signatureName, 0)
              val (withProof, proof) = validity match
                case ReplayValidity.Everywhere =>
                  signed.constantApplied(
                    s"$certificate.symmetric",
                    0,
                    Vector(signature, left.data, right.data, inner)
                  )
                case ReplayValidity.Scoped(scope) =>
                  signed.constantApplied(
                    s"$certificate.scopedSymmetric",
                    0,
                    Vector(signature, scope.data, left.data, right.data, inner)
                  )
              state.copy(
                leanExport = withProof,
                stack =
                  ReplayObject.Theorem(right, left, proof, validity) :: rest
              )
            case _ => rejected("sym", state)
        case "trans" =>
          state.stack match
            case (secondTheorem @ ReplayObject.Theorem(middle, last, _, _)) ::
                (firstTheorem @ ReplayObject.Theorem(
                  first,
                  firstRight,
                  _,
                  _
                )) :: rest =>
              if firstRight.term != middle.term then
                throw IllegalArgumentException("trans: the middle terms differ")
              val (signed, signature) =
                state.leanExport.constant(signatureName, 0)
              val (validity, withProofs, Vector(firstProof, second)) =
                combined(
                  signed,
                  signature,
                  state.abstractions,
                  Vector(firstTheorem, secondTheorem)
                ): @unchecked
              val (withProof, proof) = validity match
                case ReplayValidity.Everywhere =>
                  withProofs.constantApplied(
                    s"$certificate.transitive",
                    0,
                    Vector(
                      signature,
                      first.data,
                      middle.data,
                      last.data,
                      firstProof,
                      second
                    )
                  )
                case ReplayValidity.Scoped(scope) =>
                  withProofs.constantApplied(
                    s"$certificate.scopedTransitive",
                    0,
                    Vector(
                      signature,
                      scope.data,
                      first.data,
                      middle.data,
                      last.data,
                      firstProof,
                      second
                    )
                  )
              state.copy(
                leanExport = withProof,
                stack =
                  ReplayObject.Theorem(first, last, proof, validity) :: rest
              )
            case _ => rejected("trans", state)
        case "appThm" =>
          state.stack match
            case (argumentTheorem @ ReplayObject.Theorem(
                  leftArgument,
                  rightArgument,
                  _,
                  _
                )) ::
                (functionTheorem @ ReplayObject.Theorem(
                  leftFunction,
                  rightFunction,
                  _,
                  _
                )) :: rest =>
              val (withLeft, left) =
                application(state.leanExport, leftFunction, leftArgument)
              val (withRight, right) =
                application(withLeft, rightFunction, rightArgument)
              val (signed, signature) = withRight.constant(signatureName, 0)
              val (validity, withProofs, Vector(functions, arguments)) =
                combined(
                  signed,
                  signature,
                  state.abstractions,
                  Vector(functionTheorem, argumentTheorem)
                ): @unchecked
              val sides = Vector(
                leftFunction.data,
                rightFunction.data,
                leftArgument.data,
                rightArgument.data,
                functions,
                arguments
              )
              val (withProof, proof) = validity match
                case ReplayValidity.Everywhere =>
                  withProofs.constantApplied(
                    s"$certificate.congruence",
                    0,
                    signature +: sides
                  )
                case ReplayValidity.Scoped(scope) =>
                  withProofs.constantApplied(
                    s"$certificate.scopedCongruence",
                    0,
                    Vector(signature, scope.data) ++ sides
                  )
              state.copy(
                leanExport = withProof,
                stack =
                  ReplayObject.Theorem(left, right, proof, validity) :: rest
              )
            case _ => rejected("appThm", state)
        case "subst" =>
          state.stack match
            case (substituted @ ReplayObject.Theorem(left, right, _, _)) ::
                ReplayObject.Items(
                  Vector(ReplayObject.Items(types), ReplayObject.Items(terms))
                ) :: rest =>
              if types.nonEmpty then
                throw IllegalArgumentException(
                  "subst: a type substitution, which no article of the writer holds"
                )
              val entries = terms.map {
                case ReplayObject.Items(
                      Vector(
                        ReplayObject.VariableObject(
                          name,
                          replayType,
                          variableData
                        ),
                        ReplayObject.TermObject(term)
                      )
                    ) =>
                  ((name, replayType), variableData, term)
                case other =>
                  throw IllegalArgumentException(s"subst: the entry $other")
              }
              val image = entries.map { case (key, _, term) =>
                key -> term
              }.toMap
              val (withLeft, instantiatedLeft) =
                instantiated(state.leanExport, left, image)
              val (withRight, instantiatedRight) =
                instantiated(withLeft, right, image)
              val (withEntries, entriesData) = entryData(withRight, entries)
              val (signed, signature) = withEntries.constant(signatureName, 0)
              val (withInner, inner) =
                everywhere(signed, signature, substituted)
              val (withProof, proof) = withInner.constantApplied(
                s"$certificate.instantiated",
                0,
                Vector(signature, left.data, right.data, entriesData, inner)
              )
              state.copy(
                leanExport = withProof,
                stack = ReplayObject.Theorem(
                  instantiatedLeft,
                  instantiatedRight,
                  proof,
                  ReplayValidity.Everywhere
                ) :: rest
              )
            case ReplayObject.Schema(left, right) ::
                ReplayObject.Items(
                  Vector(
                    ReplayObject.Items(Vector()),
                    ReplayObject.Items(terms)
                  )
                ) :: rest =>
              val entries = terms.map {
                case ReplayObject.Items(
                      Vector(
                        ReplayObject.VariableObject(
                          name,
                          replayType,
                          variableData
                        ),
                        ReplayObject.TermObject(term)
                      )
                    ) =>
                  ((name, replayType), variableData, term)
                case other =>
                  throw IllegalArgumentException(s"subst: the entry $other")
              }
              val image = entries.map { case (key, _, term) =>
                key -> term
              }.toMap
              val (withLeft, instantiatedLeft) =
                instantiated(state.leanExport, left, image)
              val (withRight, instantiatedRight) =
                instantiated(withLeft, right, image)
              val (withEntries, entriesData) = entryData(withRight, entries)
              val (withScope, scope) = state.abstractions match
                case step :: _ => (withEntries, step.inner)
                case Nil       => scopeMade(withEntries, Vector.empty)
              val (signed, signature) = withScope.constant(signatureName, 0)
              val (withChecked, checked) = checkedByEvaluation(signed)
              val (withProof, proof) = withChecked.constantApplied(
                s"$certificate.schemaInstance",
                0,
                Vector(
                  signature,
                  scope.data,
                  left.data,
                  right.data,
                  entriesData,
                  checked
                )
              )
              val instance = new ReplayObject.Theorem(
                instantiatedLeft,
                instantiatedRight,
                proof,
                ReplayValidity.Scoped(scope)
              )
              val (withInstance, replayedInstance) =
                if state.abstractions.nonEmpty then (withProof, instance)
                else
                  val (withEverywhere, everywhereProof) =
                    everywhere(withProof, signature, instance)
                  (
                    withEverywhere,
                    instance.copy(
                      proof = everywhereProof,
                      validity = ReplayValidity.Everywhere
                    )
                  )
              state.copy(
                leanExport = withInstance,
                stack = replayedInstance :: rest
              )
            case _ => rejected("subst", state)
        case "axiom" =>
          state.stack match
            case ReplayObject.TermObject(conclusion) :: ReplayObject.Items(
                  Vector()
                ) :: rest =>
              val (left, right) = equationSides(state.leanExport, conclusion)
              val (signed, signature) =
                state.leanExport.constant(signatureName, 0)
              val (withChecked, checked) = checkedByEvaluation(signed)
              val theorem: (LeanExport, ReplayObject) =
                (state.closed, state.abstractions) match
                  case (None, _) if state.schema =>
                    (withChecked, ReplayObject.Schema(left, right))
                  case (Some((body, step)), _) =>
                    abstracted(
                      withChecked,
                      signature,
                      checked,
                      step,
                      left,
                      right,
                      body
                    )
                  case (None, current :: _) if state.conversion =>
                    val (withProof, proof) = withChecked.constantApplied(
                      s"$certificate.scopedConversion",
                      0,
                      Vector(
                        signature,
                        current.inner.data,
                        left.data,
                        right.data,
                        checked
                      )
                    )
                    (
                      withProof,
                      ReplayObject.Theorem(
                        left,
                        right,
                        proof,
                        ReplayValidity.Scoped(current.inner)
                      )
                    )
                  case _ =>
                    val (withSound, statements, sound) =
                      librarySide(withChecked, state.namedLemma)
                    val (withProof, proof) = withSound.constantApplied(
                      s"$certificate.imported",
                      0,
                      Vector(
                        signature,
                        statements,
                        sound,
                        left.data,
                        right.data,
                        checked
                      )
                    )
                    (
                      withProof,
                      ReplayObject.Theorem(
                        left,
                        right,
                        proof,
                        ReplayValidity.Everywhere
                      )
                    )
              val (withTheorem, replayedTheorem) = theorem
              state.copy(
                leanExport = withTheorem,
                stack = replayedTheorem :: rest,
                namedLemma = None,
                schema = false,
                conversion = false,
                closed = None
              )
            case _ => rejected("axiom", state)
        case "thm" =>
          state.stack match
            case ReplayObject.TermObject(conclusion) :: ReplayObject.Items(
                  Vector()
                ) :: (theorem: ReplayObject.Theorem) :: rest =>
              val (left, right) = equationSides(state.leanExport, conclusion)
              if left.term != theorem.left.term || right.term != theorem.right.term
              then
                throw IllegalArgumentException(
                  "thm: the claimed conclusion differs from the theorem's"
                )
              val (signed, signature) =
                state.leanExport.constant(signatureName, 0)
              val (withProof, proof) = everywhere(signed, signature, theorem)
              state.copy(
                leanExport = withProof,
                stack = rest,
                exported = state.exported :+ theorem.copy(
                  proof = proof,
                  validity = ReplayValidity.Everywhere
                )
              )
            case _ => rejected("thm", state)
        case "defineConst" =>
          state.stack match
            case ReplayObject.TermObject(value) :: ReplayObject.Name(
                  name
                ) :: rest =>
              val (withName, nameData) = nameDatum(state.leanExport, name)
              val (withPair, pair) = pairData(
                withName,
                "LambdaJit.Article.Name",
                "LambdaJit.Article.Term",
                nameData,
                value.data
              )
              state.copy(
                leanExport = withPair,
                stack = ReplayObject
                  .Definition(name) :: ReplayObject.ConstantName(name) :: rest,
                definitions = state.definitions :+ pair
              )
            case _ => rejected("defineConst", state)
        case "def" =>
          state.stack match
            case ReplayObject.Number(key) :: (rest @ (value :: _)) =>
              state.copy(
                stack = rest,
                dictionary = state.dictionary.updated(key, value)
              )
            case _ => rejected("def", state)
        case "ref" =>
          state.stack match
            case ReplayObject.Number(key) :: rest =>
              state.copy(stack =
                state.dictionary.getOrElse(
                  key,
                  throw IllegalArgumentException(s"ref: no entry $key")
                ) :: rest
              )
            case _ => rejected("ref", state)
        case "remove" =>
          state.stack match
            case ReplayObject.Number(key) :: rest =>
              state.copy(
                stack = state.dictionary.getOrElse(
                  key,
                  throw IllegalArgumentException(s"remove: no entry $key")
                ) :: rest,
                dictionary = state.dictionary.removed(key)
              )
            case _ => rejected("remove", state)
        case "pop" =>
          (state.closing, state.stack, state.abstractions) match
            case (true, (body: ReplayObject.Theorem) :: rest, step :: outer) =>
              state.copy(
                stack = rest,
                abstractions = outer,
                closing = false,
                closed = Some((body, step))
              )
            case (true, _, _) =>
              rejected("pop of an abstraction step's body", state)
            case (false, _ :: rest, _) => state.copy(stack = rest)
            case (false, Nil, _)       => rejected("pop", state)
        case "nil"  => push(state, ReplayObject.Items(Vector.empty))
        case "cons" =>
          state.stack match
            case ReplayObject.Items(items) :: head :: rest =>
              state.copy(stack = ReplayObject.Items(head +: items) :: rest)
            case _ => rejected("cons", state)
        case other =>
          throw IllegalArgumentException(
            s"the command $other is no command of the article's fragment"
          )

  /** The state after the comment that opens an abstraction step, the quoted
    * names of its eigenvariables in lambda order: the step's scope, its
    * eigenvariables the innermost first before the enclosing scope's.
    */
  private def abstractionOpened(
      state: ReplayState,
      names: String
  ): ReplayState =
    val eigenvariables = quotedNames
      .findAllIn(names)
      .toVector
      .map(name => (parsedName(name), eigenvariableType))
    val (withOuter, outer) = state.abstractions match
      case step :: _ => (state.leanExport, step.inner)
      case Nil       => scopeMade(state.leanExport, Vector.empty)
    val (withInner, inner) =
      scopeMade(withOuter, eigenvariables.reverse ++ outer.eigenvariables)
    val (withEigenvariables, eigenvariablesData) =
      entriesData(withInner, eigenvariables)
    state.copy(
      leanExport = withEigenvariables,
      abstractions = ReplayAbstraction(
        inner,
        outer,
        eigenvariablesData
      ) :: state.abstractions
    )

  private val quotedNames = "\"(?:[^\"\\\\]|\\\\.)*\"".r

  /** A scope with its Lean data. */
  private def scopeMade(
      leanExport: LeanExport,
      eigenvariables: Vector[(ReplayName, ReplayType)]
  ): (LeanExport, ReplayScope) =
    val (withData, data) = entriesData(leanExport, eigenvariables)
    (withData, ReplayScope(eigenvariables, data))

  /** The data of a `List (Name × LogicType)`. */
  private def entriesData(
      leanExport: LeanExport,
      entries: Vector[(ReplayName, ReplayType)]
  ): (LeanExport, Int) =
    val (withKeyType, keyType) = pairType(
      leanExport,
      "LambdaJit.Article.Name",
      "LambdaJit.Article.LogicType"
    )
    val (withNameType, nameType) =
      withKeyType.constant("LambdaJit.Article.Name", 0)
    val (withLogicType, logicType) =
      withNameType.constant("LambdaJit.Article.LogicType", 0)
    val (withEntries, values) =
      entries.foldLeft((withLogicType, Vector.empty[Int])) {
        case ((current, done), (name, replayType)) =>
          val (withName, nameData) = nameDatum(current, name)
          val (withType, typeData) = typeDatum(withName, replayType)
          val (withEntry, entry) = withType.constantApplied(
            "Prod.mk",
            2,
            Vector(nameType, logicType, nameData, typeData)
          )
          (withEntry, done :+ entry)
      }
    listOfType(withEntries, keyType, values)

  /** `Eq.refl true`, the proof of a check that the checker accepts by
    * evaluating it.
    */
  private def checkedByEvaluation(leanExport: LeanExport): (LeanExport, Int) =
    val (withTrue, trueValue) = leanExport.constant("Bool.true", 0)
    val (withBool, booleanType) = withTrue.constant("Bool", 0)
    val (withLevel, one) = withBool.level(ExportLevel.Successor(0))
    val (withEquality, equality) = withLevel.dottedName("Eq.refl")
    val (withReflexivity, reflexivity) =
      withEquality.expression(ExportExpression.Constant(equality, Vector(one)))
    withReflexivity.applied(reflexivity, Vector(booleanType, trueValue))

  /** The conclusion of an abstraction step, `left = right` the closures, from
    * its body's theorem: in the scope around the step, or at every valuation
    * where that scope is empty.
    */
  private def abstracted(
      leanExport: LeanExport,
      signature: Int,
      checked: Int,
      step: ReplayAbstraction,
      left: ExportedTerm,
      right: ExportedTerm,
      body: ReplayObject.Theorem
  ): (LeanExport, ReplayObject.Theorem) =
    val (withBody, bodyProof) = inScope(leanExport, signature, body, step.inner)
    val (withProof, proof) = withBody.constantApplied(
      s"$certificate.abstracted",
      0,
      Vector(
        signature,
        step.outer.data,
        step.eigenvariables,
        left.data,
        right.data,
        body.left.data,
        body.right.data,
        checked,
        checked,
        bodyProof
      )
    )
    val scoped = new ReplayObject.Theorem(
      left,
      right,
      proof,
      ReplayValidity.Scoped(step.outer)
    )
    if step.outer.eigenvariables.nonEmpty then (withProof, scoped)
    else
      val (withEverywhere, everywhereProof) =
        everywhere(withProof, signature, scoped)
      (
        withEverywhere,
        scoped.copy(
          proof = everywhereProof,
          validity = ReplayValidity.Everywhere
        )
      )

  /** A proof of the theorem at every valuation: its own, or, for one proved in
    * a scope, `unscoped` when its sides hold no variable. Throws
    * `IllegalArgumentException` for a scoped theorem over variables.
    */
  private def everywhere(
      leanExport: LeanExport,
      signature: Int,
      theorem: ReplayObject.Theorem
  ): (LeanExport, Int) =
    theorem.validity match
      case ReplayValidity.Everywhere    => (leanExport, theorem.proof)
      case ReplayValidity.Scoped(scope) =>
        if !variableFree(theorem.left.term) || !variableFree(theorem.right.term)
        then
          throw IllegalArgumentException(
            "a theorem of a scope over its eigenvariables is used outside the scope"
          )
        val (withChecked, checked) = checkedByEvaluation(leanExport)
        withChecked.constantApplied(
          s"$certificate.unscoped",
          0,
          Vector(
            signature,
            scope.data,
            theorem.left.data,
            theorem.right.data,
            checked,
            theorem.proof
          )
        )

  /** A proof of the theorem in the scope: its own, or one that holds at every
    * valuation specialized (`specialized`).
    *
    * FIXME: a theorem of an enclosing scope over its eigenvariables,
    * https://github.com/Atry/private-overlay/issues/1979 used in an abstraction
    * step nested in that scope, is refused: its valuation there shifts the
    * enclosing scope's de Bruijn variables, which no theorem of
    * `LambdaJit.RoundCertificate` states yet.
    */
  private def inScope(
      leanExport: LeanExport,
      signature: Int,
      theorem: ReplayObject.Theorem,
      scope: ReplayScope
  ): (LeanExport, Int) =
    theorem.validity match
      case ReplayValidity.Scoped(own)
          if own.eigenvariables == scope.eigenvariables =>
        (leanExport, theorem.proof)
      case _ =>
        val (withEverywhere, proof) = everywhere(leanExport, signature, theorem)
        withEverywhere.constantApplied(
          s"$certificate.specialized",
          0,
          Vector(
            signature,
            scope.data,
            theorem.left.data,
            theorem.right.data,
            proof
          )
        )

  /** The validity two or more theorems are combined at, and their proofs there:
    * every valuation when each holds there, or else the scope of the innermost
    * abstraction step being replayed, or every valuation outside every step.
    */
  private def combined(
      leanExport: LeanExport,
      signature: Int,
      abstractions: List[ReplayAbstraction],
      theorems: Vector[ReplayObject.Theorem]
  ): (ReplayValidity, LeanExport, Vector[Int]) =
    if theorems.forall(_.validity == ReplayValidity.Everywhere) then
      (ReplayValidity.Everywhere, leanExport, theorems.map(_.proof))
    else
      val validity = abstractions match
        case step :: _ => ReplayValidity.Scoped(step.inner)
        case Nil       => ReplayValidity.Everywhere
      val (withProofs, proofs) =
        theorems.foldLeft((leanExport, Vector.empty[Int])) {
          case ((current, done), theorem) =>
            val (next, proof) = validity match
              case ReplayValidity.Scoped(scope) =>
                inScope(current, signature, theorem, scope)
              case ReplayValidity.Everywhere =>
                everywhere(current, signature, theorem)
            (next, done :+ proof)
        }
      (validity, withProofs, proofs)

  /** Whether a term holds no variable. Iterative: a term is as deep as a
    * program.
    */
  private def variableFree(term: ReplayTerm): Boolean =
    @annotation.tailrec
    def searched(pending: List[ReplayTerm]): Boolean = pending match
      case Nil                                                => true
      case ReplayTerm.Variable(_, _) :: _                     => false
      case ReplayTerm.Constant(_, _) :: rest                  => searched(rest)
      case ReplayTerm.Application(function, argument) :: rest =>
        searched(function :: argument :: rest)
    searched(List(term))

  /** The statements an import is accepted under and their soundness: the named
    * lemma's statement alone, or none.
    */
  private def librarySide(
      leanExport: LeanExport,
      lemma: Option[String]
  ): (LeanExport, Int, Int) =
    val (withType, statementType) =
      leanExport.constant("LambdaJit.EndToEnd.Statement", 0)
    val (withNil, empty) =
      withType.constantApplied("List.nil", 1, Vector(statementType))
    lemma match
      case None =>
        val (withSound, sound) =
          withNil.constant(s"$certificate.noLemmasSound", 0)
        (withSound, empty, sound)
      case Some(name) =>
        val (withStatement, statement) = withNil.constantNamed(
          Vector("LambdaJit", "Exported", "Statement", name),
          0
        )
        val (withList, list) = withStatement.constantApplied(
          "List.cons",
          1,
          Vector(statementType, statement, empty)
        )
        val (withLemmaSound, lemmaSound) =
          withList.constantNamed(Vector("LambdaJit", "Exported", name), 0)
        val (withNilSound, nilSound) =
          withLemmaSound.constant("LambdaJit.Exported.soundNil", 0)
        val (withSound, sound) =
          withNilSound.constantApplied(
            "LambdaJit.Exported.soundCons",
            0,
            Vector(statement, empty, lemmaSound, nilSound)
          )
        (withSound, list, sound)

  private def push(state: ReplayState, value: ReplayObject): ReplayState =
    state.copy(stack = value :: state.stack)

  private def rejected(command: String, state: ReplayState): Nothing =
    throw IllegalArgumentException(
      s"$command: the stack begins with ${state.stack.take(3)}"
    )

  /** A name command's name: the quoted string, its components split at the dots
    * that no backslash escapes, `\\` and `\"` and `\.` read as the character
    * escaped.
    */
  private def parsedName(line: String): ReplayName =
    val body = line.substring(1, line.length - 1)
    val (components, last, _) =
      body.foldLeft((Vector.empty[String], "", false)) {
        case ((done, current, true), character) =>
          (done, current + character, false)
        case ((done, current, false), '\\')      => (done, current, true)
        case ((done, current, false), '.')       => (done :+ current, "", false)
        case ((done, current, false), character) =>
          (done, current + character, false)
      }
    ReplayName(components, last)

  private def nameDatum(
      leanExport: LeanExport,
      name: ReplayName
  ): (LeanExport, Int) =
    val (withComponents, components) =
      name.namespace.foldLeft((leanExport, Vector.empty[Int])) {
        case ((current, done), component) =>
          val (next, literal) =
            current.expression(ExportExpression.StringLiteral(component))
          (next, done :+ literal)
      }
    val (withList, list) = listData(withComponents, "String", components)
    val (withLocal, local) =
      withList.expression(ExportExpression.StringLiteral(name.local))
    withLocal.constantApplied(
      "LambdaJit.Article.Name.mk",
      0,
      Vector(list, local)
    )

  /** The data of a list whose elements are of the type `elementType`, a
    * constant name or `pairOfNameAndTerm`, and whose elements' data are
    * `elements`.
    */
  private def listData(
      leanExport: LeanExport,
      elementType: String,
      elements: Vector[Int]
  ): (LeanExport, Int) =
    val (withType, typeExpression) =
      if elementType == nameTermPairType then
        pairType(leanExport, "LambdaJit.Article.Name", "LambdaJit.Article.Term")
      else leanExport.constant(elementType, 0)
    listOfType(withType, typeExpression, elements)

  private def listOfType(
      leanExport: LeanExport,
      typeExpression: Int,
      elements: Vector[Int]
  ): (LeanExport, Int) =
    val (withNil, empty) =
      leanExport.constantApplied("List.nil", 1, Vector(typeExpression))
    elements.foldRight((withNil, empty)) { case (element, (current, tail)) =>
      current.constantApplied(
        "List.cons",
        1,
        Vector(typeExpression, element, tail)
      )
    }

  private def pairType(
      leanExport: LeanExport,
      first: String,
      second: String
  ): (LeanExport, Int) =
    val (withFirst, firstType) = leanExport.constant(first, 0)
    val (withSecond, secondType) = withFirst.constant(second, 0)
    withSecond.constantApplied("Prod", 2, Vector(firstType, secondType))

  private def pairData(
      leanExport: LeanExport,
      first: String,
      second: String,
      firstValue: Int,
      secondValue: Int
  ): (LeanExport, Int) =
    val (withFirst, firstType) = leanExport.constant(first, 0)
    val (withSecond, secondType) = withFirst.constant(second, 0)
    withSecond.constantApplied(
      "Prod.mk",
      2,
      Vector(firstType, secondType, firstValue, secondValue)
    )

  /** The data of a substitution's entries, of type
    * `List ((Name × LogicType) × Term)`.
    */
  private def entryData(
      leanExport: LeanExport,
      entries: Vector[((ReplayName, ReplayType), Int, ExportedTerm)]
  ): (LeanExport, Int) =
    val (withKeyType, keyType) = pairType(
      leanExport,
      "LambdaJit.Article.Name",
      "LambdaJit.Article.LogicType"
    )
    val (withTermType, termType) =
      withKeyType.constant("LambdaJit.Article.Term", 0)
    val (withEntryType, entryType) =
      withTermType.constantApplied("Prod", 2, Vector(keyType, termType))
    val (withNameType, nameType) =
      withEntryType.constant("LambdaJit.Article.Name", 0)
    val (withLogicType, logicType) =
      withNameType.constant("LambdaJit.Article.LogicType", 0)
    val (withEntries, entryValues) =
      entries.foldLeft((withLogicType, Vector.empty[Int])) {
        case ((current, done), ((name, replayType), _, term)) =>
          val (withName, nameData) = nameDatum(current, name)
          val (withType, typeData) = typeDatum(withName, replayType)
          val (withKey, key) = withType.constantApplied(
            "Prod.mk",
            2,
            Vector(nameType, logicType, nameData, typeData)
          )
          val (withEntry, entry) = withKey.constantApplied(
            "Prod.mk",
            2,
            Vector(keyType, termType, key, term.data)
          )
          (withEntry, done :+ entry)
      }
    listOfType(withEntries, entryType, entryValues)

  /** The data of a type, built as a trampoline: a thunk constant's type nests
    * one function type per filling.
    */
  private def typeDatum(
      leanExport: LeanExport,
      replayType: ReplayType
  ): (LeanExport, Int) =
    typeDatumBuilt(leanExport, replayType).result

  private def typeDatumBuilt(
      leanExport: LeanExport,
      replayType: ReplayType
  ): TailRec[(LeanExport, Int)] =
    replayType match
      case ReplayType.Variable(name) =>
        val (withName, nameData) = nameDatum(leanExport, name)
        TailCalls.done(
          withName.constantApplied(
            "LambdaJit.Article.LogicType.typeVariable",
            0,
            Vector(nameData)
          )
        )
      case ReplayType.Operator(name, arguments) =>
        val (withName, nameData) = nameDatum(leanExport, name)
        argumentsData(withName, arguments.toList, Vector.empty).map {
          (withArguments, argumentData) =>
            val (withList, list) = listData(
              withArguments,
              "LambdaJit.Article.LogicType",
              argumentData
            )
            withList.constantApplied(
              "LambdaJit.Article.LogicType.operator",
              0,
              Vector(nameData, list)
            )
        }

  /** The data of the argument types in order, after `data`. */
  private def argumentsData(
      leanExport: LeanExport,
      arguments: List[ReplayType],
      data: Vector[Int]
  ): TailRec[(LeanExport, Vector[Int])] = arguments match
    case Nil              => TailCalls.done((leanExport, data))
    case argument :: rest =>
      tailcall(typeDatumBuilt(leanExport, argument)).flatMap((next, datum) =>
        tailcall(argumentsData(next, rest, data :+ datum))
      )

  private def application(
      leanExport: LeanExport,
      function: ExportedTerm,
      argument: ExportedTerm
  ): (LeanExport, ExportedTerm) =
    val (withApplication, data) =
      leanExport.constantApplied(
        "LambdaJit.Article.Term.application",
        0,
        Vector(function.data, argument.data)
      )
    (
      withApplication,
      ExportedTerm(ReplayTerm.Application(function.term, argument.term), data)
    )

  /** The term with each variable of `image` replaced by its term, as
    * `Article.Term.instantiate` does under `RoundCertificate.substitution`.
    */
  private def instantiated(
      leanExport: LeanExport,
      term: ExportedTerm,
      image: Map[(ReplayName, ReplayType), ExportedTerm]
  ): (LeanExport, ExportedTerm) = term.term match
    case ReplayTerm.Variable(name, replayType) =>
      (leanExport, image.getOrElse((name, replayType), term))
    case ReplayTerm.Constant(_, _)                  => (leanExport, term)
    case ReplayTerm.Application(function, argument) =>
      val (withFunction, newFunction) =
        instantiated(leanExport, subterm(leanExport, function), image)
      val (withArgument, newArgument) =
        instantiated(withFunction, subterm(withFunction, argument), image)
      application(withArgument, newFunction, newArgument)

  /** A subterm with its data, found again by its key in the export. */
  private def subterm(leanExport: LeanExport, term: ReplayTerm): ExportedTerm =
    ExportedTerm(term, termData(leanExport, term))

  /** The index of the data of a term whose records the export already holds, as
    * every subterm of a term the replay built does; throws
    * `IllegalStateException` where a record would have to be written.
    */
  private def termData(leanExport: LeanExport, term: ReplayTerm): Int =
    val (after, data) = term match
      case ReplayTerm.Variable(name, replayType) =>
        val (withName, nameData) = nameDatum(leanExport, name)
        val (withType, typeData) = typeDatum(withName, replayType)
        withType.constantApplied(
          "LambdaJit.Article.Term.termVariable",
          0,
          Vector(nameData, typeData)
        )
      case ReplayTerm.Constant(name, replayType) =>
        val (withName, nameData) = nameDatum(leanExport, name)
        val (withType, typeData) = typeDatum(withName, replayType)
        withType.constantApplied(
          "LambdaJit.Article.Term.constant",
          0,
          Vector(nameData, typeData)
        )
      case ReplayTerm.Application(function, argument) =>
        leanExport.constantApplied(
          "LambdaJit.Article.Term.application",
          0,
          Vector(termData(leanExport, function), termData(leanExport, argument))
        )
    if after.written.size != leanExport.written.size then
      throw IllegalStateException(
        s"the data of the subterm $term is not in the export"
      )
    data

  /** The two sides of an equation `= left right`. */
  private def equationSides(
      leanExport: LeanExport,
      conclusion: ExportedTerm
  ): (ExportedTerm, ExportedTerm) =
    conclusion.term match
      case ReplayTerm.Application(
            ReplayTerm.Application(
              ReplayTerm.Constant(ReplayName(Vector(), "="), _),
              left
            ),
            right
          ) =>
        (subterm(leanExport, left), subterm(leanExport, right))
      case other =>
        throw IllegalArgumentException(s"the conclusion $other is no equation")
