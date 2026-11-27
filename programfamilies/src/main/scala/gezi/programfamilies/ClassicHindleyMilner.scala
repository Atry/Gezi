package gezi.programfamilies

import java.nio.file.Files
import java.nio.file.Path
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.frontend.Term
import gezi.knowledgereading.KnowledgeReading
import gezi.weakhead.Computation
import gezi.ir.Value
import gezi.weakhead.Values
import scala.annotation.tailrec
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Configured, NativeSpecializer, NoFacts}

/** A type of the classic Hindley-Milner reference: `natural`, `boolean`,
  * `list(Element)`, `arrow(Argument, Result)` or a type variable.
  */
enum ClassicType:
  case Natural
  case BooleanType
  case ListOf(element: ClassicType)
  case Arrow(argument: ClassicType, result: ClassicType)

  /** A type variable, by number; within a scheme the numbers are the scheme's
    * generic variables, from 0.
    */
  case Variable(number: Int)

/** A type scheme: its body, whose variables `0` to `genericCount - 1` are all
  * generic.
  */
final case class TypeScheme(genericCount: Int, body: ClassicType)

/** The substitution of algorithm J as a value: the binding of each bound type
  * variable, threaded through the inference instead of kept in place. It is a
  * persistent union-find over the type variables: a variable bound to a
  * variable points at it, the one of lower rank pointing at the one of higher
  * rank, so that a chain of variables is at most logarithmically long; a
  * variable bound to a constructed type is that class's type. Each lookup in
  * the persistent maps costs a logarithmic factor, which is counted as a
  * negligible constant.
  *
  * @param bindings
  *   the type each bound variable is bound to
  * @param ranks
  *   the rank of each unbound variable that has one, absent meaning 0
  * @param nextVariable
  *   the number of the next fresh variable
  */
final case class Substitution(
    bindings: Map[Int, ClassicType],
    ranks: Map[Int, Int],
    nextVariable: Int
):

  /** A fresh type variable and the substitution after it was made. */
  def fresh: (Substitution, ClassicType) =
    (copy(nextVariable = nextVariable + 1), ClassicType.Variable(nextVariable))

  /** The type with its outermost bound variables followed, as Prolog
    * dereferences a variable: a constructed type, or an unbound variable.
    */
  @tailrec
  final def resolved(classicType: ClassicType): ClassicType = classicType match
    case ClassicType.Variable(number) =>
      bindings.get(number) match
        case Some(bound) => resolved(bound)
        case None        => classicType
    case _ => classicType

  /** The substitution after the two types were unified with the occurs check,
    * as `unify_with_occurs_check/2` unifies, or nothing when they do not unify.
    */
  def unified(first: ClassicType, second: ClassicType): Option[Substitution] =
    Substitution.unifiedAll(List((first, second)), this)

  /** Whether the unbound variable occurs in the type. */
  def occurs(variable: Int, classicType: ClassicType): Boolean =
    Substitution.occursIn(variable, List(classicType), this)

/** The empty substitution and the steps of unification. */
object Substitution:

  /** No variable made and none bound. */
  val empty: Substitution = Substitution(Map.empty, Map.empty, 0)

  @tailrec
  private def unifiedAll(
      pending: List[(ClassicType, ClassicType)],
      substitution: Substitution
  ): Option[Substitution] = pending match
    case Nil                     => Some(substitution)
    case (first, second) :: rest =>
      (substitution.resolved(first), substitution.resolved(second)) match
        case (ClassicType.Variable(left), ClassicType.Variable(right)) =>
          if left == right then unifiedAll(rest, substitution)
          else unifiedAll(rest, variablesJoined(left, right, substitution))
        case (ClassicType.Variable(variable), constructed) =>
          if substitution.occurs(variable, constructed) then None
          else unifiedAll(rest, bound(variable, constructed, substitution))
        case (constructed, ClassicType.Variable(variable)) =>
          if substitution.occurs(variable, constructed) then None
          else unifiedAll(rest, bound(variable, constructed, substitution))
        case (ClassicType.Natural, ClassicType.Natural) =>
          unifiedAll(rest, substitution)
        case (ClassicType.BooleanType, ClassicType.BooleanType) =>
          unifiedAll(rest, substitution)
        case (ClassicType.ListOf(left), ClassicType.ListOf(right)) =>
          unifiedAll((left, right) :: rest, substitution)
        case (
              ClassicType.Arrow(leftArgument, leftResult),
              ClassicType.Arrow(rightArgument, rightResult)
            ) =>
          unifiedAll(
            (leftArgument, rightArgument) :: (leftResult, rightResult) :: rest,
            substitution
          )
        case _ => None

  /** The two unbound variables joined by rank. */
  private def variablesJoined(
      left: Int,
      right: Int,
      substitution: Substitution
  ): Substitution =
    val leftRank = substitution.ranks.getOrElse(left, 0)
    val rightRank = substitution.ranks.getOrElse(right, 0)
    if leftRank < rightRank then
      bound(left, ClassicType.Variable(right), substitution)
    else if rightRank < leftRank then
      bound(right, ClassicType.Variable(left), substitution)
    else
      val joined = bound(left, ClassicType.Variable(right), substitution)
      joined.copy(ranks = joined.ranks.updated(right, rightRank + 1))

  private def bound(
      variable: Int,
      classicType: ClassicType,
      substitution: Substitution
  ): Substitution =
    substitution.copy(
      bindings = substitution.bindings.updated(variable, classicType),
      ranks = substitution.ranks - variable
    )

  @tailrec
  private def occursIn(
      variable: Int,
      pending: List[ClassicType],
      substitution: Substitution
  ): Boolean =
    pending match
      case Nil                 => false
      case classicType :: rest =>
        substitution.resolved(classicType) match
          case ClassicType.Variable(number) =>
            number == variable || occursIn(variable, rest, substitution)
          case ClassicType.Natural | ClassicType.BooleanType =>
            occursIn(variable, rest, substitution)
          case ClassicType.ListOf(element) =>
            occursIn(variable, element :: rest, substitution)
          case ClassicType.Arrow(argument, result) =>
            occursIn(variable, argument :: result :: rest, substitution)

/** A program's principal type as inferred: the type and the substitution that
  * binds its variables.
  */
final case class InferredType(
    classicType: ClassicType,
    substitution: Substitution
):

  /** The type written with every bound variable followed and its unbound
    * variables named `T0`, `T1`, ... in the order of their first occurrence,
    * depth first and left to right: `arrow(T0,arrow(T1,T0))`. Two types are the
    * same up to renaming of type variables when they are written alike.
    */
  def written: String =
    InferredType
      .pieces(List(Left(classicType)), substitution, Map.empty, Vector.empty)
      .mkString

/** The writing of an inferred type. */
object InferredType:

  @tailrec
  private def pieces(
      pending: List[Either[ClassicType, String]],
      substitution: Substitution,
      names: Map[Int, String],
      written: Vector[String]
  ): Vector[String] = pending match
    case Nil                 => written
    case Right(text) :: rest =>
      pieces(rest, substitution, names, written :+ text)
    case Left(classicType) :: rest =>
      substitution.resolved(classicType) match
        case ClassicType.Natural =>
          pieces(rest, substitution, names, written :+ "natural")
        case ClassicType.BooleanType =>
          pieces(rest, substitution, names, written :+ "boolean")
        case ClassicType.ListOf(element) =>
          pieces(
            Left(element) :: Right(")") :: rest,
            substitution,
            names,
            written :+ "list("
          )
        case ClassicType.Arrow(argument, result) =>
          pieces(
            Left(argument) :: Right(",") :: Left(result) :: Right(")") :: rest,
            substitution,
            names,
            written :+ "arrow("
          )
        case ClassicType.Variable(number) =>
          val name = names.getOrElse(number, s"T${names.size}")
          pieces(
            rest,
            substitution,
            names.updated(number, name),
            written :+ name
          )

/** The classic Hindley-Milner type inference of Damas and Milner in the form of
  * Milner's algorithm J, the port of the Prolog reference: a measuring
  * instrument, the reference against which the cost of Gezi's pipeline is timed
  * (`jmh-pipeline`'s `ClassicHindleyMilnerBenchmark`). It is outside Gezi's
  * pipeline: no module of the pipeline depends on it. DOWNGRADE: it is a type
  * checker in the host, against the letter of the rule that the host holds no
  * type information (`CONTRIBUTING.md`, "Types live only in the term"), allowed
  * as a measuring instrument only.
  *
  * The input is a program in the HOAS of `gezi.frontend.Term`, the same term
  * the pipeline reads: an abstraction, an application, or a library name, whose
  * type scheme the table of `library_types.lambdalattice` gives. The language
  * has no let, no choice and no parallel: a choice or a parallel throws
  * `IllegalArgumentException`, and so does a variable used outside the
  * abstraction that made it. With no let, no type is ever generalized: a
  * library name's scheme, all of whose variables are generic, is instantiated
  * with fresh variables at each occurrence, and a lambda-bound variable is
  * monomorphic.
  *
  * The Prolog kept W's substitution as the bindings of Prolog variables,
  * updated in place; here it is the persistent union-find `Substitution`,
  * threaded through the inference. The environment is the textbook list
  * environment, the innermost binder first, so looking a variable up costs the
  * number of binders between its occurrence and its own binder, as the Prolog's
  * `==` search did. It computes the type only and builds no elaborated term.
  */
object ClassicHindleyMilner:

  /** `benchmarks/classic_hindley_milner/library_types.lambdalattice`, the table
    * of the type schemes of the classic reference.
    */
  def libraryTypes: Path =
    FixedPointLines.buildRoot
      .resolve(
        "../benchmarks/classic_hindley_milner/library_types.lambdalattice"
      )
      .normalize

  /** The type schemes of
    * `benchmarks/classic_hindley_milner/library_types.lambdalattice`, keyed by
    * the name its row writes: each row `_library_type Name Scheme` read under
    * weak head as `KnowledgeReading` reads knowledge, the named variables of a
    * scheme its generic variables. The key is the row's name; the key of the
    * replacement named in the TODO of `termType` is that replacement's to
    * choose. Throws `IllegalArgumentException` for a row that is no such row
    * and for a name given twice.
    */
  def schemes(libraryTypes: Path): Map[String, TypeScheme] =
    namedSchemes(libraryTypes)

  /** The evaluator steps the reading of the table, or of one type of it, may
    * spend. Measured 2026-11-10 (branch problem-data-lambdalattice, a scratch
    * probe): the table 333 steps, a field at most 1,185 (a name read as a
    * text); the limit is about 10 times the larger.
    */
  private val readingLimit: Long = 12000L

  /** A value of the table read back to its instruction, so that a later reading
    * starts from it alone.
    */
  private def opened(value: Value[NoFacts.type])(using
      NoFacts.type
  ): Value[NoFacts.type] = Value.of(Values.instruction(value))

  private def text(value: Value[NoFacts.type])(using NoFacts.type): String =
    KnowledgeReading.run(KnowledgeReading.text(value), readingLimit)

  /** The type schemes of the table by the names its rows write: the one field
    * of the tuple the file returns (`KnowledgeReading.soleField`).
    *
    * FIXME: broken since string literals became varargs (main plan
    * https://github.com/Atry/private-overlay/issues/2004 section 12.4, D9): a
    * row `λ_library_type. _library_type "zero" (λc. …)` spreads the literal
    * into its bytes and `\0`, so the row has six fields, not two, and the read
    * throws "a tuple of arity 2 has 6 fields" (measured 2026-11-13 by a scratch
    * probe on main f26d54657, the table converted to a tuple). The rows read
    * their names as text: candidate fixes are rows that apply the library's
    * `text/cbor`'s `from_cbor` to the literal, as the problems' tables do, or a
    * reader that takes the bytes up to `\0`. Its one caller is `jmh-pipeline`'s
    * `SchemesInput.schemes`, taken by `ClassicHindleyMilnerBenchmark` alone.
    */
  private def namedSchemes(libraryTypes: Path): Map[String, TypeScheme] =
    given NoFacts.type = NoFacts
    val file = Value.of(
      Defunctionalization.thunkInstruction(
        Lambdalattice.term(Files.readString(libraryTypes))
      )(using gezi.ir.NoFacts)
    )
    val rows = KnowledgeReading.run(
      KnowledgeReading
        .soleField(file)
        .flatMap(KnowledgeReading.items)
        .flatMap(items =>
          Computation.traversed(items)(item =>
            KnowledgeReading.fields(item, 2).map(_.map(opened))
          )
        ),
      readingLimit
    )
    rows.foldLeft(Map.empty[String, TypeScheme]) { (schemes, row) =>
      row match
        case Vector(nameField, scheme) =>
          val name = text(nameField)
          if schemes.contains(name) then
            throw IllegalArgumentException(
              s"$libraryTypes gives the library name $name twice"
            )
          val (body, generics) = schemeBody(scheme, Map.empty)
          schemes.updated(name, TypeScheme(generics.size, body))
        case other =>
          throw IllegalArgumentException(
            s"$libraryTypes holds a row that is no library type: $other"
          )
    }

  /** The scheme's body, each variable numbered by its name in the order first
    * met, and the numbers given.
    */
  private def schemeBody(
      scheme: Value[NoFacts.type],
      generics: Map[String, Int]
  )(using NoFacts.type): (ClassicType, Map[String, Int]) =
    val fields = KnowledgeReading
      .run(KnowledgeReading.alternative(scheme, 1), readingLimit)
      ._2
      .map(opened)
    fields.headOption.map(text) match
      case Some("natural") if fields.size == 1 =>
        (ClassicType.Natural, generics)
      case Some("boolean") if fields.size == 1 =>
        (ClassicType.BooleanType, generics)
      case Some("list") if fields.size == 2 =>
        val (elementType, afterElement) = schemeBody(fields(1), generics)
        (ClassicType.ListOf(elementType), afterElement)
      case Some("arrow") if fields.size == 3 =>
        val (argumentType, afterArgument) = schemeBody(fields(1), generics)
        val (resultType, afterResult) = schemeBody(fields(2), afterArgument)
        (ClassicType.Arrow(argumentType, resultType), afterResult)
      case Some("variable") if fields.size == 2 =>
        val name = text(fields(1))
        val generic = generics.getOrElse(name, generics.size)
        (ClassicType.Variable(generic), generics.updated(name, generic))
      case other =>
        throw IllegalArgumentException(s"a type scheme holds no type: $other")

  /** The principal type of the closed program, or nothing when it has none, as
    * for a program HM rejects (the Prolog's `program_type/2`). Throws
    * `IllegalArgumentException` for a library name with no scheme in the table
    * and for a term outside the language.
    */
  def programType(
      program: ProgramTerm,
      schemes: Map[String, TypeScheme]
  ): Option[InferredType] =
    termType(program, Nil, 0, Substitution.empty, schemes).result.map(
      (substitution, classicType) => InferredType(classicType, substitution)
    )

  /** W's case analysis on the term, at `depth` abstractions with the
    * environment of their binders' types, innermost first.
    */
  private def termType(
      term: ProgramTerm,
      environment: List[ClassicType],
      depth: Int,
      substitution: Substitution,
      schemes: Map[String, TypeScheme]
  ): TailRec[Option[(Substitution, ClassicType)]] = term match
    case Term.BoundVariable(level) =>
      environment.drop(depth - level - 1) match
        case binderType :: _ if level >= 0 && level < depth =>
          done(Some((substitution, binderType)))
        case _ =>
          throw IllegalArgumentException(
            s"a classic program uses a variable outside its abstraction: level $level at depth $depth"
          )
    case Term.Application(function, argument) =>
      tailcall(termType(function, environment, depth, substitution, schemes))
        .flatMap {
          case None                                => done(None)
          case Some((afterFunction, functionType)) =>
            tailcall(
              termType(argument, environment, depth, afterFunction, schemes)
            ).map {
              case None                                => None
              case Some((afterArgument, argumentType)) =>
                val (afterResult, resultType) = afterArgument.fresh
                afterResult
                  .unified(
                    functionType,
                    ClassicType.Arrow(argumentType, resultType)
                  )
                  .map(unified => (unified, resultType))
            }
        }
    case Term.Abstraction(body) =>
      val (afterBinder, binderType) = substitution.fresh
      tailcall(
        termType(
          body(Term.BoundVariable(depth)),
          binderType :: environment,
          depth + 1,
          afterBinder,
          schemes
        )
      ).map(
        _.map((afterBody, bodyType) =>
          (afterBody, ClassicType.Arrow(binderType, bodyType))
        )
      )
    // TODO: the `case Term.Define(name)` branch stood here. Its purpose: type a library name by instantiating its
    // type scheme. It named library terms by Term.Define, a free variable (blacklisted) and a table of library
    // files deleted when the library became files reached by paths. Its replacement types
    // the HOAS case of a closed instruction read as a member of a fixture file under tests/ by projection.
    // The key of `schemes` is the table row's name; the replacement chooses its own key.
    // The deleted code: git show 2908bffd5:lambda_jit/programfamilies/src/main/scala/lambdajit/programfamilies/ClassicHindleyMilner.scala.
    // Until it is written a library term has no scheme in the table, whose keys are names.
    case Term.Closed(instruction) =>
      throw IllegalArgumentException(
        s"a library term has no scheme in the table, which is keyed by name: $instruction"
      )
    case Term.ChoiceChain(_) | Term.Choice(_, _) | Term.Parallel(_, _) =>
      throw IllegalArgumentException(
        s"a classic program has no choice and no parallel: ${term.ordinal}"
      )

  /** A fresh instance of the scheme, its generic variables renumbered past the
    * substitution's variables, and the substitution after them.
    */
  private def instantiated(
      scheme: TypeScheme,
      substitution: Substitution
  ): (Substitution, ClassicType) =
    val offset = substitution.nextVariable
    (
      substitution.copy(nextVariable = offset + scheme.genericCount),
      renumbered(scheme.body, offset)
    )

  private def renumbered(classicType: ClassicType, offset: Int): ClassicType =
    classicType match
      case ClassicType.Variable(number) => ClassicType.Variable(number + offset)
      case ClassicType.ListOf(element)  =>
        ClassicType.ListOf(renumbered(element, offset))
      case ClassicType.Arrow(argument, result) =>
        ClassicType.Arrow(
          renumbered(argument, offset),
          renumbered(result, offset)
        )
      case constant => constant
