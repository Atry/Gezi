package gezi.contest.corpora.claims

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamily
import gezi.contest.corpora.common.ProblemField

import gezi.contest.corpora.common.DeBruijnTerms
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.ir.Spine

/** The kind of an attractor, the second field of a row of `attractor_entry`:
  * `constructor`, with no field, or `function(Dependencies, Recursion)`, the
  * constructors of problems/attractors/kind in order. A function's dependencies
  * are the names of the entries the row lists, each found as the row of the
  * same table whose record it is (`Attractors.entries`).
  */
enum AttractorKind:
  case Constructor
  case Function(dependencies: Vector[String], recursion: AttractorRecursion)

/** The recursion of a function attractor, the constructors of
  * problems/attractors/recursion in order: none, through its own copy applied
  * to itself, through the prelude's fixed point combinator.
  */
enum AttractorRecursion:
  case NotRecursive
  case SelfApplication
  case Fixpoint

/** An attractor's spelling (`problems/attractors`, SPELLINGS): `direct`, or
  * `respelled`, every application whose head is a variable written with the
  * head wrapped as `((\z. z) x)`. Its cases are the constructors of
  * problems/schema/spelling in order (`reductions.SetFree.spelling`).
  */
enum Spelling:
  case Direct, Respelled

/** The attractor library, the code of `problems/attractors`, ported from the
  * deleted Prolog file (`git show
  * 91b3f11e1^:lambda_jit/corpora/contest_attractors.pl`): the sources of the
  * attractors, their spellings and the functions they stand for. The entries
  * (`attractor_entry/3`) and the sources written as rows are read from the
  * family `gezi/problems/attractors`, and each attractor's beta eta normal form
  * (`attractor_function/2`), written as the program it is, from
  * `gezi/problems/attractor_normal_forms`.
  *
  * `attractor_address/2` is not ported: it names an attractor by the
  * `variant_sha1` of its de Bruijn term, a content address, which the
  * migration's blacklist (content addresses in process, `variant_sha1`) does
  * not let back; nothing in Scala reads it.
  */
final class Attractors(corpora: Corpora):

  /** The prelude's fixpoint combinator `Y`, which ties an attractor of
    * recursion `fixpoint` (`function_surface/3`).
    */
  def fixpoint: ProblemTerm = corpora.prelude.fixpoint

  private def file: ProblemFamily = corpora.contestAttractors

  /** `attractor_entry(Name, Kind)`, name and kind, in the order of definition:
    * each row a record of two fields, its name a text and its kind a
    * constructor of problems/attractors/kind.
    */
  lazy val entries: Vector[(String, AttractorKind)] =
    val rows = file.rows("attractor_entry")
    rows.map {
      case Vector(name, entryKind) =>
        ProblemData.text(name) -> kind(entryKind, rows)
      case fields =>
        throw IllegalArgumentException(
          s"a row of attractor_entry has ${fields.size} fields, not two"
        )
    }

  /** The kind a field writes, a constructor of problems/attractors/kind read by
    * its position (`ProblemData.alternative`): constructor, with no field, or
    * function of its dependencies and its recursion. The dependencies are a
    * list of entries of the table, the records themselves, each read back to
    * its row (`dependencyName`).
    */
  private def kind(
      term: ProblemField,
      rows: Vector[Vector[ProblemField]]
  ): AttractorKind =
    ProblemData.alternative(term, ProblemData.caseCount[AttractorKind]) match
      case (0, Vector())                        => AttractorKind.Constructor
      case (1, Vector(dependencies, recursion)) =>
        AttractorKind.Function(
          ProblemData
            .list(dependencies)
            .map(dependency => dependencyName(dependency, rows)),
          this.recursion(recursion)
        )
      case (position, fields) =>
        throw IllegalArgumentException(
          s"an attractor kind at position $position has ${fields.size} fields"
        )

  /** The name of the entry a dependency is: the dependency is read as the
    * record it is, a constructor of one alternative
    * (`ProblemData.alternative`), and the row of the table with the same
    * fields, the same interned instructions, gives the name; the dependency's
    * own name field is never read as a text. Throws when the record is not
    * exactly one row of the table.
    */
  private def dependencyName(
      dependency: ProblemField,
      rows: Vector[Vector[ProblemField]]
  ): String =
    val (_, fields) = ProblemData.alternative(dependency, 1)
    rows.filter(_ == fields) match
      case Vector(Vector(name, _)) => ProblemData.text(name)
      case found                   =>
        throw IllegalArgumentException(
          s"a dependency of attractor_entry is ${found.size} rows of the table, not one"
        )

  /** The recursion a field writes, a constructor of
    * problems/attractors/recursion read by its position
    * (`ProblemData.alternative`).
    */
  private def recursion(term: ProblemField): AttractorRecursion =
    ProblemData.alternative(term, AttractorRecursion.values.size) match
      case (position, Vector()) => AttractorRecursion.fromOrdinal(position)
      case (_, fields)          =>
        throw IllegalArgumentException(
          s"a recursion of contest_attractors has ${fields.size} fields"
        )

  /** `attractor_function(Name, Function)`: the attractor's beta eta normal
    * form, a closed de Bruijn term of the front end, written in the table as
    * the program it is.
    */
  def attractorFunction(name: String): ProblemDeBruijnTerm =
    Defunctionalization.instructionTerm(
      corpora.contestAttractorNormalForms
        .row("attractor_function", Map(0 -> name))(1)
        .instruction
    )

  /** `attractor_library(Library)`: name and function, in the order of
    * definition.
    */
  def attractorLibrary: Vector[(String, ProblemDeBruijnTerm)] =
    entries.map((name, _) => name -> attractorFunction(name))

  /** `attractor_source(Name, Surface)`, the first row for the name: a closed
    * surface term whose beta eta normal form is the attractor's function, as
    * the table writes it, each function it imports (such as
    * `problems/prelude_clauses`' `natural_equal_body`) the term it imports.
    * Throws for a name with no source.
    */
  def attractorSource(name: String): ProblemTerm =
    file.template("attractor_source", Map(0 -> name), Map.empty, 1)

  /** `attractor_surface(Name, Spelling)`: the attractor's function in the
    * spelling.
    */
  def attractorSurface(name: String, spelling: Spelling): ProblemTerm =
    Attractors.surface(Attractors.spelled(spelling, attractorFunction(name)))

  /** `function_surface(Name, Spelling)`: the function the attractor stands for
    * (the module comment of the deleted Prolog file, RECURSION,
    * `git show 91b3f11e1^:lambda_jit/corpora/contest_attractors.pl`), every
    * copy in the spelling.
    */
  def functionSurface(name: String, spelling: Spelling): ProblemTerm =
    val kindOfName = entries
      .collectFirst { case (`name`, entryKind) => entryKind }
      .getOrElse(throw IllegalArgumentException(s"no attractor $name"))
    kindOfName match
      case AttractorKind.Constructor => attractorSurface(name, spelling)
      case AttractorKind.Function(
            dependencies,
            AttractorRecursion.NotRecursive
          ) =>
        templateApplied(name, dependencies, spelling)
      case AttractorKind.Function(
            dependencies,
            AttractorRecursion.SelfApplication
          ) =>
        templateApplied(name, dependencies, spelling)(
          templateApplied(name, dependencies, spelling)
        )
      case AttractorKind.Function(dependencies, AttractorRecursion.Fixpoint) =>
        fixpoint(templateApplied(name, dependencies, spelling))

  private def templateApplied(
      name: String,
      dependencies: Vector[String],
      spelling: Spelling
  ): ProblemTerm =
    dependencies.foldLeft(attractorSurface(name, spelling))(
      (term, dependency) => term(functionSurface(dependency, spelling))
    )

/** The spellings of closed de Bruijn terms. */
object Attractors:

  /** `spelled(Spelling, Term)`. */
  def spelled(
      spelling: Spelling,
      term: ProblemDeBruijnTerm
  ): ProblemDeBruijnTerm = spelling match
    case Spelling.Direct    => term
    case Spelling.Respelled => respelled(term)

  /** `respelled(Term)`: every application whose head is a variable has its head
    * wrapped as `((\z. z) x)`.
    */
  def respelled(term: ProblemDeBruijnTerm): ProblemDeBruijnTerm = term match
    case DeBruijnTerm.Lambda(body) => DeBruijnTerm.Lambda(respelled(body))
    case DeBruijnTerm.Apply(_, _)  =>
      val (head, arguments) = Spine.of(term)
      val newHead = head match
        case DeBruijnTerm.Variable(_) =>
          DeBruijnTerm.Apply(
            DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0)),
            head
          )
        case _ => respelled(head)
      arguments.map(respelled).foldLeft(newHead)(DeBruijnTerm.Apply(_, _))
    case other => other

  /** `de_bruijn_surface(Term)`: the closed de Bruijn term as a HOAS term
    * (`common.DeBruijnTerms.hoas`). Throws for a variable no binder binds and
    * for a constant.
    */
  def surface(term: ProblemDeBruijnTerm): ProblemTerm = DeBruijnTerms.hoas(term)

  /** `spelled_surface(Spelling, Surface)`: the closed term in the spelling, for
    * a problem that writes a term of its own as the library writes an
    * attractor.
    */
  def spelledSurface(
      spelling: Spelling,
      surfaceTerm: ProblemTerm
  ): ProblemTerm =
    surface(spelled(spelling, surfaceTerm.deBruijnTerm(Map.empty)))
