package gezi.contest.corpora.reductions

import gezi.weakhead.Computed
import gezi.weakhead.Mode
import gezi.weakhead.NormalForms
import gezi.weakhead.Reading
import gezi.weakhead.ReadingState
import gezi.weakhead.Resource
import gezi.ir.Value
import gezi.weakhead.oldcorpora.ConstructorTree
import gezi.weakhead.oldcorpora.ScottDecoding
import gezi.frontend.DeBruijnTerm
import gezi.frontend.DeBruijnTermOf
import gezi.frontend.Lambdalattice
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.ir.{Configured, NoFacts}

/** The corpora are read under no facts. */
private given reductionProblemNoFacts: NoFacts.type = NoFacts

/** The limits of a problem, `limits(Seconds, StackMegabytes, TableMegabytes)`:
  * the contest's facts. The Scala judge reads the seconds as a budget of
  * evaluator steps (`budget`); the megabytes of stack and table space are
  * SWI-Prolog's, which the Scala evaluator has no counterpart of but its table
  * limit (`ReadingState.tableLimit`), the same for every reading, so they are
  * kept as data and not applied.
  */
final case class Limits(seconds: Int, stackMegabytes: Int, tableMegabytes: Int):

  /** The seconds as a budget of evaluator steps (`Reading.budgetSteps`). */
  def budget: Long = Reading.budgetSteps(seconds)

/** How a normal-form reading of a program ended (`answered_normal_form/3`):
  * every normal form read, or a stop, which answers nothing.
  */
enum NormalFormReading:

  /** The reading finished: the distinct normal forms, read back, in the order
    * first read; none is a reading that found none.
    */
  case Finished(normalForms: Vector[DeBruijnTermOf[Configured[NoFacts.type]]])

  /** The reading ran past its budget of steps. */
  case StepLimit

  /** The reading ran out of a resource. */
  case Exhausted(resource: Resource)

/** What a problem expects: one tree, or `trees(Trees)`, a set of trees other
  * than one (two or more, or none).
  */
enum Expected:

  /** The one tree of the program's one answer. */
  case One(tree: ScottTree)

  /** The trees of a program whose answers are a finite set other than one tree;
    * `contest_reduction:expected_trees/2` asserts there are not exactly one.
    */
  case Trees(members: Vector[ScottTree])

  /** The trees this stands for, without repetition. */
  def trees: Vector[ScottTree] = this match
    case One(tree)      => Vector(tree)
    case Trees(members) => members.distinct

/** A problem of the reduction series, the port of
  * `contest_reduction:reduction_problem/4`: the closed program, the Scott type
  * its answers are values of, what it expects, and its limits.
  */
final case class ReductionProblem(
    point: String,
    program: ProblemTerm,
    typeName: String,
    expected: Expected,
    limits: Limits
):

  /** The problem as a point of its corpus: its program, the reference the
    * points writer reads by tabling(weak_head) (`Reference.Read`).
    */
  def corpusPoint: CorpusPoint =
    CorpusPoint(point, DrawnPoint(program, Reference.Read))

/** The judge of the reduction series (the deleted Prolog file,
  * `git show 6ab16a338^:lambda_jit/corpora/contest_reduction.pl`): a program's
  * root, its normal forms read on the evaluator, its snapshot and the test of a
  * normal form.
  */
object Reduction:

  /** `program_root(Surface, Root)`: the closed program as a root of the
    * evaluator, the instruction of its thunk IR. The program holds no library
    * name.
    */
  def programRoot(program: ProblemTerm): Value[NoFacts.type] =
    Value.of(
      Defunctionalization.thunkInstruction[NoFacts.type](
        program.deBruijnTerm(Map.empty)
      )
    )

  /** `answered_normal_form(Setting, Surface, NormalForm)`, the set asked whole:
    * every normal form the normal-form reader reads of the program's root under
    * the mode (`weak_head` or `tabling(weak_head)`), one reading from an empty
    * store and no table, within the limit of steps, read back as de Bruijn
    * terms. Every normal form is read before the first is answered, so a
    * program whose reading does not end within the limit answers nothing
    * (`StepLimit`), which is no claim.
    */
  def answeredNormalForms(
      mode: Mode,
      program: ProblemTerm,
      limit: Long
  ): NormalFormReading =
    val root = programRoot(program)
    NormalForms
      .normalForms(mode, root)
      .result(
        ReadingState
          .knowingTop(limit, gezi.weakhead.ReadingConfiguration.withoutFacts)
      ) match
      case Computed.Done(normalForms, _) =>
        NormalFormReading.Finished(
          normalForms.map(Defunctionalization.instructionTerm).distinct
        )
      case Computed.Stopped(after) =>
        after.exhausted match
          case Some(resource) => NormalFormReading.Exhausted(resource)
          case None           => NormalFormReading.StepLimit

  /** The constructor trees the program decodes to at the data type under the
    * mode (`ScottDecoding.decoded` under findall), one reading from an empty
    * store within the limit of steps: every tree as often as it is decoded, in
    * order, or none for a stop. A head that is no constructor reads as
    * `IllFormed`.
    */
  def decodedTrees(
      mode: Mode,
      program: ProblemTerm,
      typeName: String,
      limit: Long
  ): Option[Vector[ConstructorTree]] =
    val root = programRoot(program)
    ScottDecoding
      .decoded(mode, root, Scott.dataType(typeName))
      .collected
      .result(
        ReadingState
          .knowingTop(limit, gezi.weakhead.ReadingConfiguration.withoutFacts)
      ) match
      case Computed.Done(trees, _) => Some(trees)
      case Computed.Stopped(_)     => None

  /** The family's default limits, `limits(10, 256, 256)`, for a problem whose
    * module raises none (`reduction_limits/2`).
    */
  val defaultLimits: Limits = Limits(10, 256, 256)

  /** The raised limits of the `hidden_37_*` families, `limits(60, 1024, 1024)`.
    */
  val hiddenLimits: Limits = Limits(60, 1024, 1024)

  /** The problem's snapshot: the canonical terms of its expected trees
    * (`problem_snapshot/2`, for a problem that states no snapshot of its own,
    * which no problem of the group does), each as the lambdalattice text of its
    * tree (`Lambdalattice.textWithLiterals`), sorted as text. Not exchange
    * lines (`ExchangeText`): nothing reads a snapshot back, and the exchange
    * line of a term with little sharing costs a few times its tree's text to
    * write.
    */
  def snapshot(scott: Scott, problem: ReductionProblem): Vector[String] =
    problem.expected.trees
      .map(tree =>
        Lambdalattice.textWithLiterals(
          Encodings.deBruijn(scott.canonical(problem.typeName, tree)),
          Map.empty
        )
      )
      .distinct
      .sorted

  /** Expected one tree when the trees are one, `trees(Trees)` otherwise, as the
    * problems' `expected/2` helpers write it.
    */
  def expectedOf(trees: Vector[ScottTree]): Expected =
    trees.distinct match
      case Vector(tree) => Expected.One(tree)
      case several      => Expected.Trees(several)

  /** Whether the closed de Bruijn term is in beta eta normal form: no
    * `apply(lambda(_), _)` and no `lambda(apply(M, variable(0)))` with variable
    * 0 not free in M (`normal_form_term/1`). A choice, a parallel or a constant
    * is no normal form, as the Prolog has no clause for them.
    */
  def normalFormTerm(term: ProblemDeBruijnTerm): Boolean = normalUnder(term, 0)

  private def normalUnder(term: ProblemDeBruijnTerm, depth: Int): Boolean =
    term match
      case DeBruijnTerm.Variable(index)           => index >= 0 && index < depth
      case DeBruijnTerm.Apply(function, argument) =>
        (function match
          case DeBruijnTerm.Lambda(_) => false
          case _                      => true
        ) && normalUnder(function, depth) && normalUnder(argument, depth)
      case DeBruijnTerm.Lambda(body) =>
        !etaRedexBody(body) && normalUnder(body, depth + 1)
      case _ => false

  private def etaRedexBody(body: ProblemDeBruijnTerm): Boolean = body match
    case DeBruijnTerm.Apply(function, DeBruijnTerm.Variable(0)) =>
      !occursFree(function, 0)
    case _ => false

  private def occursFree(term: ProblemDeBruijnTerm, index: Int): Boolean =
    term match
      case DeBruijnTerm.Variable(found)           => found == index
      case DeBruijnTerm.Apply(function, argument) =>
        occursFree(function, index) || occursFree(argument, index)
      case DeBruijnTerm.Lambda(body) => occursFree(body, index + 1)
      case _                         => false
