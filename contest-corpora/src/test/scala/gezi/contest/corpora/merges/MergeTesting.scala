package gezi.contest.corpora.merges

import gezi.contest.corpora.common.ProblemFamilies
import gezi.contest.corpora.common.ProblemField
import gezi.weakhead.Expansions

import gezi.frontend.Lambdalattice
import gezi.frontend.Term
import java.nio.file.Path
import java.nio.file.Paths

/** The field of the problem data that a program of problems/mixin_datalog
  * writes, for a test that names the program by its case
  * (`MixinDatalog.ProgramKind`) and hands a generator its field.
  */
object ProgramFields:

  /** The field of problems/mixin_datalog's program of the kind, as the
    * table writes it, for a generator that takes a field: the Scott
    * constructor of problems/mixin_datalog/program at the position of the
    * case of `MixinDatalog.ProgramKind` (`ordinal`), of
    * `MixinDatalog.programKindCount` constructors,
    * `λhandler_0. … λhandler_(n-1). handler_i F1 … Fk`, its shape likewise a
    * constructor of problems/mixin_datalog/shape (`ProgramShape`), and a
    * size the library's Scott integer that `from_cbor` of `integer/cbor`
    * gives (`Literals.integerTerm`). The order of the constructors is the
    * enums'.
    */
  def field(kind: MixinDatalog.ProgramKind): ProblemField =
    def integer(value: Int): String =
      s"(${gezi.frontend.Lambdalattice.text(gezi.frontend.Literals.integerTerm(BigInt(value)), Map.empty)})"
    def constructor(position: Int, count: Int, fields: Vector[String]): String =
      val handlers = (0 until count).map(index => s"handler_$index")
      s"(${handlers.map(handler => s"λ$handler. ").mkString}${(handlers(position) +: fields).mkString(" ")})"
    def shapeWritten(shape: MixinDatalog.ProgramShape): String = shape match
      case MixinDatalog.ProgramShape.Ring(size) =>
        constructor(shape.ordinal, MixinDatalog.programShapeCount, Vector(integer(size)))
      case MixinDatalog.ProgramShape.Line(size) =>
        constructor(shape.ordinal, MixinDatalog.programShapeCount, Vector(integer(size)))
      case other => constructor(other.ordinal, MixinDatalog.programShapeCount, Vector.empty)
    def kindWritten(kind: MixinDatalog.ProgramKind): String = kind match
      case MixinDatalog.ProgramKind.Closure(shape) =>
        constructor(kind.ordinal, MixinDatalog.programKindCount, Vector(shapeWritten(shape)))
      case MixinDatalog.ProgramKind.Symmetric(shape) =>
        constructor(kind.ordinal, MixinDatalog.programKindCount, Vector(shapeWritten(shape)))
      case other => constructor(other.ordinal, MixinDatalog.programKindCount, Vector.empty)
    ProblemField(
      gezi.frontend.Defunctionalization.thunkInstruction(
        gezi.frontend.Lambdalattice.term(kindWritten(kind))
      )
    )(gezi.knowledgereading.KnowledgeReading.startingState)

/** A suite that reads `MergeTesting.problems`: the URI expansions every
  * family's tables share (`ProblemFamilies.sharedExpansions`), which the
  * first reading of any family forces, are its shared fixture
  * (`FailFastSuite.sharedFixtures`), built in `beforeAll`, so that no test
  * is charged for them and the run order does not decide which suite
  * overruns.
  */
trait MergeProblemsSuite extends gezi.generatedinputs.FailFastSuite:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    super.sharedFixtures :+ (_ => MergeTesting.problems.sharedExpansions)

/** Where the tests of this package find Gezi's files, and the form
  * their snapshots write programs in.
  */
object MergeTesting:

  /** The root of the build, which it passes to the forked test JVM. */
  val buildRoot: Path = Paths.get(
    sys.props.getOrElse(
      "gezi.buildRoot",
      throw IllegalStateException("the build passes gezi.buildRoot to the forked test JVM")
    )
  )

  /** The problem families every merge test reads, made once for the test JVM from no URI expansion, so that the tests share the families' directory listings and parsed files. */
  lazy val problems: ProblemFamilies = ProblemFamilies(buildRoot, Expansions.none, gezi.hotspot.baselines.BaselineCaches.provider())

  /** The form of a program, the lambdalattice text of its tree
    * (`Lambdalattice.textWithLiterals`): a snapshot is never read back, and
    * the exchange line (`ExchangeText`) of a program with little sharing
    * costs a few times the tree's text to write.
    */
  def form(program: Term): String =
    Lambdalattice.textWithLiterals(program.deBruijnTerm(Map.empty), Map.empty)
