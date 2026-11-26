package gezi.jupyter.kernel

import almond.interpreter.api.DisplayData
import almond.interpreter.api.ExecuteResult
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.PropertyConfig
import hedgehog.core.SuccessCount
import java.nio.file.Paths
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Defaults
import gezi.contest.entry.Entry
import gezi.contest.entry.EntryData
import gezi.contest.entry.ExecutorModules
import gezi.contest.entry.ExtractorModules
import gezi.contest.entry.generic.GenericEntryProvider
import gezi.ffi.ReplyHandler
import gezi.frontend.NameSpelling
import gezi.generatedinputs.GeneratedProperties
import gezi.hotspot.ForeignValue
import gezi.jit.NativesProvider

/** The continuation-aware method the laws below call by its symbols: it
  * replies with its first argument as many times as its second says, in the
  * thread of the call.
  */
object IoMemberApi:
  def echo(value: Byte, replies: Byte, handler: ReplyHandler): Unit =
    (0 until replies.toInt).foreach(_ => handler.resumed(ForeignValue.Bits(8, value.toLong & 0xff)))
    handler.completed()

/** An io member run end to end through the kernel, its entry and the JVM
  * service (`JvmService`), on the
  * fixture entry whose executor is the Moore module and on generated values.
  * Its purpose is to catch an argument boxed wrongly, a real method's reply
  * that does not reach the transition, and a state the library's constructors
  * build that the module's families do not read.
  */
class IoMemberLawTest extends GeneratedProperties:

  private val threeInputs: PropertyConfig => PropertyConfig = _.copy(testLimit = SuccessCount(3))

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot")).toAbsolutePath.normalize

  private lazy val entry: Entry[?] =
    val (data, afterEntry) = EntryData.at(
      buildRoot,
      buildRoot.resolve("tests/moore_fixtures/entry_with_moore.lambdalattice"),
      Defaults.entryDataState
    )
    GenericEntryProvider.initialized(
      data,
      ExecutorModules.registered(buildRoot),
      ExtractorModules.registered(buildRoot),
      NativesProvider.loaded,
      ArticleDestination.Discarded,
      afterEntry,
      Defaults.caches()
    )

  /** The fixture entry, read before the first test and not charged to it (FailFastSuite). */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => entry)

  private def lines(result: ExecuteResult): Vector[String] = result match
    case ExecuteResult.Success(data) =>
      data.detailedData.get("text/plain") match
        case Some(DisplayData.Value.String(text)) => text.linesIterator.toVector
        case other                                => throw IllegalStateException(s"the cell's text is $other")
    case other => throw IllegalStateException(s"the cell was answered with $other")

  /** The bit tuple of the byte, high bit first (`java_ffi/bits`). */
  private def byteText(value: Byte): String =
    val bits = (7 to 0 by -1).map(bit => if ((value >> bit) & 1) == 1 then "(λt e. t)" else "(λt e. e)").mkString(" ")
    s"(λtuple. tuple $bits)"

  property("a state built with the library's constructors calls the method and its reply reaches the answer", threeInputs) {
    for value <- Gen.byte(Range.constant(Byte.MinValue, Byte.MaxValue)).forAll
    yield
      val root = NameSpelling.escaped(buildRoot.getFileName.toString)
      val library = s"omega (omega (omega $root \"corpora\") \"library\")"
      val symbols = "[\"gezi/jupyter/kernel/IoMemberApi\", \"echo\", \"(BBLgezi/ffi/ReplyHandler;)V\"]"
      val program =
        s"(λtuple. tuple λmixin. mixin mixin) λomega. " +
          s"omega (omega ($library \"java_ffi\") \"moore\") λstate finish run call new decode _. " +
          s"omega (omega ($library \"prelude\") \"list\") λnil cons _ _ _. " +
          s"state (run (call (λk. k $symbols) (cons (decode ${byteText(value)}) (cons (decode ${byteText(1)}) nil)))) " +
          "λreply. state (finish reply) λignored. ignored"
      val interpreter = CellInterpreter.started(buildRoot, NotebookLocation.of(buildRoot.resolve("moore-law.ipynb")), entry, None)
      lines(interpreter.execute(s"(λ\"io\" \"k\". $program) + (λ\"v\". ${byteText(value)})", storeHistory = true, None, None, None)) match
        case Vector(io, shown) if shown.startsWith("\"v\" = ") =>
          Result.diff(io, s"\"io\" \"k\" = ${shown.stripPrefix("\"v\" = ")}")(_ == _)
        case other => Result.failure.log(s"the cell's lines: $other")
  }
