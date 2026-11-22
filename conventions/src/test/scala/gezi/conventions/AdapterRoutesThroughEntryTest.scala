package gezi.conventions

import scala.util.matching.Regex

/** An adapter runs a cell only through its entry (CONTRIBUTING.md, "The Architecture"): no source of `contest-runner` or `jupyter-kernel`, nor of
  * `ffi`, the library through which an adapter calls services, reads a term
  * itself, by the weak head (`WeakHead`), a mode of reading (`Mode`) or a
  * reading state of its own (`ReadingState`), unless it carries a FIXME
  * naming the issue that moves it onto `Entry` and `Executor`
  * (`routingIssue`, the open issue of the FFI's deferred adapter of
  * arbitrary Java, whose decoders read values today). Its purpose
  * is to catch an adapter that comes to evaluate cells under an approximation
  * and a caching policy of its own, bypassing the entry's configuration, as
  * the kernel and the FFI's runner once did. The judge's
  * reference reading, the rules' tabled weak head, is the one exception, and
  * the judge is not checked. Names are looked for in code only, comments
  * blanked; a name built at run time escapes the check.
  */
class AdapterRoutesThroughEntryTest extends gezi.generatedinputs.FailFastSuite:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => ScalaSources.texts)

  private val adapters: Vector[String] = Vector("contest-runner/src/main/scala/", "jupyter-kernel/src/main/scala/", "ffi/src/main/scala/")

  private val reading: Regex = """\bWeakHead\.|\bMode\.(TablingWeakHead|WeakHead|Jit)\b|\bReadingState\b""".r

  private val routingIssue: String = "https://github.com/Atry/private-overlay/issues/1797"

  test("an adapter's source that reads a term itself carries a FIXME naming the issue that routes it through its entry") {
    val sources = ScalaSources.texts.filter((path, _) => adapters.exists(path.startsWith))
    assert(sources.nonEmpty, s"no source of ${adapters.mkString(", ")} found under ${ScalaSources.root}")
    val unmarked = sources.flatMap((path, text) =>
      val names = reading.findAllIn(ScalaSources.commentsBlanked(text)).toVector.distinct
      Option.when(names.nonEmpty && !text.contains(s"FIXME ($routingIssue)"))(s"$path: ${names.mkString(", ")}")
    )
    assertEquals(unmarked, Vector.empty)
  }
