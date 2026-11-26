package gezi.conventions

/** No Scala source asks Hedgehog for a share of its generated inputs
  * (`.cover(percentage, label, condition)`).
  *
  * Purpose: a share is a statistical requirement, which a run's random seed
  * misses now and then; such a failure catches nothing and costs an
  * investigation. Every case a law is for is covered by construction instead:
  * a generator whose every sample falls in the case, each case checked at
  * every input (CONTRIBUTING.md, the tests' section). A source that calls it
  * fails here.
  */
class CoverageByConstructionTest extends gezi.generatedinputs.FailFastSuite:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => ScalaSources.texts)

  /** The call the check bans, spelled in two parts so that this source does not contain it. */
  private val banned: String = "." + "cover("

  test("no Scala source asks for a share of its generated inputs with Hedgehog's cover") {
    val sources = ScalaSources.texts
    assert(sources.nonEmpty, "no Scala source found")
    val found = sources.flatMap((path, text) =>
      val code = ScalaSources.commentsBlanked(text).split('\n').toVector
      code.zipWithIndex.collect { case (line, index) if line.contains(banned) => s"$path:${index + 1}: ${line.trim}" }
    )
    assert(found.isEmpty, found.mkString("\n"))
  }
