package gezi.conventions

/** Two doors of the specialized spelling that the types leave open
  * (`gezi.ir.NativeSpecializer`): a native specializer can be subclassed, and a
  * value can be cast to a native specializer's `Configured`. Each one that the
  * code base uses is listed here with its reason, and an unlisted one fails.
  *
  * Purpose: a subclass of `NativeSpecializer` makes storages through its
  * protected entry (`storedTerm`) and decides which parallel is the unique
  * spelling of one, so an unlisted subclass could put a storage into the pool
  * that no backend's facts declare, or a plain twin of a term beside its
  * storage; a cast to `Configured` declares a term specialized under a
  * configuration without its native specializer having built it. Neither is
  * visible to the type checker, which is why the list is checked here.
  */
object NativeSpecializationBoundaryCheck:

  /** The subclasses of `NativeSpecializer` allowed, by the source that declares
    * each and its name, each with its reason.
    */
  val specializers: Map[(String, String), String] =
    Map(
      ("ir/src/main/scala/gezi/ir/NativeSpecializer.scala", "NoFacts") ->
        "the native specializer of no facts: the library, an entry's data and the reference reading are read under it",
      (
        "jit/src/main/scala/gezi/jit/RepresentedStorage.scala",
        "StorageEncoding"
      ) ->
        "the native specializer of a backend's facts, the one that makes storages of the native representations",
      (
        "interface-laws/src/main/scala/gezi/interfacelaws/ExtractorLaws.scala",
        "LawNativeSpecializer"
      ) ->
        "the interface laws' native specializer of generic stand-in data, with no facts of a backend",
      (
        "ir/src/test/scala/gezi/generatedinputs/StandInStorages.scala",
        "StandInStorages"
      ) ->
        "the tests' stand-in storages (a view that throws, a test's own data), made only through this entry",
      (
        "jit/src/test/scala/gezi/irboundary/ConfigurationBoundaryTest.scala",
        "First"
      ) ->
        "one of two configurations whose terms the compile-time boundary test keeps apart",
      (
        "jit/src/test/scala/gezi/irboundary/ConfigurationBoundaryTest.scala",
        "Second"
      ) ->
        "one of two configurations whose terms the compile-time boundary test keeps apart"
    )

  /** The sources allowed to cast to `Configured`, each with its reason. */
  val casts: Map[String, String] =
    Map(
      "ir/src/main/scala/gezi/ir/NativeSpecializer.scala" ->
        ("`NativeSpecializer.configuredOf`, the one entry of a reader's value into a configuration's terms: an instruction " +
          "a reader of one configuration holds was built through its native specializer (its argument at the site)")
    )

  private val declaration =
    """(?:object|class)\s+(\w+)[^\n{=]*?(?:extends|with)\s+(?:gezi\.ir\.)?NativeSpecializer\b""".r
  private val anonymous = """new\s+(?:gezi\.ir\.)?NativeSpecializer\b""".r
  private val cast = """asInstanceOf\[[^\]]*\bConfigured\]""".r

  /** The declared subclasses not listed, and every anonymous one, each
    * `path: name`.
    */
  def unlistedSpecializers(sources: Vector[(String, String)]): Vector[String] =
    sources.flatMap((path, text) =>
      val code = ScalaSources.commentsBlanked(text)
      declaration
        .findAllMatchIn(code)
        .map(_.group(1))
        .filterNot(name => specializers.contains((path, name)))
        .map(name => s"$path: $name") ++
        anonymous.findAllMatchIn(code).map(_ => s"$path: an anonymous subclass")
    )

  /** The listed subclasses no source declares any longer: their entries are
    * deleted.
    */
  def staleSpecializers(sources: Vector[(String, String)]): Vector[String] =
    val declared = sources
      .flatMap((path, text) =>
        declaration
          .findAllMatchIn(ScalaSources.commentsBlanked(text))
          .map(found => (path, found.group(1)))
      )
      .toSet
    specializers.keys
      .filterNot(declared.contains)
      .toVector
      .sorted
      .map((path, name) => s"$path: $name")

  /** The casts to `Configured` in sources not listed, each `path:number: text`.
    */
  def unlistedCasts(sources: Vector[(String, String)]): Vector[String] =
    sources
      .filterNot((path, _) => casts.contains(path))
      .flatMap((path, text) =>
        val code = ScalaSources.commentsBlanked(text).split('\n').toVector
        val lines = text.split('\n').toVector
        lines.zipWithIndex.collect {
          case (line, index) if cast.findFirstIn(code(index)).isDefined =>
            s"$path:${index + 1}: ${line.trim}"
        }
      )

class NativeSpecializationBoundaryTest
    extends gezi.generatedinputs.FailFastSuite:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => ScalaSources.texts)

  private def sources = ScalaSources.texts

  test(
    "every subclass of NativeSpecializer is listed with its reason, and every listed one is declared"
  ) {
    assert(sources.nonEmpty, "no Scala source found")
    val unlisted =
      NativeSpecializationBoundaryCheck.unlistedSpecializers(sources)
    val stale = NativeSpecializationBoundaryCheck.staleSpecializers(sources)
    assert(
      unlisted.isEmpty && stale.isEmpty,
      s"unlisted:\n${unlisted.mkString("\n")}\nstale:\n${stale.mkString("\n")}"
    )
  }

  test("a cast to Configured stands only where it is listed") {
    val unlisted = NativeSpecializationBoundaryCheck.unlistedCasts(sources)
    assert(unlisted.isEmpty, unlisted.mkString("\n"))
  }
