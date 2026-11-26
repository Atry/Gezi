package gezi.conventions

/** The main sources that test a term's class against `Parallel` without
  * reading its `layer`.
  *
  * Purpose: a native storage is no `Parallel` object while its view is a
  * parallel (`gezi.ir.NativeStorage`), so a class test that reads no layer
  * reads a storage as something other than the term it implements. A test of
  * `Apply`, `Choice` or `Thunk` answers a storage as it answers its view
  * (false), and is not checked. Every such test is either written through
  * `layer` or listed here with how it answers a storage.
  */
object ParallelClassTests:

  private val parallelTypeTest =
    """(isInstanceOf\[|asInstanceOf\[|case\s+\w+\s*:\s*)(gezi\.ir\.)?Parallel\[""".r

  /** The sources that test a term's class against `Parallel` without reading
    * its `layer`, each with why a storage is answered right there.
    */
  val withoutLayer: Map[String, String] = Map(
    "ir/src/main/scala/gezi/ir/Interned.scala" ->
      "ConstructorIdentity.isInstruction and holdsStorage, which answer a storage in a case of their own"
  )

  /** The main sources outside `withoutLayer` whose code tests a term's class
    * against `Parallel` on a line that reads no `layer`, each
    * `path:number: text`.
    */
  def found(sources: Vector[(String, String)]): Vector[String] =
    sources
      .filter((path, _) => path.contains("/src/main/") && !withoutLayer.keys.exists(path.endsWith))
      .flatMap((path, text) =>
        val lines = text.split('\n').toVector
        val code = ScalaSources.commentsBlanked(text).split('\n').toVector
        lines.zipWithIndex.collect {
          case (line, index)
              if parallelTypeTest.findFirstIn(code(index)).isDefined && !code(index).contains(".layer") =>
            s"$path:${index + 1}: ${line.trim}"
        }
      )

class ParallelClassTestsTest extends gezi.generatedinputs.FailFastSuite:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => ScalaSources.texts)

  test("every class test of a term against Parallel reads its layer, or is listed with how it answers a storage") {
    assert(ScalaSources.texts.nonEmpty, s"no Scala source found under ${ScalaSources.root}")
    val found = ParallelClassTests.found(ScalaSources.texts)
    assert(found.isEmpty, found.mkString("\n"))
  }
