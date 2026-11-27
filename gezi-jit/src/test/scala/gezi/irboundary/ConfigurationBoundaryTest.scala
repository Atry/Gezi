package gezi.irboundary

/** The compile-time boundary of the specialized spelling: code outside `gezi.ir` cannot hand one configuration's term to
  * another's native specializer, put a storage into the pool except through a native specializer, read a storage's view without
  * the capability, build a parallel of terms except through a native specializer, or use a storage's view as a node. Its
  * purpose is to catch an API change that opens one of these doors again, which a run would not show; each snippet's
  * errors are a snapshot, so that the error is the one expected and not another that happens to stop the snippet.
  */
class ConfigurationBoundaryTest extends gezi.generatedinputs.FailFastSuite with snapshot4s.munit.SnapshotAssertions:

  import snapshot4s.generated.snapshotConfig

  /** What each snippet below tries, in order. */
  private val attempts: Vector[String] = Vector(
    "another configuration's term",
    "a storage into the pool through Interned",
    "a storage into the pool through a native specializer's protected entry",
    "a storage's view without the capability",
    "a parallel of terms as a layer",
    "a parallel of terms through the layer pool",
    "a parallel of terms through Instruction.Parallel",
    "a parallel of terms through the unchecked constructor",
    "a parallel of terms interned as written",
    "a storage's view as a node"
  )

  test("every door to an unspecialized object or another configuration's term is a compile error") {
    val errors = Vector(
      compileErrors(
        """ConfigurationBoundaryTest.Second.parallel(ConfigurationBoundaryTest.First.opaque("a"), ConfigurationBoundaryTest.First.opaque("a"))"""
      ),
      compileErrors("""gezi.ir.Interned.stored[gezi.ir.IrLayer](null.asInstanceOf[gezi.ir.NativeStorage])"""),
      compileErrors("""ConfigurationBoundaryTest.First.storedTerm(null.asInstanceOf[gezi.ir.NativeStorage])"""),
      compileErrors("""null.asInstanceOf[gezi.ir.NativeStorage].view"""),
      compileErrors("""gezi.ir.Parallel(gezi.ir.Instruction.opaque("a"), gezi.ir.Instruction.opaque("b"))"""),
      compileErrors(
        """gezi.ir.Interned.canonicalLayer(gezi.ir.Parallel(gezi.ir.Instruction.opaque("a"), gezi.ir.Instruction.opaque("b")))"""
      ),
      compileErrors("""gezi.ir.Instruction.Parallel(gezi.ir.Instruction.opaque("a"), gezi.ir.Instruction.opaque("b"))"""),
      compileErrors("""gezi.ir.Parallel.ofTerms(gezi.ir.Instruction.opaque("a"), gezi.ir.Instruction.opaque("b"))"""),
      compileErrors("""gezi.ir.Interned.parallelOfTerms(gezi.ir.Instruction.opaque("a"), gezi.ir.Instruction.opaque("b"))"""),
      compileErrors(
        """gezi.ir.Interned[gezi.ir.IrLayer](gezi.ir.StorageView(gezi.ir.Instruction.opaque("a"), gezi.ir.Instruction.opaque("b")))"""
      )
    )
    assertEquals(errors.size, attempts.size)
    val written = attempts.zip(errors).map { (attempt, found) =>
      assert(found.nonEmpty, s"$attempt compiles")
      s"== $attempt\n$found"
    }
    assertFileSnapshot(written.mkString("\n"), "configuration-boundary/errors.txt")
  }

object ConfigurationBoundaryTest:

  /** Two native specializers of no conversion, two configurations whose terms are two types. */
  object First extends gezi.ir.NativeSpecializer:
    protected def specialized(left: Configured, right: Configured): Option[Configured] = None

  object Second extends gezi.ir.NativeSpecializer:
    protected def specialized(left: Configured, right: Configured): Option[Configured] = None
