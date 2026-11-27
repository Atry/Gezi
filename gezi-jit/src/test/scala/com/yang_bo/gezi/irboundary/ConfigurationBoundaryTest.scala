package com.yang_bo.gezi.irboundary

/** The compile-time boundary of the specialized spelling: code outside
  * `com.yang_bo.gezi.ir` cannot hand one configuration's term to another's native
  * specializer, put a storage into the pool except through a native
  * specializer, read a storage's view without the capability, build a parallel
  * of terms except through a native specializer, or use a storage's view as a
  * node. Its purpose is to catch an API change that opens one of these doors
  * again, which a run would not show; each snippet's errors are a snapshot, so
  * that the error is the one expected and not another that happens to stop the
  * snippet.
  */
class ConfigurationBoundaryTest
    extends com.yang_bo.gezi.generatedinputs.FailFastSuite
    with snapshot4s.munit.SnapshotAssertions:

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

  test(
    "every door to an unspecialized object or another configuration's term is a compile error"
  ) {
    val errors = Vector(
      compileErrors(
        """ConfigurationBoundaryTest.Second.parallel(ConfigurationBoundaryTest.First.opaque("a"), ConfigurationBoundaryTest.First.opaque("a"))"""
      ),
      compileErrors(
        """com.yang_bo.gezi.ir.Interned.stored[com.yang_bo.gezi.ir.IrLayer](null.asInstanceOf[com.yang_bo.gezi.ir.NativeStorage])"""
      ),
      compileErrors(
        """ConfigurationBoundaryTest.First.storedTerm(null.asInstanceOf[com.yang_bo.gezi.ir.NativeStorage])"""
      ),
      compileErrors("""null.asInstanceOf[com.yang_bo.gezi.ir.NativeStorage].view"""),
      compileErrors(
        """com.yang_bo.gezi.ir.Parallel(com.yang_bo.gezi.ir.Instruction.opaque("a"), com.yang_bo.gezi.ir.Instruction.opaque("b"))"""
      ),
      compileErrors(
        """com.yang_bo.gezi.ir.Interned.canonicalLayer(com.yang_bo.gezi.ir.Parallel(com.yang_bo.gezi.ir.Instruction.opaque("a"), com.yang_bo.gezi.ir.Instruction.opaque("b")))"""
      ),
      compileErrors(
        """com.yang_bo.gezi.ir.Instruction.Parallel(com.yang_bo.gezi.ir.Instruction.opaque("a"), com.yang_bo.gezi.ir.Instruction.opaque("b"))"""
      ),
      compileErrors(
        """com.yang_bo.gezi.ir.Parallel.ofTerms(com.yang_bo.gezi.ir.Instruction.opaque("a"), com.yang_bo.gezi.ir.Instruction.opaque("b"))"""
      ),
      compileErrors(
        """com.yang_bo.gezi.ir.Interned.parallelOfTerms(com.yang_bo.gezi.ir.Instruction.opaque("a"), com.yang_bo.gezi.ir.Instruction.opaque("b"))"""
      ),
      compileErrors(
        """com.yang_bo.gezi.ir.Interned[com.yang_bo.gezi.ir.IrLayer](com.yang_bo.gezi.ir.StorageView(com.yang_bo.gezi.ir.Instruction.opaque("a"), com.yang_bo.gezi.ir.Instruction.opaque("b")))"""
      )
    )
    assertEquals(errors.size, attempts.size)
    val written = attempts.zip(errors).map { (attempt, found) =>
      assert(found.nonEmpty, s"$attempt compiles")
      s"== $attempt\n$found"
    }
    assertFileSnapshot(
      written.mkString("\n"),
      "configuration-boundary/errors.txt"
    )
  }

object ConfigurationBoundaryTest:

  /** Two native specializers of no conversion, two configurations whose terms
    * are two types.
    */
  object First extends com.yang_bo.gezi.ir.NativeSpecializer:
    protected def specialized(
        left: Configured,
        right: Configured
    ): Option[Configured] = None

  object Second extends com.yang_bo.gezi.ir.NativeSpecializer:
    protected def specialized(
        left: Configured,
        right: Configured
    ): Option[Configured] = None
