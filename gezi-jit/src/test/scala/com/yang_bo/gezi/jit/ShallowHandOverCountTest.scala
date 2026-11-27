package com.yang_bo.gezi.jit

import com.yang_bo.gezi.weakhead.Bounded
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.ir.{Configured, Value}

/** The JIT hands a storage to the reader one layer at a time (#2260): a closed
  * program whose answer is a list of n booleans, the list and its elements
  * storages of the natives' library's facts (element criterion `boolean_type`),
  * is read to its normal forms by the JIT, and the views it reads are counted.
  * A storage head is observed by its one-layer view (`JitRules.observed`), each
  * view read counted as an encoding (`JitCounts.encodings`) in the reading's
  * state, with no memory of views read before: each encounter is one read.
  *
  * Derived before the run: reading the answer to its normal form meets each of
  * the n cells, the nil at its end and each of the n elements once, so 2n + 1
  * views: 21 for n = 10 and 2001 for n = 1000. The boolean storages are
  * interned, so one object is met many times and read each time, one layer
  * each, never the storage taken apart whole. The normal forms are those the
  * tabled weak head reads of the same list written plainly, with no filter and
  * no storage. Its purpose is to catch a hand-over that converts a storage deep
  * (the conversion `headsExpanded` that #2260 removed), which reads no view per
  * encounter, or one that reads a view more than once per encounter.
  */
class ShallowHandOverCountTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:
  // n = 1000 reads 2n + 1 heads and their normal forms' layers.
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(20, "s")

  given com.yang_bo.gezi.ir.StorageAccess = ShallowHandOverCountTest.storageAccess

  private lazy val facts = BackendFacts.of(NativesTesting.nativesOn)
  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encoding.type = encoding

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => encoding)

  private def library(key: String): Configured[encoding.type] =
    JitTesting.libraryInstruction[encoding.type](key)

  private def booleans: Configured[encoding.type] =
    encoding.application(library("list_type"), library("boolean_type"))

  /** The truth value of the position, alternating, as its storage
    * `t ∥ boolean_type`.
    */
  private def truth(position: Int): Configured[encoding.type] =
    encoding.parallel(
      library(if position % 2 == 0 then "true" else "false"),
      library("boolean_type")
    )

  /** The list of n truth values, every cell in the unique spelling, a storage.
    */
  private def stored(size: Int): Configured[encoding.type] =
    (0 until size).foldRight(encoding.parallel(library("nil"), booleans))(
      (position, rest) =>
        encoding.parallel(
          encoding.application(
            encoding.application(library("cons"), truth(position)),
            rest
          ),
          booleans
        )
    )

  /** The same list written plainly, no filter and no storage. */
  private def plain(size: Int): Configured[encoding.type] =
    (0 until size).foldRight(library("nil"))((position, rest) =>
      encoding.application(
        encoding.application(
          library("cons"),
          library(if position % 2 == 0 then "true" else "false")
        ),
        rest
      )
    )

  private val limit: Long = 10000000

  test(
    "reading a list of n stored booleans reads 2n + 1 views, one per storage met"
  ) {
    val read = Vector(10, 1000).map { size =>
      val program = stored(size)
      assert(
        com.yang_bo.gezi.ir.NativeStorage.stored(program.representation),
        s"the list of $size truth values is no storage"
      )
      val jit = Jit(NativesTesting.configurationOf(encoding))
      val reading =
        NativesTesting.normalFormsSpent(jit, Value.of(program), limit)
      val reference = NativesTesting.normalFormsSpent(
        Mode.TablingWeakHead,
        JitTesting.referenceConfiguration(jit),
        Value.of(plain(size)),
        limit
      )
      reading.outcome match
        case Bounded.Finished(_) => ()
        case other               =>
          fail(
            s"the JIT's reading of $size truth values did not finish: $other"
          )
      assert(
        JitTesting.sameOutcomes(reading.outcome, reference.outcome),
        s"the normal forms of $size truth values: ${reading.outcome} against ${reference.outcome}"
      )
      JitTesting.counts(reading.jitState).encodings
    }
    assertEquals(read, Vector(21L, 2001L))
  }

object ShallowHandOverCountTest:

  /** The capability the test builds its storages with, granted as a test sets
    * up.
    */
  val storageAccess: com.yang_bo.gezi.ir.StorageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()
