package com.yang_bo.gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import scala.concurrent.Await
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.concurrent.duration.DurationInt

/** The hash code and the equality of an interned term cost the distinct nodes,
  * not the size as a tree. A term of `depth` levels, each the application of
  * the level below to itself, has `depth + 1` distinct nodes and 2^depth leaves
  * as a tree; two copies are built separately, so that the heap shares nothing
  * between them. Its purpose is to catch a hash code or an equality that walks
  * a shared value as a tree: `ParallelSetLawTest` ran two hours in the hash
  * codes of heads that did so (2026-11-13). Each comparison is given ten
  * seconds, so that such a walk fails the test instead of hanging it; with
  * depth at least 48 it would take years.
  */
class SharedStructureLawTest extends GeneratedProperties:

  import DeBruijnTerm.*

  /** The term of the depth over the leaf, each level built from the one below.
    */
  private def shared(depth: Int, leaf: Int): DeBruijnTerm =
    (1 to depth).foldLeft(Variable(leaf): DeBruijnTerm)((below, _) =>
      Apply(below, below)
    )

  /** The result of the computation, failing after ten seconds. */
  // FIXME (2026-11-14): the deadline runs the body on a thread of the global https://github.com/Atry/private-overlay/issues/1974
  // pool, which cannot be stopped: after a timeout the body keeps running
  // and holds a core until the forked test JVM exits. It waits on the
  // user's decision about test executors and a watchdog (CONTRIBUTING.md, "Tests fail fast"); extraction's EntrySharingLawTest has the same deadline.
  private def within[Value](computation: => Value): Value =
    Await.result(Future(computation), 10.seconds)

  property("twoCopiesOfASharedTermHashAndCompareInTheirDistinctNodes") {
    for
      depth <- Gen.int(Range.linear(48, 64)).forAll
      leaf <- Gen.int(Range.linear(0, 8)).forAll
      otherLeaf <- Gen.int(Range.linear(0, 8)).forAll
    yield
      val first = shared(depth, leaf)
      val second = shared(depth, leaf)
      val other = shared(depth, otherLeaf)
      Result.all(
        List(
          Result.assert(within(first == second)).log("equal copies are equal"),
          Result
            .assert(within(first.hashCode == second.hashCode))
            .log("equal copies hash alike"),
          Result
            .assert(within(first == other) == (leaf == otherLeaf))
            .log("copies over other leaves differ")
        )
      )
  }
