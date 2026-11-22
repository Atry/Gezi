package gezi.extraction

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Instruction
import gezi.ir.Layer
import scala.concurrent.Await
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.concurrent.duration.DurationInt
import gezi.ir.Apply

/** The hash code and the equality of `Entry` cost the distinct entries, not
  * the size of the term they spell. An entry of `depth` levels, each an
  * application whose two children are the level below, has `depth + 1`
  * distinct entries and 2^depth leaves as a term; two copies are built
  * separately, so that the heap shares nothing between them. Its purpose is
  * to catch a hash code or an equality that walks shared entries as a tree:
  * a `.distinct` of entries held main's jit NativeRouteCompilationTest for 11
  * to 13 minutes in the hash code that Scala derives for a case class
  * (2026-11-14). Each comparison is given ten seconds, so that such a walk
  * fails the test instead of hanging it; with depth at least 48 it would
  * take years.
  */
class EntrySharingLawTest extends GeneratedProperties:

  /** The entry of the depth over a leaf named by the leaf's number, each
    * level built from the one below, of cost the level.
    */
  private def shared(depth: Int, leaf: Int): Entry[Int] =
    (1 to depth).foldLeft(Entry(0, Shape.Name(Instruction.opaque(s"leaf$leaf")), Vector.empty)) { (below, level) =>
      Entry(level, Shape.Node(level, Apply(level - 1, level - 1)), Vector(below, below))
    }

  /** The result of the computation, failing after ten seconds. */
  // FIXME (2026-11-14): the deadline runs the body on a thread of the global https://github.com/Atry/private-overlay/issues/1974
  // pool, which cannot be stopped: after a timeout the body keeps running
  // and holds a core until the forked test JVM exits. It waits on the
  // user's decision about test executors and a watchdog (CONTRIBUTING.md, "Tests fail fast"); SharedStructureLawTest has the same deadline.
  private def within[Value](computation: => Value): Value =
    Await.result(Future(computation), 10.seconds)

  property("twoCopiesOfASharedEntryHashAndCompareInTheirDistinctEntries") {
    for
      depth <- Gen.int(Range.linear(48, 64)).forAll
      leaf <- Gen.int(Range.linear(0, 8)).forAll
      otherLeaf <- Gen.int(Range.linear(0, 8)).forAll
    yield
      val first = shared(depth, leaf)
      val second = shared(depth, leaf)
      val other = shared(depth, otherLeaf)
      Result.all(List(
        Result.assert(within(first == second)).log("equal copies are equal"),
        Result.assert(within(first.hashCode == second.hashCode)).log("equal copies hash alike"),
        Result.assert(within(Set(first, second, other).size) == (if leaf == otherLeaf then 1 else 2))
          .log("a set of the copies holds one entry per term"),
        Result.assert(within(first == other) == (leaf == otherLeaf)).log("copies over other leaves differ")
      ))
  }
