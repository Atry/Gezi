package gezi.contest.judge

import gezi.contest.entry.ArticleDestination

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Paths
import gezi.generatedinputs.GeneratedProperties

/** The law of the readers' heaps (`Supervisor.command`, `Supervisor.heap`):
  * an entry's JVM gets the round's entry heap
  * (`--entry-heap`), and a reference reader's JVM keeps 256 MB, whatever
  * entry heap is given. Its purpose is to catch a heap given to the wrong
  * readers: a reference reader raised with the entries, or an entry left at
  * the debugging limit when the rules give it more.
  */
class ReaderHeapLawTest extends GeneratedProperties:

  private val heaps: Gen[String] =
    for
      amount <- Gen.int(Range.linear(1, 8192))
      unit <- Gen.element1("", "k", "m", "g", "M", "G")
    yield s"$amount$unit"

  private def limits(entryHeap: String, entryParallelism: Option[Int]): Limits =
    Limits(
      FamilyBudgets(20, 60, 600),
      60,
      2,
      None,
      None,
      None,
      Paths.get("."),
      entryHeap,
      entryParallelism,
      Sandbox.Bubblewrap(Vector(Paths.get("/nix/store/runtime"))),
      ArticleDestination.Discarded,
      None
    )

  /** The framework's fixture entry, not a contributed one, so that a change of such an entry
    * never breaks the law.
    */
  private val entry = Reader("fixture", "classes", Launched.EntryLaunched(Paths.get("contest-entries-fixture")))

  private val reference = Reader("tabling(weak_head)", "classes", Launched.ReferenceLaunched("tabling(weak_head)"))

  property("an entry's JVM gets the entry heap and a reference reader's keeps 256m") {
    for heap <- heaps.forAll
    yield
      val entryOptions = Supervisor.command(entry, limits(heap, None)).filter(_.startsWith("-Xmx"))
      val referenceOptions = Supervisor.command(reference, limits(heap, None)).filter(_.startsWith("-Xmx"))
      Result.diff(entryOptions, Vector(s"-Xmx$heap"))(_ == _).and(
        Result.diff(referenceOptions, Vector("-Xmx256m"))(_ == _)
      )
  }

  /** The same law for the carrier threads (`--entry-parallelism`): an
    * entry's JVM gets exactly the round's number, or none when the round
    * sets none, and a reference reader's never gets one; it catches the
    * option given to the wrong readers or dropped from an entry's command.
    */
  property("an entry's JVM gets the entry parallelism and a reference reader's gets none") {
    for parallelism <- Gen.int(Range.linear(1, 64)).option.forAll
    yield
      val property = "-Djdk.virtualThreadScheduler.parallelism="
      val entryOptions = Supervisor.command(entry, limits("256m", parallelism)).filter(_.startsWith(property))
      val referenceOptions = Supervisor.command(reference, limits("256m", parallelism)).filter(_.startsWith(property))
      Result.diff(entryOptions, parallelism.toVector.map(carriers => s"$property$carriers"))(_ == _).and(
        Result.diff(referenceOptions, Vector.empty[String])(_ == _)
      )
  }
