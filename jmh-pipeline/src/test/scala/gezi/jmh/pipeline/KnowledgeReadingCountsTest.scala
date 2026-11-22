package gezi.jmh.pipeline

import gezi.weakhead.ApplicationReading
import gezi.weakhead.Mode
import snapshot4s.generated.snapshotConfig

/** The deterministic counts of the knowledge reading the benchmarks time
  * (`KnowledgeReadingBenchmark`): the
  * benchmarks' knowledge (`KnowledgeReadings.knowledgeFile`), the knowledge
  * term's size in instructions, and the
  * evaluator steps of each reading the benchmarks time, each reading checked
  * against the current reader's index first (`KnowledgeReadings.checkedReading`).
  * Its purpose: a change of the standard library, of the encoding or of the
  * evaluator that changes what the benchmarks read or how many steps they
  * take shows in the snapshot's diff, so that a reading is not compared with
  * a stale one.
  */
class KnowledgeReadingCountsTest extends gezi.generatedinputs.FailFastSuite with snapshot4s.munit.SnapshotAssertions:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of KnowledgeReadingCountsTest, "knowledgeReadingCounts", takes 9.951 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(15, "s")

  test("knowledgeReadingCounts") {
    val library = KnowledgeReadings.library()
    val index = library.index
    val knowledge = KnowledgeInLambdalattice.term(index)
    val (under, underMembers) = KnowledgeInLambdalattice.sizes(index, knowledge)
    // Every reading the rows below show, each taken once: the tabled rows of ByLayer and BySpine are
    // the readings of their steps rows.
    val keys = (for
      mode <- Vector(Mode.WeakHead, Mode.TablingWeakHead)
      slotReading <- SlotReading.values.toVector
      copies <- Vector(1, 2, 4, 8)
    yield (mode, ApplicationReading.ByLayer, slotReading, copies)) ++ (for
      mode <- Vector(Mode.WeakHead, Mode.TablingWeakHead)
      slotReading <- SlotReading.values.toVector
    yield (mode, ApplicationReading.BySpine, slotReading, 1)) ++
      SlotReading.values.toVector.map(slotReading => (Mode.TablingWeakHead, ApplicationReading.BySharedPrefix, slotReading, 1))
    val readings = keys.map { case key @ (mode, applications, slotReading, copies) =>
      key -> KnowledgeReadings.checkedReading(library, mode, applications, slotReading, copies)
    }.toMap
    val counts = Vector(
      s"lemmas\t${index.lemmaSides.size}",
      s"combinator properties\t${index.combinatorProperties.size}",
      s"native bindings\t${index.nativeBound.size}",
      s"slots\t${KnowledgeInLambdalattice.slots(index).size}",
      s"slots with a member\t${KnowledgeInLambdalattice.members(index).count(_.nonEmpty)}",
      s"instructions under the knowledge term\t$under",
      s"instructions under the lemma sides and the members\t$underMembers"
    ) ++ (for
      mode <- Vector(Mode.WeakHead, Mode.TablingWeakHead)
      slotReading <- SlotReading.values.toVector
      copies <- Vector(1, 2, 4, 8)
    yield s"steps\t$mode\t$slotReading\t$copies\t${readings((mode, ApplicationReading.ByLayer, slotReading, copies)).spent}") ++ (for
      // The steps of the other option of taking applications apart, one copy each, so that the steps
      // it saves show beside ByLayer's.
      mode <- Vector(Mode.WeakHead, Mode.TablingWeakHead)
      slotReading <- SlotReading.values.toVector
    yield s"steps by spine\t$mode\t$slotReading\t1\t${readings((mode, ApplicationReading.BySpine, slotReading, 1)).spent}") ++ (for
      // The steps and tables of each option tabled, one copy each, so that the tables BySharedPrefix leaves
      // out of ByLayer's, and the steps it saves of BySpine's, show beside each other. Untabled, BySharedPrefix runs BySpine's machine (`WeakHead`), so it
      // has no row of its own.
      applications <- ApplicationReading.values.toVector
      slotReading <- SlotReading.values.toVector
    yield
      val reading = readings((Mode.TablingWeakHead, applications, slotReading, 1))
      s"tabled\t$applications\t$slotReading\t1\tsteps ${reading.spent}\ttables ${reading.tables}")
    assertFileSnapshot(counts.mkString("", "\n", "\n"), "knowledge/reading_counts.tsv")
  }
