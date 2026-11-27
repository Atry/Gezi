package gezi.standardlibrary

import hedgehog.Result
import hedgehog.core.SuccessCount
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.KnowledgeGenerators
import gezi.ir.ChoiceSpine
import gezi.ir.Configured
import gezi.ir.NativeSpecializer.*
import gezi.ir.NoFacts
import gezi.knowledgereading.KnowledgeReading

/** The law of the cost of reading knowledge, on generated knowledge
  * (`KnowledgeGenerators`): the read of a knowledge term by
  * `StandardLibrary.compiled` (`KnowledgeFileReading` on the generic reader
  * `KnowledgeReading`), from the compilation's first state
  * (`KnowledgeReading.compilationState`). For two knowledges of disjoint
  * names, the evaluator steps of reading the two chosen together are at most
  * the sum of the steps of reading each alone, and so are the complete
  * tables: a reader linear in the knowledge reads each member of the two
  * together as it reads it alone, and the slots and groups once instead of
  * twice.
  *
  * Its purpose is to catch a reader whose cost grows faster than linearly in
  * the knowledge's size, such as a look-up that passes every member for each
  * member: a cost of a·n² in the n members makes the reading of the two
  * together cost 2a·n₁·n₂ more than the two readings, which the slots and
  * groups read once cannot cover once the knowledges hold a few dozen
  * members, as the generator's largest do.
  */
class KnowledgeReadingCostLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts

  // Measured 2026-11-22 on 2 CPUs (contest.slice, CPUs 10,11, nice 10), the 1-minute load 13 to 18: the law, alone in its test JVM, took 4.47 s (the deadline raised to 600 s) and 5.84 s in two runs, of which reading a knowledge of a few thousand steps takes 30 to 90 ms and parsing its text about as long; the bound is 1.5 times the slower run (8.76 s) rounded up to 10 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "s")

  /** The most members of each slot of a generated knowledge. */
  private val maximumMembers: Int = 3

  /** The evaluator steps and the complete tables of reading the knowledge. */
  private def cost(knowledge: Configured[NoFacts.type]): (Long, Int) =
    val (_, after) = StandardLibrary.compiled(knowledge, Vector.empty, KnowledgeReading.compilationState)
    (after.budget.spent, after.tables.complete.size)

  property(
    "reading two knowledges together costs at most the sum of reading each",
    // Eight inputs, their sizes growing to the largest: each input is three
    // readings, and the law needs the large ones.
    _.copy(testLimit = SuccessCount(8))
  ) {
    for
      first <- KnowledgeGenerators.knowledgeText("first", KnowledgeGenerators.fillableSlots, maximumMembers).forAll
      second <- KnowledgeGenerators.knowledgeText("second", KnowledgeGenerators.fillableSlots, maximumMembers).forAll
    yield
      val firstTerm = KnowledgeGenerators.term[NoFacts.type](first)
      val secondTerm = KnowledgeGenerators.term[NoFacts.type](second)
      val (firstSteps, firstTables) = cost(firstTerm)
      val (secondSteps, secondTables) = cost(secondTerm)
      val (togetherSteps, togetherTables) = cost(ChoiceSpine.nested[Configured[NoFacts.type]](Vector(firstTerm, secondTerm), NoFacts.choice(_, _)))
      Result
        .assert(togetherSteps <= firstSteps + secondSteps)
        .log(s"steps: $firstSteps and $secondSteps alone, $togetherSteps together")
        .and(
          Result
            .assert(togetherTables <= firstTables + secondTables)
            .log(s"tables: $firstTables and $secondTables alone, $togetherTables together")
        )
  }
