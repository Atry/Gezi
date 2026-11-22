package gezi.weakhead

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.Defunctionalization
import gezi.frontend.Literals
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.ir.Instruction

/** The options of `ApplicationReading` on generated closed terms, read
  * under the extremes of the contest's readings (top a greatest term,
  * `KnownExtremes.onlyTop`). A third of the terms are top applied to generated
  * arguments, so that top stands as a proper prefix of a spine, where
  * `BySpine` compares the listed term with the spine's first arguments.
  *
  * Under `weak_head`, `BySpine` charges one step where `ByLayer` charges one
  * for each application of a spine, and nothing else differs, so wherever
  * `ByLayer` finishes `BySpine` finishes too, with the same parallel sets in
  * the same order. Under `tabling(weak_head)`, `BySpine` makes no table for a
  * shorter prefix, so its steps are not bounded by `ByLayer`'s, and the law
  * is that two readings that both finish give the same parallel sets.
  *
  * Purpose: catch a `BySpine` machine that loses, doubles or reorders an
  * argument of a spine, or that misses a known extreme standing as a prefix
  * of one.
  *
  * `BySharedPrefix` reads as `BySpine` untabled, the same code. Tabled, it
  * calls some prefix of each spine through its table where `ByLayer` calls
  * every prefix, so the laws are that two readings that both finish give the
  * same parallel sets, and that every table it completes `ByLayer` completes
  * too; they are checked on spines that share prefixes and on keys looked up
  * in partial functions of literals as well, where it chooses which prefixes
  * to table.
  */
class ApplicationReadingLawTest extends GeneratedProperties:

  /** The steps of one reading, `TopKnowledgeLawTest`'s limit. */
  private val limit: Long = 20000

  private val top: Instruction = Defunctionalization.thunkInstruction(Literals.top)

  private val terms: Gen[Instruction] =
    val generated = HoasGenerators.evaluatorInstruction(8)
    Gen.frequency1(
      2 -> generated,
      1 -> generated.list(Range.linear(1, 3)).map(_.foldLeft(top)(Instruction.Apply(_, _)))
    )

  private def heads(
      mode: Mode,
      term: Instruction,
      applications: ApplicationReading
  ): Bounded[Vector[ParallelSet]] =
    val start = ReadingState.knowingTop(limit).copy(applications = applications)
    WeakHead.heads(mode, term).collected.result(start) match
      case Computed.Done(found, _) => Bounded.Finished(found)
      case Computed.Stopped(after) => EvaluatorTesting.stopped(after)

  property("byLayerAndBySpineGiveTheSameHeadsUnderWeakHead") {
    for term <- terms.forAll
    yield heads(Mode.WeakHead, term, ApplicationReading.ByLayer) match
      case Bounded.Finished(byLayer) =>
        heads(Mode.WeakHead, term, ApplicationReading.BySpine) match
          case Bounded.Finished(bySpine) => Result.diff(byLayer, bySpine)(_ == _)
          case other                     => Result.failure.log(s"by spine did not finish: $other")
      case _ => Result.success
  }

  property("byLayerAndBySpineGiveTheSameHeadsUnderTablingWhereBothFinish") {
    for term <- terms.forAll
    yield (
      heads(Mode.TablingWeakHead, term, ApplicationReading.ByLayer),
      heads(Mode.TablingWeakHead, term, ApplicationReading.BySpine)
    ) match
      case (Bounded.Finished(byLayer), Bounded.Finished(bySpine)) => Result.diff(byLayer.toSet, bySpine.toSet)(_ == _)
      case _                                                     => Result.success
  }

  /** Spines of one head over a pool of three arguments, several of them in
    * one choice, so that spines share prefixes and part from each other at
    * some, and a spine may be a prefix of another: what `BySharedPrefix`
    * tables (its divergence points) and what it reads from a table (its
    * longest tabled prefix).
    */
  private val sharedSpines: Gen[Instruction] =
    for
      head <- HoasGenerators.evaluatorInstruction(4)
      pool <- HoasGenerators.evaluatorInstruction(2).list(Range.singleton(3)).map(_.toVector)
      spines <- Gen.int(Range.constant(0, 2)).list(Range.linear(1, 5)).list(Range.linear(1, 4))
    yield spines
      .map(_.foldLeft(head)((function, index) => Instruction.Apply(function, pool(index))))
      .reduceLeft(Instruction.Choice(_, _))

  /** Keys of two letters looked up in a choice of variable arguments partial
    * functions of literals (`λ"key". value`), each lookup the record applied
    * to its key's elements (`Literals.arguments`), several lookups in one
    * choice: a binary trie, whose branch nodes are `BySharedPrefix`'s divergence points.
    */
  private val lookups: Gen[Instruction] =
    val key = Gen.string(Gen.element1('a', 'b'), Range.linear(1, 4))
    for
      fields <- key.list(Range.linear(1, 4)).map(_.distinct.toVector)
      looked <- key.list(Range.linear(1, 4))
    yield
      val record = fields.zipWithIndex
        .map((name, value) =>
          Defunctionalization.thunkInstruction(
            Literals.partialFunction(gezi.frontend.Literal.text(name), Literals.integerTerm(BigInt(value)))
          )
        )
        .reduceLeft(Instruction.Choice(_, _))
      looked
        .map(name =>
          Literals
            .arguments(gezi.frontend.Literal.text(name))
            .foldLeft(record)((function, element) => Instruction.Apply(function, Defunctionalization.thunkInstruction(element)))
        )
        .reduceLeft(Instruction.Choice(_, _))

  private val shared: Gen[Instruction] = Gen.frequency1(1 -> terms, 2 -> sharedSpines, 2 -> lookups)

  /** The steps of one reading of the law below. Lower than `limit`: a
    * generated self-application that never finishes runs to the limit, and
    * one step that reads a choice of n members costs n at once, so its time
    * grows faster than its steps. Measured 2026-11-21 on cores 6,7 at load 6
    * to 9: an input of `terms` (a seeded sample) read to 20,000 steps took
    * 6.9 s under `BySpine` and 4.3 s under `ByLayer` with 10,000 to 12,000
    * open tables, and the law over `sharedSpines` alone took 4 to 26 s at
    * that limit.
    *
    * FIXME (https://github.com/Atry/private-overlay/issues/1842): the lower
    * limit works around a defect of the evaluator, not of this law. A step
    * that reads a choice is charged one step and costs O(members), so the
    * step budget does not bound time. Once a choice step is charged by its
    * members (or its members are built once at interning), this law returns
    * to `limit`.
    */
  private val sharedLimit: Long = 2000

  /** The heads of a tabled reading and the keys of the tables it completed. */
  private def tabled(term: Instruction, applications: ApplicationReading): Bounded[(Set[ParallelSet], Set[Value])] =
    val start = ReadingState.knowingTop(sharedLimit).copy(applications = applications)
    WeakHead.heads(Mode.TablingWeakHead, term).collected.result(start) match
      case Computed.Done(found, after) => Bounded.Finished((found.toSet, after.tables.complete.keySet))
      case Computed.Stopped(after)     => EvaluatorTesting.stopped(after)

  /** Purpose: catch a `BySharedPrefix` reading that calls a prefix and then
    * applies the wrong arguments after it (one too many or too few, from the
    * wrong end), or that reads an extreme prefix wrongly, which would give
    * other parallel sets than `ByLayer` where both finish; and one that
    * tables a term `ByLayer` would not table, which the law below catches:
    * every table it makes is the table of a prefix of a spine or of a term
    * `ByLayer` tables too.
    */
  property("bySharedPrefixGivesByLayersHeadsAndTablesNoKeyByLayerDoesNotWhereBothFinish") {
    for term <- shared.forAll
    yield (tabled(term, ApplicationReading.ByLayer), tabled(term, ApplicationReading.BySharedPrefix)) match
      case (Bounded.Finished((byLayer, byLayerKeys)), Bounded.Finished((bySharedPrefix, bySharedPrefixKeys))) =>
        Result.all(
          List(
            Result.diff(byLayer, bySharedPrefix)(_ == _).log("the heads"),
            Result
              .assert(bySharedPrefixKeys.subsetOf(byLayerKeys))
              .log(s"tables by shared prefix only: ${(bySharedPrefixKeys -- byLayerKeys).size}")
          )
        )
      case _ => Result.success
  }
