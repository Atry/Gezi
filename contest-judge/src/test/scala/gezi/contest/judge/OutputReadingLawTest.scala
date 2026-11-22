package gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.contest.entry.OutputDisplay
import gezi.frontend.DeBruijnTerm
import gezi.generatedinputs.GeneratedProperties

/** The laws of the judge's reading of an output, the contest's rules for
  * scoring an evaluation and for reading an output, on generated references and displays
  * of Church numerals with or without a remainder (an unevaluated redex):
  * the normal form members F of the display against the reference R; F ⊄ R
  * is `False` with nothing earned; otherwise the share is (|F| + c) of
  * (|R| + 1), c = 1 exactly when F = R and there is no remainder, the share
  * 1 `Success`, 0 `NoAnswer` and any other `Incomplete`. A judgment of N is
  * the same with R = {N} on a member and R = ∅ on a trap: `N` alone is
  * `Proved` on a member, `N` with a remainder half of it, the empty answer
  * `Refuted` on a trap. Their purpose is to catch a reading that scores a
  * remainder as the whole set, voids a false negative, or lets a false
  * positive through.
  */
class OutputReadingLawTest extends GeneratedProperties:

  private def numeral(count: Int): DeBruijnTerm =
    DeBruijnTerm.Lambda(DeBruijnTerm.Lambda((1 to count).foldLeft(DeBruijnTerm.Variable(0): DeBruijnTerm)((body, _) =>
      DeBruijnTerm.Apply(DeBruijnTerm.Variable(1), body))))

  private val remainder: DeBruijnTerm =
    DeBruijnTerm.Apply(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0)), DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0)))

  /** The counts of numerals that are βη normal forms: the numeral of 1,
    * `λf. λx. f x`, is an η redex, which the judge reads as no normal form.
    */
  private val counts = Gen.element(0, List(2, 3, 4, 5, 6, 7, 8, 9))

  private def display(shown: Set[DeBruijnTerm], withRemainder: Boolean): OutputDisplay =
    val members = shown.toVector.sortBy(_.toString) ++ Option.when(withRemainder)(remainder).toVector
    if members.isEmpty then OutputDisplay.NoNormalForm else OutputDisplay.shown(DeBruijnTerm.nestedChoice(members))

  property("anEvaluationEarnsItsNormalFormsAndOneMoreForTheWholeSetWithNoRemainder") {
    for
      reference <- counts.list(Range.linear(0, 5)).forAll.map(_.distinct.map(numeral).toSet)
      shown <- counts.list(Range.linear(0, 5)).forAll.map(_.distinct.map(numeral).toSet)
      withRemainder <- Gen.boolean.forAll
    yield
      val expected =
        if !shown.subsetOf(reference) then (Outcome.False, Share.none)
        else
          val earned = shown.size + (if shown == reference && !withRemainder then 1 else 0)
          val outcome =
            if earned == reference.size + 1 then Outcome.Success
            else if earned == 0 then Outcome.NoAnswer
            else Outcome.Incomplete
          (outcome, Share(earned, reference.size + 1))
      Result.diff(Outcome.judged(Question.Evaluation(reference), display(shown, withRemainder)), expected)(_ == _)
        .log(s"reference $reference, shown $shown, remainder $withRemainder")
  }

  property("aJudgmentIsAnEvaluationOfTheCandidateOrOfNothing") {
    for
      candidate <- counts.forAll.map(numeral)
      member <- Gen.boolean.forAll
    yield
      val question = Question.Judgment(gezi.frontend.Defunctionalization.thunkInstruction(candidate), member)
      Result.all(List(
        Result.diff(Outcome.judged(question, display(Set.empty, false)), if member then (Outcome.Unknown, Share(0, 2)) else (Outcome.Refuted, Share(1, 1)))(_ == _)
          .log("the empty answer"),
        Result.diff(Outcome.judged(question, OutputDisplay.shown(candidate)), if member then (Outcome.Proved, Share(2, 2)) else (Outcome.False, Share.none))(_ == _)
          .log("the candidate alone"),
        Result.diff(Outcome.judged(question, display(Set(candidate), true)), if member then (Outcome.Incomplete, Share(1, 2)) else (Outcome.False, Share.none))(_ == _)
          .log("the candidate with a remainder"),
        Result.diff(Outcome.judged(question, OutputDisplay.shown(remainder)), (Outcome.Unknown, Share(0, if member then 2 else 1)))(_ == _).log("no normal form")
      ))
  }
