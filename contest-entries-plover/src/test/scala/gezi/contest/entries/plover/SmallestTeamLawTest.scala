package gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import gezi.contest.natives.plover.SmallestTeam
import gezi.generatedinputs.GeneratedProperties

/** The law of the smallest team: the native's value is the value of the
  * recursion the program writes, on the people and the set covered so far, for
  * every full set and cost of an uncovered set. Its purpose is to catch a person
  * with a skill outside the full set counted as useful, a cost of an uncovered
  * set that is not the bound it is, and an empty full set read as uncovered.
  */
class SmallestTeamLawTest extends GeneratedProperties:

  /** The definition, read as written, with no table. */
  private def byDefinition(people: List[Int], covered: Int, full: Int, uncovered: Int): Int = people match
    case Nil => if covered == full then 0 else uncovered
    case skills :: others =>
      math.min(
        byDefinition(others, covered, full, uncovered),
        1 + byDefinition(others, covered | skills, full, uncovered)
      )

  property("the size is the value of the recursion on the people and the covered set") {
    for
      people <- Gen.list(Gen.int(Range.linear(0, 31)), Range.linear(0, 8)).forAll
      full <- Gen.int(Range.linear(0, 31)).forAll
      uncovered <- Gen.int(Range.linear(0, 10)).forAll
    yield
      val value = SmallestTeam.size(
        people.toVector.map(person => new BigInteger(person.toString)),
        new BigInteger(full.toString),
        new BigInteger(uncovered.toString)
      )
      Result.diff(value.intValueExact, byDefinition(people, 0, full, uncovered))(_ == _)
  }
