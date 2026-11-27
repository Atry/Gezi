package com.yang_bo.gezi.contest.natives.plover

import java.math.BigInteger

/** The value of the definition it replaces, the typed version
  * `plover_typed_smallest_team`: the least, over the subsets S of the people,
  * of |S| plus nothing when the union of S's skill sets is `full` and plus
  * `uncovered` otherwise. The empty subset costs `uncovered` unless `full` is
  * empty, so that value is the smaller of `uncovered` and the size of a
  * smallest subset whose union is `full`. A person with a skill outside `full`
  * is in no such subset. The size is computed over the skills of `full`, for
  * each set of required skills the fewest people among those read so far who
  * cover it, in O(people * 2^skills) cells, keeping one row.
  *
  * The skill sets, `full` and `uncovered` are canonical naturals, which is what
  * the native's places declare, and a narrow block compiles the call only when
  * the filters at the operands' roots name them. A native does not check its
  * operands (`CONTRIBUTING.md`, "Types live only in the term"). A `full` of
  * more than `largestSkillCount` skills is more cells than a table holds, and
  * this throws `ArithmeticException` on it.
  */
object SmallestTeam:

  /** The most skills in `full` whose table is computed: 2^26 cells of an `Int`
    * are 256 MB, and each person allocates one row.
    */
  private val largestSkillCount: Int = 26

  /** A count above any count of people, whose increment does not overflow. */
  private val unreachable: Int = Int.MaxValue / 2

  /** The value of the definition on the people, the full set and the cost of a
    * set left uncovered.
    */
  def size(
      people: Vector[BigInteger],
      full: BigInteger,
      uncovered: BigInteger
  ): BigInteger =
    val skills = (0 until full.bitLength).filter(full.testBit).toVector
    if skills.size > largestSkillCount then
      throw ArithmeticException(
        s"a full set of ${skills.size} skills is more than $largestSkillCount"
      )
    val masks = people
      .filter(_.andNot(full).signum == 0)
      .map(person =>
        skills.indices.foldLeft(0)((mask, position) =>
          if person.testBit(skills(position)) then mask | (1 << position)
          else mask
        )
      )
    val cells = 1 << skills.size
    val noOne = IArray.tabulate(cells)(required =>
      if required == 0 then 0 else unreachable
    )
    val everyone = masks.foldLeft(noOne) { (before, mask) =>
      IArray.tabulate(cells)(required =>
        math.min(before(required), 1 + before(required & ~mask))
      )
    }
    val smallest = everyone(cells - 1)
    if smallest == unreachable then uncovered
    else uncovered.min(BigInteger.valueOf(smallest.toLong))
