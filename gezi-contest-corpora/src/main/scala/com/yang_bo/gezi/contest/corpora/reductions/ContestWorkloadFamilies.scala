package com.yang_bo.gezi.contest.corpora.reductions

import com.yang_bo.gezi.contest.corpora.reductions.Encodings.*
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.*

/** The hand-written native Scala solutions of the families of programming
  * contest shape (`LibraryLongestCommonSubsequences`, `LibraryBillboards`,
  * `LibraryEditDistances`, `LibrarySmallestTeams`): the computed references of
  * their points, and what the benchmarks of `jmh-pipeline` time as the
  * families' reference times.
  */
object ContestWorkloadSolutions:

  /** The length of a longest common subsequence of the two strings, by the
    * row-by-row dynamic programme over the pairs of prefixes (Wagner and
    * Fischer, J. ACM 1974), the port of `longest_common_subsequence/3` of the
    * deleted Prolog file (`git show
    * 91b3f11e1^:lambda_jit/corpora/contest_set_free_dynamic.pl`; its data are
    * `problems/set_free_dynamic`): the row of `first`'s prefix of i + 1
    * characters, at the index j + 1, is the row above at j plus one where the
    * characters i and j are equal, and the larger of the row above at j + 1 and
    * the row's own value at j otherwise. |first| * |second| cells.
    */
  def longestCommonSubsequence(first: IArray[Int], second: IArray[Int]): Int =
    val columns = IArray.range(0, second.length)
    first
      .foldLeft(IArray.fill(second.length + 1)(0))((above, character) =>
        columns.scanLeft(0)((left, column) =>
          if character == second(column) then above(column) + 1
          else math.max(above(column + 1), left)
        )
      )
      .last

  /** The heights the two supports of a billboard can share, in increasing
    * order: the h such that two disjoint sets of the rods each sum to h. The
    * dynamic programme over the difference of the two sums, each difference
    * keeping its set of left sums as a bit set, the algorithm of
    * `native_heights/2` of the deleted Prolog file (`git show
    * 91b3f11e1^:lambda_jit/corpora/contest_hidden_37_billboard.pl`): after a
    * rod of length x, the left sums at the difference d are those before it at
    * d (the rod left out), those at d - x shifted up by x (welded to the left)
    * and those at d + x (welded to the right). The differences run from -S to
    * S, S the sum of the rods; n * (2S + 1) unions of bit sets of S + 1 bits.
    */
  def billboardHeights(rods: IArray[Int]): Vector[Int] =
    val total = rods.sum
    val first = IArray.tabulate(2 * total + 1)(index =>
      if index == total then BigInt(1) else BigInt(0)
    )
    val last = rods.foldLeft(first)((sums, rod) =>
      IArray.tabulate(2 * total + 1)(index =>
        val left =
          if index - rod >= 0 then sums(index - rod) << rod else BigInt(0)
        val right =
          if index + rod <= 2 * total then sums(index + rod) else BigInt(0)
        sums(index) | left | right
      )
    )
    val balanced = last(total)
    (0 to total).filter(balanced.testBit).toVector

  /** Whether two disjoint sets of the rods each sum to the target: the heights
    * of `billboardHeights`, then the target looked up among them.
    */
  def billboardReaches(rods: IArray[Int], target: Int): Boolean =
    billboardHeights(rods).contains(target)

  /** The edit distance of the two strings, the least number of insertions,
    * deletions and substitutions that turn the first into the second, by Wagner
    * and Fischer's table over the pairs of prefixes (J. ACM 1974,
    * doi:10.1145/321796.321811), the port of `edit_distance/3` of the deleted
    * Prolog file (`git show
    * 91b3f11e1^:lambda_jit/corpora/contest_hidden_37_edits.pl`; its data are
    * `problems/hidden_37_edits`): the row of the first string's prefix of i + 1
    * characters starts at i + 1, and at the index j + 1 it is the row above at
    * j where the characters i and j are equal, and one more than the least of
    * the row above at j, the row above at j + 1 and the row's own value at j
    * otherwise. |first| * |second| cells.
    */
  def editDistance(first: IArray[Int], second: IArray[Int]): Int =
    val columns = IArray.range(0, second.length)
    IArray
      .range(0, first.length)
      .foldLeft(IArray.range(0, second.length + 1))((above, row) =>
        columns.scanLeft(row + 1)((left, column) =>
          if first(row) == second(column) then above(column)
          else 1 + math.min(above(column), math.min(above(column + 1), left))
        )
      )
      .last

  /** The size of a smallest sufficient team (LeetCode 1125): the fewest people
    * whose skill sets, bit sets over `skills` skills, together hold every
    * skill, or the number of people plus one when all of them do not. The
    * dynamic programme over the subsets of skills (Held and Karp, J. SIAM 1962,
    * doi:10.1137/0110015), the port of `smallest_team/3` of the deleted Prolog
    * file (`git show 91b3f11e1^:lambda_jit/corpora/contest_smallest_team.pl`;
    * its data are `problems/smallest_team`), here over the program's state, the
    * people not yet considered and the covered set: after the last person, the
    * full set costs 0 and every other set the people's count plus one; before a
    * person, a covered set costs the less of leaving them out and one more than
    * taking them, whose set joins the covered one. n * 2^s cells.
    */
  def smallestTeam(skills: Int, people: IArray[Int]): Int =
    val full = (1 << skills) - 1
    val afterEveryone = IArray.tabulate(full + 1)(covered =>
      if covered == full then 0 else people.length + 1
    )
    people.reverse
      .foldLeft(afterEveryone)((after, person) =>
        IArray.tabulate(full + 1)(covered =>
          math.min(after(covered), 1 + after(covered | person))
        )
      )(0)

/** The edit distance of two strings (LeetCode 72), the port of
  * `problems/hidden_37_edits`, scaled to a programming contest's size. That
  * file asked, in continuation passing style, for the set of the costs within a
  * budget of the edit scripts; here the program is the distance's definition,
  * the recursion on the two lists built from the library's terms, a pure λ term
  * whose one normal form is the distance:
  *
  * {{{
  * ed = fixpoint (\self. \xs. \ys.
  *        xs (ys binary_zero (\y. \yt. merge_binary_increment (self xs yt)))
  *           (\x. \xt. ys (merge_binary_increment (self xt ys)) (\y. \yt.
  *             merge_binary_equality x y (self xt yt)
  *               (merge_binary_increment (binary_minimum (self xt yt)
  *                                          (binary_minimum (self xt ys) (self xs yt)))))))
  * }}}
  *
  * the function let bound once and applied at R distinct sites, each a pair of
  * strings over an alphabet of k characters. Read as written, the recursion
  * recomputes the same pairs of suffixes exponentially often; recognising the
  * pair by value gives Wagner and Fischer's table over the (n + 1)(m + 1)
  * pairs. The respelled function writes the increments at the end of either
  * string through compose, `compose merge_binary_increment (self xs) yt`, and
  * takes the minimum of the three in the other order.
  *
  * The encoding: every character and every length is a canonical binary natural
  * (`corpora/standard_library/binary`), and so is each site's answer; that
  * file's characters were Booleans and its numbers unary numerals. The work and
  * the encoding: (n + 1)(m + 1) pairs, each an equality of characters of two
  * bits and a minimum and an increment of naturals of O(log n) bits; at the
  * nominal n = m = 3000, 9 * 10^6 pairs per site. The input is n + m
  * characters, about 5(n + m) constructors, and the answer one natural of 12
  * bits, so encoding and decoding are O(n) against the n^2 pairs. The
  * hand-written native solution is `ContestWorkloadSolutions.editDistance`.
  */
final class LibraryEditDistances(
    spelling: Spelling,
    val nominal: NominalRanges,
    val family: String
) extends StandardLibraryFamily[LibraryEditDistances.Drawn](spelling)
    with NativelySolved[LibraryEditDistances.Drawn]:

  import LibraryEditDistances.Strings

  val claim: String = LibraryEditDistances.claim

  /** Each site's distance, a canonical binary natural. */
  def solved(drawn: LibraryEditDistances.Drawn): Vector[NativeValue] =
    drawn.sites.map(strings =>
      NativeValue.LibraryNatural(
        BigInt(
          ContestWorkloadSolutions.editDistance(
            IArray.from(strings.first),
            IArray.from(strings.second)
          )
        )
      )
    )

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): LibraryEditDistances.Drawn =
    LibraryEditDistances.drawn(nominal, draws, repetitions)

  private def arguments(
      terms: StandardLibraryTerms,
      strings: Strings
  ): Vector[ProblemTerm] =
    import terms.*
    Vector(
      list(strings.first.map(character => binary(character))),
      list(strings.second.map(character => binary(character)))
    )

  protected def program(
      terms: StandardLibraryTerms,
      drawn: LibraryEditDistances.Drawn
  ): ProblemTerm =
    terms.sites(
      LibraryEditDistances.function(terms, spelling),
      drawn.sites.map(arguments(terms, _))
    )

  protected def singlePrograms(
      terms: StandardLibraryTerms,
      drawn: LibraryEditDistances.Drawn
  ): Vector[ProblemTerm] =
    val function = LibraryEditDistances.function(terms, spelling)
    drawn.sites.map(strings => applied(function, arguments(terms, strings)))

/** The draws, the function, the nominal ranges and the variants of
  * `LibraryEditDistances`.
  */
object LibraryEditDistances:

  /** The two strings of a site, each character a natural below k. */
  final case class Strings(first: Vector[Int], second: Vector[Int])

  /** The strings of the sites. */
  final case class Drawn(sites: Vector[Strings])

  /** R distinct pairs of strings: each string's length drawn from the range
    * `length`, then its characters from the range `character`.
    */
  def drawn(nominal: NominalRanges, draws: Draws, repetitions: Int): Drawn =
    Drawn(draws.distinct(repetitions)(pair(nominal))._1)

  /** R distinct pairs of strings of the two lengths, their characters drawn
    * from the range `character`: the draws of one parameter set of the claim's
    * parameter law.
    */
  def drawnOfLengths(
      nominal: NominalRanges,
      draws: Draws,
      repetitions: Int,
      firstLength: Int,
      secondLength: Int
  ): Drawn =
    Drawn(
      draws
        .distinct(repetitions)(
          pairOfLengths(nominal, firstLength, secondLength)
        )
        ._1
    )

  private def pair(nominal: NominalRanges)(draws: Draws): (Strings, Draws) =
    val (firstLength, afterFirstLength) =
      Repetition.drawnNumber(draws, nominal, "length")
    val (secondLength, afterSecondLength) =
      Repetition.drawnNumber(afterFirstLength, nominal, "length")
    pairOfLengths(nominal, firstLength, secondLength)(afterSecondLength)

  private def pairOfLengths(
      nominal: NominalRanges,
      firstLength: Int,
      secondLength: Int
  )(draws: Draws): (Strings, Draws) =
    val (first, afterFirst) = string(nominal, firstLength, draws)
    val (second, afterSecond) = string(nominal, secondLength, afterFirst)
    (Strings(first, second), afterSecond)

  private def string(
      nominal: NominalRanges,
      length: Int,
      draws: Draws
  ): (Vector[Int], Draws) =
    (1 to length).foldLeft((Vector.empty[Int], draws))((drawn, _) =>
      val (before, beforeDraws) = drawn
      val (character, afterCharacter) =
        Repetition.drawnNumber(beforeDraws, nominal, "character")
      (before :+ character, afterCharacter)
    )

  /** The recursion on the two lists in the spelling. */
  def function(terms: StandardLibraryTerms, spelling: Spelling): ProblemTerm =
    import terms.*
    fixpoint(
      λ(self =>
        λ(firstString =>
          λ(secondString =>
            def incremented(
                function: ProblemTerm,
                argument: ProblemTerm
            ): ProblemTerm = spelling match
              case Spelling.Direct    => binaryIncrement(function(argument))
              case Spelling.Respelled =>
                compose(binaryIncrement)(function)(argument)
            firstString(
              secondString(binaryZero)(
                λ(_ =>
                  λ(secondRest => incremented(self(firstString), secondRest))
                )
              )
            )(
              λ(character =>
                λ(firstRest =>
                  secondString(incremented(self(firstRest), secondString))(
                    λ(other =>
                      λ(secondRest =>
                        val substituted = self(firstRest)(secondRest)
                        val deleted = self(firstRest)(secondString)
                        val inserted = self(firstString)(secondRest)
                        val least = spelling match
                          case Spelling.Direct =>
                            binaryMinimum(substituted)(
                              binaryMinimum(deleted)(inserted)
                            )
                          case Spelling.Respelled =>
                            binaryMinimum(binaryMinimum(inserted)(deleted))(
                              substituted
                            )
                        binaryEquality(character)(other)(substituted)(
                          binaryIncrement(least)
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  /** The family's name. */
  val name: String = "repeated_library_edit_distances"

  /** The test that checks the computed reference against tabling(weak_head)'s
    * reading on small draws.
    */
  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.LibraryEditDistancesReferenceTest"

  /** The nominal ranges of the family's points: strings of n = m = 3000
    * characters over an alphabet of 4 (characters 0 to 3), at R up to 4; 9 *
    * 10^6 pairs of suffixes per site. weak_head's reading is exponential in n
    * (a probe of 2026-09-30, on the budgeted program: tabling(weak_head) read
    * 120 bits in 41761 ms), far beyond `judgePointsFile`'s 20,000,000 steps.
    * The native solution's time is
    * `ContestWorkloadBenchmarks.editDistancesDirect` and
    * `editDistancesRespelled` of `jmh-pipeline`.
    */
  val nominal: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(4),
    Vector(
      NominalParameter("length", 3000 to 3000),
      NominalParameter("character", 0 to 3)
    )
  )

  /** The family in both spellings at the family's nominal ranges. */
  val variants: Vector[LibraryEditDistances] = Repetition.spellings.map(
    LibraryEditDistances(_, nominal, LibraryEditDistances.name)
  )

  /** The low rung's family name. */
  val smallName: String = "repeated_library_edit_distances_small"

  /** The nominal ranges of the low rung: strings of 120 characters, the size at
    * which the Prolog corpus's edit distance was read (tabling(weak_head) read
    * 120 bits in 41761 ms), over the same alphabet and at the same R as
    * `nominal`, whose top rung stays at the contest's workload.
    */
  val smallNominal: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(4),
    Vector(
      NominalParameter("length", 120 to 120),
      NominalParameter("character", 0 to 3)
    )
  )

  /** The low rung in the spelling at its nominal ranges. */
  def small(spelling: Spelling): LibraryEditDistances =
    LibraryEditDistances(spelling, smallNominal, smallName)

  /** The low rung in both spellings at its nominal ranges. */
  val smallVariants: Vector[LibraryEditDistances] =
    Repetition.spellings.map(small)

/** The smallest sufficient team (LeetCode 1125), the port of
  * `problems/smallest_team`, scaled to a programming contest's size: people
  * with skill sets, the fewest people whose sets together hold every skill.
  * That file asked, in continuation passing style, for the set of the sizes
  * within a budget; here the program is the definition, the recursion on the
  * list of people with the covered set, built from the library's terms, a pure
  * λ term whose one normal form is the size:
  *
  * {{{
  * team = fixpoint (\self. \people. \covered.
  *          people (merge_binary_equality covered full binary_zero uncovered)
  *            (\skills. \rest. binary_minimum (self rest covered)
  *               (merge_binary_increment (self rest (binary_bitwise_or covered skills)))))
  * }}}
  *
  * with `full` the set of every skill and `uncovered` the count of people plus
  * one, the cost of a covered set that is not full after the last person; the
  * function `\people. \full. \uncovered. team people binary_zero` let bound
  * once and applied at R distinct sites. Read as written, the choices are 2^n;
  * the state is the rest of the people and the covered set, n * 2^s of them,
  * the dynamic programme over the subsets. The respelled function joins the
  * sets the other way round, `binary_bitwise_or skills covered`, writes the
  * increment through compose and takes the minimum in the other order.
  *
  * The encoding: every skill set is a canonical binary natural read as a bit
  * set, bit i for skill i (`corpora/standard_library/binary`), and so are the
  * counts and the answer. The work and the encoding: the programme is n * 2^s
  * cells, each a bitwise or of s bits, a minimum and an increment; at the
  * nominal n = 60 people and s = 19 skills, 3.1 * 10^7 cells per site. The
  * input is n sets of s bits, about 5ns constructors, and the answer one
  * natural of 6 bits, so encoding and decoding are O(ns) against the n * 2^s
  * cells: the input is small and the work large. The hand-written native
  * solution is `ContestWorkloadSolutions.smallestTeam`.
  */
final class LibrarySmallestTeams(
    spelling: Spelling,
    val nominal: NominalRanges,
    val family: String
) extends StandardLibraryFamily[LibrarySmallestTeams.Drawn](spelling)
    with NativelySolved[LibrarySmallestTeams.Drawn]:

  import LibrarySmallestTeams.Team

  val claim: String = LibrarySmallestTeams.claim

  /** Each site's size, a canonical binary natural. */
  def solved(drawn: LibrarySmallestTeams.Drawn): Vector[NativeValue] =
    drawn.sites.map(team =>
      NativeValue.LibraryNatural(
        BigInt(
          ContestWorkloadSolutions.smallestTeam(
            team.skills,
            IArray.from(team.people)
          )
        )
      )
    )

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): LibrarySmallestTeams.Drawn =
    LibrarySmallestTeams.drawn(nominal, draws, repetitions)

  private def arguments(
      terms: StandardLibraryTerms,
      team: Team
  ): Vector[ProblemTerm] =
    import terms.*
    Vector(
      list(team.people.map(person => binary(person))),
      binary((BigInt(1) << team.skills) - 1),
      binary(team.people.size + 1)
    )

  protected def program(
      terms: StandardLibraryTerms,
      drawn: LibrarySmallestTeams.Drawn
  ): ProblemTerm =
    terms.sites(
      LibrarySmallestTeams.function(terms, spelling),
      drawn.sites.map(arguments(terms, _))
    )

  protected def singlePrograms(
      terms: StandardLibraryTerms,
      drawn: LibrarySmallestTeams.Drawn
  ): Vector[ProblemTerm] =
    val function = LibrarySmallestTeams.function(terms, spelling)
    drawn.sites.map(team => applied(function, arguments(terms, team)))

/** The draws, the function, the nominal ranges and the variants of
  * `LibrarySmallestTeams`.
  */
object LibrarySmallestTeams:

  /** The count of skills of a site and its people's skill sets, each a bit set
    * below 2^skills.
    */
  final case class Team(skills: Int, people: Vector[Int])

  /** The teams of the sites. */
  final case class Drawn(sites: Vector[Team])

  /** R distinct teams: the count of skills and the count of people drawn for
    * each, then whether each person holds each skill, held when the draw from
    * the range `held` is 0.
    */
  def drawn(nominal: NominalRanges, draws: Draws, repetitions: Int): Drawn =
    Drawn(draws.distinct(repetitions)(team(nominal))._1)

  /** R distinct teams of the two counts, the skills drawn as `drawn` draws
    * them: the draws of one parameter set of the claim's parameter law.
    */
  def drawnOfCounts(
      nominal: NominalRanges,
      draws: Draws,
      repetitions: Int,
      skills: Int,
      people: Int
  ): Drawn =
    Drawn(draws.distinct(repetitions)(teamOfCounts(nominal, skills, people))._1)

  private def team(nominal: NominalRanges)(draws: Draws): (Team, Draws) =
    val (skills, afterSkills) = Repetition.drawnNumber(draws, nominal, "skills")
    val (people, afterPeople) =
      Repetition.drawnNumber(afterSkills, nominal, "people")
    teamOfCounts(nominal, skills, people)(afterPeople)

  private def teamOfCounts(nominal: NominalRanges, skills: Int, people: Int)(
      draws: Draws
  ): (Team, Draws) =
    val (sets, afterSets) =
      (1 to people).foldLeft((Vector.empty[Int], draws))((drawn, _) =>
        val (before, beforeDraws) = drawn
        val (set, afterSet) =
          (0 until skills).foldLeft((0, beforeDraws))((held, skill) =>
            val (bits, bitsDraws) = held
            val (holding, afterHolding) =
              Repetition.drawnNumber(bitsDraws, nominal, "held")
            (if holding == 0 then bits | (1 << skill) else bits, afterHolding)
          )
        (before :+ set, afterSet)
      )
    (Team(skills, sets), afterSets)

  /** The function of the people, the full set and the count plus one, in the
    * spelling.
    */
  def function(terms: StandardLibraryTerms, spelling: Spelling): ProblemTerm =
    import terms.*
    λ(people =>
      λ(full =>
        λ(uncovered =>
          fixpoint(
            λ(self =>
              λ(rest =>
                λ(covered =>
                  rest(binaryEquality(covered)(full)(binaryZero)(uncovered))(
                    λ(skills =>
                      λ(others =>
                        spelling match
                          case Spelling.Direct =>
                            binaryMinimum(self(others)(covered))(
                              binaryIncrement(
                                self(others)(binaryBitwiseOr(covered)(skills))
                              )
                            )
                          case Spelling.Respelled =>
                            binaryMinimum(
                              compose(binaryIncrement)(self(others))(
                                binaryBitwiseOr(skills)(covered)
                              )
                            )(
                              self(others)(covered)
                            )
                      )
                    )
                  )
                )
              )
            )
          )(people)(binaryZero)
        )
      )
    )

  /** The family's name. */
  val name: String = "repeated_library_smallest_teams"

  /** The test that checks the computed reference against tabling(weak_head)'s
    * reading on small draws.
    */
  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.LibrarySmallestTeamsReferenceTest"

  /** The nominal ranges of the family's points: 60 people, LeetCode 1125's
    * bound, and 19 skills, each skill held with probability one in four, as in
    * the Prolog family, at R up to 6. LeetCode's bound of 16 skills is passed,
    * as the billboards' sum is, for the tenth of a second a contest test's
    * workload asks: at 18 skills and R = 4 the native solution took 68.6 ± 6.9
    * ms (`ContestWorkloadBenchmarks.smallestTeamsDirect`, 2026-11-01 06:58 UTC,
    * CPUs 0 to 5 at nice 19, load average 7.7 to 12.8). weak_head's reading is
    * exponential in the people (the Prolog family's probe of 2026-09-30, on the
    * budgeted program: weak_head read 8 skills and 12 people in 5866 ms), far
    * beyond `judgePointsFile`'s 20,000,000 steps. The native solution's time is
    * `ContestWorkloadBenchmarks.smallestTeamsDirect` and
    * `smallestTeamsRespelled` of `jmh-pipeline`.
    */
  val nominal: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(6),
    Vector(
      NominalParameter("skills", 19 to 19),
      NominalParameter("people", 60 to 60),
      NominalParameter("held", 0 to 3)
    )
  )

  /** The family in both spellings at the family's nominal ranges. */
  val variants: Vector[LibrarySmallestTeams] = Repetition.spellings.map(
    LibrarySmallestTeams(_, nominal, LibrarySmallestTeams.name)
  )

  /** The low rung's family name. */
  val smallName: String = "repeated_library_smallest_teams_small"

  /** The nominal ranges of the low rung: 8 skills and 12 people, the size at
    * which the Prolog family was read (weak_head read it in 5866 ms), with the
    * same holding probability and the same R as `nominal`, whose top rung stays
    * at the contest's workload.
    */
  val smallNominal: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(6),
    Vector(
      NominalParameter("skills", 8 to 8),
      NominalParameter("people", 12 to 12),
      NominalParameter("held", 0 to 3)
    )
  )

  /** The low rung in the spelling at its nominal ranges. */
  def small(spelling: Spelling): LibrarySmallestTeams =
    LibrarySmallestTeams(spelling, smallNominal, smallName)

  /** The low rung in both spellings at its nominal ranges. */
  val smallVariants: Vector[LibrarySmallestTeams] =
    Repetition.spellings.map(small)

/** The length of a longest common subsequence of two strings, the port of the
  * set-free family `problems/set_free_dynamic`, whose aim is a typical
  * programming contest problem written by its definition running at native
  * speed, scaled to a programming contest's size. The program is that file's
  * definition, the recursion on the two lists, built from the library's terms:
  *
  * {{{
  * lcs = fixpoint (\self. \xs. \ys. xs binary_zero (\x. \xt. ys binary_zero (\y. \yt.
  *         merge_binary_equality x y (merge_binary_increment (self xt yt))
  *                                   (binary_maximum (self xt ys) (self xs yt)))))
  * }}}
  *
  * the function let bound once and applied at R distinct sites, each a pair of
  * strings of one length n over an alphabet of k characters. Read as written,
  * the recursion recomputes the same pairs of suffixes exponentially often;
  * recognising the pair by value gives the dynamic programme over the (n + 1)^2
  * pairs. The respelled function writes the match through compose,
  * `compose merge_binary_increment (self xt) yt`.
  *
  * The encoding: every character and every length is a canonical binary natural
  * (`corpora/standard_library/binary`: binary_zero, binary_even h = 2h,
  * binary_odd h = 2h + 1, no binary_even over binary_zero), and so is each
  * site's answer. The Prolog family's characters were Booleans compared by
  * merge_symbols_equal and its lengths unary numerals; here a character is a
  * natural below k compared by merge_binary_equality, and the maximum is the
  * plain library term binary_maximum. The work and the encoding: (n + 1)^2
  * pairs, each an equality of characters of five bits and a maximum or an
  * increment of naturals of O(log n) bits; at the nominal n = 3000, 9 * 10^6
  * pairs per site. The input is 2n characters, about 10n constructors, and the
  * answer one natural of 12 bits, so encoding and decoding are O(n) against the
  * n^2 pairs. The hand-written native solution is
  * `ContestWorkloadSolutions.longestCommonSubsequence`.
  */
final class LibraryLongestCommonSubsequences(
    spelling: Spelling,
    val nominal: NominalRanges,
    val family: String
) extends StandardLibraryFamily[LibraryLongestCommonSubsequences.Drawn](
      spelling
    ):

  import LibraryLongestCommonSubsequences.Strings

  /** The point with its reference computed: the list, in site order, of the
    * lengths of the sites' longest common subsequences, canonical binary
    * naturals (`StandardLibraryNormalForms`).
    */
  override def point(
      group: ReductionGroup,
      seed: Long,
      repetitions: Int
  ): DrawnPoint =
    val drawn = drawnOf(group, seed, repetitions)
    val lengths = drawn.sites.map(strings =>
      StandardLibraryNormalForms.binary(
        ContestWorkloadSolutions.longestCommonSubsequence(
          IArray.from(strings.first),
          IArray.from(strings.second)
        )
      )
    )
    DrawnPoint(
      repeated(group, drawn),
      Reference.Computed(
        Vector(StandardLibraryNormalForms.list(lengths)),
        LibraryLongestCommonSubsequences.claim
      )
    )

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): LibraryLongestCommonSubsequences.Drawn =
    LibraryLongestCommonSubsequences.drawn(nominal, draws, repetitions)

  private def arguments(
      terms: StandardLibraryTerms,
      strings: Strings
  ): Vector[ProblemTerm] =
    import terms.*
    Vector(
      list(strings.first.map(character => binary(character))),
      list(strings.second.map(character => binary(character)))
    )

  protected def program(
      terms: StandardLibraryTerms,
      drawn: LibraryLongestCommonSubsequences.Drawn
  ): ProblemTerm =
    terms.sites(
      LibraryLongestCommonSubsequences.function(terms, spelling),
      drawn.sites.map(arguments(terms, _))
    )

  protected def singlePrograms(
      terms: StandardLibraryTerms,
      drawn: LibraryLongestCommonSubsequences.Drawn
  ): Vector[ProblemTerm] =
    val function = LibraryLongestCommonSubsequences.function(terms, spelling)
    drawn.sites.map(strings => applied(function, arguments(terms, strings)))

/** The draws, the function, the nominal ranges and the variants of
  * `LibraryLongestCommonSubsequences`.
  */
object LibraryLongestCommonSubsequences:

  /** The two strings of a site, each character a natural below k. */
  final case class Strings(first: Vector[Int], second: Vector[Int])

  /** The strings of the sites. */
  final case class Drawn(sites: Vector[Strings])

  /** R distinct pairs of strings: the length n drawn for each pair, then both
    * strings' characters from the range `character`.
    */
  def drawn(nominal: NominalRanges, draws: Draws, repetitions: Int): Drawn =
    Drawn(draws.distinct(repetitions)(pair(nominal))._1)

  private def pair(nominal: NominalRanges)(draws: Draws): (Strings, Draws) =
    val (length, afterLength) = Repetition.drawnNumber(draws, nominal, "length")
    val (first, afterFirst) = string(nominal, length, afterLength)
    val (second, afterSecond) = string(nominal, length, afterFirst)
    (Strings(first, second), afterSecond)

  private def string(
      nominal: NominalRanges,
      length: Int,
      draws: Draws
  ): (Vector[Int], Draws) =
    (1 to length).foldLeft((Vector.empty[Int], draws))((drawn, _) =>
      val (before, beforeDraws) = drawn
      val (character, afterCharacter) =
        Repetition.drawnNumber(beforeDraws, nominal, "character")
      (before :+ character, afterCharacter)
    )

  /** The recursion on the two lists in the spelling. */
  def function(terms: StandardLibraryTerms, spelling: Spelling): ProblemTerm =
    import terms.*
    fixpoint(
      λ(self =>
        λ(firstString =>
          λ(secondString =>
            firstString(binaryZero)(
              λ(character =>
                λ(firstRest =>
                  secondString(binaryZero)(
                    λ(other =>
                      λ(secondRest =>
                        val matched = spelling match
                          case Spelling.Direct =>
                            binaryIncrement(self(firstRest)(secondRest))
                          case Spelling.Respelled =>
                            compose(binaryIncrement)(self(firstRest))(
                              secondRest
                            )
                        binaryEquality(character)(other)(matched)(
                          binaryMaximum(self(firstRest)(secondString))(
                            self(firstString)(secondRest)
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  /** The family's name. */
  val name: String = "repeated_library_longest_common_subsequences"

  /** The test that checks the computed reference against tabling(weak_head)'s
    * reading on small draws.
    */
  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.LibraryLongestCommonSubsequencesReferenceTest"

  /** The nominal ranges of the family's points: strings of n = 3000 characters
    * over an alphabet of 26 (characters 0 to 25), at R up to 4; 9 * 10^6 pairs
    * of suffixes per site. weak_head's reading is exponential in n (the Prolog
    * family's probe of 2026-09-30: weak_head read n = 12 in 2085 ms and stopped
    * at 40), far beyond `judgePointsFile`'s 20,000,000 steps. The native
    * solution's time is `ContestWorkloadBenchmarks.longestCommonSubsequences`
    * of `jmh-pipeline`.
    */
  val nominal: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(4),
    Vector(
      NominalParameter("length", 3000 to 3000),
      NominalParameter("character", 0 to 25)
    )
  )

  /** The family in both spellings at the family's nominal ranges. */
  val variants: Vector[LibraryLongestCommonSubsequences] =
    Repetition.spellings.map(
      LibraryLongestCommonSubsequences(
        _,
        nominal,
        LibraryLongestCommonSubsequences.name
      )
    )

  /** The low rung's family name. */
  val smallName: String = "repeated_library_longest_common_subsequences_small"

  /** The nominal ranges of the low rung: strings of 150 characters, the size at
    * which the Prolog family (`problems/set_free_dynamic`) was read under
    * tabling(weak_head), over the same alphabet and at the same R as `nominal`,
    * whose top rung stays at the contest's workload.
    */
  val smallNominal: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(4),
    Vector(
      NominalParameter("length", 150 to 150),
      NominalParameter("character", 0 to 25)
    )
  )

  /** The low rung in the spelling at its nominal ranges. */
  def small(spelling: Spelling): LibraryLongestCommonSubsequences =
    LibraryLongestCommonSubsequences(spelling, smallNominal, smallName)

  /** The low rung in both spellings at its nominal ranges. */
  val smallVariants: Vector[LibraryLongestCommonSubsequences] =
    Repetition.spellings.map(small)

/** The tallest billboard (LeetCode 956), the port of
  * `problems/hidden_37_billboard`, scaled to LeetCode's bounds on the rods'
  * count and length (the sum may pass its 5000): rods of given lengths, each
  * welded into the left support, the right support or left out; the heights the
  * two supports can share. The program is that file's definition, built from
  * the library's terms:
  *
  * {{{
  * go = fixpoint (\self. \rods. \l. \r.
  *        rods (merge_binary_equality l r l 0)
  *             (\x. \rest. self rest l r + self rest (merge_binary_plus x l) r
  *                                       + self rest l (merge_binary_plus x r)))
  * }}}
  *
  * (the library file `billboard_go` of
  * `corpora/standard_library/round37_billboard`), and the function
  *
  * {{{
  * \rods. \target. go rods binary_zero binary_zero ∥ target
  * }}}
  *
  * let bound once and applied at the R distinct sites, each a list of rods and
  * a target height. The heights two disjoint sets of the rods reach are the
  * choice `go rods binary_zero binary_zero`; its parallel with the target reads
  * to the target when the target is among them, and to no normal form
  * otherwise. So a site has at most one normal form, and a point, the list of
  * its sites, at most one: the list of the targets when every site reaches its
  * own, and none otherwise (the contest's rule of at most N = 8 normal forms
  * per point). Read as written, the choices are 3^n; the state is the rest of
  * the rods and the two sums. The respelled function adds the rod on the other
  * side of the sums, `merge_binary_plus l x`, and lists the three members in
  * the opposite order; the parallel with the target is the same in both
  * spellings.
  *
  * The targets. At half the sites, drawn, the target is the largest height the
  * rods reach (0 when they reach no other): a member site, whose normal form is
  * the target. At the others it is a height from 1 to S / 2, S the sum of the
  * rods, that no two disjoint sets of the rods reach, drawn uniformly among
  * those: a trap site, with no normal form; a site whose rods reach every such
  * height is a member site. The target is written in the program, so an entry
  * that answered the target without a derivation would score every member site;
  * the trap sites make such an answer a false answer.
  *
  * The encoding: every length, every height and every target is a canonical
  * binary natural (`corpora/standard_library/binary`), as in the Prolog family.
  * The work and the encoding: the dynamic programme over the differences of the
  * sums is n * (2S + 1) unions of bit sets of S bits; at the nominal n = 20
  * rods of 1 to 1000, S about 10000, that is 4 * 10^5 unions of 10000 bits, 6.3
  * * 10^7 machine words, per site. The input is n naturals of at most ten bits
  * and a target of at most 14 bits; the answer is the target or nothing, read
  * back in O(log S), against the n * S^2 / 64 words of the programme. The
  * hand-written native solution is `ContestWorkloadSolutions.billboardReaches`:
  * the heights of `ContestWorkloadSolutions.billboardHeights`, then whether the
  * target is among them.
  */
final class LibraryBillboards(
    spelling: Spelling,
    val nominal: NominalRanges,
    val family: String
) extends StandardLibraryFamily[LibraryBillboards.Drawn](spelling):

  import LibraryBillboards.Site

  override def point(
      group: ReductionGroup,
      seed: Long,
      repetitions: Int
  ): DrawnPoint =
    drawnPoint(group, drawnOf(group, seed, repetitions))

  /** The point of the draws with its reference computed: the list, in site
    * order, of the sites' targets, canonical binary naturals
    * (`StandardLibraryNormalForms`), when every site's rods reach its target
    * (`ContestWorkloadSolutions.billboardReaches`), and no normal form
    * otherwise. `point` builds it from the draws of a seed; the claim's test
    * gives draws whose sites it chooses member or trap
    * (`LibraryBillboardsReferenceTest`).
    */
  def drawnPoint(
      group: ReductionGroup,
      drawn: LibraryBillboards.Drawn
  ): DrawnPoint =
    val reached = drawn.sites.forall(site =>
      ContestWorkloadSolutions.billboardReaches(
        IArray.from(site.rods),
        site.target
      )
    )
    val normalForms =
      if reached then
        Vector(
          StandardLibraryNormalForms.list(
            drawn.sites.map(site =>
              StandardLibraryNormalForms.binary(site.target)
            )
          )
        )
      else Vector.empty
    DrawnPoint(
      repeated(group, drawn),
      Reference.Computed(normalForms, LibraryBillboards.claim)
    )

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): LibraryBillboards.Drawn =
    LibraryBillboards.drawn(nominal, draws, repetitions)

  private def arguments(
      terms: StandardLibraryTerms,
      site: Site
  ): Vector[ProblemTerm] =
    Vector(
      terms.list(site.rods.map(rod => terms.binary(rod))),
      terms.binary(site.target)
    )

  protected def program(
      terms: StandardLibraryTerms,
      drawn: LibraryBillboards.Drawn
  ): ProblemTerm =
    terms.sites(
      LibraryBillboards.function(terms, spelling),
      drawn.sites.map(arguments(terms, _))
    )

  protected def singlePrograms(
      terms: StandardLibraryTerms,
      drawn: LibraryBillboards.Drawn
  ): Vector[ProblemTerm] =
    val function = LibraryBillboards.function(terms, spelling)
    drawn.sites.map(site => applied(function, arguments(terms, site)))

/** The draws, the function, the nominal ranges and the variants of
  * `LibraryBillboards`.
  */
object LibraryBillboards:

  /** The rods of a site and its target height. */
  final case class Site(rods: Vector[Int], target: Int)

  /** The sites. */
  final case class Drawn(sites: Vector[Site])

  /** Whether a site's target is a height its rods reach or one they do not. */
  enum Kind:
    case Member, Trap

  /** R distinct lists of rods, the count drawn for each, then each rod's
    * length; then, site by site, whether it is a member or a trap site, each
    * with probability one half, and its target (`site`).
    */
  def drawn(nominal: NominalRanges, draws: Draws, repetitions: Int): Drawn =
    val (rodLists, afterRods) = draws.distinct(repetitions)(rods(nominal))
    val (sites, _) =
      rodLists.foldLeft((Vector.empty[Site], afterRods))((drawn, siteRods) =>
        val (before, beforeDraws) = drawn
        val (kind, afterKind) = beforeDraws.chosen(Kind.values.toVector)
        val (drawnSite, afterSite) = site(siteRods, kind, afterKind)
        (before :+ drawnSite, afterSite)
      )
    Drawn(sites)

  /** One list of rods: the count drawn, then each rod's length. */
  def rods(nominal: NominalRanges)(draws: Draws): (Vector[Int], Draws) =
    val (count, afterCount) = Repetition.drawnNumber(draws, nominal, "rods")
    (1 to count).foldLeft((Vector.empty[Int], afterCount))((drawn, _) =>
      val (before, beforeDraws) = drawn
      val (rod, afterRod) =
        Repetition.drawnNumber(beforeDraws, nominal, "length")
      (before :+ rod, afterRod)
    )

  /** The site of the rods of the kind: for a member, the largest height the
    * rods reach (0 when they reach no other), with nothing drawn; for a trap, a
    * height from 1 to S / 2, S the sum of the rods, that they do not reach,
    * drawn uniformly among those, or the member's target with nothing drawn
    * when they reach every such height.
    */
  def site(rods: Vector[Int], kind: Kind, draws: Draws): (Site, Draws) =
    val heights = ContestWorkloadSolutions.billboardHeights(IArray.from(rods))
    val reached = heights.toSet
    val unreached = (1 to rods.sum / 2).filterNot(reached.contains).toVector
    kind match
      case Kind.Trap if unreached.nonEmpty =>
        val (target, afterTarget) = draws.chosen(unreached)
        (Site(rods, target), afterTarget)
      case _ => (Site(rods, heights.max), draws)

  /** The function of the rods and the target in the spelling. */
  def function(terms: StandardLibraryTerms, spelling: Spelling): ProblemTerm =
    import terms.*
    val go = fixpoint(
      λ(self =>
        λ(rods =>
          λ(left =>
            λ(right =>
              rods(binaryEquality(left)(right)(left)(top))(
                λ(rod =>
                  λ(rest =>
                    spelling match
                      case Spelling.Direct =>
                        choice(
                          self(rest)(left)(right),
                          self(rest)(binaryPlus(rod)(left))(right),
                          self(rest)(left)(binaryPlus(rod)(right))
                        )
                      case Spelling.Respelled =>
                        choice(
                          self(rest)(left)(binaryPlus(right)(rod)),
                          self(rest)(binaryPlus(left)(rod))(right),
                          self(rest)(left)(right)
                        )
                  )
                )
              )
            )
          )
        )
      )
    )
    λ(rods => λ(target => go(rods)(binaryZero)(binaryZero) ∥ target))

  /** The family's name. */
  val name: String = "repeated_library_billboards"

  /** The test that checks the computed reference against tabling(weak_head)'s
    * reading on small draws.
    */
  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.LibraryBillboardsReferenceTest"

  /** The nominal ranges of the family's points: 20 rods of lengths 1 to 1000,
    * LeetCode 956's bounds on the count and the length (its sum's bound of 5000
    * is passed: at lengths 1 to 500 the native solution took 31 ms on a quiet
    * machine, below the tenth of a second a contest test's workload asks), at R = 1.
    * weak_head's reading is exponential in the rods (a probe of 2026-09-30 read
    * nine rods of 1 to 20 under tabling(weak_head) in 14782 ms and was stopped
    * at 60 s on twelve), far beyond `judgePointsFile`'s 20,000,000 steps. The
    * native solution's time is `ContestWorkloadBenchmarks.billboards` of
    * `jmh-pipeline`.
    */
  val nominal: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(1),
    Vector(
      NominalParameter("rods", 20 to 20),
      NominalParameter("length", 1 to 1000)
    )
  )

  /** The family in both spellings at the family's nominal ranges. */
  val variants: Vector[LibraryBillboards] = Repetition.spellings.map(
    LibraryBillboards(_, nominal, LibraryBillboards.name)
  )

  /** The low rung's family name. */
  val smallName: String = "repeated_library_billboards_small"

  /** The nominal ranges of the low rung: 12 rods of lengths 1 to 20, the size
    * at which the Prolog corpus's billboard was read (nine rods of 1 to 20 read
    * under tabling(weak_head) in 14782 ms), at the same R as `nominal`, whose
    * top rung stays at the contest's workload.
    */
  val smallNominal: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(1),
    Vector(
      NominalParameter("rods", 12 to 12),
      NominalParameter("length", 1 to 20)
    )
  )

  /** The low rung in the spelling at its nominal ranges. */
  def small(spelling: Spelling): LibraryBillboards =
    LibraryBillboards(spelling, smallNominal, smallName)

  /** The low rung in both spellings at its nominal ranges. */
  val smallVariants: Vector[LibraryBillboards] = Repetition.spellings.map(small)
