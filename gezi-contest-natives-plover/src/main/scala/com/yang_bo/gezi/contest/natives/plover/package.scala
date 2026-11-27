package com.yang_bo.gezi.contest.natives

/** The natives of the knowledge modules
  * `corpora/compiler/plover_ordered_compositions`,
  * `plover_unordered_combinations`, `plover_edit_distance`,
  * `plover_longest_common_subsequence`, `plover_smallest_team`,
  * `plover_billboard`, `plover_digit_steps`, `plover_modular_power`,
  * `plover_trailing_zeros`, `plover_divisor_sums`, `plover_rectangle_cutting`,
  * `plover_money_sums`, `plover_modular_tower`, `plover_book_shop`,
  * `plover_minimizing_coins` and `plover_natural_arithmetic`.
  * [[PloverNatives]], registered with `java.util.ServiceLoader` as a
  * `com.yang_bo.gezi.jit.NativesProvider`, binds `plover_ordered_compositions` to
  * [[OrderedCompositions.count]], the number of ordered sequences of items that
  * sum to a target, modulo a modulus, by a table over the distance still to
  * cover; `plover_unordered_combinations` to [[UnorderedCombinations.count]],
  * the number of ways that use each position of the list some number of times,
  * by the knapsack over the items in turn; `plover_edit_distance` to
  * [[EditDistance.distance]], the edit distance of two lists, by a table over
  * their suffixes; `plover_longest_common_subsequence` to
  * [[LongestCommonSubsequence.length]], the length of a longest common
  * subsequence of two lists, by a table over their suffixes;
  * `plover_smallest_team` to [[SmallestTeam.size]], the size of a smallest
  * sufficient team, by a table over the sets of required skills;
  * `plover_billboard` to [[Billboard.term]], the target when two disjoint
  * subsets of the rods both sum to it, and otherwise the choice of the heights
  * they can share in parallel with the target; `plover_digit_steps` to
  * [[DigitSteps.count]], the fewest steps that take a natural to zero by
  * subtracting one of its nonzero decimal digits; `plover_modular_power` to
  * [[ModularPower.power]], a power modulo a positive modulus;
  * `plover_trailing_zeros` to [[TrailingZeros.count]], the decimal zeros that
  * end a factorial, by Legendre's formula; `plover_divisor_sums` to
  * [[DivisorSums.total]], the sum of the divisor sums up to a limit modulo a
  * positive modulus, by runs of equal quotients; `plover_rectangle_cutting` to
  * [[RectangleCutting.cuts]], the fewest cuts that leave a rectangle in
  * squares, by a table over the rectangles up to it; `plover_money_sums` to
  * [[MoneySums.total]], the sum of the distinct sums of the nonempty sets of
  * coins, by a bit set of the reachable sums; `plover_modular_tower` to
  * [[ModularTower.power]], a power of a power modulo a positive modulus, by
  * Euler's theorem on the exponent; `plover_book_shop` to [[BookShop.most]],
  * the most pages within a budget, by the 0-1 knapsack, its books at a
  * `com.yang_bo.gezi.jit.NativePlace.NaturalRecordList` place; `plover_minimizing_coins` to
  * [[MinimizingCoins.fewest]], the fewest coins that sum to a target, an
  * option, its result at `com.yang_bo.gezi.jit.NativePlace.DeclaredFamilyValue`; and
  * `plover_natural_modulo` and `plover_natural_difference` to
  * [[NaturalArithmetic.modulo]] and [[NaturalArithmetic.difference]], what the
  * recursions of the remainder and of the subtraction with no borrow give on
  * canonical naturals, a zero modulus and a larger subtrahend included.
  *
  * The first six and `plover_money_sums` take their lists at
  * `com.yang_bo.gezi.jit.NativePlace.NaturalList` places, so only a narrow block with lists
  * calls them. The first two declare positive items and a positive modulus, the
  * other five canonical naturals, and a narrow block compiles the call only
  * when the filters at the operands' roots name them. No implementation checks
  * an operand.
  */
package object plover
