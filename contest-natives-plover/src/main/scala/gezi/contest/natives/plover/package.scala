package gezi.contest.natives

/** The natives of the knowledge modules `corpora/compiler/plover_ordered_compositions`,
  * `plover_unordered_combinations`, `plover_digit_steps` and
  * `plover_modular_power`. [[PloverNatives]],
  * registered with `java.util.ServiceLoader` as a `gezi.jit.NativesProvider`,
  * binds `plover_ordered_compositions` to [[OrderedCompositions.count]], the
  * number of ordered sequences of items that sum to a target, modulo a modulus,
  * by a table over the distance still to cover;
  * `plover_unordered_combinations` to [[UnorderedCombinations.count]], the
  * number of ways that use each position of the list some number of times, by
  * the knapsack over the items in turn; `plover_digit_steps` to
  * [[DigitSteps.count]], the fewest steps that take a natural to zero by
  * subtracting one of its nonzero decimal digits; and `plover_modular_power` to
  * [[ModularPower.power]], a power modulo a positive modulus.
  *
  * The first two take their items at a `gezi.jit.NativePlace.NaturalList` place,
  * so only a narrow block with lists calls them. Their places declare positive
  * items and a positive modulus, and a narrow block compiles the call only when
  * the filters at the operands' roots name them. No implementation checks an
  * operand.
  */
package object plover
