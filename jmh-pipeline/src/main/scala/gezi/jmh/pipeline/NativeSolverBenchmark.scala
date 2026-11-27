package gezi.jmh.pipeline

import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"): the time unit of JMH's annotations, an immutable enum of the concurrency package
import gezi.contest.corpora.reductions.NativeProblem
import gezi.contest.corpora.reductions.NativeValue
import gezi.contest.corpora.reductions.NativelySolved
import gezi.contest.corpora.reductions.ReductionGroup
import gezi.contest.corpora.reductions.RepeatedVariants
import gezi.programfamilies.FixedPointLines
import gezi.weakhead.Expansions
import org.openjdk.jmh.annotations.Benchmark
import org.openjdk.jmh.annotations.BenchmarkMode
import org.openjdk.jmh.annotations.Fork
import org.openjdk.jmh.annotations.Level
import org.openjdk.jmh.annotations.Measurement
import org.openjdk.jmh.annotations.Mode
import org.openjdk.jmh.annotations.OutputTimeUnit
import org.openjdk.jmh.annotations.Param
import org.openjdk.jmh.annotations.Scope
import org.openjdk.jmh.annotations.Setup
import org.openjdk.jmh.annotations.State
import org.openjdk.jmh.annotations.Warmup
import scala.compiletime.uninitialized

/** The input of a native solver's benchmark: a natively solved repeated family,
  * by its stem, and the draws of its point at the public seed 20261031 and its
  * nominal top rung (`NativeProblem.topRung`), drawn before the trial as the
  * generator draws them.
  */
@State(Scope.Benchmark)
class NativeSolverInput:

  /** The family's stem, which JMH assigns: every natively solved variant of
    * `RepeatedVariants.all`.
    */
  @SuppressWarnings(
    Array("org.wartremover.warts.Var")
  ) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  @Param(
    Array(
      "repeated_reduction_meanings",
      "repeated_reduction_interpreter",
      "repeated_set_free_premises",
      "repeated_set_free_scope",
      "repeated_set_free_list_laws",
      "repeated_reduction_problems_fibonacci",
      "repeated_reduction_problems_products",
      "repeated_reduction_problems_grids",
      "repeated_reduction_problems_sums",
      "repeated_reduction_mixin_binary",
      "repeated_set_free_arithmetic",
      "repeated_identical_subterms/direct",
      "repeated_identical_subterms/respelled",
      "repeated_closures/direct",
      "repeated_closures/respelled",
      "repeated_library_compositions/direct",
      "repeated_library_compositions/respelled",
      "repeated_general_compositions/direct",
      "repeated_general_compositions/respelled",
      "repeated_nested_compositions/direct",
      "repeated_nested_compositions/respelled",
      "repeated_library_doubling_parities/direct",
      "repeated_library_doubling_parities/respelled",
      "repeated_library_binary_parities/direct",
      "repeated_library_binary_parities/respelled",
      "repeated_library_unshared_doublings/direct",
      "repeated_library_unshared_doublings/respelled",
      "repeated_library_unshared_binary/direct",
      "repeated_library_unshared_binary/respelled",
      "repeated_library_unshared_doublings_large/direct",
      "repeated_library_unshared_doublings_large/respelled",
      "repeated_library_unshared_binary_large/direct",
      "repeated_library_unshared_binary_large/respelled",
      "repeated_library_unshared_word_powers/direct",
      "repeated_library_unshared_word_powers/respelled",
      "repeated_library_binary_domain_traps/direct",
      "repeated_library_binary_domain_traps/respelled",
      "repeated_reduction_mixin_builtin_binary/direct",
      "repeated_reduction_mixin_builtin_binary/respelled",
      "repeated_reduction_mixin_builtin_natural/direct",
      "repeated_reduction_mixin_builtin_natural/respelled",
      "repeated_reduction_mixin_builtin_boolean_depth_8/direct",
      "repeated_reduction_mixin_builtin_boolean_depth_8/respelled",
      "repeated_reduction_mixin_builtin_boolean_depth_12/direct",
      "repeated_reduction_mixin_builtin_boolean_depth_12/respelled",
      "repeated_reduction_mixin_builtin_boolean_depth_16/direct",
      "repeated_reduction_mixin_builtin_boolean_depth_16/respelled",
      "repeated_cses_dice_combinations_sum_4/direct",
      "repeated_cses_dice_combinations_sum_4/respelled",
      "repeated_cses_dice_combinations_sum_6/direct",
      "repeated_cses_dice_combinations_sum_6/respelled",
      "repeated_cses_dice_combinations_sum_1000000/direct",
      "repeated_cses_dice_combinations_sum_1000000/respelled",
      "repeated_cses_minimizing_coins_target_6/direct",
      "repeated_cses_minimizing_coins_target_6/respelled",
      "repeated_cses_minimizing_coins_target_8/direct",
      "repeated_cses_minimizing_coins_target_8/respelled",
      "repeated_cses_minimizing_coins_target_1000000/direct",
      "repeated_cses_minimizing_coins_target_1000000/respelled",
      "repeated_cses_message_route_computers_5/direct",
      "repeated_cses_message_route_computers_5/respelled",
      "repeated_cses_message_route_computers_8/direct",
      "repeated_cses_message_route_computers_8/respelled",
      "repeated_cses_message_route_computers_100000/direct",
      "repeated_cses_message_route_computers_100000/respelled",
      "repeated_cses_counting_rooms_squares_9/direct",
      "repeated_cses_counting_rooms_squares_9/respelled",
      "repeated_cses_counting_rooms_squares_16/direct",
      "repeated_cses_counting_rooms_squares_16/respelled",
      "repeated_cses_counting_rooms_squares_1000000/direct",
      "repeated_cses_counting_rooms_squares_1000000/respelled",
      "repeated_cses_exponentiation_exponent_4/direct",
      "repeated_cses_exponentiation_exponent_4/respelled",
      "repeated_cses_exponentiation_exponent_8/direct",
      "repeated_cses_exponentiation_exponent_8/respelled",
      "repeated_cses_exponentiation_exponent_1000000000/direct",
      "repeated_cses_exponentiation_exponent_1000000000/respelled"
    )
  ) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  var stem: String =
    uninitialized // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")

  /** The public seed of the readings. */
  val seed: Long = 20261031L

  /** The reduction group read from Gezi's directory. */
  lazy val group: ReductionGroup = ReductionGroup(
    FixedPointLines.buildRoot,
    Expansions.none,
    gezi.contest.entry.Defaults.caches()
  )

  /** The family's point at the seed and its top rung. */
  lazy val problem: NativeProblem[?] =
    RepeatedVariants.all
      .collectFirst {
        case family: NativelySolved[drawn] if family.stem == stem =>
          NativeProblem.topRung(family, group, seed)
      }
      .getOrElse(
        throw IllegalArgumentException(
          s"no natively solved family has the stem $stem"
        )
      )

  /** The draws made before the trial, so that no iteration draws. */
  @Setup(Level.Trial)
  def built(): Unit =
    assert(
      problem.solved.size == problem.family.nominal.repetitions.end,
      s"$stem answers another count of sites"
    )

/** The native solver of each natively solved repeated family
  * (`gezi.contest.corpora.reductions.NativelySolved`) on one point at its
  * nominal top rung: the family's yardstick, the reference time its readings
  * are scored against. The benchmark times the solver alone, from the drawn
  * data to each site's answer as plain data; neither the draws nor the answers'
  * normal forms are timed. It returns the answers, so that JMH consumes them.
  * The mode is the average time of a call, in microseconds; the fork has the
  * serial collector, so that no collection runs on threads beside the
  * benchmark's. The warm-up and the measurement are five iterations of one
  * second each, set by the annotations below from the readings of the warm-up
  * iterations.
  */
@BenchmarkMode(
  Array(Mode.AverageTime)
) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Fork(
  value = 1,
  jvmArgsAppend = Array("-Xmx256m", "-XX:+UseSerialGC")
) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
class NativeSolverBenchmark:

  /** The family's native solver on the point's draws. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MICROSECONDS)
  def solved(input: NativeSolverInput): Vector[NativeValue] =
    input.problem.solved
