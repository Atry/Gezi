package gezi.hotspot

import gezi.ir.NativeSpecializer

/** The place of the strategy: a function of costs and what the cache service
  * holds to a decision among the parts a tiered executor holds. Thresholds and
  * the detection of hot units are the policy's own; it reads costs only, never
  * a type.
  *
  * FIXME (https://github.com/Atry/private-overlay/issues/1788): no tiered
  * executor runs a policy: an entry's executor is the JIT alone
  * (`gezi.contest.entry.Defaults.executor`), and the baseline's
  * `WholeBudgetInterpretation` is the one policy. A policy is to become an
  * option of the entry's data once a tiered executor exists.
  */
trait TieringPolicy[C <: NativeSpecializer & Singleton]:

  /** The decision for the program being run, after what was spent on it so far.
    * The program is the unit the tiered executor runs, which a decision may
    * name (`Decision.Compile`) and whose artifact the policy may look up in the
    * cache service under the compiler's key; the policy reads it as a key only,
    * never its term (costs only).
    */
  def decided(
      program: CompilationUnit.Program[C],
      spent: Spent,
      cache: Cache
  ): Decision[C]

/** What a tiering policy decides. A decision chooses among the parts the tiered
  * executor holds and never hands out an executor or a compiler, whose
  * suspension type would not be the tiered executor's.
  */
sealed trait Decision[C <: NativeSpecializer & Singleton]

object Decision:

  /** Run the interpreting executor within the budget. */
  final case class Interpret[C <: NativeSpecializer & Singleton](budget: Budget)
      extends Decision[C]

  /** Run the compiled executor within the budget. */
  final case class RunCompiled[C <: NativeSpecializer & Singleton](
      budget: Budget
  ) extends Decision[C]

  /** Compile the units. */
  final case class Compile[C <: NativeSpecializer & Singleton](
      units: Vector[CompilationUnit[C]]
  ) extends Decision[C]

  /** Answer that the point is not known now, so that the points after it in its
    * family are read.
    */
  final case class GiveUp[C <: NativeSpecializer & Singleton]()
      extends Decision[C]
