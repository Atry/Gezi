package gezi.hotspot.baselines

import gezi.hotspot.Budget
import gezi.hotspot.Cache
import gezi.hotspot.CompilationUnit
import gezi.hotspot.Decision
import gezi.hotspot.Spent
import gezi.hotspot.TieringPolicy
import gezi.ir.NativeSpecializer

/** The tiering policy of the baseline: always interpret, with the whole budget,
  * whatever was spent, so that a tiered executor under it reads as its
  * interpreting executor reads alone.
  *
  * @param budget
  *   the whole budget
  */
final case class WholeBudgetInterpretation[C <: NativeSpecializer & Singleton](
    budget: Budget
) extends TieringPolicy[C]:
  def decided(
      program: CompilationUnit.Program[C],
      spent: Spent,
      cache: Cache
  ): Decision[C] = Decision.Interpret(budget)
