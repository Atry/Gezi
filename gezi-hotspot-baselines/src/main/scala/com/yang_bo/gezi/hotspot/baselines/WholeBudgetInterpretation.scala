package com.yang_bo.gezi.hotspot.baselines

import com.yang_bo.gezi.hotspot.Budget
import com.yang_bo.gezi.hotspot.Cache
import com.yang_bo.gezi.hotspot.CompilationUnit
import com.yang_bo.gezi.hotspot.Decision
import com.yang_bo.gezi.hotspot.Spent
import com.yang_bo.gezi.hotspot.TieringPolicy
import com.yang_bo.gezi.ir.NativeSpecializer

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
