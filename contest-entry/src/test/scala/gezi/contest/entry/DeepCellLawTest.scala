package gezi.contest.entry

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.DeBruijnTerm
import gezi.generatedinputs.GeneratedProperties

/** The law of the two projections on deep cells: for a cell
  * `λs.λk. k S P` whose S holds the state variable at the bottom of a
  * generated nest of tens of thousands of lambdas and applications, and
  * whose P is closed, the state after the cell is S with the state planted
  * and the Output is P. Its purpose is to catch a projection that overflows
  * the JVM stack on a cell as deep as a large workload's program (the
  * defect of 2026-11-02: `Cells.substituted` recursed once per level), or
  * that plants the state at the wrong binder depth.
  */
class DeepCellLawTest extends GeneratedProperties:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of DeepCellLawTest, "a deep cell's next state plants the state at the bottom, and its Output is its closed Output", takes 6.849 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(15, "s")

  /** The leaf under `levels` levels, every `period`-th one a lambda and the
    * others an application to the identity.
    */
  private def nested(levels: Int, period: Int, leaf: DeBruijnTerm): DeBruijnTerm =
    (0 until levels).foldLeft(leaf)((inner, level) =>
      if level % period == 0 then DeBruijnTerm.Lambda(inner)
      else DeBruijnTerm.Apply(inner, DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0)))
    )

  property("a deep cell's next state plants the state at the bottom, and its Output is its closed Output") {
    for
      levels <- Gen.int(Range.linear(20000, 60000)).forAll
      period <- Gen.int(Range.linear(1, 5)).forAll
    yield
      val lambdas = (levels + period - 1) / period
      val closedOutput = nested(levels, period, DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0)))
      val cell = DeBruijnTerm.Lambda(
        DeBruijnTerm.Lambda(
          DeBruijnTerm.Apply(
            DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), nested(levels, period, DeBruijnTerm.Variable(lambdas + 1))),
            closedOutput
          )
        )
      )
      val state = Cells.initialState
      Result.all(
        List(
          Result.assert(Cells.nextState(cell, state) == nested(levels, period, state)),
          Result.assert(Cells.output(cell, state) == closedOutput)
        )
      )
  }
