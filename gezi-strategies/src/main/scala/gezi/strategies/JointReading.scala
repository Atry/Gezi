package gezi.strategies

/** How an extraction reads a thunk's jointly read fillings
  * (`ThunkCandidates.jointFillings`, `CodeCandidates.candidates`), two
  * choices of the e-graph line that decide what a reading enumerates and
  * which of two paths reads it.
  * Both are a search's choices: whatever they are, the extraction spells
  * each class by a term of it.
  *
  * @param enumerationBound
  *   the largest product of the entries of the jointly read fillings that a
  *   reading enumerates:
  *   above it each such filling is settled to its first entry
  *   (`CodeCandidates.enumeratedOrSettled`), so that the reading stays linear in
  *   the code's size and may miss a cheaper combination. It also bounds the
  *   listings by contract value of a thunk whose choices are folded by parts
  *   (`CodeCandidates.contractListingsWithinBound`), each of which enumerates
  *   up to it in turn, so such a thunk's reading evaluates its code at most
  *   the square of the bound times.
  * @param wholeFoldBound
  *   the largest such product, capped by the enumeration bound
  *   (`wholeFoldLimit`), at which a thunk the modules could fold by
  *   parts (`CodeCandidates.foldsByParts`) is read whole
  *   (`ThunkCandidates.candidates`) instead of by the dynamic program
  *   (`CodeCandidates.candidates`). Both give each reading's least cost over
  *   the combinations they enumerate (the laws `candidatesByParts` and
  *   `wholeFoldBoundKeepsLeastCosts` of `CostMonotonicityLaws`); a tie may
  *   resolve to a different entry across the bound. A thunk is read whole
  *   for this reason only at a product within the enumeration bound as well
  *   (`wholeFoldLimit`): read whole above it, the thunk would settle fillings
  *   the dynamic program does not at more entries, and what is settled would
  *   not be monotone in the numbers of entries
  *   (`gezi.extraction.CostModel.settledChildren`).
  */
final case class JointReading(enumerationBound: Long, wholeFoldBound: Long):
  require(enumerationBound >= 1, s"the enumeration bound $enumerationBound is below 1")
  require(wholeFoldBound >= 0, s"the whole fold bound $wholeFoldBound is negative")

  /** The largest product at which a thunk the modules could fold by parts
    * is read whole: the whole fold bound, within the enumeration bound.
    */
  def wholeFoldLimit: Long = wholeFoldBound.min(enumerationBound)

object JointReading:

  /** The bounds as measured.
    *
    * `enumerationBound` 256: every combination is read, so the reading costs
    * the product times the code's size. Measured 2026-11-17: the products on
    * the hot points of a published points file are 2 to 64, and 128 on `contest-entries-solo`'s
    * nested_calls_10000_hot/direct (the FIXME on `CodeCandidates.candidates`);
    * on its repeated_library_hotspots_calls_1000 direct point (seed
    * 20261116) one thunk, the whole program of 2,418 fillings, had a product
    * over its jointly read fillings (`ThunkCandidates.jointProduct`) of about
    * 2^800, and its reading ran 121 s until a stop and, unstopped, out of a
    * 4.3 GB heap after 1,040 s; with the bound, no reading of that point's
    * thunks takes more than 2.1 s. The bound is twice the largest product of
    * a hot point.
    *
    * `wholeFoldBound` 1: on those 18 hot points, 2026-11-16, two thirds
    * of the thunk readings have product 1, where the dynamic program took 3.5
    * times the whole fold's time (16.0 s against 4.6 s summed over the 33
    * rows both finish) and 4 times its allocation (28.0 GB against 7.0 GB);
    * at the products above 1 the dynamic program allocates 1.57 times the
    * whole fold's (the FIXME on `CodeCandidates.candidates`), so a larger
    * bound may be cheaper, unmeasured.
    */
  val measured: JointReading = JointReading(256, 1)
