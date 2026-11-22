package gezi.traceplayer

/** What the player shows at a position of a sequence of terms
  * (a pure function): the step, the progress within it, and the term the step
  * shows. Step k shows term k; the progress is how far the position has gone
  * from term k towards term k + 1, the time a transition between the two
  * would read.
  */
final case class Frame[+Term](step: Int, progress: Double, term: Term)

object Frame:

  /** The frame at the position, a number of steps from the first term: step
    * `floor(position)`, progress the fraction past it. A position before the
    * first term is the first term with no progress, one at or past the last
    * term the last term with no progress, so that playing past the end
    * stays on the last term. The steps and the term are computed from the
    * terms and the position alone; nothing is kept.
    *
    * Throws `IllegalArgumentException` for no terms and for a position that
    * is not a number.
    */
  def frame[Term](terms: Vector[Term], position: Double): Frame[Term] =
    val shown = indexed(terms.size, position)
    Frame(shown.step, shown.progress, terms(shown.step))

  /** `frame` on `count` terms known by their indices, the term of the frame
    * its index: for a page whose terms are made when a frame shows them
    * (`Played`). Throws `IllegalArgumentException` for no terms and for a
    * position that is not a number.
    */
  def indexed(count: Int, position: Double): Frame[Int] =
    require(count > 0, "a sequence of terms to play has at least one term")
    require(!position.isNaN, "the position is a number")
    val last = count - 1
    if position <= 0 then Frame(0, 0, 0)
    else if position >= last then Frame(last, 0, last)
    else
      val step = position.floor.toInt
      Frame(step, position - step, step)
