package gezi.weakhead

/** A pseudo-random generator as a value, SplitMix64 (a copy of
  * `gezi.standardlibrary.SplitMix`, a test class of another project).
  */
private final case class SplitMix(state: Long):

  /** The next 64 random bits. */
  def bits: (Long, SplitMix) =
    val next = state + 0x9e3779b97f4a7c15L
    val mixed = (next ^ (next >>> 30)) * 0xbf58476d1ce4e5b9L
    val further = (mixed ^ (mixed >>> 27)) * 0x94d049bb133111ebL
    (further ^ (further >>> 31), SplitMix(next))

  /** An integer between the bounds, both included. */
  def between(low: Int, high: Int): (Int, SplitMix) =
    val (drawn, after) = bits
    (low + java.lang.Math.floorMod(drawn, (high - low + 1).toLong).toInt, after)

/** A program of the trampoline's constructions, generated: a value, a deferred
  * program, or a program whose value chooses the next by an affine map of it.
  */
private enum Program:
  case Value(value: Long)
  case Deferred(program: Program)
  case Bound(first: Program, multiplier: Long, addend: Long, next: Program)

/** The law of `Trampoline`: a program's trampolined result is its direct
  * evaluation, on generated programs nested to the left and to the right, and a
  * chain of 200,000 sequenced steps nested either way runs without growing the
  * JVM stack. Its purpose: to catch a wrong reassociation in
  * `Trampoline.flatMap` or in the trampoline's run, the two places it departs
  * from `scala.util.control.TailCalls`.
  */
class TrampolineLawTest extends gezi.generatedinputs.FailFastSuite:

  private def generated(random: SplitMix, depth: Int): (Program, SplitMix) =
    val (choice, afterChoice) = random.between(0, if depth == 0 then 0 else 2)
    choice match
      case 0 =>
        val (value, after) = afterChoice.between(-1000, 1000)
        (Program.Value(value.toLong), after)
      case 1 =>
        val (program, after) = generated(afterChoice, depth - 1)
        (Program.Deferred(program), after)
      case _ =>
        val (first, afterFirst) = generated(afterChoice, depth - 1)
        val (multiplier, afterMultiplier) = afterFirst.between(-3, 3)
        val (addend, afterAddend) = afterMultiplier.between(-5, 5)
        val (next, after) = generated(afterAddend, depth - 1)
        (Program.Bound(first, multiplier.toLong, addend.toLong, next), after)

  private def direct(program: Program): Long = program match
    case Program.Value(value)                           => value
    case Program.Deferred(inner)                        => direct(inner)
    case Program.Bound(first, multiplier, addend, next) =>
      direct(next) + multiplier * direct(first) + addend

  private def trampolined(program: Program): Trampoline[Long] = program match
    case Program.Value(value)    => Trampoline.done(value)
    case Program.Deferred(inner) => Trampoline.tailcall(trampolined(inner))
    case Program.Bound(first, multiplier, addend, next) =>
      trampolined(first).flatMap(value =>
        trampolined(next).map(_ + multiplier * value + addend)
      )

  test("a generated program's trampolined result is its direct evaluation") {
    val (_, failures) =
      (1 to 500).foldLeft((SplitMix(20261103L), Vector.empty[Program])) {
        case ((random, failed), _) =>
          val (depth, afterDepth) = random.between(0, 9)
          val (program, after) = generated(afterDepth, depth)
          (
            after,
            if trampolined(program).result == direct(program) then failed
            else failed :+ program
          )
      }
    assertEquals(failures, Vector.empty)
  }

  test(
    "200,000 sequenced steps nested to the left or to the right run without growing the JVM stack"
  ) {
    val steps = 200000
    val leftNested =
      (1 to steps).foldLeft(Trampoline.done(0L))((computation, _) =>
        computation.flatMap(value => Trampoline.done(value + 1))
      )
    def rightNested(remaining: Int, value: Long): Trampoline[Long] =
      if remaining == 0 then Trampoline.done(value)
      else
        Trampoline
          .tailcall(rightNested(remaining - 1, value + 1))
          .flatMap(Trampoline.done)
    assertEquals(leftNested.result, rightNested(steps, 0L).result)
  }

  stoppableTest(
    "run under a signal that never stops, a generated program's result is the plain run's"
  ) { stopped =>
    val (_, failures) =
      (1 to 500).foldLeft((SplitMix(20261107L), Vector.empty[Program])) {
        case ((random, failed), _) =>
          val (depth, afterDepth) = random.between(0, 9)
          val (program, after) = generated(afterDepth, depth)
          val unless = trampolined(program).resultUnless(
            gezi.saturation.StopSignal.completedWith(stopped),
            Long.MinValue
          )
          (
            after,
            if unless == trampolined(program).result then failed
            else failed :+ program
          )
      }
    assertEquals(failures, Vector.empty)
  }

  test(
    "a stop asked for from the start ends a long chain at a read of the signal and never a chain shorter than the reads' interval"
  ) {
    val stopped = new gezi.saturation.StopSignal:
      def stopRequested: Boolean = true
    def chain(steps: Int): Trampoline[Long] =
      (1 to steps).foldLeft(Trampoline.done(0L))((computation, _) =>
        computation.flatMap(value => Trampoline.done(value + 1))
      )
    assertEquals(chain(200000).resultUnless(stopped, -1L), -1L)
    val short = Trampoline.stopCheckBounces / 4
    assertEquals(chain(short).resultUnless(stopped, -1L), short.toLong)
  }
