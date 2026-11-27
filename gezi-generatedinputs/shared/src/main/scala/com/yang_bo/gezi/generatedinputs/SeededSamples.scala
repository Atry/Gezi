package com.yang_bo.gezi.generatedinputs

import hedgehog.Gen
import hedgehog.Size
import hedgehog.core.Seed
import scala.annotation.tailrec

/** Samples drawn from a generator with a fixed seed: the same seed gives the
  * same samples on every run and every machine.
  *
  * WHY THEY ARE REPRODUCIBLE: a Hedgehog generator is a pure function of a size
  * and a seed (`GenT.run`), and the seed is a value, `hedgehog.core.Seed`, over
  * Hedgehog's own Mersenne Twister (`hedgehog.random.MersenneTwister64`), which
  * reads no clock, no thread and no global state. Each draw returns the seed
  * after it, and the next sample is drawn from that seed. The samples therefore
  * depend on the seed, the count, the generator's code and Hedgehog's code
  * alone; the builds pin Hedgehog's version (0.15.1), since another version may
  * draw other values from the same seed.
  */
object SeededSamples:

  /** The number of discarded draws (a generator's `filter` rejecting its value)
    * after which the drawing gives up, per sample asked for.
    */
  private val discardsPerSample = 100

  /** The size of the sample at the position among `count` samples: from 1 for
    * the first to Hedgehog's largest, 100, for the last, growing linearly, so
    * that a snapshot shows small inputs first, as a property's run tries them.
    */
  def size(position: Int, count: Int): Size =
    require(
      0 <= position && position < count,
      s"position $position of $count samples"
    )
    if count == 1 then Size(Size.max)
    else Size(1 + position * (Size.max - 1) / (count - 1))

  /** `count` samples of the generator from the seed, the sizes growing as
    * `size` says. Throws `IllegalStateException` when the generator discards
    * more than `100 * count` draws: its filter rejects too much.
    */
  def samples[Value](
      generator: Gen[Value],
      seed: Long,
      count: Int
  ): Vector[Value] =
    require(count > 0, s"at least one sample is asked for: $count")
    drawn(generator, count, Seed.fromLong(seed), Vector.empty, 0)

  @tailrec
  private def drawn[Value](
      generator: Gen[Value],
      count: Int,
      seed: Seed,
      samples: Vector[Value],
      discards: Int
  ): Vector[Value] =
    if samples.size == count then samples
    else if discards > discardsPerSample * count then
      throw IllegalStateException(
        s"the generator discarded $discards draws for ${samples.size} of $count samples"
      )
    else
      val tree = generator.run(size(samples.size, count), seed)
      val (after, value) = tree.value
      value match
        case Some(sample) =>
          drawn(generator, count, after, samples :+ sample, discards)
        case None => drawn(generator, count, after, samples, discards + 1)
