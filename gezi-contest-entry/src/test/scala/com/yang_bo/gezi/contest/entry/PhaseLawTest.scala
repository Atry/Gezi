package com.yang_bo.gezi.contest.entry

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import scala.util.Try

/** The law of a phase's constructor: it refuses exactly a name that is not of
  * lowercase letters and underscores, and seconds that are negative or not
  * finite. Its purpose is to catch a phase whose name could break the answer
  * line's phases field (a tab, a `:` or a `;`, an empty name) or whose seconds
  * could not be written as six decimals, getting through to the pipe.
  */
class PhaseLawTest extends GeneratedProperties:

  /** Names of lowercase letters and underscores, mixed with characters outside
    * them: capitals, digits and the separators of the pipe.
    */
  private val name: Gen[String] =
    Gen.string(
      Gen.element1(
        'a',
        ('b' to 'z') ++ Seq('_', 'A', 'Z', '0', '9', '-', ':', ';', '\t', ' ')*
      ),
      Range.linear(0, 8)
    )

  private val seconds: Gen[Double] = Gen.choice1(
    Gen.double(Range.linearFracFrom(0.0, -1000.0, 1000.0)),
    Gen.element1(
      Double.NaN,
      Double.PositiveInfinity,
      Double.NegativeInfinity,
      -0.0,
      0.0,
      Double.MinPositiveValue,
      -Double.MinPositiveValue
    )
  )

  property(
    "a phase is refused exactly for a name outside [a-z_]+ or negative or non-finite seconds"
  ) {
    for
      phaseName <- name.forAll
      taken <- seconds.forAll
    yield
      val accepted = phaseName.nonEmpty && phaseName.forall(character =>
        character == '_' || ('a' <= character && character <= 'z')
      ) &&
        taken.isFinite && taken >= 0
      val refused = Try(Phase(phaseName, taken)).failed.toOption
        .exists(_.isInstanceOf[IllegalArgumentException])
      Result.diff(refused, !accepted)(_ == _)
  }
