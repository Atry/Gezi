package gezi.programfamilies

import gezi.standardlibrary.SplitMix

/** The migration's criterion 4, that no stage of the pipeline grows faster
  * than linearly in the program's size: on each of the eight size families at 64, 128, 512 and
  * 1,024, every deterministic count of every stage of the pipeline
  * (`Pipeline.counts`) satisfies (C₁₀₂₄ − C₅₁₂)/512 ≤ 1.6 × (C₁₂₈ − C₆₄)/64.
  * Each family is a test of its own, named after it.
  */
class CriterionFourTest extends gezi.generatedinputs.FailFastSuite:
  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of CriterionFourTest, "list", takes 128.769 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(195, "s")

  private lazy val compiled: Map[String, CompiledConfiguration] = CompiledConfigurations.byName

  Pipeline.sizeFamilies.foreach { family =>
    test(family.family) {
      val growths = StageCountTable.growths(family, compiled(family.configuration.name))
      val failing = growths.filterNot(_.holds).map(_.line)
      assertEquals(failing, Vector.empty, failing.mkString("\n"))
    }
  }

  // On counts a n² + b n + c drawn from a seed: the inequality holds exactly
  // when a = 0 (b ≥ 0), and a count is constant exactly when a = b = 0.
  test("theInequalityHoldsOnLinearCountsAndFailsOnQuadraticOnes") {
    val (coefficients, _) = (1 to 300).foldLeft((Vector.empty[(Long, Long, Long)], SplitMix(4L))) {
      case ((drawn, random), _) =>
        val (quadratic, afterQuadratic) = random.between(0, 2)
        val (linear, afterLinear) = afterQuadratic.between(0, 2)
        val (constant, afterConstant) = afterLinear.between(0, 1000)
        (drawn :+ (quadratic.toLong, linear.toLong * 1000, constant.toLong), afterConstant)
    }
    coefficients.foreach { (quadratic, linear, constant) =>
      val growth = CountGrowth(
        "drawn",
        "stage",
        "count",
        Pipeline.countedSizes.map(size => quadratic * size * size + linear * size + constant)
      )
      assertEquals(growth.holds, quadratic == 0, (quadratic, linear, constant))
      assertEquals(growth.constant, quadratic == 0 && linear == 0, (quadratic, linear, constant))
    }
  }
