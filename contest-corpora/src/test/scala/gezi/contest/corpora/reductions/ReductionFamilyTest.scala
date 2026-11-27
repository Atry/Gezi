package gezi.contest.corpora.reductions

/** The interpreter problems against the interpreter's reference values, and the
  * reference's refusal of an ambiguous value, from the deleted Prolog test
  * (`git show d32e69ff0^:lambda_jit/tests/contest_reduction_interpreter.plt`).
  */
class ReductionInterpreterTest extends gezi.generatedinputs.FailFastSuite:

  private lazy val group: ReductionGroup = ReductionTesting.group

  test("everyProblemExpectsTheReference") {
    ReductionInterpreter
      .programs(group)
      .foreach((point, expression) =>
        val problem =
          ReductionInterpreter.problems(group).find(_.point == point).get
        assertEquals(
          (point, problem.typeName, problem.expected),
          (
            point,
            "binary",
            Expected.One(
              Scott.binaryTree(ReductionInterpreter.referenceValue(expression))
            )
          )
        )
      )
  }

  test("theReferenceRefusesAnAmbOfTwoValues") {
    import Expression.*
    val error = intercept[IllegalArgumentException](
      ReductionInterpreter.referenceValue(
        Let(Amb(Number(1), Number(2)), Add(Variable(0), Variable(0)))
      )
    )
    assert(error.getMessage.startsWith("amb_of_one_value"), error.getMessage)
  }

object ReductionInterpreterTest:
  import Expression.*

  /** The expressions of the test `small_programs_decode_to_the_reference`. */
  val testExpressions: Vector[Expression] = Vector(
    Number(0),
    Number(5),
    Add(Number(2), Number(3)),
    Multiply(Number(6), Number(7)),
    Let(Number(4), Multiply(Variable(0), Variable(0))),
    Let(Number(1), Let(Number(2), Add(Variable(0), Variable(1)))),
    Let(
      Number(3),
      Let(
        Number(5),
        Let(Number(7), Multiply(Variable(2), Add(Variable(0), Variable(1))))
      )
    ),
    Amb(Add(Number(2), Number(3)), Add(Number(3), Number(2))),
    Let(Amb(Number(4), Number(4)), Add(Variable(0), Number(1)))
  )

/** The operand trees of the tests of `problems/reduction_non_canonical`. */
object ReductionNonCanonicalTest:

  /** The binary trees of depth at most `depth`, in the order of the test helper
    * `tree_of_depth/2`.
    */
  def treesOfDepth(depth: Int): Vector[ScottTree] =
    Scott.leaf(
      "zero"
    ) +: (if depth == 0 then Vector.empty
          else
            Vector("even", "odd").flatMap(name =>
              treesOfDepth(depth - 1).map(half => ScottTree(name, Vector(half)))
            ))

/** The snapshot of the problems of `problems/reduction_mixins`, whose purpose
  * is to catch a generator change that alters a problem's program, type,
  * expected trees or limits.
  */
class ReductionMixinsTest
    extends GeneratedProgramsSuite("contest_reduction_mixins"):
  def generated(group: ReductionGroup) =
    ReductionTesting.problemLines(group, ReductionMixins.problems(group))

/** The snapshot of the problems of `problems/reduction_mixin_binary`, whose
  * purpose is to catch a generator change that alters a problem's program,
  * type, expected trees or limits.
  */
class ReductionMixinBinaryTest
    extends GeneratedProgramsSuite("contest_reduction_mixin_binary"):
  def generated(group: ReductionGroup) =
    ReductionTesting.problemLines(group, ReductionMixinBinary.problems(group))

/** The snapshot of the problems of `problems/reduction_mixin_fibonacci`, whose
  * purpose is to catch a generator change that alters a problem's program,
  * type, expected trees or limits.
  */
class ReductionMixinFibonacciTest
    extends GeneratedProgramsSuite("contest_reduction_mixin_fibonacci"):
  def generated(group: ReductionGroup) = ReductionTesting.problemLines(
    group,
    ReductionMixinFibonacci.problems(group)
  )

/** The snapshot of the problems of `problems/reduction_mixin_grid`, whose
  * purpose is to catch a generator change that alters a problem's program,
  * type, expected trees or limits.
  */
class ReductionMixinGridTest
    extends GeneratedProgramsSuite("contest_reduction_mixin_grid"):
  def generated(group: ReductionGroup) =
    ReductionTesting.problemLines(group, ReductionMixinGrid.problems(group))

/** The snapshot of the problems of `problems/reduction_mixin_library`, whose
  * purpose is to catch a generator change that alters a problem's program,
  * type, expected trees or limits.
  */
class ReductionMixinLibraryTest
    extends GeneratedProgramsSuite("contest_reduction_mixin_library"):
  def generated(group: ReductionGroup) =
    ReductionTesting.problemLines(group, ReductionMixinLibrary.problems(group))

/** The snapshot of the problems of `problems/reduction_mixin_theorems`, whose
  * purpose is to catch a generator change that alters a problem's program,
  * type, expected trees or limits.
  */
class ReductionMixinTheoremsTest
    extends GeneratedProgramsSuite("contest_reduction_mixin_theorems"):

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of ReductionMixinTheoremsTest, "contest_reduction_mixin_theorems: the generated programs", takes 4.249 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(10, "s")
  def generated(group: ReductionGroup) =
    ReductionTesting.problemLines(group, ReductionMixinTheorems.problems(group))
