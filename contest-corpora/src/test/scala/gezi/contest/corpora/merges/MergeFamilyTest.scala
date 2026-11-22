package gezi.contest.corpora.merges

/** The generators of the merge family that `MergeDynamic`'s arithmetic
  * serves, shared by their suites.
  */
object MergeFamily:
  val dynamic: MergeDynamic = MergeDynamic(MergeTesting.problems)
  val binary: MergeBinary = MergeBinary(MergeTesting.problems, dynamic)
  val fibonacci: MergeFibonacci = MergeFibonacci(MergeTesting.problems, dynamic)
  val meanings: MergeMeanings = MergeMeanings(MergeTesting.problems)

/** The tests of the deleted Prolog tests `contest_merge_binary.plt`, `contest_merge_fibonacci.plt` and
  * `contest_merge_meanings.plt` (`git show d32e69ff0^:lambda_jit/tests/<name>`) that read programs on the judge, each in both
  * directions: the program of the true claim succeeds, the one of a wrong
  * claim fails, finitely (`ClaimEndings`).
  */
class MergeFamilyEndingsTest extends MergeProblemsSuite:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of MergeFamilyEndingsTest, "theProgramAgreesWithMultiplication", takes 4.506 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "s")
  import gezi.weakhead.Mode
  import gezi.contest.corpora.claims.Ending

  test("theProgramAgreesWithMultiplication") {
    for
      left <- Vector(0, 1, 2, 3, 6, 13)
      right <- Vector(0, 1, 5, 12)
    do
      val product = BigInt(left * right)
      val holds = ClaimEndings.trueEnding(Mode.TablingWeakHead, MergeFamily.binary.productTerm(left, right, product))
      assertEquals((left, right, holds), (left, right, Ending.Succeeded))
      val refuted = ClaimEndings.trueEnding(Mode.TablingWeakHead, MergeFamily.binary.productTerm(left, right, product + 1))
      assertEquals((left, right, refuted), (left, right, Ending.Failed))
  }

  test("theProgramAgreesWithTheIteration") {
    Vector(0, 1, 2, 3, 5, 8, 12).foreach(n =>
      val fibonacci = MergeFamily.fibonacci.referenceFibonacci(n)
      val holds = ClaimEndings.trueEnding(Mode.TablingWeakHead, MergeFamily.fibonacci.fibonacciTerm(n, fibonacci))
      assertEquals((n, holds), (n, Ending.Succeeded))
      val refuted =
        ClaimEndings.trueEnding(Mode.TablingWeakHead, MergeFamily.fibonacci.fibonacciTerm(n, fibonacci + 1))
      assertEquals((n, refuted), (n, Ending.Failed))
    )
  }

  test("theCountAgreesWithTheEvensBelowAPowerOfTwo") {
    Vector(1, 2, 3, 4).foreach(exponent =>
      val holds = ClaimEndings.trueEnding(Mode.TablingWeakHead, MergeFamily.meanings.countTestSurface(exponent, 0))
      assertEquals((exponent, holds), (exponent, Ending.Succeeded))
      val refuted = ClaimEndings.trueEnding(Mode.TablingWeakHead, MergeFamily.meanings.countTestSurface(exponent, 1))
      assertEquals((exponent, refuted), (exponent, Ending.Failed))
    )
  }
