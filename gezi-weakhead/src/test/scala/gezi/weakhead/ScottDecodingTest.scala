package gezi.weakhead

import gezi.ir.NoFacts

import gezi.weakhead.EvaluatorTesting.*
import gezi.weakhead.oldcorpora.Confirmation
import gezi.weakhead.oldcorpora.ConstructorTree
import gezi.weakhead.oldcorpora.ScottDataType
import gezi.weakhead.oldcorpora.ScottDecoding
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The port of `gezi/tests/scott_decoding.plt`: the Scott decoder's evaluating
  * half on the weak-head evaluator: a term applied to one neutral value per
  * constructor reads its constructor tree; every tree of every head is an
  * answer; a head that is no constructor of the level reads ill-formed; a
  * parallel reads the trees both sides read. Every run is bounded by a budget
  * of steps.
  */
class ScottDecodingTest extends gezi.generatedinputs.FailFastSuite:

  given NoFacts.type = NoFacts

  private def omega: Term = λ(a => a(a))(λ(b => b(b)))

  /** The distinct trees decoded under the mode, as a set, within the limit of
    * small terms.
    */
  private def trees(
      mode: Mode,
      term: Term,
      dataType: ScottDataType
  ): Set[ConstructorTree] =
    val value = valueOf(term)
    finishedValue(treesWithin(mode, value, dataType, smallTermLimit)).toSet

  /** Both modes decode exactly the expected trees, as a set. */
  private def decodes(
      term: Term,
      dataType: ScottDataType,
      expected: Vector[ConstructorTree]
  ): Unit =
    assertEquals(trees(Mode.WeakHead, term, dataType), expected.toSet)
    assertEquals(trees(Mode.TablingWeakHead, term, dataType), expected.toSet)

  private def unary(count: Int): ConstructorTree =
    if count == 0 then ConstructorTree.Constructor("zero", Vector.empty)
    else ConstructorTree.Constructor("successor", Vector(unary(count - 1)))

  private def surfaceOf(dataType: ScottDataType, tree: ConstructorTree): Term =
    ScottDecoding.treeSurface(dataType, tree)

  test("aCanonicalTermDecodesToItsTree") {
    Vector(0, 1, 2, 5).foreach(count =>
      decodes(
        surfaceOf(ScottDataType.Unary, unary(count)),
        ScottDataType.Unary,
        Vector(unary(count))
      )
    )
    (0 to 9).foreach(natural =>
      val tree = ScottDecoding.binaryTree(natural)
      decodes(
        surfaceOf(ScottDataType.Binary, tree),
        ScottDataType.Binary,
        Vector(tree)
      )
    )
    decodes(
      λ(t => λ(_ => t)),
      ScottDataType.Booleans,
      Vector(ConstructorTree.Constructor("true", Vector.empty))
    )
    decodes(
      λ(_ => λ(f => f)),
      ScottDataType.Booleans,
      Vector(ConstructorTree.Constructor("false", Vector.empty))
    )
  }

  /** even zero denotes 0 as zero does, but case analysis tells them apart. */
  test("aNonCanonicalTermDecodesToItsOwnTree") {
    decodes(
      λ(_ => λ(e => λ(_ => e(λ(z => λ(_ => λ(_ => z))))))),
      ScottDataType.Binary,
      Vector(
        ConstructorTree.Constructor(
          "even",
          Vector(ConstructorTree.Constructor("zero", Vector.empty))
        )
      )
    )
  }

  test("aComputedValueDecodes") {
    decodes(
      λ(n => λ(_ => λ(s => s(n))))(surfaceOf(ScottDataType.Unary, unary(1))),
      ScottDataType.Unary,
      Vector(unary(2))
    )
  }

  test("aHeadThatIsNoConstructorReadsIllFormed") {
    decodes(
      λ(_ => λ(s => s)),
      ScottDataType.Unary,
      Vector(ConstructorTree.IllFormed)
    )
    decodes(
      λ(_ => λ(_ => λ(x => x))),
      ScottDataType.Unary,
      Vector(ConstructorTree.IllFormed)
    )
    decodes(λ(t => λ(_ => t)), ScottDataType.Unary, Vector(unary(0)))
  }

  /** Each level has cases of its own: the inner field answers the outer even.
    */
  test("aFieldAnsweringAnOuterCaseReadsIllFormed") {
    decodes(
      λ(_ =>
        λ(e => λ(_ => e(λ(_ => λ(_ => λ(_ => e(λ(z => λ(_ => λ(_ => z))))))))))
      ),
      ScottDataType.Binary,
      Vector(
        ConstructorTree.Constructor("even", Vector(ConstructorTree.IllFormed))
      )
    )
  }

  test("aChoiceDecodesEveryTree") {
    val one = surfaceOf(ScottDataType.Unary, unary(1))
    val two = surfaceOf(ScottDataType.Unary, unary(2))
    decodes(choice(one, two), ScottDataType.Unary, Vector(unary(1), unary(2)))
    decodes(
      λ(_ =>
        λ(s =>
          s(
            choice(
              surfaceOf(ScottDataType.Unary, unary(1)),
              surfaceOf(ScottDataType.Unary, unary(2))
            )
          )
        )
      ),
      ScottDataType.Unary,
      Vector(unary(3), unary(2))
    )
  }

  test("aParallelDecodesTheTreesBothSidesDecode") {
    def one = surfaceOf(ScottDataType.Unary, unary(1))
    def two = surfaceOf(ScottDataType.Unary, unary(2))
    decodes(one ∥ choice(one, two), ScottDataType.Unary, Vector(unary(1)))
    decodes(one ∥ two, ScottDataType.Unary, Vector.empty)
    decodes(
      λ(_ => λ(s => s(one ∥ choice(one, two)))),
      ScottDataType.Unary,
      Vector(unary(2))
    )
  }

  /** Tabled, the decoding of successor Ω finishes within 100,000 steps (the
    * Prolog test's 100,000 inferences) with no tree; untabled, any finite
    * budget is exceeded (the Prolog test's 1,000,000 inferences, 1,000,000
    * steps here).
    */
  test("aFieldWithNoHeadDecodesNothingTabled") {
    val value = valueOf(λ(_ => λ(s => s(omega))))
    assertEquals(
      treesWithin(Mode.TablingWeakHead, value, ScottDataType.Unary, 100000),
      Bounded.Finished(Vector.empty)
    )
    assertEquals(
      treesWithin(Mode.WeakHead, value, ScottDataType.Unary, 1000000),
      Bounded.Exceeded
    )
  }

  /** The Prolog predicate had no budget; here each decoding is one tabled
    * reading within the limit of small terms, and a decoding past its limit (a
    * limit of 0 steps here) answers neither way.
    */
  test("meaningConfirmedHoldsOfOneTreeOnly") {
    val two = valueOf(surfaceOf(ScottDataType.Unary, unary(2)))
    assertEquals(
      ScottDecoding
        .meaningConfirmed(two, ScottDataType.Unary, unary(2), smallTermLimit),
      Confirmation.Confirmed
    )
    val both = valueOf(
      choice(
        surfaceOf(ScottDataType.Unary, unary(1)),
        surfaceOf(ScottDataType.Unary, unary(2))
      )
    )
    assertEquals(
      ScottDecoding
        .meaningConfirmed(both, ScottDataType.Unary, unary(2), smallTermLimit),
      Confirmation.NotConfirmed
    )
    val omegaField = valueOf(λ(_ => λ(s => s(omega))))
    assertEquals(
      ScottDecoding
        .meaningConfirmed(omegaField, ScottDataType.Unary, unary(1), 0),
      Confirmation.LimitReached
    )
  }
