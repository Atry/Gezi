package gezi.narrowblocks

import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Pure
import gezi.jit.BinaryNaturalFamily
import gezi.jit.NativesProvider
import gezi.saturation.StopSignal
import gezi.standardlibrary.CombinatorProperty
import gezi.standardlibrary.NativeBound
import gezi.standardlibrary.Property
import gezi.standardlibrary.StandardLibraryIndex
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger

private given narrowBlockDepthLawTestNoFacts: NoFacts.type = NoFacts

/** The laws that a closed narrow natural nested thousands deep compiles to one
  * block that computes it, or is refused with its reason, and is never thrown
  * on. Their purpose is to catch a pass of the narrow blocks (the reading of a
  * closed natural, the fold of its constants, the walks over its expression,
  * the bytecode's emission) that recurses on the term's depth, which threw
  * `StackOverflowError` on a program 3,003 levels deep, and on these laws
  * before the passes were made stack-safe.
  *
  * Two shapes of chain. A left-nested chain of the binary naturals' plus,
  * `plus (… (plus l0 l1) …) ln`, over the literals 1 and 2, is a constant: the
  * reader folds it into the literal of its sum (`NarrowExpression.Folded`), so
  * it meets the depth in the reading and the fold, 5,000 to 25,000 levels, and
  * the block is one `ldc`. A chain of calls of closed functions that add 1 or
  * 2, `f_k (… (f_l l0) …)`, is no constant, so its expression is emitted whole
  * into the block's one JVM method, whose code is at most 65,535 bytes: a call
  * takes at most 17 bytes besides its argument (`callBound`), so the depth
  * stops at 3,500, at most 59,503 bytes of bound. Deeper, 20,000 to 25,000, the
  * same chain is refused, not thrown on. The call chain also catches a stack
  * map that grows with the depth: when a call pushed its stop signal before its
  * argument, the chain held one stop a level on the operand stack, and the JVM
  * failed defining the class at 3,000 to 4,000 levels.
  *
  * The names are bound by hand, as in `NarrowBlockCostMonotonicityLawTest`:
  * four closed instructions bound by `native` facts to the binary naturals'
  * constructors zero, even and odd and to the native plus, over the natives the
  * tree loads.
  */
class NarrowBlockDepthLawTest extends GeneratedProperties:

  /** λx. x x, bound to zero. */
  private val zero = NoFacts.thunkOrInstance(
    Code.Apply(Code.Slot(0), Code.Slot(0)),
    Vector(Hole.Bound(0)),
    Vector.empty
  )

  /** λx y. y x, bound to even. */
  private val even =
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Slot(1), Code.Slot(0)),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector.empty
    )

  /** λx y z. z y x, bound to odd. */
  private val odd = NoFacts.thunkOrInstance(
    Code.Apply(Code.Apply(Code.Slot(2), Code.Slot(1)), Code.Slot(0)),
    Vector(Hole.Bound(0), Hole.Bound(1), Hole.Bound(2)),
    Vector.empty
  )

  /** λx y. x (y y), the criterion `binary_set` whose `data_family` lists zero,
    * even and odd, in the codec's order (`BinaryNaturalFamily`).
    */
  private val binarySet = NoFacts.thunkOrInstance(
    Code.Apply(Code.Slot(0), Code.Apply(Code.Slot(1), Code.Slot(1))),
    Vector(Hole.Bound(0), Hole.Bound(1)),
    Vector.empty
  )

  /** λx y. y y x, bound to plus. */
  private val plus = NoFacts.thunkOrInstance(
    Code.Apply(Code.Apply(Code.Slot(1), Code.Slot(1)), Code.Slot(0)),
    Vector(Hole.Bound(0), Hole.Bound(1)),
    Vector.empty
  )

  private val compilation = NarrowBlockCompilation(
    StandardLibraryIndex(
      NoFacts,
      Vector.empty,
      Vector.empty,
      Vector(
        NativeBound(Pure.required(plus), "wren_binary_plus")
      ),
      Vector(
        CombinatorProperty(
          Pure.required(binarySet),
          Property.NativeSpecialization(BinaryNaturalFamily.identity.name)
        ),
        CombinatorProperty(
          Pure.required(binarySet),
          Property.DataFamily(0, Vector(zero, even, odd).map(Pure.required))
        )
      )
    ),
    NativesProvider.loaded,
    gezi.weakhead.ReadingConfiguration.withoutFacts
  )

  /** The canonical binary numeral of the value, least significant digit
    * outermost.
    */
  private def numeral(value: Int): Configured[NoFacts.type] =
    if value == 0 then zero
    else
      NoFacts.application(
        if (value & 1) == 1 then odd else even,
        numeral(value >> 1)
      )

  /** `λx. plus x l`, the literal l a filling: a closed function that adds the
    * literal's value.
    */
  private def adding(literal: Int): Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Apply(Code.Slot(1), Code.Slot(0)), Code.Slot(2)),
      Vector(Hole.Bound(0)),
      Vector(plus, numeral(literal))
    )

  /** The chain of calls of the functions adding each literal of `rest`, the
    * first innermost, over the numeral of `first`.
    */
  private def calls(first: Int, rest: List[Int]): Configured[NoFacts.type] =
    rest.foldLeft(numeral(first))((sum, literal) =>
      NoFacts.application(adding(literal), sum)
    )

  /** The left-nested chain of plus over the numerals. */
  private def sums(first: Int, rest: List[Int]): Configured[NoFacts.type] =
    rest.foldLeft(numeral(first))((sum, literal) =>
      NoFacts.application(NoFacts.application(plus, sum), numeral(literal))
    )

  // Five inputs, not the default 20: every input is thousands of levels
  // deep, so each one checks the law at the depth it is about; one input
  // took 0.07 to 0.8 s at depth 7,000 (a probe of 2026-11-17, two CPUs at
  // nice 10, the first input cold), so 20 overran the 3 s deadline.
  stoppableProperty(
    "a chain of calls nested thousands deep compiles to a block that computes its sum",
    _.copy(testLimit = hedgehog.core.SuccessCount(5))
  ) { stopped =>
    for
      first <- Gen.int(Range.constant(1, 2)).forAll
      rest <- Gen
        .list(Gen.int(Range.constant(1, 2)), Range.linear(3_000, 3_500))
        .forAll
    yield
      val chain = calls(first, rest)
      val stop = StopSignal.completedWith(stopped)
      val blocks = compilation.blocks(chain)
      val computed = compilation
        .compiled(blocks, DebugAttributes.Omitted, stop)
        .map(_.map(_.run(stop)))
      Result
        .all(
          List(
            Result
              .assert(blocks == Vector(chain))
              .log(s"the blocks are not the chain: ${blocks.size} blocks"),
            Result.diff(
              computed,
              Right(
                Vector(
                  Some(BigInteger.valueOf((first +: rest).map(_.toLong).sum))
                )
              )
            )(_ == _)
          )
        )
        .log(s"depth ${rest.size}")
  }

  stoppableProperty(
    "a constant chain of plus nested thousands deep folds into a block that computes its sum",
    _.copy(testLimit = hedgehog.core.SuccessCount(5))
  ) { stopped =>
    for
      first <- Gen.int(Range.constant(1, 2)).forAll
      rest <- Gen
        .list(Gen.int(Range.constant(1, 2)), Range.linear(5_000, 25_000))
        .forAll
    yield
      val chain = sums(first, rest)
      val stop = StopSignal.completedWith(stopped)
      val blocks = compilation.blocks(chain)
      val computed = compilation
        .compiled(blocks, DebugAttributes.Omitted, stop)
        .map(_.map(_.run(stop)))
      Result
        .all(
          List(
            Result
              .assert(blocks == Vector(chain))
              .log(s"the blocks are not the chain: ${blocks.size} blocks"),
            Result.diff(
              computed,
              Right(
                Vector(
                  Some(BigInteger.valueOf((first +: rest).map(_.toLong).sum))
                )
              )
            )(_ == _)
          )
        )
        .log(s"depth ${rest.size}")
  }

  /** A chain of calls deep enough that its method could exceed the JVM's limit
    * is refused with its reason, so that the program is left to the general
    * reading, never thrown on by the class build: before the bound, a chain of
    * plus 20,000 deep threw `IllegalArgumentException` (code length 100003).
    */
  stoppableProperty(
    "a chain of calls too deep for one method is refused, not thrown on",
    _.copy(testLimit = hedgehog.core.SuccessCount(3))
  ) { stopped =>
    for
      first <- Gen.int(Range.constant(1, 2)).forAll
      rest <- Gen
        .list(Gen.int(Range.constant(1, 2)), Range.linear(20_000, 25_000))
        .forAll
    yield
      val chain = calls(first, rest)
      compilation.compiled(
        compilation.blocks(chain),
        DebugAttributes.Omitted,
        StopSignal.completedWith(stopped)
      ) match
        case Left(reason) =>
          Result.assert(reason.contains("beyond the JVM's")).log(reason)
        case Right(programs) =>
          Result.failure.log(
            s"${programs.size} blocks compiled at depth ${rest.size}"
          )
  }
