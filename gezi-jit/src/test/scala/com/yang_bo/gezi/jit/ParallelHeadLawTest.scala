package com.yang_bo.gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.jit.JitTesting.*
import com.yang_bo.gezi.weakhead.EvaluatorTesting

/** The law of the JIT's parallel heads (`JitHead.Parallel`): a parallel head
  * made twice over the same two values is equal to itself made again, with one
  * hash. A parallel head is a head, never interned (`ParallelHead`), equal by
  * its interned sides, so its purpose is to catch a head whose equality is its
  * identity, which a set of answers would hold twice and which a table's
  * answers would never equal when another computation made them again
  * (`AnswerSet`, `Jit.tableHolds`).
  */
class ParallelHeadLawTest extends GeneratedProperties:

  private val encoding = noFactsEncoding

  private given encoding.type = encoding

  private val configuration: JitConfiguration[encoding.type] =
    JitConfiguration[encoding.type](
      encoding,
      JitConfiguration.defaultBudget,
      PredicatePerCode,
      ClosureBackend,
      DispatchMode.NoDispatch,
      instanceTable = false,
      storageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()
    )

  /** A JIT value of a random closed term with choices and parallels. */
  private val values: Gen[JitValue[encoding.type]] =
    for
      seed <- Gen.long(Range.linear(0L, Long.MaxValue))
      size <- Gen.int(Range.linear(4, 12))
    yield
      val term = EvaluatorTesting.draws(1, seed)(random =>
        randomLatticeApplication(size, random)
      ) match
        case Vector(only) => only
        case other        =>
          throw IllegalStateException(s"one term drawn, not ${other.size}")
      valuesOf(Vector(instructionOf(term))) match
        case Vector(only) => only
        case other        =>
          throw IllegalStateException(s"one value per term, not ${other.size}")

  property(
    "a parallel head made twice over the same sides is equal to itself, with one hash"
  ) {
    for
      left <- values.forAll
      right <- values.forAll
    yield
      val (first, second) =
        (JitHead.Parallel(left, right), JitHead.Parallel(left, right))
      Result.assert(first == second && first.## == second.##)
  }
