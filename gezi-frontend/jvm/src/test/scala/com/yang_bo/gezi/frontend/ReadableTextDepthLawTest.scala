package com.yang_bo.gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.StorageAccess

/** The printer's text with the places of the subterms marked
  * (`ReadableText.printedNameless`) on a chain of abstractions nested 3,000 to
  * 4,000 deep, the shape a text in the multi-line CPS layout gives: each level
  * `λx. h L`, `L` the next level, its head `h` drawn for each level among the
  * nearest binder, the outermost binder, and a closed function, so that each
  * thunk captures a few binders while a read of the outermost binder or of the
  * function crosses every level above it, the function a filling of the root
  * read through all the thunks around the read.
  *
  * Purpose: catch a marked printing whose cost grows with the square of the
  * depth: places keyed by their whole paths, a read's path prefixed at each
  * level of code, a slot's read passed through each thunk around it, and a mark
  * lost on the way: there is one mark for the root, one for each read of the
  * function, and one for the value of each binding, which binds the function
  * when the text refers to it twice. Measured 2026-11-19 on cores 0-5, load 3
  * to 4, two samples: the printer before its places cost linear time
  * (feba9ebbd) ran past the default deadline of 3 s in each of two runs, a
  * sample of depth 4,000 alone printing marked in 3.2 to 3.9 s on a warm JVM;
  * the printer that followed passes in 1.3 to 1.4 s in each of four runs, most
  * of it the JVM's warm-up.
  */
class ReadableTextDepthLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts
  given StorageAccess = StorageAccess.granted()

  private type NoFactsTerm = Configured[NoFacts.type]

  import DeBruijnTerm.*

  private val function: NoFactsTerm =
    Defunctionalization.thunkInstruction[NoFacts.type](Lambda(Variable(0)))

  /** The head of each level: 0 the nearest binder, 1 the outermost, 2 the
    * function.
    */
  private val levels: Gen[List[Int]] =
    Gen
      .int(Range.linear(3000, 4000))
      .flatMap(depth => Gen.element1(0, 1, 2).list(Range.singleton(depth)))

  /** The chain, its innermost body the outermost binder. */
  private def chain(heads: List[Int]): DeBruijnTermOf[NoFactsTerm] =
    val depth = heads.size
    heads.zipWithIndex.foldRight(
      Variable(depth - 1): DeBruijnTermOf[NoFactsTerm]
    ) { case ((head, level), inner) =>
      val written = head match
        case 0 => Variable(0)
        case 1 => Variable(level)
        case _ => Constant(function)
      Lambda(Apply(written, inner))
    }

  property(
    "the text of abstractions nested thousands deep is marked at the root, at each read of the function and at each bound value",
    _.copy(testLimit = hedgehog.core.SuccessCount(2))
  ) {
    for heads <- levels.forAll
    yield
      val instruction =
        Defunctionalization.thunkInstruction[NoFacts.type](chain(heads))
      val printed = ReadableText.printedNameless(instruction)
      val marks = printed.pieces.count {
        case ReadableText.Piece.At(_, _) => true
        case _                           => false
      }
      Result.diff(marks, 1 + heads.count(_ == 2) + printed.bindings)(_ == _)
  }
