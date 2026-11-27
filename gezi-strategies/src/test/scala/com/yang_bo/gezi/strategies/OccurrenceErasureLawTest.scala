package com.yang_bo.gezi.strategies

import hedgehog.Gen
import hedgehog.Result
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.Lambdalattice
import com.yang_bo.gezi.frontend.OccurrenceMarkers
import com.yang_bo.gezi.frontend.Occurrences
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.generatedinputs.LambdalatticeText
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.Pure
import com.yang_bo.gezi.rewritetrace.OccurrenceErasure
import com.yang_bo.gezi.rewritetrace.TraceLemma

/** The certificate of the occurrence tagging (`OccurrenceErasure.trace`):
  * replayed from the program the front end tagged, its erasures end at a term
  * whose readback is the untagged program's. The programs are `HoasGenerators`'
  * closed terms over three library terms, which the tagging tags at each
  * occurrence; the markers are terms that behave as the library's `$name` and
  * `$closure` do (`corpora/library/native_types/markers.lambdalattice`), the
  * identity on what they wrap by the β rule, and the erasure lemmas are given
  * in either orientation.
  *
  * Purpose: catch an erasure at a wrong position (the replay refuses a subterm
  * that is no instance of the lemma's side), a tag left in place (the readback
  * keeps it), and above all a closure tag in a code, which only an opened thunk
  * reaches.
  */
class OccurrenceErasureLawTest extends GeneratedProperties:

  private given NoFacts.type = NoFacts

  private given com.yang_bo.gezi.ir.StorageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()

  private def closed(text: String): Configured[NoFacts.type] =
    Defunctionalization.thunkInstruction[com.yang_bo.gezi.ir.NoFacts.type](
      Lambdalattice.term(text)
    )(using com.yang_bo.gezi.ir.NoFacts)

  /** Two markers that behave as the library's `$name` and `$closure` do, each
    * the identity on its second argument by the β rule, spelled without the
    * literal the library's markers read, and two tag constructors.
    */
  private def pure(text: String): Pure =
    Defunctionalization.pure(Lambdalattice.term(text))

  private val markers: OccurrenceMarkers = OccurrenceMarkers(
    pure("λt. λx. (λy. λz. z) t x"),
    pure("λt. λc. (λy. λz. y) c t"),
    pure("λa. λb. λc. c"),
    pure("λn. λa. λb. λc. n")
  )

  private val libraryTerms: Vector[StrategyTesting.ProgramTerm] =
    Vector("λx. x", "λx. λy. x", "λf. λx. f (f x)").map(text =>
      Term.closed(closed(text))
    )

  /** The two erasure lemmas, `λt. λx. M t x = λt. λx. x` for each marker M,
    * each in the orientation drawn.
    */
  private val lemmas: Gen[Vector[TraceLemma[NoFacts.type]]] =
    val sides = Vector(markers.name, markers.closure).map(marker =>
      (
        OccurrenceMarkers.erasing[NoFacts.type](marker),
        OccurrenceMarkers.erased[NoFacts.type]
      )
    )
    Gen
      .list(Gen.boolean, hedgehog.Range.singleton(sides.size))
      .map(turned =>
        sides.zip(turned).map { case ((erasing, erased), backward) =>
          if backward then TraceLemma(erased, erasing)
          else TraceLemma(erasing, erased)
        }
      )

  property(
    "the erasure trace replayed from the tagged program ends at the untagged program, up to respelling"
  ) {
    for
      program <- HoasGenerators
        .closedTermOver(libraryTerms)
        .forAllWithLog(term => LambdalatticeText.text(term))
      erasureLemmas <- lemmas.forAll
    yield
      val term = program.deBruijnTerm(Map.empty)
      val encoded = Defunctionalization
        .thunkInstruction[com.yang_bo.gezi.ir.NoFacts.type](term)(using com.yang_bo.gezi.ir.NoFacts)
      val tagged = Defunctionalization.thunkInstruction[com.yang_bo.gezi.ir.NoFacts.type](
        Occurrences.tagged(term, markers)
      )(using com.yang_bo.gezi.ir.NoFacts)
      val end =
        OccurrenceErasure.trace(tagged, markers, erasureLemmas).output(tagged)
      Result.diff(
        Defunctionalization.instructionTerm(end),
        Defunctionalization.instructionTerm(encoded)
      )(_ == _)
  }
