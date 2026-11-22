package gezi.strategies

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.Defunctionalization
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Instruction
import gezi.rewritetrace.PositionSegment
import gezi.rewritetrace.Positions
import gezi.rewritetrace.ReplaySpelling

/** The laws of the spelling a trace replays in (`ReplaySpelling.term`), on
  * generated closed terms as the front end makes them and on the β residuals
  * of generated thunks, which are not their own spelling
  * (`ResidualPrograms`):
  *
  *   1. a term's spelling reads back to the term's readback;
  *   2. spelling a spelled term changes nothing;
  *   3. a term the front end made is its own spelling, so that a trace's
  *      start, the front end's program, is the term the player replays from;
  *   4. every thunk with holes of a spelled term is its own respelling
  *      (`BindingNormalForm.respelled` gives none), so that a respelling step
  *      is an identity in the replay.
  *
  * The spelling is not the front end's spelling of the term's readback: it
  * respells each thunk over placeholders, and the front end goes on through
  * a lambda that fills a chain's body and makes equal fillings one slot,
  * which a placeholder hides (`ReplaySpelling`).
  *
  * Purpose: catch a spelling that changes the λ-term a trace stands for
  * (1), one that is no function onto its image, so that the writer and the
  * player could hold two spellings of one step (2), one that moves the start
  * off the front end's program (3), and one that leaves a respelling the
  * replay would have to write a command for (4). With `ReplaySpelling.term`
  * the identity, law 4 fails on a residual.
  */
class ReplaySpellingLawTest extends GeneratedProperties:

  private def readback(term: Instruction): String = gezi.frontend.Lambdalattice.closedText(term)

  private val frontEndTerms: Gen[Instruction] =
    HoasGenerators.closedTerm.map(term => Defunctionalization.thunkInstruction(term.deBruijnTerm(Map.empty)))

  private val residuals: Gen[Instruction] =
    for
      thunk <- ResidualPrograms.thunks
      argument <- frontEndTerms
    yield ResidualPrograms.residual(thunk, argument)

  private val terms: Gen[Instruction] = Gen.choice1(frontEndTerms, residuals)

  property("a term's spelling reads back to the term's readback") {
    for term <- terms.forAll
    yield Result.diff(readback(ReplaySpelling.term(term)), readback(term))(_ == _)
  }

  property("spelling a spelled term changes nothing") {
    for term <- terms.forAll
    yield
      val spelled = ReplaySpelling.term(term)
      Result.diff(ReplaySpelling.term(spelled), spelled)(_ eq _)
  }

  property("a term the front end made is its own spelling") {
    for term <- frontEndTerms.forAll
    yield Result.diff(ReplaySpelling.term(term), term)(_ eq _)
  }

  property("every thunk with holes of a spelled term is its own respelling") {
    for term <- terms.forAll
    yield Result.diff(ResidualPrograms.respellable(ReplaySpelling.term(term)), Set.empty[Instruction])(_ == _)
  }

  /** A thunk of one hole z whose code is `z (s1 (s1 (… (s1 s2))))`, `depth`
    * applications of slot 1 deep, its fillings two closed terms: the chain
    * reads no binder, so its respelling is one filling as deep as the code.
    * The depth stays under the bound of `BindingNormalForm.respelled`, which
    * recurses on the code (its FIXME at `read`).
    */
  private val deepCodes: Gen[(Instruction, Instruction)] =
    for
      depth <- Gen.int(Range.linear(200, 1000))
      first <- frontEndTerms
      second <- frontEndTerms
    yield
      val chain = (1 to depth).foldLeft(Code.Slot(2))((inner, _) => Code.Apply(Code.Slot(1), inner))
      (Instruction.Thunk(Code.Apply(Code.Slot(0), chain), Vector(Hole.Bound(0)), Vector(first, second)), second)

  /** Purpose: catch positions translated wrongly through a respelled
    * filling as deep as its code: the spelling leaves no thunk respellable,
    * and every position the second filling has in it holds that filling.
    * Not a test of stack depth: past about 1,500 applications
    * `BindingNormalForm.respelled` overflows the stack before the spelling's
    * own trampolines are reached (its FIXME at `read`).
    */
  property("the positions of a filling hold it through a deep respelled code", _.copy(testLimit = hedgehog.core.SuccessCount(5))) {
    for (thunk, second) <- deepCodes.forAll
    yield
      val spelled = ReplaySpelling.term(thunk)
      val found = ReplaySpelling.positions(thunk, Vector(PositionSegment.Filling(1)))
      Result.all(
        List(
          Result.diff(ResidualPrograms.respellable(spelled), Set.empty[Instruction])(_ == _),
          Result.assert(found.nonEmpty).log("the second filling has no position in the spelling"),
          Result.assert(found.forall(position => Positions.subterm(spelled, position) eq second)).log(s"${found.size} positions")
        )
      )
  }

