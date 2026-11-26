package gezi.ir

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The binding normal form (`BindingNormalForm`) of terms nested 5,000 to
  * 10,000 deep, each already in the front end's spelling by construction, so
  * that each entry point gives back what it was given: `spelled` the term,
  * `respelled` nothing, `of` of the η-shaped pattern `λx. F x`, F a
  * higher-order metavariable bound to a thunk, that thunk, and
  * `placeholdersMapped` rebuilding each layer the filling it folds. Three
  * shapes of depth, each level's operator drawn: (a) an instruction nested
  * through applications (on either side), choices, parallels and thunks
  * `λx. x M` over placeholders; (b) a thunk `λx. x ∘ (x ∘ (… (x ∘ c)))`
  * whose code is nested, `∘` an application, a choice or a parallel; (c) a
  * thunk `λx. x ∘ (c ∘ λy. y ∘ (x ∘ λz. z ∘ (y ∘ …)))` whose inner thunks are
  * nested, as a chain of lets in the multi-line CPS layout nests them.
  *
  * Purpose: catch a function of the normal form that recurses on the JVM
  * stack once per level of nesting, which overflowed when an e-graph read a
  * programfamilies `list` item of size 512 (2,461 frames), and a spelling
  * that changes such a term on the way. Measured 2026-11-19: before the
  * normal form's recursions were trampolines, every one of the three
  * properties threw `StackOverflowError` at these depths.
  */
class BindingNormalFormDepthLawTest extends GeneratedProperties:

  private def depths: Gen[Int] = Gen.int(Range.linear(5000, 10000))

  /** The operator of a level: 0 to 2 nest through an application's
    * function, an application's argument, a choice's right; 3 a parallel's
    * left; 4 a thunk `λx. x M`.
    */
  private val instructionLevels: Gen[List[Int]] =
    depths.flatMap(depth => Gen.int(Range.constant(0, 4)).list(Range.singleton(depth)))

  /** The operator of a level of a code: 0 an application, 1 a choice, 2 a
    * parallel.
    */
  private val codeLevels: Gen[List[Int]] =
    depths.flatMap(depth => Gen.int(Range.constant(0, 2)).list(Range.singleton(depth)))

  private val leaves: Vector[Instruction] = BindingNormalForm.placeholders(3)

  /** Shape (a), over the placeholders `leaves`. */
  private def nestedInstruction(levels: List[Int]): Instruction =
    levels.zipWithIndex.foldLeft(leaves(0)) { case (inner, (level, index)) =>
      val leaf = leaves(1 + index % 2)
      level match
        case 0 => Instruction.Apply(inner, leaf)
        case 1 => Instruction.Apply(leaf, inner)
        case 2 => Instruction.Choice(leaf, inner)
        case 3 => Instruction.Parallel(inner, leaf)
        case _ => Instruction.Thunk(Code.Apply(Code.Slot(0), Code.Slot(1)), Vector(Hole.Bound(0)), Vector(inner))
    }

  private def operated(level: Int, left: Code, right: Code): Code = level match
    case 0 => Code.Apply(left, right)
    case 1 => Code.Choice(left, right)
    case _ => Code.Parallel(left, right)

  /** The code of shape (b): slot 0 the binder, slot 1 the filling. */
  private def nestedCode(levels: List[Int]): Code =
    levels.foldLeft(Code.Slot(1))((inner, level) => operated(level, Code.Slot(0), inner))

  /** The code of shape (c): each level reads its binder, slot 0, and the
    * binder of the level around it, slot 1 (the outermost level's slot 1 the
    * filling), and its inner thunk's slot 1 is its slot 0, so that no inner
    * thunk is closed and each stays a thunk of the code.
    */
  private def nestedThunks(levels: List[Int]): Code =
    levels.foldLeft(Code.Apply(Code.Slot(0), Code.Slot(1)))((inner, level) =>
      operated(
        level,
        Code.Slot(0),
        operated(level, Code.Slot(1), Code.Thunk(inner, Vector(Hole.Bound(0)), Vector(Code.Slot(0))))
      )
    )

  private val filling: Instruction = Instruction.opaque("a filling")

  /** `λx. F x`: slot 0 the filling F, metavariable 0; slot 1 the binder. */
  private val etaShaped: Pattern.Thunk =
    Pattern.Thunk(Code.Apply(Code.Slot(0), Code.Slot(1)), Vector(Hole.Bound(1)), Vector(Pattern.Metavariable(0)))

  /** The filling with each layer rebuilt, its placeholders standing for
    * themselves.
    */
  private def rebuilt(term: Instruction): Instruction =
    BindingNormalForm.placeholdersMapped(term, leaves)(layer => Instruction(layer))

  /** The laws of a thunk of the code with one hole and one filling. */
  private def thunkLaws(code: Code): Result =
    val thunk = Instruction.Thunk(code, Vector(Hole.Bound(0)), Vector(filling))
    Result.all(
      List(
        Result.diff(BindingNormalForm.spelled(thunk), thunk)(_ == _).log("spelled"),
        Result.diff(BindingNormalForm.respelled(code, Vector(Hole.Bound(0)), 1), None)(_ == _).log("respelled"),
        Result
          .diff(BindingNormalForm.of(etaShaped, Map(0 -> thunk), Set(0)), thunk)(_ == _)
          .log("of the eta-shaped pattern")
      )
    )

  property("an instruction nested thousands deep is spelled and folded as it is", _.copy(testLimit = hedgehog.core.SuccessCount(5))) {
    for levels <- instructionLevels.forAll
    yield
      val term = nestedInstruction(levels)
      Result.all(
        List(
          Result.diff(BindingNormalForm.spelled(term), term)(_ == _).log("spelled"),
          Result.diff(rebuilt(term), term)(_ == _).log("placeholders mapped")
        )
      )
  }

  property("a thunk whose code is nested thousands deep is its own normal form", _.copy(testLimit = hedgehog.core.SuccessCount(5))) {
    for levels <- codeLevels.forAll
    yield thunkLaws(nestedCode(levels))
  }

  property("a thunk whose inner thunks are nested thousands deep is its own normal form", _.copy(testLimit = hedgehog.core.SuccessCount(5))) {
    for levels <- codeLevels.forAll
    yield thunkLaws(nestedThunks(levels))
  }
