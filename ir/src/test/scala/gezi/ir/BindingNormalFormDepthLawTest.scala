package gezi.ir

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The binding normal form (`BindingNormalForm`) of terms nested 5,000 to
  * 10,000 deep, each already in the front end's spelling by construction, so
  * that each entry point gives back what it was given: `spelled` the term,
  * `respelled` nothing, `of` of the η-shaped pattern `λx. F x`, F a
  * higher-order metavariable bound to a thunk, that thunk, and `fillingMapped`
  * rebuilding each layer of the filling it folds (the shape (a) as a code over
  * the slots). Three shapes of depth, each level's operator drawn: (a) an
  * instruction nested through applications (on either side), choices, parallels
  * and thunks `λx. x M` over placeholders; (b) a thunk
  * `λx. x ∘ (x ∘ (… (x ∘ c)))` whose code is nested, `∘` an application, a
  * choice or a parallel; (c) a thunk
  * `λx. x ∘ (c ∘ λy. y ∘ (x ∘ λz. z ∘ (y ∘ …)))` whose inner thunks are nested,
  * as a chain of lets in the multi-line CPS layout nests them.
  *
  * Purpose: catch a function of the normal form that recurses on the JVM stack
  * once per level of nesting, which overflowed when an e-graph read a
  * programfamilies `list` item of size 512 (2,461 frames), and a spelling that
  * changes such a term on the way. Measured 2026-11-19: before the normal
  * form's recursions were trampolines, every one of the three properties threw
  * `StackOverflowError` at these depths.
  */
class BindingNormalFormDepthLawTest extends GeneratedProperties:

  given gezi.ir.NoFacts.type = gezi.ir.NoFacts

  private def depths: Gen[Int] = Gen.int(Range.linear(5000, 10000))

  /** The operator of a level: 0 to 2 nest through an application's function, an
    * application's argument, a choice's right; 3 a parallel's left; 4 a thunk
    * `λx. x M`.
    */
  private val instructionLevels: Gen[List[Int]] =
    depths.flatMap(depth =>
      Gen.int(Range.constant(0, 4)).list(Range.singleton(depth))
    )

  /** The operator of a level of a code: 0 an application, 1 a choice, 2 a
    * parallel.
    */
  private val codeLevels: Gen[List[Int]] =
    depths.flatMap(depth =>
      Gen.int(Range.constant(0, 2)).list(Range.singleton(depth))
    )

  private val leaves: Vector[Configured[NoFacts.type]] =
    Vector.tabulate(3)(position => NoFacts.opaque(s"placeholder $position"))

  private val oneHole: NonEmptyHoles =
    NonEmptyHoles(Hole.Bound(0), Vector.empty)

  /** Shape (a), over the placeholders `leaves`. */
  private def nestedInstruction(levels: List[Int]): Configured[NoFacts.type] =
    levels.zipWithIndex.foldLeft(leaves(0)) { case (inner, (level, index)) =>
      val leaf = leaves(1 + index % 2)
      level match
        case 0 => NoFacts.application(inner, leaf)
        case 1 => NoFacts.application(leaf, inner)
        case 2 => NoFacts.choice(leaf, inner)
        case 3 => NoFacts.parallel(inner, leaf)
        case _ =>
          NoFacts.thunk(
            Code.Apply(Code.Slot(0), Code.Slot(1)),
            oneHole,
            Vector(inner)
          )
    }

  /** Shape (a) as a filling, a code over the slots 0 to 2 that the placeholders
    * stand for, its operators drawn as `nestedInstruction`'s are.
    */
  private def nestedFilling(levels: List[Int]): Code =
    levels.zipWithIndex.foldLeft(Code.Slot(0)) { case (inner, (level, index)) =>
      val leaf = Code.Slot(1 + index % 2)
      level match
        case 0 => Code.Apply(inner, leaf)
        case 1 => Code.Apply(leaf, inner)
        case 2 => Code.Choice(leaf, inner)
        case 3 => Code.Parallel(inner, leaf)
        case _ =>
          Code.Thunk(
            Code.Apply(Code.Slot(0), Code.Slot(1)),
            Vector(Hole.Bound(0)),
            Vector(inner)
          )
    }

  private def operated(level: Int, left: Code, right: Code): Code = level match
    case 0 => Code.Apply(left, right)
    case 1 => Code.Choice(left, right)
    case _ => Code.Parallel(left, right)

  /** The code of shape (b): slot 0 the binder, slot 1 the filling. */
  private def nestedCode(levels: List[Int]): Code =
    levels.foldLeft(Code.Slot(1))((inner, level) =>
      operated(level, Code.Slot(0), inner)
    )

  /** The code of shape (c): each level reads its binder, slot 0, and the binder
    * of the level around it, slot 1 (the outermost level's slot 1 the filling),
    * and its inner thunk's slot 1 is its slot 0, so that no inner thunk is
    * closed and each stays a thunk of the code.
    */
  private def nestedThunks(levels: List[Int]): Code =
    levels.foldLeft(Code.Apply(Code.Slot(0), Code.Slot(1)))((inner, level) =>
      operated(
        level,
        Code.Slot(0),
        operated(
          level,
          Code.Slot(1),
          Code.Thunk(inner, Vector(Hole.Bound(0)), Vector(Code.Slot(0)))
        )
      )
    )

  private val filling: Configured[NoFacts.type] = NoFacts.opaque("a filling")

  /** `λx. F x`: slot 0 the filling F, metavariable 0; slot 1 the binder. */
  private val etaShaped: Pattern.Thunk[NoFacts.type] =
    Pattern.Thunk(
      Code.Apply(Code.Slot(0), Code.Slot(1)),
      Vector(Hole.Bound(1)),
      Vector(Pattern.Metavariable[NoFacts.type](0))
    )

  /** The filling with each layer rebuilt, its slots standing for themselves. */
  private def rebuilt(filling: Code): Code =
    BindingNormalForm.fillingMapped(
      filling,
      Vector.tabulate(3)(position => Code.Slot(position))
    ) {
      case Apply(function, argument)    => Code(Apply(function, argument))
      case Parallel(left, right)        => Code(Parallel(left, right))
      case Choice(left, right)          => Code(Choice(left, right))
      case Thunk(code, holes, fillings) => Code(Thunk(code, holes, fillings))
      case other                        =>
        throw IllegalStateException(
          s"a filling's fold made a layer that is no code's: $other"
        )
    }

  /** The laws of a thunk of the code with one hole and one filling. */
  private def thunkLaws(code: Code): Result =
    val thunk = NoFacts.thunk(code, oneHole, Vector(filling))
    Result.all(
      List(
        Result
          .diff(BindingNormalForm.spelled(thunk), thunk)(Configured.same(_, _))
          .log("spelled"),
        Result
          .diff(
            BindingNormalForm.respelled(code, Vector(Hole.Bound(0)), 1),
            None
          )(_ == _)
          .log("respelled"),
        Result
          .diff(
            BindingNormalForm.of(etaShaped, Map(0 -> thunk), Set(0)),
            thunk
          )(Configured.same(_, _))
          .log("of the eta-shaped pattern")
      )
    )

  property(
    "an instruction nested thousands deep is spelled and folded as it is",
    _.copy(testLimit = hedgehog.core.SuccessCount(5))
  ) {
    for levels <- instructionLevels.forAll
    yield
      val term = nestedInstruction(levels)
      val folded = nestedFilling(levels)
      Result.all(
        List(
          Result
            .diff(BindingNormalForm.spelled(term), term)(Configured.same(_, _))
            .log("spelled"),
          Result.diff(rebuilt(folded), folded)(_ eq _).log("filling mapped")
        )
      )
  }

  property(
    "a thunk whose code is nested thousands deep is its own normal form",
    _.copy(testLimit = hedgehog.core.SuccessCount(5))
  ) {
    for levels <- codeLevels.forAll
    yield thunkLaws(nestedCode(levels))
  }

  property(
    "a thunk whose inner thunks are nested thousands deep is its own normal form",
    _.copy(testLimit = hedgehog.core.SuccessCount(5))
  ) {
    for levels <- codeLevels.forAll
    yield thunkLaws(nestedThunks(levels))
  }
