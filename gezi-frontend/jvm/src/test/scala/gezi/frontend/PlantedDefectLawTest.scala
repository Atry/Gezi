package gezi.frontend

import hedgehog.Result
import gezi.generatedinputs.PlantedDefects
import gezi.generatedinputs.GeneratedProperties
import scala.util.Try

/** The laws that a malformed input with one planted defect is rejected with the
  * reason the defect predicts (`PlantedDefects`), whose purpose is to catch an
  * error reported at the wrong offset (counted in bytes or UTF-16 units instead
  * of code points, or after skipping the layout), of the wrong kind (a syntax
  * error where the name is unbound), or not at all (a read-back that accepts a
  * thunk whose code reads a slot it lacks, or whose fillings are short).
  */
class PlantedDefectLawTest extends GeneratedProperties:

  given gezi.ir.NoFacts.type = gezi.ir.NoFacts

  // TODO: defines and instructions stood here, the library names of the generated terms and their opaque instructions, with
  // which `rejection` converted a text's free names. They named library terms by Term.define leaves and a map of
  // names to instructions, a free variable (blacklisted) and a table of library files deleted when the library became files reached by paths.
  // The generated terms now have no free name, so
  // `rejection` reads a text closed. The deleted code:
  // git show 2908bffd5:lambda_jit/frontend/src/test/scala/lambdajit/frontend/PlantedDefectLawTest.scala.

  /** The problem of reading the closed text and converting it. */
  private def rejection(text: String): Option[LambdalatticeProblem] =
    Try(
      Defunctionalization.thunkInstruction(Lambdalattice.term(text))(using
        gezi.ir.NoFacts
      )
    ).failed.toOption
      .collect { case LambdalatticeMalformed(problem) => problem }

  property(
    "a text with an unexpected character is rejected at that character"
  ) {
    for malformed <- PlantedDefects.unexpectedCharacter.forAll
    yield Result.diff(rejection(malformed.text), Some(malformed.expected))(
      _ == _
    )
  }

  // TODO: the property "a text with an unbound name is rejected for that name" stood here. Its purpose: catch an
  // unbound name reported as a syntax error, or not at all. It named library terms by PlantedDefects.unboundName,
  // whose generated terms used Term.define leaves of library names, a free variable (blacklisted) and a table of
  // library files deleted when the library became files reached by paths. Its replacement
  // generates lambdalattice text with the free name directly. The deleted code:
  // git show 2908bffd5:lambda_jit/frontend/src/test/scala/lambdajit/frontend/PlantedDefectLawTest.scala.

  property("a thunk with a planted defect is rejected for it when read back") {
    for (instruction, defect) <- PlantedDefects.malformedThunk.forAll
    yield
      val reason = Try(
        Defunctionalization.instructionTerm(instruction)
      ).failed.toOption.collect { case LambdaError(reason) =>
        reason
      }
      val expected = defect match
        case PlantedDefects.ThunkDefect.SlotOutOfRange =>
          reason.exists(_.isInstanceOf[LambdaErrorReason.SlotOutOfRange])
        case PlantedDefects.ThunkDefect.MissingFilling =>
          reason.exists(_.isInstanceOf[LambdaErrorReason.FillingsNotMatched])
      Result.assert(expected).log(s"rejected with $reason")
  }
