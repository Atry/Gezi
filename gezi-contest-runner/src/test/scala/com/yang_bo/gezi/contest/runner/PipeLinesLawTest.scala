package com.yang_bo.gezi.contest.runner

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.contest.entry.Cells
import com.yang_bo.gezi.contest.entry.Count
import com.yang_bo.gezi.contest.entry.OutputDisplay
import com.yang_bo.gezi.contest.entry.Phase
import com.yang_bo.gezi.contest.entry.Report
import com.yang_bo.gezi.frontend.ExchangeText
import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.hotspot.LifecycleEvent
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts

private given pipeLinesLawTestNoFacts: NoFacts.type = NoFacts

/** The laws that the supervisor's side and the runner's side of the pipe read
  * each other's lines: `cellRead` reads a point's line (`evaluationLine`,
  * `judgmentLine`) as the point's cell, and `answerRead` inverts `answerLine`,
  * on generated closed programs and candidates, displays (a closed pure term or
  * a choice of several) and phases (none or several), and no line holds a
  * newline. Its purpose is to catch a field lost or reordered when the pipe's
  * two sides were split between the judge and the runner.
  *
  * A third law: a line whose first field is not `answer` is no answer. Its
  * purpose is to catch a reader that takes a message the JVM writes on the pipe
  * (such as the one `-XX:+ExitOnOutOfMemoryError` writes) for an answer; the
  * lines are made of the answer lines' own words, so that only the prefix tells
  * them apart.
  *
  * A fourth law: an answer line whose phases field is malformed (a field
  * `phasesField` cannot write, made by corrupting one it wrote) is no answer.
  * Its purpose is to catch a reader that trusts an untrusted process's phases
  * field, or takes a malformed one for no phases.
  *
  * A fifth law: `receivedRead` reads a lifecycle line as its event, a point's
  * line, of any name, `lifecycle` and `cancel` included, as its cell, and the
  * cancel line as the cancel. Its purpose is to catch a runner that takes one
  * kind of line for another, which would lose a cell, hand the entry an event
  * the supervisor did not send, or stop a call no cancel asked to stop.
  */
class PipeLinesLawTest extends GeneratedProperties:

  private val pureTerm =
    HoasGenerators.closedTerm.map(_.deBruijnTerm(Map.empty))

  /** A phase of a name of lowercase letters and underscores, its seconds with
    * at most six decimals, as the answer line writes them.
    */
  private val phase: Gen[Phase] =
    for
      name <- Gen.string(Gen.element1('_', ('a' to 'z')*), Range.linear(1, 12))
      microseconds <- Gen.long(Range.linear(0L, 600000000L))
    yield Phase(name, microseconds / 1e6)

  /** A count of a name of lowercase letters and underscores. */
  private val count: Gen[Count] =
    for
      name <- Gen.string(Gen.element1('_', ('a' to 'z')*), Range.linear(1, 12))
      value <- Gen.long(Range.linear(0L, Long.MaxValue))
    yield Count(name, value)

  /** A report: a phase or a count. */
  private val report: Gen[Report] =
    Gen.choice1(phase.map(identity[Report]), count.map(identity[Report]))

  /** The display of the normal forms the term holds as its choice's members,
    * read as Scott ADT values.
    */
  private def normalFormsDisplay(
      term: DeBruijnTerm
  ): OutputDisplay[NoFacts.type] =
    given com.yang_bo.gezi.ir.StorageAccess =
      com.yang_bo.gezi.weakhead.ReadingConfiguration.withoutFacts.storageAccess
    OutputDisplay.Values(
      com.yang_bo.gezi.weakhead.ScottADTChoices
        .ofNormalForm(
          com.yang_bo.gezi.frontend.Defunctionalization.thunkInstruction[NoFacts.type](term)
        )
        .getOrElse(
          throw IllegalArgumentException(
            s"the term is no Scott ADT value: $term"
          )
        )
    )

  /** A display: no normal form, a closed pure term, or a choice of two or three
    * of them.
    */
  private val display: Gen[OutputDisplay[NoFacts.type]] = Gen.choice1(
    Gen.constant(OutputDisplay.noScottADTValue[NoFacts.type]),
    pureTerm.map(OutputDisplay.shown),
    pureTerm
      .list(Range.linear(2, 3))
      .map(members =>
        normalFormsDisplay(DeBruijnTerm.nestedChoice(members.toVector))
      )
  )

  /** Its purpose is to catch a runner that builds another cell than the one the
    * judge built before it sent programs as their lines: the cell of an
    * evaluation, `λs.λk. k s p`, and of a judgment, `λs.λk. k s (N ∥ p)`, the
    * Output a constant (`Cells.cell`) converted as it is, the same interned
    * instruction as the cell built from the program's and the candidate's
    * lines; read with its Output a constant of the very program written, or a
    * parallel of the candidate's and the program's constants, which an entry
    * tells a judgment by, and with the same instruction as the full readback
    * gives; a name read back, and no newline in the line.
    */
  property(
    "a point's line reads as the point's cell, its Output a constant of the program"
  ) {
    for
      program <- pureTerm.forAll
      candidate <- pureTerm.forAll
      judged <- Gen.boolean.forAll
    yield
      val programInstruction =
        Defunctionalization.thunkInstruction(program)(using com.yang_bo.gezi.ir.NoFacts)
      val candidateInstruction =
        Defunctionalization.thunkInstruction(candidate)(using com.yang_bo.gezi.ir.NoFacts)
      val output =
        if judged then
          NoFacts.parallel(candidateInstruction, programInstruction)
        else programInstruction
      val expected =
        if judged then
          DeBruijnTerm.Parallel(
            DeBruijnTerm.Constant(candidateInstruction),
            DeBruijnTerm.Constant(programInstruction)
          )
        else DeBruijnTerm.Constant(programInstruction)
      val cell = Defunctionalization.thunkInstruction(
        Cells.cell(DeBruijnTerm.Constant(output))
      )(using com.yang_bo.gezi.ir.NoFacts)
      val written =
        if judged then
          PipeLines.judgmentLine(
            "point",
            ExchangeText.line(candidateInstruction),
            ExchangeText.line(programInstruction)
          )
        else
          PipeLines.evaluationLine(
            "point",
            ExchangeText.line(programInstruction)
          )
      val (name, read) = PipeLines.cellRead(written)
      val readOutput = Cells.output(read, Cells.initialState)
      Result.all(
        List(
          Result.diff(name, "point")(_ == _),
          Result
            .assert(
              Defunctionalization.thunkInstruction(read)(using
                com.yang_bo.gezi.ir.NoFacts
              ) eq cell
            )
            .log("the cell read is not the cell the judge built"),
          Result
            .diff(readOutput, expected)(_ == _)
            .log("the Output of the cell read"),
          Result
            .assert(
              Defunctionalization.thunkInstruction(readOutput)(using
                com.yang_bo.gezi.ir.NoFacts
              ) eq output
            )
            .log("the Output's instruction is not the program written"),
          Result
            .diff(
              Defunctionalization.thunkInstruction(read)(using com.yang_bo.gezi.ir.NoFacts),
              Defunctionalization.thunkInstruction(
                Defunctionalization.instructionTerm(cell)
              )(using com.yang_bo.gezi.ir.NoFacts)
            )(_ == _)
            .log("the cell read and the full readback, as instructions"),
          Result.assert(!written.contains('\n'))
        )
      )
  }

  property(
    "a lifecycle line, a point's line and the cancel line are received as what they are"
  ) {
    for
      event <- Gen
        .element1(LifecycleEvent.values.head, LifecycleEvent.values.tail*)
        .forAll
      name <- Gen
        .element1("lifecycle", "point", "family_started", PipeLines.cancelLine)
        .forAll
      cell <- pureTerm.forAll
    yield Result.all(
      List(
        Result.diff(
          PipeLines.receivedRead(PipeLines.lifecycleLine(event)),
          PipeLines.Received.Lifecycle(event)
        )(_ == _),
        PipeLines.receivedRead(
          PipeLines.evaluationLine(
            name,
            ExchangeText.line(
              Defunctionalization.thunkInstruction(cell)(using com.yang_bo.gezi.ir.NoFacts)
            )
          )
        ) match
          case PipeLines.Received.Cell(read, readCell) =>
            Result.diff(
              (
                read,
                Defunctionalization.thunkInstruction(readCell)(using
                  com.yang_bo.gezi.ir.NoFacts
                )
              ),
              (
                name,
                PipeLines.pointCell(
                  Defunctionalization.thunkInstruction(cell)(using
                    com.yang_bo.gezi.ir.NoFacts
                  )
                )
              )
            )(_ == _)
          case other =>
            Result.failure.log(s"a point's line received as $other"),
        Result.diff(
          PipeLines.receivedRead(PipeLines.cancelLine),
          PipeLines.Received.Cancel
        )(_ == _)
      )
    )
  }

  property("an answer line reads back as its name, reports and display") {
    for
      answer <- display.forAll
      phases <- report.list(Range.linear(0, 4)).forAll
    yield
      val written = PipeLines.answerLine("point", phases.toVector, answer)
      Result.all(
        List(
          Result.diff(
            PipeLines.answerRead(written),
            PipeLines.AnswerRead.Answer("point", phases.toVector, answer)
          )(_ == _),
          Result.assert(!written.contains('\n'))
        )
      )
  }

  property("an answer line with a malformed phases field is no answer") {
    val corrupted: Gen[String => String] = Gen.element1[String => String](
      _ => "",
      field => field + ";",
      field => ";" + field,
      field => field.replaceFirst(":", ""),
      field => field + ":1.000000",
      field => "A" + field,
      field => "1" + field,
      field => field.dropRight(1),
      field => field + "0",
      field => field.replaceFirst(":", ":-"),
      field => field.takeWhile(_ != ':') + ":NaN",
      field => field.takeWhile(_ != ':') + ":Infinity",
      field => field + "\u0000"
    )
    for
      answer <- display.forAll
      phases <- phase.list(Range.linear(1, 4)).forAll
      corruption <- corrupted.forAll
    yield
      val field = corruption(PipeLines.phasesField(phases.toVector))
      val text = PipeLines
        .answerLine("point", Vector.empty, answer)
        .split("\t", -1)
        .toVector
        .updated(2, field)
        .mkString("\t")
      Result.diff(
        PipeLines.answerRead(text),
        PipeLines.AnswerRead.NotAnswer(text)
      )(_ == _)
  }

  /** The same law for a field of one count: a count corrupted into something
    * `phasesField` cannot write is no answer, never a count of another value or
    * a phase.
    */
  property("an answer line with a malformed count is no answer") {
    val corrupted: Gen[String => String] = Gen.element1[String => String](
      field => field.replaceFirst("#", ""),
      field => field.replaceFirst("#", "#-"),
      field => field + "#1",
      field => field + "a",
      field => "A" + field,
      field => field.takeWhile(_ != '#') + "#",
      field => field + "\u0000"
    )
    for
      answer <- display.forAll
      counted <- count.forAll
      corruption <- corrupted.forAll
    yield
      val field = corruption(PipeLines.phasesField(Vector(counted)))
      val text = PipeLines
        .answerLine("point", Vector.empty, answer)
        .split("\t", -1)
        .toVector
        .updated(2, field)
        .mkString("\t")
      Result.diff(
        PipeLines.answerRead(text),
        PipeLines.AnswerRead.NotAnswer(text)
      )(_ == _)
  }

  property("a line whose first field is not the prefix is no answer") {
    val firstField = Gen.element1(
      "Terminating due to java.lang.OutOfMemoryError: Java heap space",
      "OpenJDK 64-Bit Server VM warning: Options -Xverify:none have been deprecated",
      "answer ",
      "Answer",
      "lifecycle_done",
      "answers",
      "",
      "point"
    )
    val field = Gen.choice1(
      Gen.element1("answer", "point", "cell", "-", ""),
      pureTerm.map(term =>
        ExchangeText.line(
          Defunctionalization.thunkInstruction(term)(using com.yang_bo.gezi.ir.NoFacts)
        )
      )
    )
    for
      first <- firstField.forAll
      rest <- field.list(Range.linear(0, 4)).forAll
    yield
      val text = (first +: rest).mkString("\t")
      Result.diff(
        PipeLines.answerRead(text),
        PipeLines.AnswerRead.NotAnswer(text)
      )(_ == _)
  }
