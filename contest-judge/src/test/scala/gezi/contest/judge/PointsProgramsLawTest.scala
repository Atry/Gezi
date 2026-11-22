package gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import gezi.generatedinputs.GeneratedProperties
import scala.jdk.CollectionConverters.*

/** The laws of the programs file (`PointsFile`, `programs.tsv`), which holds
  * each judged program once while a judgment row refers to it by `@<name>`:
  *
  *   - a file written and read gives every point its source's program, the
  *     judgment points made from an evaluation point the program of that
  *     point and a judgment source its own, gives a judgment source back as
  *     it was given, and writes each judged program once. Its purpose is to
  *     catch a reference resolved to another point's program, which would
  *     ask an entry about the wrong program, and a program written once per
  *     row again, the layout whose size ran the writer out of heap;
  *   - a judgment row whose program column is not a reference, a reference
  *     to a program the programs file lacks, and a missing programs file are
  *     each refused, naming the points file and the row's line. Its purpose
  *     is to catch a file in the layout before the programs file, or a
  *     programs file lost in a copy, read as if it were whole.
  *
  * The sources are a repeated family drawn from a seed, with traps from a
  * second seed, `judgmentsOnly` drawn, and one judgment source per
  * evaluation source, its candidate the point's own program, so that every
  * input has judgment rows of both origins. An input is logged by its draw,
  * not by its points (`MemberJudgmentsLawTest`).
  */
class PointsProgramsLawTest extends GeneratedProperties:

  /** The parts of the law families' group the draws read, built once (`LawFamilies.sharedFixtures`). */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    super.sharedFixtures ++ LawFamilies.sharedFixtures

  // Measured 2026-11-19 at 552062eef (CPUs 10 and 11): the suite, two tests, takes 25.7 s alone and 27.2 s in
  // contest-judge/test at the 1-minute load 4.7 to 4.9, and 32.3 s in contest-judge/test at 5.4 with the law families'
  // fixtures built in `beforeAll`, which the suite's time includes. The draws differ from run to run. A passing test
  // reports no time of its own, so the bound is 1.5 times the longest, rounded up to 5 s.
  // Measured again 2026-11-20 (CPUs 0 to 7, the 1-minute load 2.4 to 2.9): 15.4 and 14.6 s in one JVM after
  // TrapJudgmentsLawTest and MemberJudgmentsLawTest, against 23.6 s before the first law read each written file once
  // (its coverage read the file, and its body read it again).
  // The cost is the draws' work, not a defect: by a JFR
  // profile of TrapJudgmentsLawTest that day (2,212 samples), writing the points file and reading it back, each linear
  // in the line: the parse, the contraction of the printer's bindings (each value converted once), the printer (at most
  // two passes); each point writes in its line the library it uses. The lexer's per-call compile, the one defect found,
  // was removed in b18f8f987.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(50, "s")


  /** The tabling(weak_head) steps the writer reads a reference within: small points
    * only.
    */
  private val writerBudget: Long = 200000

  /** A draw: a repeated family, its points' seed, a different trap seed,
    * the R values, small, whether the evaluation rows are left out, and the
    * expectation of each judgment source, by its index.
    */
  private final case class Draw(
      family: String,
      seed: Long,
      trapSeed: Long,
      repetitions: Vector[Int],
      judgmentsOnly: Boolean,
      members: Vector[Boolean]
  )

  private val draws: Gen[Draw] =
    for
      family <- Gen.elementUnsafe(LawFamilies.names)
      seed <- Gen.long(Range.constant(0L, (1L << 31) - 1))
      trapSeed <- Gen.long(Range.constant(0L, (1L << 31) - 1)).filter(_ != seed)
      repetitions <- LawFamilies.repetitions(family, 3, 2)
      judgmentsOnly <- Gen.boolean
      members <- Gen.boolean.list(Range.singleton(8))
    yield Draw(family, seed, trapSeed, repetitions, judgmentsOnly, members.toVector)

  private def evaluationSources(draw: Draw, seed: Long): Vector[PointSource.EvaluationSource] =
    LawFamilies.sources(draw.family, seed, draw.repetitions, "test", BigDecimal(1)).collect {
      case source: PointSource.EvaluationSource => source
    }

  /** One judgment source per evaluation source, named `<point>/given`, in
    * the family `<family>_given`, its candidate the point's program.
    */
  private def judgmentSources(draw: Draw, evaluations: Vector[PointSource.EvaluationSource]): Vector[PointSource.JudgmentSource] =
    evaluations.zipWithIndex.map((source, index) =>
      PointSource.JudgmentSource(
        s"${source.name}/given",
        source.stage,
        s"${source.family}_given",
        BigDecimal(3),
        source.program,
        source.program,
        draw.members(index % draw.members.size)
      )
    )

  /** The directory written from the draw, with its evaluation sources and
    * its judgment sources.
    */
  private def writtenDirectory(draw: Draw): (Path, Vector[PointSource.EvaluationSource], Vector[PointSource.JudgmentSource]) =
    val evaluations = evaluationSources(draw, draw.seed)
    val judgments = judgmentSources(draw, evaluations)
    val directory = Files.createTempDirectory("points-programs")
    PointsFile.written(
      directory,
      evaluations ++ judgments,
      writerBudget,
      Some(JudgmentPoints(BigDecimal(2), draw.judgmentsOnly, Some(TrapDraw(evaluationSources(draw, draw.trapSeed), 3))))
    )
    (directory, evaluations, judgments)

  private def logged(draw: Draw): String =
    s"${draw.family} seed ${draw.seed} trap seed ${draw.trapSeed} R ${draw.repetitions.mkString(",")} judgments only ${draw.judgmentsOnly}"

  private def isTrap(point: Point): Boolean = point.question match
    case Question.Judgment(_, false) => true
    case _                           => false

  /** The lines of a file of the directory. */
  private def lines(directory: Path, name: String): Vector[String] =
    Files.readAllLines(directory.resolve(name), StandardCharsets.UTF_8).asScala.toVector

  property("a file written and read gives each point its source's program, each judged program written once", _.copy(testLimit = 20)) {
    for
      written <- draws
        .forAllWithLog(logged)
        .map(draw =>
          val found = writtenDirectory(draw)
          (draw, found, PointsFile.read(found._1))
        )
        .cover(20, "writes a trap", (_, _, points) => points.exists(isTrap))
    yield
      val (draw, (directory, evaluations, judgments), points) = written
      val programs: Map[String, gezi.ir.Instruction] =
        (evaluations.map(source => source.name -> source.program) ++ judgments.map(source => source.name -> source.program))
          .map((name, program) => name -> PointsFile.closedTerm(program))
          .toMap
      val givenNames = judgments.map(_.name).toSet
      def owner(point: Point): String = point.question match
        case Question.Judgment(_, _) if !givenNames.contains(point.name) => point.name.substring(0, point.name.lastIndexOf("/candidate_"))
        case _                                                          => point.name
      val judged = points.collect { case point @ Point(_, _, _, _, _, Question.Judgment(_, _)) => owner(point) }.distinct
      val resolved = points.map(point =>
        Result.assert(programs.get(owner(point)).contains(point.program)).log(s"${point.name}: not the program of ${owner(point)}")
      )
      val givenBack = judgments.map(source =>
        Result.diff(
          points.find(_.name == source.name),
          Some(
            Point(
              source.name,
              source.stage,
              source.family,
              source.weight,
              PointsFile.closedTerm(source.program),
              Question.Judgment(PointsFile.closedTerm(source.candidate), source.member)
            )
          )
        )(_ == _)
      )
      val onlyJudgments = Result
        .assert(!draw.judgmentsOnly || points.forall(point => point.question match
          case Question.Judgment(_, _) => true
          case _                       => false
        ))
        .log("an evaluation point written with judgmentsOnly")
      val programRows = Result.diff(lines(directory, PointsFile.programsFileName).size - 1, judged.size)(_ == _).log("programs written")
      Result.all((resolved ++ givenBack :+ onlyJudgments :+ programRows).toList)
  }

  /** The tab-separated fields of a line. */
  private def columns(line: String): Vector[String] = line.split("\t", -1).toVector

  /** The positions of the points file's `kind` and `program` columns and of
    * the programs file's `term` column, from the headers.
    */
  private val kindColumn: Int = columns(PointsFile.header).indexOf("kind")
  private val programColumn: Int = columns(PointsFile.header).indexOf("program")
  private val termColumn: Int = columns(PointsFile.programsHeader).indexOf("term")

  /** A way to spoil a written directory, each named by what it does. */
  private enum Spoiling:
    case ProgramInline, ProgramRowRemoved, ProgramsFileRemoved

  property("a judgment row without its program is refused, naming the file and the line", _.copy(testLimit = 20)) {
    for
      draw <- draws.forAllWithLog(logged)
      spoiling <- Gen.elementUnsafe(Spoiling.values.toList).forAll
      choice <- Gen.int(Range.constant(0, 1000)).forAll
    yield
      val (directory, _, _) = writtenDirectory(draw)
      val points = directory.resolve(PointsFile.fileName)
      val programsFile = directory.resolve(PointsFile.programsFileName)
      val pointLines = lines(directory, PointsFile.fileName)
      val programLines = lines(directory, PointsFile.programsFileName)
      val judgmentLines = pointLines.zipWithIndex.drop(1).filter((line, _) => columns(line)(kindColumn) == "judgment")
      val (target, targetIndex) = judgmentLines(choice % judgmentLines.size)
      val reference = columns(target)(programColumn)
      val programRow = programLines.find(_.startsWith(s"${reference.drop(1)}\t"))
      val expectedLine = spoiling match
        case Spoiling.ProgramInline =>
          val inline = programRow.map(row => columns(row)(termColumn)).getOrElse("")
          Files.write(
            points,
            pointLines.updated(targetIndex, columns(target).updated(programColumn, inline).mkString("\t")).asJava,
            StandardCharsets.UTF_8
          )
          targetIndex + 1
        case Spoiling.ProgramRowRemoved =>
          Files.write(programsFile, programLines.filterNot(programRow.contains).asJava, StandardCharsets.UTF_8)
          judgmentLines.collectFirst { case (line, index) if columns(line)(programColumn) == reference => index + 1 }.getOrElse(0)
        case Spoiling.ProgramsFileRemoved =>
          Files.delete(programsFile)
          judgmentLines.headOption.map(_._2 + 1).getOrElse(0)
      val refusal = intercept[IllegalArgumentException](PointsFile.read(directory))
      Result
        .assert(refusal.getMessage.startsWith(s"$points:$expectedLine: "))
        .log(s"$spoiling: refused with ${refusal.getMessage.take(200)}, not at $points:$expectedLine")
  }
