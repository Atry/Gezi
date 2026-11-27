package gezi.standardlibrary

import gezi.frontend.DeBruijnTerm
import gezi.frontend.DeBruijnTermOf
import gezi.frontend.Defunctionalization
import gezi.ir.Configured
import gezi.ir.NoFacts

/** A pseudo-random generator as a value, SplitMix64: each draw returns the
  * generator after it.
  */
final case class SplitMix(state: Long):

  /** The next 64 random bits. */
  def bits: (Long, SplitMix) =
    val next = state + 0x9e3779b97f4a7c15L
    val mixed = (next ^ (next >>> 30)) * 0xbf58476d1ce4e5b9L
    val further = (mixed ^ (mixed >>> 27)) * 0x94d049bb133111ebL
    (further ^ (further >>> 31), SplitMix(next))

  /** A number between 0 and 1, 1 excluded. */
  def fraction: (Double, SplitMix) =
    val (drawn, after) = bits
    ((drawn >>> 11).toDouble / (1L << 53).toDouble, after)

  /** An integer between the bounds, both included. */
  def between(low: Int, high: Int): (Int, SplitMix) =
    val (drawn, after) = bits
    (low + java.lang.Math.floorMod(drawn, (high - low + 1).toLong).toInt, after)

/** The port of `gezi/tests/defunctionalization_agreement.plt`: the agreement of
  * the front end with the finite terms of the Lean package `gezi/lean`, in five
  * tests, which the Prolog file's comment explains; here the Scala front end
  * (`Defunctionalization.thunkInstruction` and the library's compiler) takes
  * the place of the Prolog one.
  *
  * The first two compare the front end, every instruction replaced by the
  * finite term of its layer, with its Lean definition `thunkInstruction`, for
  * which Lean proves link (i) of D6 (`lean/README.md`, "Design decisions"): on
  * 100 random source programs over generated files, and on the term of every
  * such file. A file is a random closed term whose constants are the
  * instructions of the files drawn before it, so that its content is generated
  * rather than the library's. The third compares the defunctionalization of 100
  * random closed terms of the calculus with Lean's `defunctionalize`. The
  * fourth measures link (i) on the random source programs: Lean's `readback` of
  * the finite term is δ of the program. The fifth checks that the sides of the
  * prelude's lemmas in `LambdaJit/PreludeLemmas.lean` are the sides the index
  * holds. These tests compare the two definitions on the samples by running
  * them, and prove nothing beyond the samples.
  *
  * The samples are drawn as the Prolog file drew them, from a generator of this
  * file (`SplitMix`) seeded with the Prolog file's seed: SWI-Prolog's generator
  * is not reproduced, so the samples are other samples of the same
  * distribution.
  *
  * TODO (https://github.com/Atry/private-overlay/issues/1526; carried from
  * defunctionalization_agreement.plt): the second test also ran on the files of
  * the old HM baseline's library; it runs on the new HM baseline's library once
  * that exists.
  */
class DefunctionalizationAgreementTest
    extends gezi.generatedinputs.FailFastSuite:
  // Measured 2026-11-22 on 2 CPUs (contest.slice, CPUs 8 and 9, nice 10), the 1-minute load 10: the whole suite, its
  // fixtures included, 24.7 s for five tests, each of which starts `lake env lean` once.
  // FIXME: this suite exceeds the 3 s default; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(20, "s")

  import LeanFiniteTerms.*

  given NoFacts.type = NoFacts

  private type NoFactsTerm = Configured[NoFacts.type]

  private val sampleCount = 100

  private val sampleSeed = 20261007L

  private lazy val prelude = LibraryFiles.compiled(
    "corpora/compiler/prelude.lambdalattice",
    Vector.empty
  )

  private val fileCount = 8

  /** The generated files: each its instruction, its name and its de Bruijn
    * term, a closed term drawn as a sample is (`sample`) whose constants are
    * the instructions of the files before it, the first one's none.
    */
  private lazy val files
      : Vector[(NoFactsTerm, String, DeBruijnTermOf[NoFactsTerm])] =
    (0 until fileCount)
      .foldLeft(
        (
          Vector.empty[(NoFactsTerm, String, DeBruijnTermOf[NoFactsTerm])],
          SplitMix(sampleSeed + 1)
        )
      ) { case ((made, random), index) =>
        val shape = if made.isEmpty then Shape.Calculus
        else Shape.Source(made.map(_._1).distinct)
        val (term, after) = sample(shape, random)
        (
          made :+ (
            Defunctionalization.thunkInstruction[NoFacts.type](term),
            s"file_$index",
            term
          ),
          after
        )
      }
      ._1

  /** The prelude's library, forced before the first test and not charged to it
    * (FailFastSuite).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => prelude, _ => files)

  // ---- the samples ----

  private enum Shape:
    case Calculus
    case Source(instructions: Vector[NoFactsTerm])

  private enum Kind:
    case Variable, Lambda, Apply, Choice, Parallel, Empty, Constant

  private def samples(shape: Shape): Vector[DeBruijnTermOf[NoFactsTerm]] =
    (0 until sampleCount)
      .foldLeft(
        (Vector.empty[DeBruijnTermOf[NoFactsTerm]], SplitMix(sampleSeed))
      ) { case ((drawn, random), _) =>
        val (term, after) = sample(shape, random)
        (drawn :+ term, after)
      }
      ._1

  /** Four fifths an abstraction around a body under one binder, the rest a term
    * under none; 1 to 30 nodes either way.
    */
  private def sample(
      shape: Shape,
      random: SplitMix
  ): (DeBruijnTermOf[NoFactsTerm], SplitMix) =
    val (draw, afterDraw) = random.fraction
    val (size, afterSize) = afterDraw.between(1, 30)
    if draw < 0.8 then
      val (body, after) = randomTerm(shape, 1, size, afterSize)
      (DeBruijnTerm.Lambda(body), after)
    else randomTerm(shape, 0, size, afterSize)

  /** The kinds to draw from, each as often as its weight: a variable only under
    * a binder, a compound only while the size is positive, top (`Literals.top`,
    * the term of no answer, in place of the empty choice) once the size is
    * spent and otherwise with probability 1/20, and, in a source program, a
    * constant always.
    */
  private def randomTerm(
      shape: Shape,
      depth: Int,
      size: Int,
      random: SplitMix
  ): (DeBruijnTermOf[NoFactsTerm], SplitMix) =
    val variables =
      if depth > 0 then Vector.fill(4)(Kind.Variable) else Vector.empty
    val compounds =
      if size > 0 then
        Vector(
          Kind.Lambda,
          Kind.Lambda,
          Kind.Lambda,
          Kind.Apply,
          Kind.Apply,
          Kind.Apply,
          Kind.Choice,
          Kind.Parallel
        )
      else Vector.empty
    val (draw, afterDraw) = random.fraction
    val empty =
      if size <= 0 || draw < 0.05 then Vector(Kind.Empty) else Vector.empty
    val constants = shape match
      case Shape.Calculus  => Vector.empty
      case Shape.Source(_) => Vector(Kind.Constant)
    val drawn = variables ++ compounds ++ empty ++ constants
    val kinds = if drawn.isEmpty then Vector(Kind.Lambda) else drawn
    val (position, afterKind) = afterDraw.between(0, kinds.size - 1)
    termOfKind(kinds(position), shape, depth, size, afterKind)

  private def termOfKind(
      kind: Kind,
      shape: Shape,
      depth: Int,
      size: Int,
      random: SplitMix
  ): (DeBruijnTermOf[NoFactsTerm], SplitMix) = kind match
    case Kind.Variable =>
      val (index, after) = random.between(0, depth - 1)
      (DeBruijnTerm.Variable(index), after)
    case Kind.Lambda =>
      val (body, after) = randomTerm(shape, depth + 1, size - 1, random)
      (DeBruijnTerm.Lambda(body), after)
    case Kind.Apply =>
      val (function, argument, after) = randomSplit(shape, depth, size, random)
      (DeBruijnTerm.Apply(function, argument), after)
    case Kind.Choice =>
      shape match
        case Shape.Calculus =>
          val (left, right, after) = randomSplit(shape, depth, size, random)
          (DeBruijnTerm.Choice(left, right), after)
        case Shape.Source(_) =>
          val (count, afterCount) = random.between(1, 4)
          val (members, after) =
            randomMembers(count, shape, depth, size - 1, afterCount)
          (DeBruijnTerm.nestedChoice(members), after)
    case Kind.Parallel =>
      val (left, right, after) = randomSplit(shape, depth, size, random)
      (DeBruijnTerm.Parallel(left, right), after)
    case Kind.Empty    => (gezi.frontend.Literals.top, random)
    case Kind.Constant =>
      shape match
        case Shape.Source(instructions) =>
          val (position, after) = random.between(0, instructions.size - 1)
          (DeBruijnTerm.Constant(instructions(position)), after)
        case Shape.Calculus =>
          throw IllegalStateException("a term of the calculus has no constant")

  /** Two terms whose sizes add up to the size less one. */
  private def randomSplit(
      shape: Shape,
      depth: Int,
      size: Int,
      random: SplitMix
  ): (DeBruijnTermOf[NoFactsTerm], DeBruijnTermOf[NoFactsTerm], SplitMix) =
    val (leftSize, afterSize) = random.between(0, size - 1)
    val (left, afterLeft) = randomTerm(shape, depth, leftSize, afterSize)
    val (right, after) =
      randomTerm(shape, depth, size - 1 - leftSize, afterLeft)
    (left, right, after)

  /** The count terms whose sizes add up to the size. */
  private def randomMembers(
      count: Int,
      shape: Shape,
      depth: Int,
      size: Int,
      random: SplitMix
  ): (Vector[DeBruijnTermOf[NoFactsTerm]], SplitMix) =
    if count == 1 then
      val (member, after) = randomTerm(shape, depth, size, random)
      (Vector(member), after)
    else
      val (memberSize, afterSize) = random.between(0, size)
      val (member, afterMember) =
        randomTerm(shape, depth, memberSize, afterSize)
      val (rest, after) =
        randomMembers(count - 1, shape, depth, size - memberSize, afterMember)
      (member +: rest, after)

  private lazy val sourceSamples: Vector[DeBruijnTermOf[NoFactsTerm]] =
    samples(Shape.Source(files.map(_._1).distinct))

  // ---- the front end ----

  /** The finite term of the front end's instruction of the program. */
  private def solvedText(program: DeBruijnTermOf[NoFactsTerm]): String =
    finiteText(Defunctionalization.thunkInstruction[NoFacts.type](program))

  /** The instructions the programs reach, each after the instructions its
    * file's term reaches (`source_definitions/4`), with the identifier and the
    * program of the first generated file of the instruction whose term is not
    * the constant of the instruction.
    */
  private def sourceDefinitions(
      programs: Vector[DeBruijnTermOf[NoFactsTerm]]
  ): Vector[(NoFactsTerm, String, DeBruijnTermOf[NoFactsTerm])] =
    def file(
        instruction: NoFactsTerm
    ): (NoFactsTerm, String, DeBruijnTermOf[NoFactsTerm]) =
      files
        .find((found, _, term) =>
          Configured.same(found, instruction) && term != DeBruijnTerm.Constant(
            instruction
          )
        )
        .getOrElse(
          throw IllegalStateException(s"no generated file at $instruction")
        )
    def constants(term: DeBruijnTermOf[NoFactsTerm]): Vector[NoFactsTerm] =
      term match
        case DeBruijnTerm.Constant(instruction) => Vector(instruction)
        case DeBruijnTerm.Free(name)            =>
          throw IllegalArgumentException(s"a free name $name in a program")
        case DeBruijnTerm.Variable(_)               => Vector.empty
        case DeBruijnTerm.Lambda(body)              => constants(body)
        case DeBruijnTerm.Apply(function, argument) =>
          constants(function) ++ constants(argument)
        case DeBruijnTerm.Choice(left, right) =>
          constants(left) ++ constants(right)
        case DeBruijnTerm.Parallel(left, right) =>
          constants(left) ++ constants(right)
    def reached(
        term: DeBruijnTermOf[NoFactsTerm],
        known: Vector[NoFactsTerm]
    ): Vector[NoFactsTerm] =
      constants(term).foldLeft(known)((current, instruction) =>
        if current.exists(Configured.same(_, instruction)) then current
        else reached(file(instruction)._3, current) :+ instruction
      )
    val instructions = programs.foldLeft(Vector.empty[NoFactsTerm])(
      (known, program) => reached(program, known)
    )
    val definitions = instructions.map(instruction =>
      val (_, name, term) = file(instruction)
      (instruction, lowerCamelCase(s"generated_$name"), term)
    )
    assert(
      definitions.map(_._2).distinct.size == definitions.size,
      "lean_identifiers_collide"
    )
    definitions

  /** The programs on which the front end and Lean's `thunkInstruction` give
    * different texts, with both texts; `lake` is stopped when `stopped`
    * completes.
    */
  private def frontEndDisagreements(
      programs: Vector[DeBruijnTermOf[NoFactsTerm]],
      stopped: scala.concurrent.Future[Unit]
  ): Vector[(Int, String, String)] =
    val definitions = sourceDefinitions(programs)
    val identifiers = definitions
      .map((instruction, identifier, _) => (instruction, identifier))
      .toMap
    val definitionsText = definitions
      .map((_, identifier, term) =>
        s"def $identifier : Program :=\n  ${sourceProgramLeanText(term, identifiers)}\n\n"
      )
      .mkString
    val program =
      s"""$definitionsText
         |def programs : List Program := [
         |  ${programs
          .map(sourceProgramLeanText(_, identifiers))
          .mkString(",\n  ")}]
         |
         |def main : IO Unit := do
         |  for program in programs do
         |    match thunkInstruction program with
         |    | some finite => IO.println (finiteText finite)
         |    | none => IO.println "none"
         |
         |#eval main
         |""".stripMargin
    val leans = leanLines("LambdaJit.Defunctionalization", program, stopped)
    assertEquals(leans.size, programs.size, "lean_printed_other_lines")
    programs.map(solvedText).zip(leans).zipWithIndex.collect {
      case ((scala, lean), index) if scala != lean => (index, scala, lean)
    }

  /** The texts of the lines `lean(Index, Text).` Lean printed, in order. */
  private def indexedTexts(lines: Vector[String]): Vector[String] =
    lines.zipWithIndex.map((line, index) =>
      val prefix = s"lean($index, "
      if line.startsWith(prefix) && line.endsWith(").") then
        line.drop(prefix.length).dropRight(2)
      else fail(s"lean_printed_unexpected_line($index, $line)")
    )

  /** δ of link (i) of D6: the program with every constant replaced by δ of its
    * generated file's term, as a de Bruijn term in the Prolog syntax Lean's
    * `termText` writes.
    */
  private def deltaText(program: DeBruijnTermOf[NoFactsTerm]): String =
    program match
      case DeBruijnTerm.Variable(index) => s"variable($index)"
      case DeBruijnTerm.Lambda(body)    => s"lambda(${deltaText(body)})"
      case DeBruijnTerm.Apply(function, argument) =>
        s"apply(${deltaText(function)},${deltaText(argument)})"
      case DeBruijnTerm.Parallel(left, right) =>
        s"parallel(${deltaText(left)},${deltaText(right)})"
      case DeBruijnTerm.Choice(left, right) =>
        s"choice([${deltaText(left)},${deltaText(right)}])"
      case DeBruijnTerm.Constant(instruction) =>
        val (_, _, term) = files
          .find((found, _, term) =>
            Configured.same(found, instruction) && term != DeBruijnTerm
              .Constant(instruction)
          )
          .getOrElse(
            throw IllegalStateException(s"no generated file at $instruction")
          )
        deltaText(term)
      case DeBruijnTerm.Free(name) =>
        throw IllegalArgumentException(s"a free name $name in a program")

  stoppableTest("theLeanFrontEndIsThePrologFrontEndOnRandomSourcePrograms") {
    stopped =>
      assertEquals(sourceSamples.size, sampleCount)
      assertEquals(frontEndDisagreements(sourceSamples, stopped), Vector.empty)
  }

  stoppableTest("theLeanFrontEndIsThePrologFrontEndOnTheGeneratedFiles") {
    stopped =>
      val programs = files.map(_._3)
      assert(programs.nonEmpty)
      assertEquals(frontEndDisagreements(programs, stopped), Vector.empty)
  }

  stoppableTest("prologAndLeanAgreeOnRandomClosedTerms") { stopped =>
    val calculusSamples = samples(Shape.Calculus)
    assertEquals(calculusSamples.size, sampleCount)
    val program =
      s"""def samples : List Term := [
         |  ${calculusSamples.map(calculusLeanText).mkString(",\n  ")}]
         |
         |def main : IO Unit := do
         |  let mut index := 0
         |  for sample in samples do
         |    match defunctionalize sample with
         |    | some finite => IO.println s!"lean({index}, {finiteText finite})."
         |    | none => IO.println s!"lean({index}, none)."
         |    index := index + 1
         |
         |#eval main
         |""".stripMargin
    val leans =
      indexedTexts(leanLines("LambdaJit.Defunctionalization", program, stopped))
    assertEquals(leans.size, sampleCount)
    val disagreements = calculusSamples.zip(leans).zipWithIndex.collect {
      case ((sample, lean), index)
          if finiteText(
            Defunctionalization.thunkInstruction[NoFacts.type](sample)
          ) != lean =>
        (index, sample, lean)
    }
    assertEquals(disagreements, Vector.empty)
  }

  stoppableTest("readbackOfSourceProgramsIsDelta") { stopped =>
    // The generated files that share an instruction have one δ (prelude_terms/1).
    files.foreach((instruction, name, term) =>
      assertEquals(
        deltaText(term),
        deltaText(DeBruijnTerm.Constant(instruction)),
        s"files_of_one_handle_differ($name)"
      )
    )
    assertEquals(sourceSamples.size, sampleCount)
    val finiteTerms =
      sourceSamples.map(Defunctionalization.thunkInstruction[NoFacts.type](_))
    val program =
      s"""partial def termText : Term → String
         |  | .boundVariable index => s!"variable({index})"
         |  | .abstraction body => s!"lambda({termText body})"
         |  | .application function argument => s!"apply({termText function},{termText argument})"
         |  | .choice left right => s!"choice([{termText left},{termText right}])"
         |  | .parallel left right => s!"parallel({termText left},{termText right})"
         |
         |def finiteTerms : List FiniteTerm := [
         |  ${finiteTerms.map(finiteLeanText).mkString(",\n  ")}]
         |
         |def main : IO Unit := do
         |  let mut index := 0
         |  for finiteTerm in finiteTerms do
         |    match LambdaJit.Readback.readback finiteTerm with
         |    | some term => IO.println s!"lean({index}, {termText term})."
         |    | none => IO.println s!"lean({index}, none)."
         |    index := index + 1
         |
         |#eval main
         |""".stripMargin
    val readbacks =
      indexedTexts(leanLines("LambdaJit.Defunctionalization", program, stopped))
    assertEquals(readbacks.size, sampleCount)
    val disagreements = sourceSamples.zip(readbacks).zipWithIndex.collect {
      case ((sourceProgram, readback), index)
          if readback != deltaText(sourceProgram) =>
        (index, sourceProgram, readback)
    }
    assertEquals(disagreements, Vector.empty)
  }

  stoppableTest("theLeanPreludeSidesAreTheIndexSides") { stopped =>
    val sides = prelude.index.lemmaNames.collect {
      case LemmaNamed(identifier, name)
          if prelude.index.sides(identifier).isDefined =>
        val lemmaSides = prelude.index.sides(identifier).get
        (
          name,
          finiteText(lemmaSides.left),
          finiteText(lemmaSides.right)
        )
    }
    assert(sides.nonEmpty, "the prelude has no lemma with sides")
    val entries = sides.map((name, _, _) =>
      val identifier = lowerCamelCase(name)
      s"""("$name", LambdaJit.PreludeLemmas.${identifier}Left, LambdaJit.PreludeLemmas.${identifier}Right)"""
    )
    val program =
      s"""def sides : List (String × FiniteTerm × FiniteTerm) := [
         |  ${entries.mkString(",\n  ")}]
         |
         |#eval show IO Unit from do
         |  for (name, left, right) in sides do
         |    IO.println s!"sides({name}, {finiteText left}, {finiteText right})."
         |""".stripMargin
    val printed = leanLines("LambdaJit.PreludeLemmas", program, stopped)
    assertEquals(
      printed,
      sides.map((name, left, right) => s"sides($name, $left, $right).")
    )
  }
