package com.yang_bo.gezi.proofs

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import com.yang_bo.gezi.standardlibrary.LeanFiniteTerms
import com.yang_bo.gezi.standardlibrary.LibraryFiles
import scala.concurrent.Future
import scala.jdk.StreamConverters.*
import scala.util.Using

/** The files the proof tests read, the opentheory tool and the reading of
  * Lean's output, shared by the suites of this module.
  */
object ProofTestFiles:

  /** The monorepo's root, above Gezi's build. */
  val repository: Path = LibraryFiles.buildRoot.getParent

  /** The tests of Gezi. */
  val testDirectory: Path = LibraryFiles.buildRoot.resolve("tests")

  /** The expected articles. */
  val expectedDirectory: Path =
    testDirectory.resolve("opentheory_article_expected")

  /** The Lean package's modules. */
  val leanModules: Path = LeanFiniteTerms.leanDirectory.resolve("LambdaJit")

  def expectedFile(base: String): Path = expectedDirectory.resolve(s"$base.art")

  def textRead(file: Path): String =
    Files.readString(file, StandardCharsets.UTF_8)

  /** The exit status and the standard error of the checker
    * `check_opentheory_article.sh`, Joe Leslie-Hurd's opentheory tool, on the
    * article file; its standard output, the theory the article proves, is
    * discarded. The tool is on the dev shell's PATH.
    */
  def articleChecked(article: Path): (Int, String) =
    processRun(
      Vector(
        testDirectory.resolve("check_opentheory_article.sh").toString,
        article.toString
      )
    )

  /** The exit status and the standard error of the command the checker runs,
    * `opentheory info --inference article:FILE`, run directly, as the Prolog
    * tests' `tool_checked/1` ran it: the tool accepts the article when it exits
    * with 0 and writes nothing on standard error.
    *
    * The checks that require nothing on standard error run the tool directly,
    * not through the checker: the checker starts with `#!/usr/bin/env bash`,
    * and the host's `/usr/bin/env`, linked against glibc 2.42, cannot load the
    * dev shell's audit library `LD_AUDIT`, linked against glibc 2.44
    * (`undefined symbol: __pointer_chk_guard, version GLIBC_PRIVATE`), so ld.so
    * writes a warning on standard error before `env` starts bash and the tool
    * (measured 2026-10-31; the tool's own output is unaffected). The Prolog
    * tests ran the tool directly too.
    */
  def toolChecked(article: Path): (Int, String) =
    processRun(Vector("opentheory", "info", "--inference", s"article:$article"))

  private def processRun(command: Vector[String]): (Int, String) =
    val errors = Files.createTempFile("opentheory", ".err")
    val status = ProcessBuilder(command*)
      .redirectOutput(ProcessBuilder.Redirect.DISCARD)
      .redirectError(errors.toFile)
      .start()
      .waitFor()
    val errorText = textRead(errors)
    Files.delete(errors)
    (status, errorText)

  /** The article text with its first or its last line `sym` deleted, written to
    * a temporary file, checked: the exit status and the standard error.
    */
  def checkedWithoutSym(text: String, last: Boolean): (Int, String) =
    val lines = text.split("\n", -1).toVector
    val position =
      if last then lines.lastIndexOf("sym") else lines.indexOf("sym")
    require(position >= 0, "the article has no sym")
    val mutant = Files.createTempFile("opentheory_mutated", ".art")
    Files.writeString(
      mutant,
      lines.patch(position, Vector.empty, 1).mkString("\n"),
      StandardCharsets.UTF_8
    )
    try toolChecked(mutant)
    finally Files.delete(mutant)

  /** The article text written to a temporary file and checked. */
  def textChecked(text: String): (Int, String) =
    val file = Files.createTempFile("opentheory_article", ".art")
    Files.writeString(file, text, StandardCharsets.UTF_8)
    try toolChecked(file)
    finally Files.delete(file)

  /** The names of the files of the directory, sorted. */
  def entries(directory: Path): Vector[String] =
    Using.resource(Files.list(directory))(
      _.toScala(Vector).map(_.getFileName.toString).sorted
    )

  /** The axioms of Lean's core library that the end-to-end theorem depends on
    * (module EndToEndAxioms), sorted.
    */
  val builtInAxioms: Vector[String] =
    Vector("propext", "Classical.choice", "Quot.sound").sorted

  /** Lean's output with every run of spaces and line ends written as one space,
    * so that a message wrapped over several lines reads as one line.
    */
  def normalisedOutput(output: String): String =
    output.split("[ \n]+").toVector.filter(_.nonEmpty).mkString(" ")

  /** Where the message of `#print axioms` for the theorem, a full name, begins
    * in the normalised output, how long it is, and the text between its
    * brackets. Throws when Lean printed none.
    */
  def axiomsMessage(normalised: String, theorem: String): (Int, Int, String) =
    val head = s"'$theorem' depends on axioms: ["
    val before = normalised.indexOf(head)
    val start = before + head.length
    val close = if before < 0 then -1 else normalised.indexOf("]", start)
    if before < 0 || close < 0 then
      throw IllegalStateException(
        s"no axioms printed for $theorem in $normalised"
      )
    (before, close + 1 - before, normalised.substring(start, close))

  /** The axioms the output lists for the theorem, sorted. */
  def printedAxioms(normalised: String, theorem: String): Vector[String] =
    axiomsMessage(normalised, theorem)._3.split(",").toVector.map(_.trim).sorted

  /** The normalised output without the `#print axioms` message of each theorem:
    * what else Lean printed, "" when nothing.
    */
  def otherOutput(normalised: String, theorems: Vector[String]): String =
    theorems
      .foldLeft(normalised)((text, theorem) =>
        val (before, length, _) = axiomsMessage(text, theorem)
        text.substring(0, before) + text.substring(before + length)
      )
      .split("\\s+")
      .toVector
      .filter(_.nonEmpty)
      .mkString(" ")

  /** Lean's output of `lake env lean` on the text, written to a temporary file,
    * after `lake build` of the targets, the whole package when there is none.
    * Throws with the output when either exits with a status other than 0. Each
    * `lake` is stopped when `stopped` completes (`LeanFiniteTerms.lakeOutput`).
    */
  def leanRun(
      text: String,
      stem: String,
      targets: Seq[String],
      stopped: Future[Unit]
  ): String =
    LeanFiniteTerms.lakeOutput("build" +: targets, stopped)
    val file = Files.createTempFile(stem, ".lean")
    Files.writeString(file, text, StandardCharsets.UTF_8)
    try LeanFiniteTerms.lakeOutput(Seq("env", "lean", file.toString), stopped)
    finally Files.delete(file)

  /** The tokens of a Lean term after the line begun so far, separated by
    * spaces, a line ending before it would pass 100 columns, the next one
    * indented by four spaces (`tokens_filled/3` of tests/lean_finite_terms.pl).
    */
  @scala.annotation.tailrec
  def tokensFilled(
      tokens: List[String],
      current: String,
      done: Vector[String]
  ): Vector[String] = tokens match
    case Nil           => done :+ current
    case token :: rest =>
      if current == "  " || current == "    " then
        tokensFilled(rest, current + token, done)
      else if length(current) + 1 + length(token) <= 100 then
        tokensFilled(rest, s"$current $token", done)
      else tokensFilled(rest, "    " + token, done :+ current)

  /** The number of characters of the text. */
  def length(text: String): Int = text.codePointCount(0, text.length)
