package gezi.generatedinputs

import hedgehog.Gen
import snapshot4s.SnapshotConfig

/** Snapshot tests on generated inputs (`CONTRIBUTING.md`, "Tests"): where the
  * expected output is as complex as the implementation, the test records
  * generated inputs together with their outputs in one snapshot file, so that a
  * change of the implementation shows as a diff of outputs beside their inputs.
  *
  * The inputs are `SeededSamples.samples` of the generator from a fixed seed,
  * so the file is the same on every run and every machine; changing the seed,
  * the count or the generator changes the inputs, and the diff then shows new
  * inputs, to be reviewed as rule 2 says.
  */
trait SeededSnapshots extends snapshot4s.munit.SnapshotAssertions:
  self: munit.FunSuite =>

  /** The samples of the generator from the seed, each rendered with its output
    * (`SeededSnapshots.text`), compared with the snapshot file at the path,
    * relative to the snapshot directory of the calling test's project. Inline,
    * so that snapshot4s's macro sees the calling test's source file, from which
    * it finds that project's directories.
    */
  inline def assertSeededSnapshot[Input, Output](
      generator: Gen[Input],
      seed: Long,
      count: Int,
      snapshotPath: String
  )(renderInput: Input => String, renderOutput: Output => String)(
      function: Input => Output
  )(using SnapshotConfig): Unit =
    assertFileSnapshot(
      SeededSnapshots.text(generator, seed, count)(renderInput, renderOutput)(
        function
      ),
      snapshotPath
    )

/** The text of a seeded snapshot. */
object SeededSnapshots:

  /** The samples of the generator from the seed (`SeededSamples.samples`), each
    * an entry: a header line with the sample's position, the input's rendering,
    * a line `=>`, and the output's rendering; entries are separated by an empty
    * line.
    */
  def text[Input, Output](generator: Gen[Input], seed: Long, count: Int)(
      renderInput: Input => String,
      renderOutput: Output => String
  )(function: Input => Output): String =
    SeededSamples
      .samples(generator, seed, count)
      .zipWithIndex
      .map((input, position) =>
        s"# sample $position\n${renderInput(input)}\n=>\n${renderOutput(function(input))}\n"
      )
      .mkString("\n")
