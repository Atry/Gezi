package gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Files
import gezi.contest.entry.Phase
import gezi.generatedinputs.GeneratedProperties

/** The laws of the table file that `--reuse-table` reads back (`TableFile`): a
  * table written and read gives back its seed, provenance and rows, the phases
  * and the cancel of each row included, and an earlier table is refused unless
  * its points, programs, build and seed are the run's. Its purpose is to catch
  * a reader that reads a table other than the one written, which would put
  * another table's rows in a run's, and a check that lets a stale table
  * through.
  */
class TableFileLawTest extends GeneratedProperties:

  private val word: Gen[String] = Gen.string(Gen.lower, Range.linear(1, 12))

  private val digest: Gen[String] = Gen.string(
    Gen.element1('0', "123456789abcdef".toList*),
    Range.singleton(64)
  )

  /** A wall time with at most six decimals, as the table writes it. */
  private val seconds: Gen[Double] =
    Gen.long(Range.linear(0L, 600000000L)).map(_ / 1e6)

  /** A phase of a name of lowercase letters and underscores. */
  private val phase: Gen[Phase] =
    for
      name <- Gen.string(Gen.element1('_', ('a' to 'z')*), Range.linear(1, 12))
      taken <- seconds
    yield Phase(name, taken)

  private val row: Gen[Row] =
    for
      point <- word
      reader <- word
      family <- word
      kind <- Gen.element1("evaluation", "judgment", "-")
      outcome <- Gen.element1("correct", "wrong", "stopped", "ready")
      of <- Gen.int(Range.linear(1, 9))
      earned <- Gen.int(Range.linear(0, of))
      share = Share(earned, of)
      wall <- seconds
      familyWall <- seconds
      cores <- Gen.element1("8,9", "any", "0-1")
      exhausted <- Gen.boolean
      phases <- phase.list(Range.linear(0, 4))
      exitStatus <- Gen.int(Range.linear(0, 255))
      cancel <- Gen.element1(
        Cancel.NotSent,
        Cancel.Returned,
        Cancel.Killed,
        Cancel.Died(exitStatus)
      )
    yield Row(
      point,
      reader,
      family,
      kind,
      outcome,
      share,
      wall,
      familyWall,
      cores,
      exhausted,
      phases.toVector,
      cancel
    )

  private val provenance: Gen[TableProvenance] =
    for
      points <- digest
      programs <- Gen.choice1(digest, Gen.constant(TableFile.noPrograms))
      commit <- digest.map(_.take(40))
      dirty <- Gen.boolean
      reusedPath <- word
      reusedDigest <- digest
      withReused <- Gen.boolean
      referencesPath <- word
      referencesDigest <- digest
      withReferences <- Gen.boolean
    yield TableProvenance(
      points,
      programs,
      if dirty then s"$commit-dirty" else commit,
      Option.when(withReused)((s"/tmp/$reusedPath.tsv", reusedDigest)),
      Option.when(withReferences)(
        (s"/tmp/$referencesPath.tsv", referencesDigest)
      )
    )

  property(
    "a table written and read gives back its seed, provenance and rows"
  ) {
    for
      seed <- Gen
        .long(Range.linearFrom(0L, Long.MinValue, Long.MaxValue))
        .forAll
      written <- provenance.forAll
      rows <- row.list(Range.linear(0, 20)).forAll
    yield
      val path = Files.createTempFile("table", ".tsv")
      Files.writeString(path, Supervisor.table(seed, written, rows.toVector))
      Result.diff(
        TableFile.read(path),
        ReadTable(seed, written, rows.toVector)
      )(_ == _)
  }

  property(
    "an earlier table is reused only on the same points, programs, build and seed"
  ) {
    for
      seed <- Gen.long(Range.linear(0L, 1000L)).forAll
      earlier <- provenance.forAll
      rows <- row.list(Range.linear(0, 5)).forAll
      otherPoints <- digest.forAll
      otherPrograms <- Gen
        .choice1(digest, Gen.constant(TableFile.noPrograms))
        .forAll
    yield
      val table = ReadTable(seed, earlier, rows.toVector)
      val points = earlier.pointsDigest
      val programs = earlier.programsDigest
      val accepted = TableFile.reused(
        table,
        seed,
        points,
        programs,
        earlier.build
      ) == rows.toVector
      def refused(run: => Vector[Row]): Boolean =
        intercept[IllegalArgumentException](run)
        true
      Result.all(
        List(
          Result.assert(accepted),
          Result.assert(
            otherPoints == points || refused(
              TableFile
                .reused(table, seed, otherPoints, programs, earlier.build)
            )
          ),
          Result.assert(
            otherPrograms == programs || refused(
              TableFile
                .reused(table, seed, points, otherPrograms, earlier.build)
            )
          ),
          Result.assert(
            refused(
              TableFile
                .reused(table, seed, points, programs, earlier.build + "x")
            )
          ),
          Result.assert(
            refused(
              TableFile.reused(table, seed + 1, points, programs, earlier.build)
            )
          )
        )
      )
  }
