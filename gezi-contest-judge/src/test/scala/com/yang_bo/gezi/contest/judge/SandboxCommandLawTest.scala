package com.yang_bo.gezi.contest.judge

import com.yang_bo.gezi.contest.entry.ArticleDestination

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.io.File
import java.nio.file.Path
import java.nio.file.Paths
import com.yang_bo.gezi.generatedinputs.GeneratedProperties

/** The laws of the sandbox's command (`Supervisor.command`, `Sandbox`): in the
  * bubblewrap sandbox an entry's JVM binds exactly the readable paths
  * (`Sandbox.Bubblewrap`), its classpath's elements and its directory, each
  * read only at its own place, in new namespaces of every kind, dying with its
  * parent, and the runner is told to deny the execution of programs; with
  * `--sandbox none` there is no `bwrap` and the runner allows it; a reference
  * reader's JVM is never sandboxed; `--sandbox` takes `bubblewrap` or `none`
  * and nothing else. Its purpose is to catch a binding that creeps in (a parent
  * directory, the points directory, the build's root), a namespace dropped, or
  * the filter left off while the sandbox is on.
  */
class SandboxCommandLawTest extends GeneratedProperties:

  private val names: Gen[String] = Gen.string(Gen.lower, Range.linear(1, 8))

  private val paths: Gen[Path] =
    names.list(Range.linear(1, 4)).map(parts => Paths.get("/", parts*))

  private val placements: Gen[(Vector[Path], Vector[Path], Path)] =
    for
      readablePaths <- paths.list(Range.linear(1, 5))
      classpath <- paths.list(Range.linear(0, 6))
      entryDirectory <- paths
    yield (readablePaths.toVector, classpath.toVector, entryDirectory)

  private def limits(sandbox: Sandbox): Limits =
    Limits(
      FamilyBudgets(20, 60, 600),
      60,
      2,
      None,
      None,
      None,
      Paths.get("."),
      "256m",
      None,
      sandbox,
      ArticleDestination.Discarded,
      None
    )

  /** The bindings of a command, each source with its destination. */
  private def bindings(command: Vector[String]): Vector[(String, String)] =
    command.sliding(3).toVector.collect {
      case Vector(option, source, destination)
          if option == "--ro-bind" || option == "--ro-bind-try" =>
        (source, destination)
    }

  property(
    "in the bubblewrap sandbox an entry's JVM binds the readable paths, its classpath and its directory alone"
  ) {
    for (readablePaths, classpath, entryDirectory) <- placements.forAll
    yield
      val reader = Reader(
        "probe",
        classpath.mkString(File.pathSeparator),
        Launched.EntryLaunched(entryDirectory)
      )
      val command =
        Supervisor.command(reader, limits(Sandbox.Bubblewrap(readablePaths)))
      val bound = bindings(command)
      val expected =
        (readablePaths ++ classpath :+ entryDirectory).map(_.toString).toSet
      Result
        .diff(bound.map(_._1).toSet, expected)(_ == _)
        .and(
          Result.assert(
            bound.forall((source, destination) => source == destination)
          )
        )
        .and(Result.assert(command.headOption.contains("bwrap")))
        .and(
          Result.assert(
            Vector("--unshare-all", "--die-with-parent", "--new-session")
              .forall(command.contains)
          )
        )
        .and(
          Result.diff(
            command.takeRight(4),
            Vector(entryDirectory.toString, "denied", "discarded", "none")
          )(_ == _)
        )
  }

  /** A second law, for the article re-read: the writable paths are bound
    * writable at their own places, after every read-only binding and before the
    * root is made read only, and nothing else is bound writable. Its purpose is
    * to catch a writable binding that an earlier read-only one would cover, or
    * one that leaks to a scored pass, whose sandbox has none.
    */
  property(
    "in the bubblewrap sandbox the writable paths alone are bound writable, after the read-only bindings"
  ) {
    for
      (readablePaths, classpath, entryDirectory) <- placements.forAll
      writablePaths <- paths.list(Range.linear(0, 2)).forAll
    yield
      val reader = Reader(
        "probe",
        classpath.mkString(File.pathSeparator),
        Launched.EntryLaunched(entryDirectory)
      )
      val command = Supervisor.command(
        reader,
        limits(
          writablePaths.foldLeft(Sandbox.Bubblewrap(readablePaths): Sandbox)(
            _.writable(_)
          )
        )
      )
      val writable = command.sliding(3).toVector.zipWithIndex.collect {
        case (Vector("--bind", source, destination), position) =>
          (source, destination, position)
      }
      val lastReadOnly = command.lastIndexWhere(word =>
        word == "--ro-bind" || word == "--ro-bind-try"
      )
      Result
        .diff(
          writable.map((source, _, _) => source),
          writablePaths.map(_.toString).toVector
        )(_ == _)
        .and(
          Result.assert(
            writable.forall((source, destination, position) =>
              source == destination && position > lastReadOnly
            )
          )
        )
        .and(
          Result.assert(
            writable.forall((_, _, position) =>
              position < command.indexOf("--remount-ro")
            )
          )
        )
  }

  property(
    "with --sandbox none an entry's JVM has no bwrap and may execute programs"
  ) {
    for (_, classpath, entryDirectory) <- placements.forAll
    yield
      val reader = Reader(
        "probe",
        classpath.mkString(File.pathSeparator),
        Launched.EntryLaunched(entryDirectory)
      )
      val command = Supervisor.command(reader, limits(Sandbox.Unconfined))
      Result
        .assert(!command.contains("bwrap"))
        .and(
          Result.diff(
            command.takeRight(4),
            Vector(entryDirectory.toString, "allowed", "discarded", "none")
          )(_ == _)
        )
  }

  /** A law for the flight recordings: with `--flight-recordings` an entry's JVM
    * binds its own directory of recordings writable, puts the recorder's
    * repository there and hands the runner that directory; a reference reader's
    * JVM records nothing. Its purpose is to catch a recording that the sandbox
    * cannot write, or one that leaks to a reference reader.
    */
  property(
    "with --flight-recordings an entry's JVM writes into its own directory of recordings, and a reference reader's records nothing"
  ) {
    for
      (readablePaths, classpath, entryDirectory) <- placements.forAll
      recordings <- paths.forAll
    yield
      val recorded = limits(Sandbox.Bubblewrap(readablePaths))
        .copy(flightRecordings = Some(recordings))
      val reader = Reader(
        "probe",
        classpath.mkString(File.pathSeparator),
        Launched.EntryLaunched(entryDirectory)
      )
      val command = Supervisor.command(reader, recorded)
      val directory = recordings.resolve("probe").toString
      val reference = Supervisor.command(
        Reader(
          "tabling(weak_head)",
          "classes",
          Launched.ReferenceLaunched("tabling(weak_head)")
        ),
        recorded
      )
      Result
        .assert(
          command.sliding(3).contains(Vector("--bind", directory, directory))
        )
        .and(
          Result.assert(
            command.contains(
              s"-XX:FlightRecorderOptions=repository=$directory/repository"
            )
          )
        )
        .and(Result.diff(command.takeRight(1), Vector(directory))(_ == _))
        .and(
          Result.assert(
            !reference.exists(word =>
              word.startsWith("-XX:FlightRecorderOptions") || word == "--bind"
            )
          )
        )
        .and(
          Result.diff(reference.takeRight(1), Vector("tabling(weak_head)"))(
            _ == _
          )
        )
  }

  property("a reference reader's JVM is never sandboxed") {
    for
      (readablePaths, _, _) <- placements.forAll
      sandbox <- Gen
        .element1(Sandbox.Unconfined, Sandbox.Bubblewrap(readablePaths))
        .forAll
    yield
      val command =
        Supervisor.command(
          Reader(
            "tabling(weak_head)",
            "classes",
            Launched.ReferenceLaunched("tabling(weak_head)")
          ),
          limits(sandbox)
        )
      Result.assert(!command.contains("bwrap") && bindings(command).isEmpty)
  }

  property("--sandbox is bubblewrap or none") {
    for value <- names
        .filter(name => name != "bubblewrap" && name != "none")
        .forAll
    yield
      val thrown = intercept[IllegalArgumentException](
        SupervisorCommand.sandbox(Map("sandbox" -> value), Paths.get("."))
      )
      Result
        .assert(thrown.getMessage.contains("--sandbox"))
        .and(
          Result.assert(
            SupervisorCommand.sandbox(
              Map("sandbox" -> "none"),
              Paths.get(".")
            ) == Sandbox.Unconfined
          )
        )
  }
