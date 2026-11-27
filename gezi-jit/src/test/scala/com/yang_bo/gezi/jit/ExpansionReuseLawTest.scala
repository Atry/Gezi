package com.yang_bo.gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import scala.jdk.StreamConverters.*
import scala.util.Using
import com.yang_bo.gezi.directorysugar.DirectoryTree
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.hotspot.Budget
import com.yang_bo.gezi.hotspot.ExecutionDependencies
import com.yang_bo.gezi.hotspot.ExpansionSource
import com.yang_bo.gezi.hotspot.baselines.BaselineCaches
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.weakhead.Expansions
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.NoJitState
import com.yang_bo.gezi.weakhead.ReadingExecutor

/** The laws of reusing what was read through URI nodes (`Expansions`). The
  * first, a state machine over generated edits of a directory, each followed by
  * a new version of the contents, catches an expansion reused from a content
  * that has changed, and one built again from a content that has not. The
  * second catches an executor that drops its expansions between two calls under
  * one source. That an executor does not answer from a content that has changed
  * is the law of `ExpansionSourceLawTest`.
  */
class ExpansionReuseLawTest extends GeneratedProperties:

  /** The URI nodes and their expansions are read under no facts. */
  private given NoFacts.type = NoFacts

  private enum Operation:
    case Rewritten(numeral: Int)
    case OtherToggled
    case Untouched

  private val operations: Gen[List[Operation]] =
    Gen
      .frequency1(
        2 -> Gen.int(Range.constant(0, 3)).map(Operation.Rewritten(_)),
        1 -> Gen.constant(Operation.OtherToggled),
        3 -> Gen.constant(Operation.Untouched)
      )
      .list(Range.constant(2, 4))

  /** Under the project's `target`, not the system's temporary directory, which
    * other runs fill.
    */
  private val trees: Path = Files.createDirectories(
    Paths.get("target", "expansion-reuse-law").toAbsolutePath.normalize
  )

  private def budget(stop: StopSignal): Budget =
    Budget(2000000, countedUnits = false, stop)

  /** The result of the body on a new directory, removed with its files after
    * it.
    */
  private def inDirectory(prefix: String)(body: Path => Result): Result =
    val directory = Files.createTempDirectory(trees, prefix)
    try body(directory)
    finally
      Using
        .resource(Files.list(directory))(_.toScala(Vector))
        .foreach(Files.delete)
      Files.delete(directory)

  /** A directory and a file expanded once, so that the first test does not pay
    * the loading of the front end's classes inside its deadline.
    */
  private lazy val frontEndLoaded: Configured[NoFacts.type] =
    val directory = Files.createTempDirectory(trees, "loaded")
    val file = directory.resolve("member.lambdalattice")
    val _ = Files.writeString(file, text(1))
    val _ = DirectoryTree.expansion(node(directory))
    val loaded = DirectoryTree.expansion(node(file))
    Files.delete(file)
    Files.delete(directory)
    loaded

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => frontEndLoaded)

  private def text(numeral: Int): String =
    s"λtuple. tuple (λf x. ${"f (" * numeral}x${")" * numeral})\n"

  private def node(path: Path): Configured[NoFacts.type] =
    NoFacts.uri(path.toAbsolutePath.normalize.toUri)

  private def applied(operation: Operation, file: Path, other: Path): Unit =
    operation match
      case Operation.Rewritten(numeral) =>
        val _ = Files.writeString(file, text(numeral))
      case Operation.OtherToggled =>
        if Files.exists(other) then Files.delete(other)
        else
          val _ = Files.writeString(other, text(0))
      case Operation.Untouched => ()

  /** The nodes read under a new version after `before`, and whether each
    * expansion is the earlier one exactly when its content is unchanged, a
    * reused one being the expansion of the content now.
    */
  private def readAgain(
      before: Expansions[NoFacts.type],
      nodes: Vector[Configured[NoFacts.type]]
  ): (Expansions[NoFacts.type], Result) =
    val after = nodes.foldLeft(before.underAnotherVersion)((current, read) =>
      current.expanded(read, NoFacts)._2
    )
    val laws = nodes.toList.flatMap { read =>
      val found = after.byNode.getOrElse(
        read,
        throw IllegalStateException(s"the node was not expanded: $read")
      )
      before.byNode
        .get(read)
        .toList
        .flatMap(earlier =>
          List(
            Result
              .assert((found eq earlier) == (found.content == earlier.content))
              .log(s"reuse of $read differs from its content's change"),
            if found eq earlier then
              Result
                .assert(
                  Configured
                    .same(found.expansion, DirectoryTree.expansion(read))
                )
                .log(s"$read reused from another content")
            else Result.success
          )
        )
    }
    (after, Result.all(laws))

  // Six inputs: each writes and converts files, and every kind of edit is among
  // the few operations of one input.
  property(
    "an expansion is reused exactly when its content is unchanged",
    _.copy(testLimit = SuccessCount(6))
  ) {
    for edits <- operations.forAll
    yield inDirectory("tree") { directory =>
      val file = directory.resolve("member.lambdalattice")
      val other = directory.resolve("other.lambdalattice")
      val _ = Files.writeString(file, text(1))
      val nodes = Vector(node(directory), node(file))
      val (first, _) = readAgain(Expansions.none[NoFacts.type], nodes)
      val (_, results) = edits.foldLeft((first, List.empty[Result])) {
        case ((expansions, found), operation) =>
          applied(operation, file, other)
          val (after, result) = readAgain(expansions, nodes)
          (after, result :: found)
      }
      Result.all(results)
    }
  }

  stoppableProperty(
    "an executor keeps its expansions between two calls under one source"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for numeral <- Gen.int(Range.constant(0, 3)).forAll
    yield inDirectory("executor") { directory =>
      val file = directory.resolve("member.lambdalattice")
      val _ = Files.writeString(file, text(numeral))
      val read = node(file)
      val dependencies = ExecutionDependencies(
        BaselineCaches.provider(),
        ExpansionSource.fresh()
      )
      val (first, _, _) = ReadingExecutor(
        Mode.TablingWeakHead,
        com.yang_bo.gezi.weakhead.ReadingConfiguration.withoutFacts,
        NoJitState
      ).executed(read, dependencies, budget(stop))
      val (second, _, _) = first.executed(read, dependencies, budget(stop))
      Result.assert(
        first.expansions.byNode
          .get(read)
          .exists(earlier =>
            second.expansions.byNode.get(read).exists(_ eq earlier)
          )
      )
    }
  }
