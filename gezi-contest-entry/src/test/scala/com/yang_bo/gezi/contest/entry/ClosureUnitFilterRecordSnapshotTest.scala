package com.yang_bo.gezi.contest.entry

import java.nio.file.Paths
import com.yang_bo.gezi.egraph.LiveNode
import com.yang_bo.gezi.jit.BackendFacts
import com.yang_bo.gezi.knowledgereading.KnowledgeReading
import com.yang_bo.gezi.narrowblocks.ClosureUnits
import com.yang_bo.gezi.narrowblocks.ProgramCompilation
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.StandardLibrary
import com.yang_bo.gezi.standardlibrary.TermTable
import com.yang_bo.gezi.weakhead.Expansions
import snapshot4s.generated.snapshotConfig

/** A record, not an acceptance: what the closure unit of the library edit
  * distances' family (tests/jit_fixtures/edit_distance_unit.lambdalattice, the
  * family's function at arity 2) gives under the elimination preset's type
  * check (corpora/compiler/wren_elimination_preset, the round
  * tests/round_fixtures/wren_elimination_type_check), the round opening the
  * closures that call a head, its rules those enabled before the opt-in ones,
  * and its extraction the narrow-block extractor. Recorded: whether the unit
  * kept F, the instances the rounds spent and how the last one ended, the
  * unions by justification, and, for every eigenvariable the graph opened, how
  * many parallels `v ∥ T` have it on their left: whether the parameters were
  * typed in the graph, and whether the extraction kept their filters. It is the
  * reading the native data structures plan's hypothesis H1′ asks for (the
  * parameters' filters, `list_type (binary_set …)`), which no deliverable
  * depends on; its purpose is to show it, and to show a change of it in the
  * snapshot's diff.
  */
class ClosureUnitFilterRecordSnapshotTest
    extends com.yang_bo.gezi.generatedinputs.FailFastSuite
    with snapshot4s.munit.SnapshotAssertions:

  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(120, "s")

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  stoppableTest(
    "the edit distances' closure unit under the elimination preset"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val library =
      StandardLibrary.compiledAt(
        buildRoot,
        buildRoot.resolve(
          "tests/library_fixtures/wren_elimination_preset.lambdalattice"
        ),
        Vector.empty
      )
    val StandardLibrary.EntryReading(entry, afterEntry, _, _) =
      StandardLibrary.entryTerm(
        buildRoot,
        buildRoot.resolve(
          "tests/round_fixtures/wren_elimination_type_check.lambdalattice"
        ),
        KnowledgeReading.compilationState
      )
    val round = KnowledgeReading
      .run(KnowledgeReading.memberTerm(entry), 20000L, afterEntry)
      ._1
    val lemmas = library.lemmas(round, KnowledgeReading.startingState)._1
    val settings = RoundSettings(
      opening = true,
      builtInRules = com.yang_bo.gezi.ir.BuiltInRule.beforeOptIn,
      IndexerImplementation.Standard,
      OrientationCompilerImplementation.Standard,
      SaturatorImplementation.HigherOrder,
      ExtractorImplementation.NarrowBlock(256, 1),
      LemmaEncodingImplementation.Baseline,
      EmatchingImplementation.Closures,
      MemoRetentionOption.Kept,
      WriteBackSpellingsOption.KeptWithinAPass,
      OpeningCriterionOption.CallsAHead
    )
    val facts = BackendFacts.of(library)
    val encoding = facts.storageEncoding
    val crossedIndex =
      com.yang_bo.gezi.standardlibrary.StandardLibraryIndex.crossed(library.index, encoding)
    val prepared = Defaults
      .lemmaCompilation(
        lemmas,
        settings,
        20000,
        facts.nativeBackend,
        ExtractorModules(Map.empty),
        com.yang_bo.gezi.ir.TermConstruction(encoding),
        com.yang_bo.gezi.weakhead
          .ReadingConfiguration(encoding, com.yang_bo.gezi.ir.StorageAccess.granted())
      )
      .prepared(crossedIndex)
    val configuration = ProgramCompilation(
      crossedIndex,
      Vector(prepared),
      facts.nativeBackend,
      encoding
    )
    val function = StandardLibrary
      .entryMembers(
        buildRoot,
        TermTable(
          "tests/jit_fixtures/edit_distance_unit.lambdalattice",
          Vector("edit_distance")
        ),
        Expansions.none
      )
      ._1("edit_distance")
    val unit = ClosureUnits.compiledUnit(
      configuration,
      function,
      2,
      explained = false,
      stop
    )
    val graph =
      unit.graph.getOrElse(fail("a compilation that ran leaves its graph"))
    val unions = graph.unions
      .map(_.justification.getClass.getSimpleName)
      .groupBy(identity)
      .view
      .mapValues(_.size)
      .toVector
      .sorted
    val eigenvariableRoots = graph.liveNodes.collect {
      case LiveNode(node, root, com.yang_bo.gezi.ir.NoinlineLeaf(leaf))
          if leaf.toString.contains("eigenvariable") =>
        root
    }
    val filtersAtEigenvariables = eigenvariableRoots
      .map(root =>
        graph.liveNodes.count {
          case LiveNode(_, _, com.yang_bo.gezi.ir.Parallel(left, _)) => left == root;
          case _                                         => false
        }
      )
      .sorted
    assertFileSnapshot(
      s"""lemmas: ${lemmas.size}
         |kept: ${unit.kept}
         |instances: ${unit.instances}
         |end: ${unit.end}
         |unions: ${unions.map((kind, count) => s"$kind $count").mkString(", ")}
         |eigenvariables: ${eigenvariableRoots.size}
         |parallels at each eigenvariable, sorted: ${filtersAtEigenvariables
          .mkString(" ")}
         |""".stripMargin,
      "closure_units/edit_distance_elimination_preset.txt"
    )
  }
