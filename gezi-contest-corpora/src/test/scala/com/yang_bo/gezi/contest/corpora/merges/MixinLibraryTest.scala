package com.yang_bo.gezi.contest.corpora.merges

import hedgehog.Gen
import hedgehog.Range
import com.yang_bo.gezi.contest.corpora.common.ProblemData
import com.yang_bo.gezi.contest.corpora.common.ProblemFamily
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.generatedinputs.SeededSamples
import snapshot4s.generated.snapshotConfig

/** The snapshot of `problems/mixin_library`, whose purpose is to catch a
  * generator change that alters a library's module or an instance built under
  * it: under the lets of a library's module, every class of the module of every
  * library of `library_module` (`library_class(Library,Class)`), which together
  * hold every contribution of every library file, and the naturals of
  * `naturalInstance` and `binaryInstance` at counts drawn from a fixed seed.
  */
class MixinLibraryTest
    extends MergeProblemsSuite
    with snapshot4s.munit.SnapshotAssertions:

  private val library = MixinLibrary(MergeTesting.problems)

  /** The seed of the drawn counts. */
  private val seed = 20261112L

  /** A count from 0 to 6. */
  private val count: Gen[Int] = Gen.int(Range.constant(0, 6))

  private def classes: Vector[(String, () => Term)] =
    MergeTesting
      .problems("mixin_library")
      .rows("library_module")
      .map(arguments => ProblemData.text(arguments(0)))
      .flatMap(name =>
        library
          .libraryModule(name)
          .slots
          .map(className =>
            s"library_class($name,$className)" ->
              (() =>
                library.withMixinLibrary(
                  Vector(name),
                  names => library.libraryClass(names, name, className)
                )
              )
          )
      )

  private def instances: Vector[(String, () => Term)] =
    SeededSamples
      .samples(count, seed, 4)
      .distinct
      .map(drawn =>
        s"natural_instance($drawn)" ->
          (() =>
            library.withMixinLibrary(
              Vector("natural"),
              names => library.naturalInstance(names, drawn)
            )
          )
      ) ++ SeededSamples
      .samples(count, seed + 1, 7)
      .distinct
      .map(drawn =>
        s"binary_instance($drawn)" ->
          (() =>
            library.withMixinLibrary(
              Vector("binary"),
              names => library.binaryInstance(names, BigInt(drawn))
            )
          )
      )

  test("the classes' and the drawn instances' programs") {
    assertFileSnapshot(
      GeneratedProgramLines.programs(classes ++ instances),
      "generated_programs/contest_mixin_library.txt"
    )
  }
