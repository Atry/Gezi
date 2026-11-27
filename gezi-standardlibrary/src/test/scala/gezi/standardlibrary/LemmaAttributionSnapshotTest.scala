package gezi.standardlibrary

import snapshot4s.generated.snapshotConfig

/** The knowledge file each lemma of the native route's library
  * (`tests/library_fixtures/native_route_lemmas.lambdalattice`, the choice of
  * seven compiler knowledge files) is attributed to by
  * `LemmaSources.attributed`, among the files of `corpora/compiler`, and the
  * lemmas attributed to none.
  *
  * Purpose: catch an attribution that misses a lemma the library holds, or
  * gives it a file whose declaration of the name reads as other sides, so that
  * a trace's lemma would point at no text or at the wrong one. The input is the
  * corpus and a fixture the library's tests already read; the output is a table
  * of 85-odd rows, so it is a snapshot.
  */
class LemmaAttributionSnapshotTest
    extends gezi.generatedinputs.FailFastSuite
    with snapshot4s.munit.SnapshotAssertions:

  /** The library the lemmas are taken from, a shared fixture, not the subject
    * of the test.
    */
  private lazy val library: StandardLibrary =
    LibraryFiles.compiled(
      "tests/library_fixtures/native_route_lemmas.lambdalattice",
      Vector.empty
    )

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => library)

  test("the knowledge file of each lemma of the native route's library") {
    // The seven files the fixture chooses, and two that declare other
    // lemmas, so that a file is chosen by its declarations, not by being
    // the only candidate. All 39 files of corpora/compiler took the test
    // over its 3 s deadline (3.03 s, cores 4-7, 2026-11-17).
    val files = Vector(
      "closure_application",
      "hindley_milner_unions",
      "top",
      "native_arithmetic",
      "native_arithmetic_unions",
      "native_types",
      "occurrence_erasure",
      "prelude",
      "prolog_backend_shapes"
    ).map(name =>
      LibraryFiles.buildRoot
        .resolve("corpora")
        .resolve("compiler")
        .resolve(s"$name.lambdalattice")
    )
    val lemmas = library.index.lemmaNames.flatMap(named =>
      library.index.lemmaSides
        .find(_.lemma == named.lemma)
        .map(sides => (named, sides))
    )
    val found = LemmaSources.attributed(LibraryFiles.buildRoot, files, lemmas)
    val lines = lemmas.map((named, _) =>
      found
        .get(named.lemma)
        .fold(s"${named.name}: none")((file, _) =>
          s"${named.name}: ${file.getFileName}"
        )
    )
    assertFileSnapshot(
      lines.sorted.mkString("", "\n", "\n"),
      "lemma_sources/native_route_attribution.txt"
    )
  }
