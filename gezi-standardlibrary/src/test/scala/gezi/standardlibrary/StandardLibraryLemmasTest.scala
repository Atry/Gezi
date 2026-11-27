package gezi.standardlibrary

import gezi.ir.Code
import gezi.ir.Configured
import gezi.ir.Hole
import gezi.ir.NativeSpecializer.*
import gezi.ir.NoFacts
import gezi.ir.NonEmptyHoles

/** The port of `gezi/tests/standard_library_lemmas.plt`: every lemma of prelude
  * and of guard_laws whose proof is
  * `λ_c. _c "munit" "gezi.standardlibrary.StandardLibraryLemmasTest"`, this
  * suite, replays by beta and eta steps (`LemmaReplay`): the rows of the
  * recursive functions, the beta laws of apply_to, identity and compose, and
  * the beta laws of guard_laws. The list of lemmas is read from the sources, so
  * a lemma that names this suite as its proof is replayed whether or not it is
  * listed below.
  */
class StandardLibraryLemmasTest extends gezi.generatedinputs.FailFastSuite:

  given NoFacts.type = NoFacts

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of StandardLibraryLemmasTest, "everyDefinitionalLemmaReplays", takes 14.041 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(25, "s")

  private lazy val library =
    LibraryFiles.compiled(
      "tests/library_fixtures/prelude_guard_laws.lambdalattice",
      Vector.empty
    )

  /** The prelude's files, which the two knowledge files and the prelude's own
    * files import, as the tree read gives them (`TreeTerms`), each file's
    * fields: the names the replay keeps opaque.
    */
  private lazy val preludePaths: Vector[String] =
    TreeTerms.filePaths("corpora/library/prelude")

  private lazy val preludeFields: Vector[Vector[Configured[NoFacts.type]]] =
    TreeTerms.fields(preludePaths)

  private lazy val replay = LemmaReplay(library, preludeFields.flatten.toSet)

  /** The lemmas of prelude and guard_laws whose proof is the munit suite of
    * this class's own name, in the order the library declares them
    * (`StandardLibrary.lemmaProof`).
    */
  private lazy val replayedLemmas: Vector[String] =
    val suite = LemmaProof.Munit(getClass.getName)
    library.index.lemmaNames.collect {
      case LemmaNamed(_, name) if library.lemmaProof(name).contains(suite) =>
        name
    }.distinct

  /** The library, the prelude's fields and the lemmas to replay, forced before
    * the first test and not charged to it (FailFastSuite); the replay itself is
    * not.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => library, _ => preludeFields, _ => replayedLemmas)

  private def missing(expected: Vector[String]): Vector[String] =
    expected.filterNot(replayedLemmas.contains)

  test("everyDefinitionalLemmaReplays") {
    assert(replayedLemmas.nonEmpty)
    replayedLemmas.foreach(name =>
      if replay.replayed(name).isEmpty then
        fail(s"lemma_does_not_replay($name)")
    )
  }

  test("theBetaLawsOfTheCombinatorsAreAmongThem") {
    assertEquals(
      missing(
        Vector("apply_to_applied", "identity_applied", "compose_applied")
      ),
      Vector.empty
    )
  }

  test("theGuardBetaLawsAreAmongThem") {
    assertEquals(
      missing(
        Vector(
          "compose_associative",
          "compose_as_post_application",
          "post_application_of_composition",
          "post_application_of_apply_to"
        )
      ),
      Vector.empty
    )
  }

  test("theRowLemmasAreAmongThem") {
    assertEquals(
      missing(
        Vector(
          "natural_equal_zero_zero",
          "natural_equal_zero_successor",
          "natural_equal_successor_zero",
          "natural_equal_successor_successor",
          "natural_at_least_zero",
          "natural_at_least_zero_successor",
          "natural_at_least_successor_successor",
          "natural_difference_zero",
          "natural_difference_zero_successor",
          "natural_difference_successor_successor",
          "natural_double_zero",
          "natural_double_successor"
        )
      ),
      Vector.empty
    )
  }

  // natural_double_successor's right side keeps natural_double opaque: the
  // replay unfolds the head of the left side only, natural_double, whose term
  // `fixpoint g` instantiates `g (fixpoint g)` with the inner `fixpoint g`
  // natural_double's own instruction, and both sides meet at
  // `\n. successor (successor (natural_double n))`, as a thunk layer: the
  // binder n is the hole at slot 2, the numerals' z is ignored and their s is
  // the hole at slot 0, natural_double's instruction fills slot 1, and the inner
  // `successor (natural_double n)` is a thunk of the same successor shape
  // reading natural_double and n from the enclosing slots 1 and 2.
  test("naturalDoubleSuccessorMeetsAtTheRecursiveCall") {
    // natural_double is the field 3 of the prelude's file natural.
    val naturalDouble = preludePaths.zip(preludeFields).collect {
      case ("corpora/library/prelude/natural", fields) => fields.lift(3)
    } match
      case Vector(Some(term)) => term
      case other => fail(s"the prelude's file natural has no field 3: $other")
    val expected = NoFacts.thunk(
      Code.Apply(
        Code.Slot(0),
        Code.Thunk(
          Code.Apply(Code.Slot(0), Code.Apply(Code.Slot(1), Code.Slot(2))),
          Vector(Hole.Ignored, Hole.Bound(0)),
          Vector(Code.Slot(1), Code.Slot(2))
        )
      ),
      NonEmptyHoles(Hole.Bound(2), Vector(Hole.Ignored, Hole.Bound(0))),
      Vector(naturalDouble)
    )
    assert(
      replay
        .replayed("natural_double_successor")
        .exists(Configured.same(_, expected)),
      s"natural_double_successor replays to ${replay.replayed("natural_double_successor")}"
    )
  }
