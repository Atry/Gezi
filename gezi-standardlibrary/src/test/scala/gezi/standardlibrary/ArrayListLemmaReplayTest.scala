package gezi.standardlibrary

import gezi.generatedinputs.FailFastSuite

/** The replay of the array lists' conversion lemma, `array_list_conversion` of
  * `corpora/compiler/array_list`, `l ∥ list_type e = l ∥ array_list e`, by β
  * and η steps on the IR (`LemmaReplay`). Derived from lemma 24.1 of
  * `docs/design/gezi-set-equations-proofs.md`: `array_list e` is
  * `(λ"$array" v. v) "$array" (list_type e)`, the label's partial function
  * applied to its own key the identity by β, so both sides reach one normal
  * form once the native types' files are read by their layers (their names
  * whose term is no thunk, `fixpoint` among them, kept opaque, so that
  * `list_type e` stops at its fixed point's application), and `top`, the
  * partial function's miss at every bit, is kept opaque too: the replay
  * evaluates every argument, and `top`, a fixed point's application, has no
  * normal form. Its purpose is to catch an array list's criterion that is not
  * `list_type` by the β rule, which would make the lemma unsound.
  */
class ArrayListLemmaReplayTest extends FailFastSuite:

  private lazy val library = LibraryFiles.compiled(
    "tests/library_fixtures/array_list.lambdalattice",
    Vector.empty
  )

  private lazy val names =
    TreeTerms
      .fields(
        TreeTerms.filePaths(
          "corpora/library/native_types"
        ) :+ "corpora/library/top"
      )
      .flatten
      .toSet

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => library, _ => names)

  test("the conversion lemma's two sides reach one normal form") {
    assert(
      LemmaReplay(library, names).replayed("array_list_conversion").isDefined
    )
  }
