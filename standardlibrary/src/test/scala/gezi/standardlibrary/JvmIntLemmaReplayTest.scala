package gezi.standardlibrary

import gezi.generatedinputs.FailFastSuite

/** The replay of the 32-bit words' conversion lemma, `jvm_int_conversion` of
  * `corpora/compiler/jvm_int`, `x ∥ int32_type = x ∥ jvm_int_type`, by β and η
  * steps on the IR (`LemmaReplay`). Derived from lemma 25.1 of
  * `docs/design/gezi-set-equations-proofs.md`: `jvm_int_type` is
  * `(λ"$int" v. v) "$int" int32_type`, the label's partial function applied to
  * its own key the identity by β, so both sides reach one normal form. The
  * names are the native types' and `top`, as in the array lists' replay: those
  * whose term is no thunk (`nat_fold`, a fixed point's application, and `top`,
  * the partial function's miss) stay opaque, so that `word_type` stops at its
  * fold. The fixed-width words' terms are no names here: `int32_type` and
  * `jvm_int_type` are applications, which a name would keep opaque, so the two
  * sides would stop at the two criteria themselves; read by their layers, they
  * meet. Its purpose is to catch a criterion that is not `int32_type` by the β
  * rule, which would make the lemma unsound.
  */
class JvmIntLemmaReplayTest extends FailFastSuite:

  private lazy val library = LibraryFiles.compiled(
    "tests/library_fixtures/jvm_int.lambdalattice",
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
    assert(LemmaReplay(library, names).replayed("jvm_int_conversion").isDefined)
  }
