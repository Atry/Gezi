package gezi.standardlibrary

import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.StorageAccess

/** The law of `LemmaSources.texts` on the native route's library
  * (`tests/library_fixtures/native_route_lemmas.lambdalattice`): each side's
  * text, under abstractions of its names applied to their values, reads as the
  * lemma's side, the very instruction (a trace writes a lemma's sides as their
  * text and binds the names they use by β redexes).
  *
  * Purpose: catch a name read with the wrong value, a name missed, or a side's
  * text taken from another span, any of which would make a trace's lemma read
  * as another term than the library's.
  */
class LemmaTextsLawTest extends gezi.generatedinputs.FailFastSuite:

  given NoFacts.type = NoFacts
  given StorageAccess = StorageAccess.granted()

  private type NoFactsTerm = Configured[NoFacts.type]

  /** The library the lemmas are taken from, a shared fixture. */
  private lazy val library: StandardLibrary =
    LibraryFiles.compiled(
      "tests/library_fixtures/native_route_lemmas.lambdalattice",
      Vector.empty
    )

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => library)

  /** The fixture's knowledge files that write lemmas, hindley_milner_unions
    * being hindley_milner_unions_judgments, hindley_milner_unions_application
    * and hindley_milner_unions_occurrences.
    */
  private val files = Vector(
    "closure_application",
    "hindley_milner_unions_application",
    "hindley_milner_unions_judgments",
    "hindley_milner_unions_occurrences",
    "native_arithmetic",
    "native_arithmetic_unions",
    "native_types",
    "occurrence_erasure",
    "prolog_backend_shapes"
  ).map(name =>
    LibraryFiles.buildRoot
      .resolve("corpora")
      .resolve("compiler")
      .resolve(s"$name.lambdalattice")
  )

  /** The text's reading with each name bound to its value by a β redex of the
    * data, read as a trace reads a lemma: the text the one field of a tuple
    * under the redex, the field read back under the weak head
    * (`KnowledgeReading.soleField`, `KnowledgeReading.term`), so that the redex
    * is evaluated and the values stand in the names' places. A
    * `thunkInstruction` of the text alone would keep the redex.
    */
  private def bound(
      text: String,
      names: Vector[(String, NoFactsTerm)]
  ): NoFactsTerm =
    val holder = "side_holder"
    assert(!names.exists(_._1 == holder), s"a lemma names $holder")
    val abstracted = names.foldRight(s"(λ$holder. $holder ($text))")(
      (name, body) => s"(λ${name._1}. $body)"
    )
    val applied = names.foldLeft(abstracted)((function, name) =>
      s"$function (${Lambdalattice.closedText(name._2)})"
    )
    val instruction = Defunctionalization.thunkInstruction[NoFacts.type](
      Lambdalattice.term(applied)
    )
    // One evaluator step per character, as a trace's text is read (TraceReading.readingLimit).
    gezi.knowledgereading.KnowledgeReading.run(
      gezi.knowledgereading.KnowledgeReading
        .soleField(gezi.ir.Value.of(instruction))
        .map(field =>
          gezi.knowledgereading.KnowledgeReading.term(field, Set.empty)
        ),
      applied.length.toLong
    )

  // One test per file, so that each reads one file within the default
  // deadline: the seven files in one test took over 3 s (cores 4-7,
  // 2026-11-17), the attribution alone 2.9 s. Every lemma of the library
  // is offered to each file; a file's test checks the lemmas it declares.
  files.foreach(file =>
    test(
      s"each side's text in ${file.getFileName}, its names bound to their values, reads as the lemma's side"
    ) {
      val lemmas = library.index.lemmaNames.flatMap(named =>
        library.index.lemmaSides
          .find(_.lemma == named.lemma)
          .map(sides => (named, sides))
      )
      val texts =
        LemmaSources.texts(LibraryFiles.buildRoot, Vector(file), lemmas)
      val problems = lemmas.flatMap((named, sides) =>
        texts
          .get(named.lemma)
          .toVector
          .flatMap(text =>
            Vector(
              Option.unless(
                Configured.same(bound(text.leftText, text.names), sides.left)
              )(s"${named.name}: the left side reads otherwise"),
              Option.unless(
                Configured.same(bound(text.rightText, text.names), sides.right)
              )(s"${named.name}: the right side reads otherwise")
            ).flatten
          )
      )
      assert(texts.nonEmpty, s"no lemma of the library is written in $file")
      assertEquals(
        problems,
        Vector.empty[String],
        s"${texts.size} lemmas of $file"
      )
    }
  )
