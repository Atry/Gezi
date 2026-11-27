package gezi.proofs

/** The OpenTheory article checker, `gezi/tests/check_opentheory_article.sh`,
  * which runs Joe Leslie-Hurd's opentheory tool on an article, on the 15
  * article files of the tests: the port of
  * `gezi/tests/opentheory_articles.plt`, which checks the two hand-written
  * articles of `gezi/tests/opentheory_fixtures/` (the tool accepts the article
  * whose thm exports the theorem its proof derives, and rejects at that thm the
  * article whose thm claims another conclusion), and a check of the 13 expected
  * articles of `gezi/tests/opentheory_article_expected/`, each accepted by the
  * tool, run as the checker runs it, with nothing on standard error
  * (`ProofTestFiles.toolChecked` says why it is run directly). The tests need
  * `opentheory` on the path, as the dev shell has it.
  */
class OpentheoryArticlesTest extends gezi.generatedinputs.FailFastSuite:

  private val fixtures =
    ProofTestFiles.testDirectory.resolve("opentheory_fixtures")

  test("theToolAcceptsTheDerivedTheorem") {
    val (status, errors) = ProofTestFiles.articleChecked(
      fixtures.resolve("accepted_choice_commutativity_instance.art")
    )
    assertEquals(status, 0, s"the tool's errors: $errors")
  }

  test("theToolRejectsAnotherConclusionAtThm") {
    val (status, errors) = ProofTestFiles.articleChecked(
      fixtures.resolve("rejected_wrong_conclusion.art")
    )
    assertEquals(status, 1)
    assert(
      errors.contains(
        "while executing thm command:\nterms not alpha-equivalent"
      ),
      s"the tool's errors: $errors"
    )
  }

  test("theToolAcceptsEveryExpectedArticle") {
    val articles = ProofTestFiles
      .entries(ProofTestFiles.expectedDirectory)
      .filter(_.endsWith(".art"))
    assertEquals(articles.size, 13)
    articles.foreach(article =>
      val checked = ProofTestFiles.toolChecked(
        ProofTestFiles.expectedDirectory.resolve(article)
      )
      assertEquals((article, checked), (article, (0, "")))
    )
  }
