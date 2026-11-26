package gezi.proofs

/** The committed Lean module of the expected articles' lines,
  * `gezi/lean/LambdaJit/ExpectedArticles.lean`, is the regeneration of
  * `ExpectedArticlesModule.text` from the expected articles: the test catches
  * an article changed without its module regenerated, which the Lean build
  * cannot see, since the package reads only the module. It was a test of
  * `OpentheoryArticleTest` until that class was deleted when the library
  * became files reached by paths; this
  * test reads no library term.
  */
class ExpectedArticlesModuleTest extends gezi.generatedinputs.FailFastSuite:

  test("theLeanModuleOfTheExpectedArticlesIsTheirRegeneration") {
    assertEquals(
      ProofTestFiles.textRead(ProofTestFiles.leanModules.resolve("ExpectedArticles.lean")),
      ExpectedArticlesModule.text
    )
  }
