package gezi.proofs

import gezi.standardlibrary.LeanFiniteTerms
import gezi.standardlibrary.LibraryFiles

/** The check of round certificates whose library statements are written for the
  * lemmas the articles import only (`LeanStatements.selectedText`), in a
  * temporary Lean package that requires the package
  * (`CertificateChecks.statementsPackage`): the way
  * `gezi.contest.entry.generic.EntryArticleVerification` verifies an entry's
  * articles against the entry's own library.
  *
  * Purpose: catch a module of selected statements that Lean does not elaborate,
  * a temporary package Lake does not build against the package's built modules,
  * or selected statements that do not agree with the imports of the articles
  * (`EndToEnd.Statement.imports`), which nanoda then rejects: the expected
  * articles of three fixpoint runs that import lemmas of the native route's
  * library (15 lemmas in all), written by the baseline's encoding of that
  * library, are accepted with only those lemmas stated.
  */
class SelectedStatementsCertificateTest
    extends gezi.generatedinputs.FailFastSuite:

  private given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  // Measured 2026-11-17 on 2 CPUs (contest.slice, CPUs 10,11, nice 10): the suite, the library's compilation
  // included, takes 50.9 s, 43.1 s and 42.5 s at the 1-minute load 7.5, 4.6 and 3.5 (Lake elaborating the 15
  // statements' soundness, lean4export, and nanoda). The bound is 1.5 times the slowest, rounded up to 5 s.
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(80, "s")

  private lazy val library =
    LibraryFiles.compiled(
      "tests/library_fixtures/native_route_lemmas.lambdalattice",
      Vector.empty
    )

  /** The native route's library, forced before the first test and not charged
    * to it (FailFastSuite).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => library)

  private val runs = Vector(
    "identity_closure_beta",
    "twice_closure_beta",
    "successor_zero_type_check"
  )

  stoppableTest(
    "the certificates of articles check with the statements of the lemmas they import only"
  ) { stopped =>
    val articles = runs.map(run =>
      ProofTestFiles.textRead(
        ProofTestFiles.repository.resolve(
          s"gezi/tests/opentheory_article_expected/$run.art"
        )
      )
    )
    val lemmaNames = articles.flatMap(RoundCertificates.lemmaNames).distinct
    assert(lemmaNames.nonEmpty, "the articles import no library lemma")
    val statements = LeanStatements.selectedText(
      library,
      library.index,
      LeanStatementsChecks.baselineEncodings(library),
      ProofTestFiles.repository,
      lemmaNames
    )
    val directory = CertificateChecks.statementsPackage(
      LeanFiniteTerms.leanDirectory,
      statements
    )
    val (status, report) =
      try
        CertificateChecks.verified(
          directory,
          CertificateChecks.packageStatements,
          articles,
          stopped
        )
      finally CertificateChecks.packageDeleted(directory)
    assert(CertificateChecks.accepted(status, report), report)
  }
