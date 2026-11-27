package com.yang_bo.gezi.contest.entry.generic

import java.nio.file.Files
import java.nio.file.Path
import com.yang_bo.gezi.contest.entry.Defaults
import com.yang_bo.gezi.contest.entry.ArticleDestination
import com.yang_bo.gezi.contest.entry.EntryData
import com.yang_bo.gezi.jit.NativesProvider
import com.yang_bo.gezi.proofs.CertificateChecks
import com.yang_bo.gezi.proofs.RoundCertificates
import scala.concurrent.Future

/** The verifier of the articles an entry wrote, run on demand outside the
  * judging, as `com.yang_bo.gezi.proofs.ArticleVerification` is for the native route's
  * library: the statements of the lemmas the articles import are written from
  * the entry's own library and its lemma encodings
  * (`LeanStatements.selectedText`) into a temporary Lean package that requires
  * the Lean package (`CertificateChecks.statementsPackage`), and the articles'
  * round certificates, written after the closure of that package, are checked
  * by nanoda.
  *
  * {{{
  * sbt 'contest-entry-generic/runMain com.yang_bo.gezi.contest.entry.generic.EntryArticleVerification <Lean package> <entry directory> <article> ...'
  * }}}
  *
  * run in the dev shell. A lemma whose soundness `lemma_soundness` declares by
  * a named axiom (no hand-written proof, no decision) makes nanoda reject the
  * check: it permits Lean's three axioms only, so an unproved lemma of the
  * entry fails the verification instead of passing it. The citations of the
  * lemmas' proofs are checked against the monorepo, the parent of the Lean
  * package's parent. It writes nanoda's report and throws
  * `IllegalStateException` with it when nanoda rejects, keeping the temporary
  * package for inspection; it deletes the package when nanoda accepts.
  */
object EntryArticleVerification:

  def main(arguments: Array[String]): Unit =
    val (leanDirectory, entryDirectory, articleFiles) = arguments.toVector match
      case leanPackage +: entry +: articles if articles.nonEmpty =>
        (
          Path.of(leanPackage).toAbsolutePath,
          Path.of(entry),
          articles.map(Path.of(_))
        )
      case _ =>
        throw IllegalArgumentException(
          "usage: EntryArticleVerification <Lean package> <entry directory> <article> ..."
        )
    val repository = leanDirectory.getParent.getParent
    val articles = articleFiles.map(Files.readString)
    val (data, afterEntry) =
      EntryData.read(entryDirectory, Defaults.entryDataState)
    val (library, entry) =
      GenericEntryProvider.initializedWithLibrary(
        data,
        com.yang_bo.gezi.contest.entry.ExecutorModules.registeredFor(entryDirectory),
        com.yang_bo.gezi.contest.entry.ExtractorModules.registeredFor(entryDirectory),
        NativesProvider.loaded,
        ArticleDestination.Discarded,
        afterEntry,
        com.yang_bo.gezi.contest.entry.Defaults.caches()
      )
    val statements = entry.leanStatementsText(
      library,
      repository,
      articles.flatMap(RoundCertificates.lemmaNames).distinct
    )
    val statementsDirectory =
      CertificateChecks.statementsPackage(leanDirectory, statements)
    val (status, report) = CertificateChecks.verified(
      statementsDirectory,
      CertificateChecks.packageStatements,
      articles,
      Future.never
    )
    System.out.println(report)
    if !CertificateChecks.accepted(status, report) then
      throw IllegalStateException(
        s"nanoda rejected the certificates of ${articleFiles.mkString(", ")} (statements in $statementsDirectory):\n$report"
      )
    CertificateChecks.packageDeleted(statementsDirectory)
