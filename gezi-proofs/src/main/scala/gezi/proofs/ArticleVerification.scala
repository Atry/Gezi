package gezi.proofs

import java.nio.file.Files
import java.nio.file.Path
import scala.concurrent.Future

/** The verifier of stored articles, run on demand outside the judging: what
  * matters is that the exported evidence can be verified, not that every
  * judging runs Lean. Each article is replayed into its round certificate (`RoundCertificates`), the
  * certificates are written after the closure lean4export writes from the Lean package, and
  * nanoda checks them all (`CertificateChecks`). This one takes the statements of the
  * native route's library; the articles of an entry, whose lemmas are its own, are verified by
  * `gezi.contest.entry.generic.EntryArticleVerification`.
  *
  * {{{
  * sbt 'proofs/runMain gezi.proofs.ArticleVerification <Lean package> <article> ...'
  * }}}
  *
  * run in the dev shell, which puts `lake`, lean4export and nanoda on the path. It writes
  * nanoda's report and throws `IllegalStateException` with it when nanoda rejects an article.
  *
  * What a reader trusts besides the checker and the Lean library: each certificate's theorem
  * is `EquationSound signature left right` of the equation its article exports, as the
  * replay reads it; that the first article's left side is the encoding of the point's
  * program, and each article's left side the previous article's right side, this verifier
  * does not check.
  */
object ArticleVerification:

  def main(arguments: Array[String]): Unit =
    val (leanDirectory, articleFiles) = arguments.toVector match
      case leanPackage +: articles if articles.nonEmpty => (Path.of(leanPackage), articles.map(Path.of(_)))
      case _ => throw IllegalArgumentException("usage: ArticleVerification <Lean package> <article> ...")
    val (status, report) = CertificateChecks.verified(
      leanDirectory,
      RoundCertificates.nativeRouteStatements,
      articleFiles.map(Files.readString),
      Future.never
    )
    System.out.println(report)
    if !CertificateChecks.accepted(status, report) then
      throw IllegalStateException(s"nanoda rejected the certificates of ${articleFiles.mkString(", ")}:\n$report")
