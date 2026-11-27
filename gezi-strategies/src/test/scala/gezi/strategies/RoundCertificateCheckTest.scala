package gezi.strategies

import gezi.generatedinputs.FailFastSuite
import gezi.generatedinputs.SeededSamples
import gezi.proofs.CertificateChecks
import gezi.proofs.ExportExpression
import gezi.proofs.OpentheoryArticle
import gezi.proofs.RoundCertificates
import gezi.standardlibrary.LeanFiniteTerms
import scala.concurrent.duration.Duration

/** The check of round certificates by lean4export and nanoda, on the articles
  * of `RewriteTraceLawTest`'s higher-order rounds.
  *
  * The suite is in `strategies` because it runs the strategy.
  */
class RoundCertificateCheckTest extends FailFastSuite:

  given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  private given gezi.ir.NoFacts.type = gezi.ir.NoFacts
  import RewriteTraceLawTest.*

  // Measured 2026-11-17 on 2 CPUs (contest.slice, CPUs 10 and 11, nice 10), the Lean package built:
  // the test of the higher-order rounds takes 20.4 s and 24.6 s in two runs (the closure's lake build
  // and lean4export, eight rounds, and nanoda twice, each about 4 s), and the two tests 41.3 s
  // together; the bound is 1.5 times the slower single run, rounded up to 5 s.
  override val munitTimeout: Duration = Duration(40, "s")

  /** The number of higher-order rounds whose certificates the test below
    * checks: each adds a certificate to the one export nanoda reads after the
    * closure, which alone takes most of the check's time (3.2 s of 4.3 s on two
    * cores for a certificate of 4,683 records, 2026-11-17).
    */
  private val certificateCount: Int = 8

  /** Purpose: catch a round certificate (`gezi.proofs.RoundCertificates`) that
    * the checker rejects, a certificate that leaves out a constant the closure
    * must hold (`RoundCertificates.closureConstants`), or a check that accepts
    * what it is not shown: the certificates of the articles of higher-order
    * rounds drawn from a fixed seed, written after the closure lean4export
    * writes, are accepted by nanoda, and the same export with the last
    * certificate's equation stated turned, output = input, is rejected.
    */
  stoppableTest(
    "the certificates of higher-order rounds check, and one stated turned does not"
  ) { stopped =>
    certificatesChecked(
      SeededSamples
        .samples(higherOrderPrograms, 20261117L, certificateCount)
        .map { program =>
          val (input, output, proof) = higherOrderRan(program, stopped)
          OpentheoryArticle.text(higherOrderIndex, input, output, proof)
        },
      stopped
    )
  }

  /** Purpose: catch an abstraction step ξ
    * (`LambdaJit.RoundCertificate.abstracted`) that the article writer writes
    * or the certificate writer replays wrong, or a β conversion between the
    * opened bodies' terms, over eigenvariables, checked wrong
    * (`scopedConversion`): the certificates of rounds that write a body back,
    * each with an abstraction step (`RewriteTraceLawTest`'s law of their
    * traces), drawn from a fixed seed, are accepted, and one stated turned is
    * rejected.
    */
  stoppableTest(
    "the certificates of rounds that write a body back check, and one stated turned does not"
  ) { stopped =>
    certificatesChecked(
      SeededSamples.samples(openingPrograms, 20261117L, certificateCount).map {
        program =>
          val (input, output, proof) = openingRan(program, stopped)
          OpentheoryArticle.text(openingIndex, input, output, proof)
      },
      stopped
    )
  }

  /** The certificates of the articles, after the closure lean4export writes,
    * are accepted by nanoda, and the same export with the last certificate's
    * equation stated turned is rejected.
    */
  private def certificatesChecked(
      articles: Vector[String],
      stopped: scala.concurrent.Future[Unit]
  ): Unit =
    val certified = CertificateChecks.certified(
      CertificateChecks.closure(
        LeanFiniteTerms.leanDirectory,
        RoundCertificates.nativeRouteStatements,
        articles.flatMap(RoundCertificates.lemmaNames).distinct,
        stopped
      ),
      articles
    )
    val (status, output) = CertificateChecks.checked(certified.written, stopped)
    assert(status == 0 && output.contains("with no typechecker errors"), output)
    // The last certificate's theorem `EquationSound signature left right`, stated turned instead.
    val last = certified.written.last
    val theoremType = "\"type\":([0-9]+)".r
    val statedType =
      theoremType.findFirstMatchIn(last).getOrElse(fail(last)).group(1).toInt
    val byIndex = certified.expressions.map(_.swap)
    val (stated, right) = byIndex.get(statedType) match
      case Some(ExportExpression.Application(function, argument)) =>
        (function, argument)
      case other => fail(s"the theorem's type is $other")
    val (head, left) = byIndex.get(stated) match
      case Some(ExportExpression.Application(function, argument)) =>
        (function, argument)
      case other => fail(s"the theorem's type applies $other")
    assert(left != right, "the last round's input and output are one term")
    val (withPartial, partial) =
      certified.expression(ExportExpression.Application(head, right))
    val (withTurned, turned) =
      withPartial.expression(ExportExpression.Application(partial, left))
    val misstated = withTurned.written.filterNot(_ == last) :+ theoremType
      .replaceFirstIn(last, s"\"type\":$turned")
    val (misstatedStatus, misstatedOutput) =
      CertificateChecks.checked(misstated, stopped)
    assert(misstatedStatus != 0, misstatedOutput)
