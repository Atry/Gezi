package gezi.proofs

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import gezi.standardlibrary.LeanProcesses
import scala.concurrent.ExecutionContext
import scala.concurrent.Future
import scala.jdk.StreamConverters.*

/** The check of round certificates ([[RoundCertificates]]) by the dev shell's
  * lean4export and nanoda (gezi/modules/lean-certificate-checkers.nix): the
  * closure of the constants the certificates name, written by lean4export from
  * the built Lean package, then the certificates after it, read by nanoda. The
  * tests of the certificates and the verifier of stored articles
  * (`ArticleVerification`) run it.
  */
object CertificateChecks:

  /** The closure lean4export writes for certificates whose articles import the
    * library lemmas `lemmaNames`, stated in the module `statements`, after
    * `lake build` of its modules (`RoundCertificates.closureModules`,
    * `closureConstants`) in the Lean package `leanDirectory`.
    */
  def closure(
      leanDirectory: Path,
      statements: String,
      lemmaNames: Vector[String],
      stopped: Future[Unit]
  ): LeanExport =
    val modules = RoundCertificates.closureModules(lemmaNames, statements)
    LeanProcesses.lakeOutput(leanDirectory, "build" +: modules, stopped)
    val lines = LeanProcesses.lakeOutput(
      leanDirectory,
      Seq("env", "lean4export") ++ modules ++ Seq("--") ++ RoundCertificates
        .closureConstants(lemmaNames),
      stopped
    )
    LeanExport.continuing(lines.split("\n").toVector.filter(_.nonEmpty))

  /** The module of the statements in a package of `statementsPackage`. */
  val packageStatements: String = "EntryStatements"

  /** A new Lean package in a temporary directory that requires the package
    * `leanDirectory` by its path, with its toolchain, and holds one module,
    * `packageStatements`, of the text `statements` (`LeanStatements`): so that
    * a closure (`closure`, run in the new package) imports the statements of an
    * entry's library without a file written into the package `leanDirectory`,
    * whose built modules Lake reuses (measured 2026-11-17: a module of the new
    * package that imports `LambdaJit.RoundCertificate` built in 2 s).
    */
  def statementsPackage(leanDirectory: Path, statements: String): Path =
    val directory = Files.createTempDirectory("entry-statements")
    Files.writeString(
      directory.resolve("lakefile.lean"),
      s"""import Lake
         |open Lake DSL
         |
         |require LambdaJit from ${LeanExport.quoted(
          leanDirectory.toAbsolutePath.toString
        )}
         |
         |package EntryStatements where
         |
         |lean_lib $packageStatements where
         |""".stripMargin,
      StandardCharsets.UTF_8
    )
    // Without the dependency's toolchain, Lake writes it itself on the first
    // run and exits with 4, asking to be restarted.
    Files.copy(
      leanDirectory.resolve("lean-toolchain"),
      directory.resolve("lean-toolchain")
    )
    Files.writeString(
      directory.resolve(s"$packageStatements.lean"),
      statements,
      StandardCharsets.UTF_8
    )
    directory

  /** Deletes a package `statementsPackage` made, with everything Lake wrote in
    * it, the files before their directories.
    */
  def packageDeleted(directory: Path): Unit =
    val entries = Files.walk(directory)
    val paths = entries.toScala(Vector)
    entries.close()
    paths.sortBy(-_.getNameCount).foreach(Files.delete)

  /** The certificates of `articles` after `closure`, each in the namespace
    * `Certificate<position>`.
    */
  def certified(closure: LeanExport, articles: Vector[String]): LeanExport =
    articles.zipWithIndex.foldLeft(closure) {
      case (current, (article, position)) =>
        RoundCertificates.written(current, article, s"Certificate$position")
    }

  /** The certificates of `articles`, after the closure of the package
    * `leanDirectory` with the statements module `statements`, checked by
    * nanoda: its status and report (`checked`).
    */
  def verified(
      leanDirectory: Path,
      statements: String,
      articles: Vector[String],
      stopped: Future[Unit]
  ): (Int, String) =
    val certificates = certified(
      closure(
        leanDirectory,
        statements,
        articles.flatMap(RoundCertificates.lemmaNames).distinct,
        stopped
      ),
      articles
    )
    checked(certificates.written, stopped)

  /** Whether nanoda's status and report say that it accepted every declaration.
    */
  def accepted(status: Int, report: String): Boolean =
    status == 0 && report.contains("with no typechecker errors")

  /** The status nanoda exits with on the export's lines and what it writes on
    * its standard output; its standard error, where it reports a rejection,
    * follows the output. Only Lean's three axioms are permitted, any other
    * being an error. Destroyed when `stopped` completes.
    */
  def checked(lines: Vector[String], stopped: Future[Unit]): (Int, String) =
    val exportFile = Files.createTempFile("certificate", ".ndjson")
    val configuration = Files.createTempFile("nanoda", ".json")
    val outputFile = Files.createTempFile("nanoda", ".out")
    val errorFile = Files.createTempFile("nanoda", ".err")
    Files.write(
      exportFile,
      lines.map(_ + "\n").mkString.getBytes(StandardCharsets.UTF_8)
    )
    Files.writeString(
      configuration,
      s"""{"export_file_path":${LeanExport.quoted(
          exportFile.toString
        )},"num_threads":1,""" +
        """"permitted_axioms":["propext","Classical.choice","Quot.sound"],"unpermitted_axiom_hard_error":true,""" +
        """"nat_extension":true,"string_extension":true,"print_success_message":true}""",
      StandardCharsets.UTF_8
    )
    val process = ProcessBuilder("nanoda_bin", configuration.toString)
      .redirectOutput(outputFile.toFile)
      .redirectError(errorFile.toFile)
      .start()
    stopped.foreach(_ => LeanProcesses.processTreeDestroyed(process.toHandle))(
      using ExecutionContext.parasitic
    )
    val status = process.waitFor()
    val output = Files.readString(outputFile) + Files.readString(errorFile)
    Vector(exportFile, configuration, outputFile, errorFile).foreach(
      Files.delete
    )
    (status, output)
