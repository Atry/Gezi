package com.yang_bo.gezi.standardlibrary

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.Lambdalattice
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.LemmaIdentifier
import com.yang_bo.gezi.ir.NoFacts

/** Law: over generated knowledge files, in a directory of their own, that
  * declare lemmas from a small pool of names, so that one name is declared in
  * several files with other sides, `LemmaSources.attributed` gives each lemma
  * the first file whose declaration of its name has its two sides, and none to
  * a lemma no file declares so.
  *
  * Purpose: catch an attribution that misses a lemma, or gives it a file whose
  * declaration of the name reads as other sides, so that a trace's lemma would
  * point at no text or at the wrong one. The files are generated, so the law
  * holds of the attribution and not of the repository's knowledge files.
  */
class LemmaAttributionLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts

  /** A β-normal closed side, `λv0 … vk. BODY`: a variable applied to arguments,
    * or an abstraction, each compound argument parenthesized, so that the
    * library's readback spells it as the front end does.
    */
  private def normal(depth: Int, size: Int): Gen[String] =
    if size <= 0 then
      Gen.int(Range.linear(0, depth - 1)).map(index => s"v$index")
    else
      Gen.boolean.flatMap(abstraction =>
        if abstraction then
          normal(depth + 1, size - 1).map(inner => s"(λv$depth. $inner)")
        else
          for
            head <- Gen.int(Range.linear(0, depth - 1))
            arguments <- normal(depth, size / 2).list(Range.linear(1, 2))
          yield (s"v$head" +: arguments.map(argument => s"($argument)"))
            .mkString(" ")
      )

  private val sides: Gen[String] =
    for
      binders <- Gen.int(Range.linear(1, 2))
      size <- Gen.int(Range.linear(0, 4))
      written <- normal(binders, size)
    yield s"λ${(0 until binders).map(index => s"v$index").mkString(" ")}. $written"

  private val names: Gen[String] =
    Gen.elementUnsafe(List("unit_law", "choice_applied", "ß_erased"))

  private final case class Planted(name: String, left: String, right: String)

  private val declarations: Gen[Vector[Planted]] =
    (for name <- names; left <- sides; right <- sides
    yield Planted(name, left, right))
      .list(Range.linear(0, 3))
      .map(found => found.toVector.distinctBy(_.name))

  private def fileText(planted: Vector[Planted]): String =
    val members = planted.map(declaration =>
      s"""(λs. s (λk. k "${declaration.name}") (${declaration.left}) (${declaration.right}) λ_ md _. md λk. k "proof")"""
    )
    val lemmas =
      if members.isEmpty then "λx. x" else members.mkString("\n      + ")
    s"λ export\n. export λ _ rewriting _ _. rewriting λ _ lemmas _. lemmas (\n      $lemmas\n    )\n"

  private def instruction(side: String): Configured[NoFacts.type] =
    Defunctionalization.thunkInstruction[NoFacts.type](Lambdalattice.term(side))

  /** One attribution read before the property, so that the readers' first
    * calls, which took 0.4 s to 0.5 s of the first two samples while the later
    * ones took 40 ms to 170 ms each (measured 2026-11-22, two cores, load 7),
    * are charged to the fixture (FailFastSuite), not to the law.
    */
  private lazy val warmedUp
      : Map[LemmaIdentifier, (java.nio.file.Path, LemmaDeclarationSource)] =
    val directory = Files.createTempDirectory("lemma-attribution")
    val planted = Planted("unit_law", "λv0. v0", "λv0 v1. v1")
    val path = Files.writeString(
      directory.resolve("knowledge.lambdalattice"),
      fileText(Vector(planted)),
      StandardCharsets.UTF_8
    )
    val lemma = LemmaIdentifier(0)
    val found = LemmaSources.attributed(
      directory,
      Vector(path),
      Vector(
        (
          LemmaNamed(lemma, planted.name),
          LemmaSides(
            lemma,
            instruction(planted.left),
            instruction(planted.right)
          )
        )
      )
    )
    Files.delete(path)
    Files.delete(directory)
    found

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => warmedUp)

  property(
    "each lemma is attributed to the first file whose declaration of its name has its sides"
  ) {
    val inputs =
      for
        files <- declarations.list(Range.linear(1, 3))
        unplanted <- (for name <- names; left <- sides; right <- sides
        yield Planted(name, left, right)).list(Range.linear(0, 2))
      yield (files, unplanted)
    for (files, unplanted) <- inputs.forAll
    yield
      val directory = Files.createTempDirectory("lemma-attribution")
      val paths = files.toVector.zipWithIndex.map((planted, index) =>
        Files.writeString(
          directory.resolve(s"knowledge_$index.lambdalattice"),
          fileText(planted),
          StandardCharsets.UTF_8
        )
      )
      val asked = (files.flatten ++ unplanted).toVector.distinct
      val lemmas = asked.zipWithIndex.map((planted, index) =>
        (
          LemmaNamed(LemmaIdentifier(index), planted.name),
          LemmaSides(
            LemmaIdentifier(index),
            instruction(planted.left),
            instruction(planted.right)
          )
        )
      )
      val expected = asked.zipWithIndex
        .flatMap((planted, index) =>
          files.toVector.zipWithIndex
            .collectFirst {
              case (declared, file)
                  if declared.exists(found =>
                    found.name == planted.name &&
                      Configured.same(
                        instruction(found.left),
                        instruction(planted.left)
                      ) &&
                      Configured.same(
                        instruction(found.right),
                        instruction(planted.right)
                      )
                  ) =>
                LemmaIdentifier(index) -> paths(file).getFileName.toString
            }
        )
        .toMap
      val found = LemmaSources
        .attributed(directory, paths, lemmas)
        .map((lemma, attribution) =>
          lemma -> attribution._1.getFileName.toString
        )
      paths.foreach(Files.delete)
      Files.delete(directory)
      Result.diff(found, expected)(_ == _)
  }
