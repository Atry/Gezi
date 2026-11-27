package com.yang_bo.gezi.standardlibrary

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties

/** Law: in a generated knowledge text holding planted lemma declarations,
  * `λs. s (λk. k "NAME") (LEFT) (RIGHT) PROOF` among other terms, comments and
  * line breaks, `LemmaSources.declared` finds exactly the planted declarations,
  * each with its name and the spans of its two sides, which slice the text back
  * to the sides as written.
  *
  * Purpose: catch a reader that misses a declaration, decodes a name otherwise
  * than the literal the file writes, or takes a side's span from another node,
  * so that a trace's lemma would point at the wrong text. The texts are
  * generated, so the law holds of the reader and not of the repository's
  * knowledge files: a name holds a character beyond the basic plane, where a
  * span counts code points, not UTF-16 units.
  */
class LemmaDeclarationsLawTest extends GeneratedProperties:

  /** A closed side's text, `λv0 … vk. BODY`, its body an application of
    * variables and abstractions, each compound argument parenthesized.
    */
  private def body(depth: Int, size: Int): Gen[String] =
    if size <= 0 then
      Gen.int(Range.linear(0, depth - 1)).map(index => s"v$index")
    else
      Gen.int(Range.linear(0, 2)).flatMap {
        case 0 => Gen.int(Range.linear(0, depth - 1)).map(index => s"v$index")
        case 1 =>
          for
            function <- body(depth, size / 2)
            argument <- body(depth, size / 2)
          yield s"$function ($argument)"
        case _ => body(depth + 1, size - 1).map(inner => s"(λv$depth. $inner)")
      }

  private val sides: Gen[String] =
    for
      binders <- Gen.int(Range.linear(1, 3))
      size <- Gen.int(Range.linear(0, 6))
      written <- body(binders, size)
    yield s"λ${(0 until binders).map(index => s"v$index").mkString(" ")}. $written"

  private val names: Gen[String] =
    for
      words <- Gen
        .elementUnsafe(List("closure", "applied", "unit", "choice", "𝔽", "ß"))
        .list(Range.linear(1, 3))
      number <- Gen.int(Range.linear(0, 99))
    yield s"${words.mkString("_")}_$number"

  private final case class Planted(name: String, left: String, right: String)

  private val separators: Gen[String] =
    Gen.elementUnsafe(List(" ", "\n  ", "\n  # a comment = λ \"name\"\n  "))

  private def declaration(planted: Planted, separator: String): String =
    s"""(λs. s${separator}(λk. k "${planted.name}")${separator}(${planted.left})${separator}(${planted.right}) λproof. proof)"""

  /** The text: the planted declarations and some decoys (a declaration's shape
    * with no string literal for a name) in one choice under `export`.
    */
  private val texts: Gen[(String, Vector[Planted])] =
    for
      count <- Gen.int(Range.linear(0, 4))
      planted <- (for name <- names; left <- sides; right <- sides
      yield (name, left, right)).list(Range.singleton(count))
      decoys <- sides.list(Range.linear(0, 2))
      separator <- separators
    yield
      val distinct = planted.zipWithIndex.map {
        case ((name, left, right), index) =>
          Planted(s"${name}_$index", left, right)
      }.toVector
      val members = distinct.map(declaration(_, separator)) ++ decoys.map(
        decoy => s"(λs. s ($decoy) ($decoy) ($decoy) λproof. proof)"
      )
      val chain =
        if members.isEmpty then "λx. x" else members.mkString(s"${separator}+ ")
      (s"# generated knowledge\nλ export\n. export ($chain)\n", distinct)

  property(
    "the declarations found are the planted ones, their spans slicing back to their sides"
  ) {
    for (text, planted) <- texts.forAll
    yield
      val path = LibraryFiles.buildRoot
        .resolve("corpora")
        .resolve("compiler")
        .resolve("generated.lambdalattice")
      @scala.annotation.tailrec
      def codePointsFrom(index: Int, found: Vector[Int]): Vector[Int] =
        if index >= text.length then found
        else
          val point = text.codePointAt(index)
          codePointsFrom(index + Character.charCount(point), found :+ point)
      val codePoints = codePointsFrom(0, Vector.empty)
      def slice(span: com.yang_bo.gezi.locations.Span): String =
        codePoints
          .slice(span.start, span.end)
          .map(Character.toString(_))
          .mkString
      val found = LemmaSources
        .declared(path, text)
        .map(source =>
          Planted(source.name, slice(source.left), slice(source.right))
        )
      Result.diff(found.sortBy(_.name), planted.sortBy(_.name))(_ == _)
  }
