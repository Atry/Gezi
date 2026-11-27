package gezi.migration

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.generatedinputs.SeededSnapshots
import snapshot4s.generated.snapshotConfig

/** The conversion of a file's export to the binder `export`
  * (`ExportBinderConversion.converted`) on generated module texts: a spine of
  * zero to three local definitions `(λtuple. tuple V) λx.`, V a generated
  * closed term, ending with the tuple `λx tuple. tuple M1 … Mn`, each member a
  * name the spine binds or a closed term, or, with no definition, the tuple
  * alone, `λtuple. tuple M1 … Mn`; with generated layout (spaces, line breaks,
  * blank lines and comments).
  *
  *   - Law: the conversion succeeds (each conversion checks that the new text
  *     reads to the old term with its export moved, holds the same comments and
  *     is formatted), and converting its output again is refused, since no
  *     tuple is left at the end of the spine. Its purpose is to catch a
  *     conversion that moves the wrong binder, loses a comment or a name, or
  *     leaves a tuple behind.
  *   - Snapshot: texts and their conversions, from a fixed seed. Its purpose is
  *     to record the text the conversion writes, an output as complex as the
  *     conversion.
  */
class ExportBinderConversionTest
    extends GeneratedProperties
    with SeededSnapshots:

  /** A closed text the printer writes. */
  private val printed: Gen[String] =
    HoasGenerators.closedTerm.map(LambdalatticeText.text)

  /** A module text: the local definitions' values, then the members. */
  private val modules: Gen[String] =
    for
      values <- printed.list(Range.linear(0, 3))
      names = values.indices.map(index => s"x$index").toVector
      memberCount <- Gen.int(Range.linear(1, 3))
      closedMember = printed.map(text => s"($text)")
      member = names match
        case first +: rest =>
          Gen.frequency1(1 -> closedMember, 2 -> Gen.element1(first, rest*))
        case _ => closedMember
      members <- member.list(Range.singleton(memberCount))
      laidOut <- LambdalatticeText.withLayout(
        module(values.toVector, names, members.toVector)
      )
    yield laidOut

  /** The text of a module of the local definitions and the members. */
  private def module(
      values: Vector[String],
      names: Vector[String],
      members: Vector[String]
  ): String =
    val tuple = s"tuple ${members.mkString(" ")}"
    if values.isEmpty then s"λtuple. $tuple"
    else
      val definitions =
        values.zip(names).zipWithIndex.map { case ((value, name), index) =>
          val binders =
            if index == values.size - 1 then s"$name tuple" else name
          s"(λtuple. tuple ($value)) λ$binders."
        }
      s"λ. ${definitions.mkString(" ")} $tuple"

  private def converted(text: String): String =
    ExportBinderConversion.converted(Vector.empty, text)

  property(
    "the conversion succeeds, and converting its output again is refused"
  ) {
    modules
      .forAllWithLog(identity)
      .map(text =>
        val once = converted(text)
        val again =
          try Left(converted(once))
          catch case ExportBinderConversion.Refused(reason) => Right(reason)
        Result
          .assert(again.isRight)
          .log(s"converted again: ${again.left.getOrElse("")}")
      )
  }

  test("converting generated module texts") {
    assertSeededSnapshot(
      modules,
      20261120L,
      12,
      "export_binder/generated_modules.txt"
    )(identity, identity[String])(converted)
  }
