package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The law of `ReadableText.Printed.laidOutPieces`
  * on the instructions
  * of `SharingInstructions`, printed by `ReadableText.printedNameless`, at
  * generated widths: the tokens of the laid out pieces spell `laidOut` at the
  * same width, and their other pieces (openings, closings and marks) are the
  * printed pieces' own, in the same order. Its purpose is to catch a text view
  * whose text differs from the laid out text, such as white space put inside
  * a node it does not belong to or a token respelled, and pieces whose
  * structure or marks the respelling lost.
  */
class LaidOutPiecesLawTest extends GeneratedProperties:

  property("the laid out pieces spell the laid out text and keep the printed structure") {
    (for
      instruction <- SharingInstructions.instructions
      width <- Gen.int(Range.linear(8, ReadableText.lineWidth))
    yield (instruction, width))
      .forAllWithLog((instruction, width) => s"width $width: ${ReadableText.printedNameless(instruction).text}")
      .map((instruction, width) =>
        val printed = ReadableText.printedNameless(instruction)
        val pieces = printed.laidOutPieces(width)
        val laidOut = printed.laidOut(width)
        val spelled = pieces.collect { case ReadableText.Piece.Token(token) => token }.mkString
        def structure(of: Vector[ReadableText.Piece]): Vector[ReadableText.Piece] =
          of.filter {
            case ReadableText.Piece.Token(_) => false
            case _                           => true
          }
        Result.all(
          List(
            Result
              .assert(spelled == laidOut)
              .log(s"the tokens spell\n$spelled\nnot the laid out text\n$laidOut"),
            Result.assert(structure(pieces) == structure(printed.pieces)).log("the structure differs from the printed pieces'")
          )
        )
      )
  }
