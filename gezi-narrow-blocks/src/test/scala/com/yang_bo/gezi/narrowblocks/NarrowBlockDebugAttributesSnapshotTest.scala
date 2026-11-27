package com.yang_bo.gezi.narrowblocks

import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.FreeNames
import com.yang_bo.gezi.frontend.Lambdalattice
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.SeededSnapshots
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.Pure
import com.yang_bo.gezi.jit.BinaryNaturalFamily
import com.yang_bo.gezi.jit.NativesProvider
import com.yang_bo.gezi.locations.SourceMap
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.CombinatorProperty
import com.yang_bo.gezi.standardlibrary.NativeBound
import com.yang_bo.gezi.standardlibrary.Property
import com.yang_bo.gezi.standardlibrary.StandardLibraryIndex
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.io.PrintWriter
import java.io.StringWriter
import java.lang.classfile.Attributes
import java.lang.classfile.ClassFile
import java.net.URI
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.util.spi.ToolProvider
import scala.jdk.OptionConverters.*
import scala.util.Using
import snapshot4s.generated.snapshotConfig

private given narrowBlockDebugAttributesSnapshotTestNoFacts: NoFacts.type =
  NoFacts

/** The debugging attributes of a class of narrow blocks, on generated narrow
  * programs written as texts: in each of one or two files, closed narrow
  * naturals, sums of the binary naturals' plus over numerals, each on a line of
  * its own after a generated number of empty lines, the definitions written in
  * place. The blocks of every file (`NarrowBlockCompilation.locatedBlocks`, the
  * file read with its map) are compiled into one class with their attributes
  * written, and the snapshot records the texts with what a reader of the class
  * file sees: what `javap -c -l` prints (the `SourceFile` and each method's
  * `LineNumberTable`) and the `SourceDebugExtension`. Its purpose is to catch a
  * block given another line than its root's, a class whose blocks come from two
  * files given no source map or one whose lines do not lead back to them, and a
  * block's place taken from another occurrence than its first. The second test
  * checks that a class compiled with the attributes omitted has none of them.
  *
  * The names are bound by hand, as in `NarrowBlockDepthLawTest`, here to the
  * instructions of the definitions' texts, so that a definition written in
  * place in a program is the instruction bound.
  */
class NarrowBlockDebugAttributesSnapshotTest
    extends GeneratedProperties
    with SeededSnapshots:

  private val zeroText = "(λx. x x)"
  private val evenText = "(λx. λy. y x)"
  private val oddText = "(λx. λy. λz. z y x)"
  private val plusText = "(λx. λy. y y x)"

  /** The criterion `binary_set` whose `data_family` lists zero, even and odd,
    * in the codec's order (`BinaryNaturalFamily`).
    */
  private val binarySetText = "(λx. λy. x (y y))"

  private def instruction(text: String): Configured[NoFacts.type] =
    val read = Lambdalattice.located(text, FreeNames.Rejected)
    Defunctionalization
      .locatedThunkInstruction(read.term, read.spans, URI("test:definition"))(
        using com.yang_bo.gezi.ir.NoFacts
      )
      ._1

  private val compilation = NarrowBlockCompilation(
    StandardLibraryIndex(
      NoFacts,
      Vector.empty,
      Vector.empty,
      Vector(
        NativeBound(Pure.required(instruction(plusText)), "wren_binary_plus")
      ),
      Vector(
        CombinatorProperty(
          Pure.required(instruction(binarySetText)),
          Property.NativeSpecialization(BinaryNaturalFamily.identity.name)
        ),
        CombinatorProperty(
          Pure.required(instruction(binarySetText)),
          Property.DataFamily(
            0,
            Vector(
              instruction(zeroText),
              instruction(evenText),
              instruction(oddText)
            ).map(Pure.required)
          )
        )
      )
    ),
    NativesProvider.loaded,
    com.yang_bo.gezi.weakhead.ReadingConfiguration.withoutFacts
  )

  /** The canonical binary numeral of the value, written in place, least
    * significant digit outermost.
    */
  private def numeral(value: Int): String =
    if value == 0 then zeroText
    else
      s"(${if (value & 1) == 1 then oddText else evenText} ${numeral(value >> 1)})"

  /** A closed narrow natural with a sum in it, which makes it a block: a
    * left-nested sum of two or three numerals of at most 5.
    */
  private val natural: Gen[String] =
    for
      first <- Gen.int(Range.constant(0, 5))
      rest <- Gen.list(Gen.int(Range.constant(0, 5)), Range.constant(1, 2))
    yield rest.foldLeft(numeral(first))((sum, literal) =>
      s"($plusText $sum ${numeral(literal)})"
    )

  /** A file's text: one to three naturals, each after zero to two empty lines
    * on a line of its own, the arguments of a function of one more parameter,
    * written on the first line, `(λa0. … λz. z)`, so that the application is no
    * natural and each argument is a block of its own. (A choice of naturals
    * would be one block, its chosen member's.)
    */
  private val file: Gen[String] =
    for naturals <- Gen.list(
        for
          empty <- Gen.int(Range.constant(0, 2))
          written <- natural
        yield "\n" * empty + written,
        Range.constant(1, 3)
      )
    yield
      val parameters = naturals.indices.map(number => s"λa$number. ").mkString
      s"($parameters λz. z)\n" + naturals.mkString("\n")

  /** One or two files, the second's name distinct from the first's. */
  private val files: Gen[Vector[(URI, String)]] =
    Gen
      .list(file, Range.constant(1, 2))
      .map(
        _.toVector.zipWithIndex.map((text, number) =>
          (URI(s"file:///corpora/narrow/program_$number.lambdalattice"), text)
        )
      )

  /** The blocks of the files, each file read with its map, in the files' order.
    */
  private def located(
      written: Vector[(URI, String)]
  ): Vector[(Configured[NoFacts.type], SourceMap)] =
    written.flatMap((uri, text) =>
      val read = Lambdalattice.located(text, FreeNames.Rejected)
      val (program, map) =
        Defunctionalization.locatedThunkInstruction(read.term, read.spans, uri)(
          using com.yang_bo.gezi.ir.NoFacts
        )
      compilation.locatedBlocks(program, map)
    )

  /** What a reader of the class file of the files' blocks, compiled with the
    * attributes asked for, reads of it: what `javap -c -l` prints (its
    * `SourceFile`, as the line `Compiled from`, its methods and their
    * `LineNumberTable`s), the instructions left out, and its
    * `SourceDebugExtension`, which javap prints only verbosely, with the
    * constant pool. Throws `IllegalStateException` when javap fails.
    */
  private def read(
      texts: Vector[(URI, String)],
      debug: Vector[(Configured[NoFacts.type], SourceMap)] => DebugAttributes,
      stop: StopSignal
  ): Either[String, ReadClass] =
    val blocks = located(texts)
    compilation.classFile(blocks.map(_._1), debug(blocks), stop).map(javap)

  private def javap(
      bytes: scala.collection.immutable.ArraySeq[Byte]
  ): ReadClass =
    val file = Files.createTempFile("narrow-blocks", ".class")
    Using.resource(Files.newOutputStream(file))(stream =>
      bytes.foreach(byte => stream.write(byte.toInt))
    )
    val printed = StringWriter()
    val errors = StringWriter()
    val status = ToolProvider
      .findFirst("javap")
      .orElseThrow(() => IllegalStateException("no javap in this JDK"))
      .run(PrintWriter(printed), PrintWriter(errors), "-c", "-l", file.toString)
    val sourceMap = ClassFile
      .of()
      .parse(file)
      .findAttribute(Attributes.sourceDebugExtension())
      .toScala
      .map(found => String(found.contents(), StandardCharsets.UTF_8))
    Files.delete(file)
    if status != 0 then
      throw IllegalStateException(s"javap failed with $status: $errors")
    val instruction = """\s+(Code:|\d+: .*)""".r
    ReadClass(
      printed.toString.linesIterator
        .filterNot(line =>
          line.startsWith("Classfile ") || instruction.matches(line)
        )
        .mkString("\n"),
      sourceMap
    )

  private def written(texts: Vector[(URI, String)])(
      blocks: Vector[(Configured[NoFacts.type], SourceMap)]
  ): DebugAttributes =
    DebugAttributes.Written(blocks.map(_._2), texts.toMap)

  stoppableTest(
    "a class of narrow blocks gives each block's method the line of its root, through a source map for two files"
  ) { stopped =>
    assertSeededSnapshot(
      files,
      seed = 1504L,
      count = 10,
      "narrow-blocks/debug-attributes.txt"
    )(
      _.map((uri, text) => s"## $uri\n$text").mkString("\n"),
      identity[String]
    )(texts =>
      read(texts, written(texts), StopSignal.completedWith(stopped))
        .fold(reason => s"the blocks do not compile: $reason", _.text)
    )
  }

  stoppableProperty(
    "a class of narrow blocks compiled with the attributes omitted has none of them"
  ) { stopped =>
    for texts <- files.forAllWithLog(
        _.map((uri, text) => s"## $uri\n$text").mkString("\n")
      )
    yield read(
      texts,
      _ => DebugAttributes.Omitted,
      StopSignal.completedWith(stopped)
    ) match
      case Left(reason) =>
        Result.failure.log(s"the blocks do not compile: $reason")
      case Right(found) =>
        Result.all(
          List(
            Result
              .assert(!found.javap.contains("Compiled from"))
              .log("a SourceFile"),
            Result
              .assert(found.sourceMap.isEmpty)
              .log("a SourceDebugExtension"),
            Result
              .assert(!found.javap.contains("LineNumberTable"))
              .log(found.javap)
          )
        )
  }

/** What `NarrowBlockDebugAttributesSnapshotTest` reads of a class file: what
  * `javap -c -l` prints of it, its instructions left out, and its
  * `SourceDebugExtension`.
  */
final case class ReadClass(javap: String, sourceMap: Option[String]):

  /** Both, the source map after javap's text. */
  def text: String = (javap +: sourceMap.toVector.map(map =>
    s"SourceDebugExtension:\n$map".stripSuffix("\n")
  )).mkString("\n")
