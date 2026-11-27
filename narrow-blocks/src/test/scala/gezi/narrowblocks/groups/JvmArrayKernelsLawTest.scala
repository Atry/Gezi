package gezi.narrowblocks.groups

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import gezi.generatedinputs.GeneratedProperties

/** The laws of the JVM array group backend's kernels (`JvmArrayKernels`), each
  * the concise definition of its kernel, on generated arrays whose cells
  * include 0, ±1, `Int.MinValue` and `Int.MaxValue` (a selection's masks of
  * cells 0 or 1), the packed keys' among them (their order the rows' under each
  * flip, their merge join the nested loop's pairs of equal keys); and the shape
  * of the loops C2 is to vectorize: the elementwise kernels, the negation and
  * the gather allocate their array once, before the loop, and their loop holds
  * no allocation, no call and no branch but the loop's test and its back edge.
  *
  * Its purpose is to catch a kernel that computes another value (an operand
  * swapped, a signed comparison for an unsigned one, a sign bit lost in the
  * branch-free comparisons, a row number off by one in an outer product's
  * factors, a flip applied to the wrong half of a packed key, a merge that
  * skips a run of equal keys) and a loop body that a change made into a shape
  * C2 does not vectorize.
  */
class JvmArrayKernelsLawTest extends GeneratedProperties:

  /** The kernels' class, defined before the first test. */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => JvmArrayKernels.iota(1))

  private val cell: Gen[Int] =
    Gen.frequency1(
      3 -> Gen.int(Range.linearFrom(0, Int.MinValue, Int.MaxValue)),
      1 -> Gen.element1(0, 1, -1, Int.MinValue, Int.MaxValue)
    )

  private def column(length: Int): Gen[IArray[Int]] =
    cell.list(Range.singleton(length)).map(IArray.from(_))

  private val length: Gen[Int] = Gen.int(Range.linear(0, 40))

  private def definition(name: String, left: Int, right: Int): Int = name match
    case "added"      => left + right
    case "subtracted" => left - right
    case "multiplied" => left * right
    case "equal"      => if left == right then 1 else 0
    case "lessThan"   => if left < right then 1 else 0
    case other        =>
      throw IllegalArgumentException(s"no elementwise kernel $other")

  property("an elementwise kernel computes its definition cell by cell") {
    for
      name <- Gen
        .int(Range.constant(0, JvmArrayKernels.elementwiseNames.size - 1))
        .map(JvmArrayKernels.elementwiseNames)
        .forAll
      count <- length.forAll
      left <- column(count).forAll
      // Half the time the right is the left, so that equality holds somewhere.
      same <- Gen.boolean.forAll
      drawn <- column(count).forAll
    yield
      val right = if same then left else drawn
      Result
        .diff(
          JvmArrayKernels.elementwiseOf(name, left, right).toVector,
          left.toVector.lazyZip(right.toVector).map(definition(name, _, _))
        )(_ == _)
        .log(name)
  }

  property("the negation, the concatenation and the selection") {
    for
      count <- length.forAll
      left <- column(count).forAll
      other <- length.forAll
      right <- column(other).forAll
      mask <- Gen
        .int(Range.constant(0, 1))
        .list(Range.singleton(count))
        .map(IArray.from(_))
        .forAll
    yield Result.diff(
      (
        JvmArrayKernels.negated(left).toVector,
        JvmArrayKernels.concatenated(left, right).toVector,
        JvmArrayKernels.compressed(left).toVector,
        JvmArrayKernels.compressedZeros(mask).toVector
      ),
      (
        left.toVector.map(-_),
        left.toVector ++ right.toVector,
        left.toVector.indices.filter(left(_) != 0).toVector,
        mask.toVector.indices.filter(mask(_) == 0).toVector
      )
    )(_ == _)
  }

  property("the row numbers, the gather and the outer product's factors") {
    for
      count <- length.forAll
      values <- column(count + 1).forAll
      rows <- Gen
        .int(Range.linear(0, count))
        .list(Range.linear(0, 30))
        .map(IArray.from(_))
        .forAll
      width <- Gen.int(Range.linear(0, 8)).forAll
    yield Result.diff(
      (
        JvmArrayKernels.iota(count).toVector,
        JvmArrayKernels.gathered(values, rows).toVector,
        JvmArrayKernels.repeated(count, width).toVector,
        JvmArrayKernels.tiled(count, width).toVector
      ),
      (
        (0 until count).toVector,
        rows.toVector.map(values(_)),
        (0 until count).toVector.flatMap(row => Vector.fill(width)(row)),
        Vector.fill(width)((0 until count).toVector).flatten
      )
    )(_ == _)
  }

  /** A cell's order in a column with the flip: unsigned for the sign bit,
    * signed for 0.
    */
  private def comparedWith(flip: Int)(left: Int, right: Int): Int =
    if flip == JvmArrayKernels.unsignedFlip then
      Integer.compareUnsigned(left, right)
    else Integer.compare(left, right)

  private val flip: Gen[Int] = Gen.element1(0, JvmArrayKernels.unsignedFlip)

  property(
    "packed keys: high and low undo the packing, the keys' signed order is the rows', and sortedUnique keeps one of each in that order"
  ) {
    for
      count <- length.forAll
      first <- column(count).forAll
      second <- Gen
        .element1(0, 1, -1, Int.MinValue, Int.MaxValue)
        .list(Range.singleton(count))
        .map(IArray.from(_))
        .forAll
      firstFlip <- flip.forAll
      secondFlip <- flip.forAll
    yield
      val keys = JvmArrayKernels.packed(first, firstFlip, second, secondFlip)
      val rows = first.toVector.zip(second.toVector)
      def rowCompared(left: (Int, Int), right: (Int, Int)): Int =
        val byFirst = comparedWith(firstFlip)(left._1, right._1)
        if byFirst != 0 then byFirst
        else comparedWith(secondFlip)(left._2, right._2)
      val pairs = for i <- rows.indices.toVector; j <- rows.indices.toVector
      yield (i, j)
      val rowOrder = Ordering.fromLessThan[(Int, Int)](rowCompared(_, _) < 0)
      Result.diff(
        (
          JvmArrayKernels.high(keys, firstFlip).toVector,
          JvmArrayKernels.low(keys, secondFlip).toVector,
          pairs.map((i, j) =>
            Integer.signum(java.lang.Long.compare(keys(i), keys(j)))
          ),
          JvmArrayKernels
            .sortedUnique(keys)
            .toVector
            .map(key => (rows(keys.indexOf(key))))
        ),
        (
          first.toVector,
          second.toVector,
          pairs.map((i, j) => Integer.signum(rowCompared(rows(i), rows(j)))),
          rows.distinct.sorted(using rowOrder)
        )
      )(_ == _)
  }

  property(
    "mergeJoined pairs the positions of equal keys, and histogram counts each row"
  ) {
    for
      leftCount <- length.forAll
      rightCount <- length.forAll
      leftKeys <- Gen
        .element1(0, 1, -1, Int.MinValue, Int.MaxValue)
        .list(Range.singleton(leftCount))
        .map(IArray.from(_))
        .forAll
      rightKeys <- Gen
        .element1(0, 1, -1, Int.MinValue, Int.MaxValue)
        .list(Range.singleton(rightCount))
        .map(IArray.from(_))
        .forAll
      keyFlip <- flip.forAll
      rowCount <- Gen.int(Range.linear(1, 6)).forAll
      rows <- Gen.int(Range.constant(0, 5)).list(Range.linear(0, 30)).forAll
    yield
      def sorted(keys: IArray[Int]): IArray[Long] =
        JvmArrayKernels.sortedUnique(
          JvmArrayKernels.packed(
            keys,
            keyFlip,
            JvmArrayKernels.iota(keys.length),
            0
          )
        )
      val joined =
        JvmArrayKernels.mergeJoined(sorted(leftKeys), sorted(rightKeys))
      val bounded = IArray.from(rows.map(_ % rowCount))
      Result.diff(
        (
          JvmArrayKernels
            .high(joined, 0)
            .toVector
            .zip(JvmArrayKernels.low(joined, 0).toVector)
            .sorted,
          JvmArrayKernels.histogram(bounded, rowCount).toVector
        ),
        (
          (for
            i <- leftKeys.indices.toVector; j <- rightKeys.indices.toVector
            if leftKeys(i) == rightKeys(j)
          yield (i, j)),
          (0 until rowCount).toVector.map(row => bounded.count(_ == row))
        )
      )(_ == _)
  }

  property(
    "filled repeats its value, ranked gives each key's position among the distinct keys, firstRows each rank's first position"
  ) {
    for
      count <- length.forAll
      value <- cell.forAll
      keys <- Gen
        .element1(0L, 1L, -1L, Long.MinValue, Long.MaxValue)
        .list(Range.singleton(count))
        .map(IArray.from(_))
        .forAll
    yield
      val distinct = JvmArrayKernels.sortedUnique(keys)
      val ranks = JvmArrayKernels.ranked(keys, distinct)
      Result.diff(
        (
          JvmArrayKernels.filled(count, value).toVector,
          ranks.toVector,
          JvmArrayKernels.firstRows(ranks, distinct.length).toVector
        ),
        (
          Vector.fill(count)(value),
          keys.toVector.map(key => keys.toVector.distinct.sorted.indexOf(key)),
          keys.toVector.distinct.sorted.map(key => keys.indexOf(key))
        )
      )(_ == _)
  }

  test(
    "the vectorized kernels' loops allocate before the loop and hold no call or other branch"
  ) {
    // The class file read by the JDK's javap, beside the JVM this test runs
    // on: Scala 3 does not load the sealed models of java.lang.classfile.
    val directory = Files.createTempDirectory("jvm-array-kernels-shape")
    val classFile = directory.resolve("JvmArrayKernelClass.class")
    Files.write(classFile, JvmArrayKernels.classBytes)
    val javap = Path
      .of(ProcessHandle.current().info().command().orElseThrow())
      .resolveSibling("javap")
    val process =
      ProcessBuilder(javap.toString, "-c", classFile.toString).start()
    val listing = String(
      process.getInputStream.readAllBytes(),
      StandardCharsets.UTF_8
    ).linesIterator.toVector
    assertEquals(process.waitFor(), 0)
    val method = """\s*public static int\[\] (\w+)\(.*""".r
    val bodies = listing
      .foldLeft((Map.empty[String, Vector[String]], Option.empty[String])) {
        case ((found, _), method(name)) =>
          (found.updated(name, Vector.empty), Some(name))
        case ((found, Some(name)), line) =>
          (found.updated(name, found(name) :+ line), Some(name))
        case ((found, None), _) => (found, None)
      }
      ._1
    val opcode = """\s*\d+: (\w+).*""".r
    val shapes =
      (JvmArrayKernels.elementwiseNames ++ Vector("negated", "gathered")).map {
        name =>
          val opcodes = bodies
            .getOrElse(name, throw IllegalStateException(s"no kernel $name"))
            .collect { case opcode(found) => found }
          (
            name,
            opcodes.count(_ == "newarray"),
            opcodes.count(_.startsWith("invoke")),
            opcodes
              .filter(found => found.startsWith("if") || found == "goto")
              .sorted
          )
      }
    assertEquals(
      shapes,
      shapes.map((name, _, _, _) => (name, 1, 0, Vector("goto", "if_icmpge")))
    )
  }
