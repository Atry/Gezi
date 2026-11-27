package com.yang_bo.gezi.narrowblocks.groups

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.NoFacts

/** The law of the JVM array group backend (`JvmArrayGroupBackend`): each
  * operation gives the rows the scalar backend, the reference semantics of
  * every backend (`GroupBackend`), gives on the same table, on generated tables
  * of row numbers, naturals and truth values, joins by keys of values, of two
  * columns and of unlike kinds among them, a constant and a filter's test
  * decided column by column; and the row numbers a table makes are held as
  * `int[]` (`JvmArrayColumn.Rows`), so that the kernels, not the scalar walk,
  * move them; and a 32-bit native on columns of ints gives the scalar backend's
  * rows, its sum, difference, product or negation kept as a column of ints; and
  * two operands of k distinct values in one frame row join to k² rows, the size
  * read back before the join is made.
  *
  * Its purpose is to catch a kernel used with its operands swapped or its
  * factors misaligned (the outer product's left rows outer), a join that pairs
  * rows by another key, and a column of row numbers left as values, which would
  * give the right rows and skip the kernels.
  */
class JvmArrayGroupBackendLawTest extends GeneratedProperties:

  private val scalar = ScalarGroupBackend
  private val arrays = JvmArrayGroupBackend

  /** The kernels' class, defined before the first test. */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => JvmArrayKernels.iota(1))

  private val natural: Gen[GroupValue] = Gen
    .long(Range.linear(0L, 4L))
    .map(value => GroupValue.Natural(BigInteger.valueOf(value)))

  private val truth: Gen[GroupValue] = Gen.boolean.map(GroupValue.Truth(_))

  /** The rows of a generated table, a column of row numbers below 4, then
    * naturals below 5, then truth values, up to 6 rows.
    */
  private val tableRows: Gen[Vector[Vector[GroupValue]]] =
    for
      rowCount <- Gen.int(Range.linear(0, 6))
      rows <- Gen
        .int(Range.linear(0, 3))
        .map(GroupValue.Row(_))
        .list(Range.singleton(rowCount))
      naturals <- natural.list(Range.singleton(rowCount))
      truths <- truth.list(Range.singleton(rowCount))
    yield rows
      .lazyZip(naturals)
      .lazyZip(truths)
      .map((row, value, test) => Vector(row, value, test))
      .toVector

  private def scalarTable(
      rows: Vector[Vector[GroupValue]]
  ): GroupTable[scalar.Column] =
    scalar.table(
      Vector.tabulate(3)(index => scalar.column(rows.map(_(index)))),
      rows.size
    )

  private def arrayTable(
      rows: Vector[Vector[GroupValue]]
  ): GroupTable[arrays.Column] =
    arrays.table(
      Vector.tabulate(3)(index => arrays.column(rows.map(_(index)))),
      rows.size
    )

  /** Whether every column of the table that holds row numbers holds them as
    * `int[]`.
    */
  private def rowsAsArrays(table: GroupTable[arrays.Column]): Boolean =
    table.columns.forall {
      case JvmArrayColumn.Values(values) =>
        values.isEmpty || !(values.forall(
          _.isInstanceOf[GroupValue.Row]
        ) || values.forall(_.isInstanceOf[GroupValue.IntBits]) ||
          values.forall(_.isInstanceOf[GroupValue.Truth]))
      case JvmArrayColumn.Rows(_) | JvmArrayColumn.Ints(_, _) |
          JvmArrayColumn.Truths(_) =>
        true
    }

  property(
    "each operation gives the scalar backend's rows, row numbers held as arrays"
  ) {
    for
      leftRows <- tableRows.forAll
      rightRows <- tableRows.forAll
    yield
      val (leftScalar, rightScalar) =
        (scalarTable(leftRows), scalarTable(rightRows))
      val (leftArrays, rightArrays) =
        (arrayTable(leftRows), arrayTable(rightRows))
      val operations: Vector[
        (String, GroupTable[arrays.Column], Vector[Vector[GroupValue]])
      ] = Vector(
        (
          "product",
          arrays.product(leftArrays, rightArrays),
          scalar.rows(scalar.product(leftScalar, rightScalar))
        ),
        (
          "concatenated",
          arrays.concatenated(leftArrays, rightArrays),
          scalar.rows(scalar.concatenated(leftScalar, rightScalar))
        ),
        (
          "numbered",
          arrays.numbered(leftArrays),
          scalar.rows(scalar.numbered(leftScalar))
        ),
        (
          "joined",
          arrays.joined(leftArrays, rightArrays, Vector(0), Vector(0)),
          scalar.rows(
            scalar.joined(leftScalar, rightScalar, Vector(0), Vector(0))
          )
        ),
        (
          "selected",
          arrays.selected(leftArrays, 2)._1,
          scalar.rows(scalar.selected(leftScalar, 2)._1)
        ),
        (
          "unique",
          arrays.unique(leftArrays),
          scalar.rows(scalar.unique(leftScalar))
        ),
        (
          "projected",
          arrays.projected(leftArrays, Vector(2, 0)),
          scalar.rows(scalar.projected(leftScalar, Vector(2, 0)))
        ),
        (
          "computed",
          arrays.computed(leftArrays, GroupOperation.Zero, Vector(1)),
          scalar.rows(
            scalar.computed(leftScalar, GroupOperation.Zero, Vector(1))
          )
        ),
        // Keys of values and of two columns, ranked over both sides together.
        (
          "joined by naturals",
          arrays.joined(leftArrays, rightArrays, Vector(1), Vector(1)),
          scalar.rows(
            scalar.joined(leftScalar, rightScalar, Vector(1), Vector(1))
          )
        ),
        (
          "joined by two keys",
          arrays.joined(leftArrays, rightArrays, Vector(1, 2), Vector(1, 2)),
          scalar.rows(
            scalar.joined(leftScalar, rightScalar, Vector(1, 2), Vector(1, 2))
          )
        ),
        (
          "joined by unlike keys",
          arrays.joined(leftArrays, rightArrays, Vector(0), Vector(2)),
          scalar.rows(
            scalar.joined(leftScalar, rightScalar, Vector(0), Vector(2))
          )
        ),
        (
          "unique of two columns",
          arrays.unique(arrays.projected(leftArrays, Vector(2, 1))),
          scalar.rows(scalar.unique(scalar.projected(leftScalar, Vector(2, 1))))
        ),
        // Filled and decided column by column.
        (
          "a word constant",
          arrays.computed(
            leftArrays,
            GroupOperation.Constant(
              GroupValue.IntBits(com.yang_bo.gezi.jit.JvmIntFamily.identity, -1)
            ),
            Vector()
          ),
          scalar.rows(
            scalar.computed(
              leftScalar,
              GroupOperation.Constant(
                GroupValue.IntBits(com.yang_bo.gezi.jit.JvmIntFamily.identity, -1)
              ),
              Vector()
            )
          )
        ),
        (
          "a natural constant",
          arrays.computed(
            leftArrays,
            GroupOperation.Constant(GroupValue.Natural(BigInteger.TWO)),
            Vector()
          ),
          scalar.rows(
            scalar.computed(
              leftScalar,
              GroupOperation.Constant(GroupValue.Natural(BigInteger.TWO)),
              Vector()
            )
          )
        ),
        (
          "admits truths",
          arrays.computed(
            leftArrays,
            GroupOperation.Admits(GroupRepresentation.Truth),
            Vector(2)
          ),
          scalar.rows(
            scalar.computed(
              leftScalar,
              GroupOperation.Admits(GroupRepresentation.Truth),
              Vector(2)
            )
          )
        ),
        (
          "admits no natural among truths",
          arrays.computed(
            leftArrays,
            GroupOperation.Admits(GroupRepresentation.Natural),
            Vector(2)
          ),
          scalar.rows(
            scalar.computed(
              leftScalar,
              GroupOperation.Admits(GroupRepresentation.Natural),
              Vector(2)
            )
          )
        ),
        (
          "admits positive naturals",
          arrays.computed(
            leftArrays,
            GroupOperation.Admits(GroupRepresentation.Positive),
            Vector(1)
          ),
          scalar.rows(
            scalar.computed(
              leftScalar,
              GroupOperation.Admits(GroupRepresentation.Positive),
              Vector(1)
            )
          )
        )
      )
      Result.all(
        operations.toList.map((name, found, expected) =>
          Result
            .diff((arrays.rows(found), rowsAsArrays(found)), (expected, true))(
              _ == _
            )
            .log(name)
        ) ++ List(
          Result
            .diff(
              (
                arrays.joinedSize(Vector(leftArrays, rightArrays), 4),
                arrays
                  .rowsAt(leftArrays, 0, IArray.from(leftRows.indices))
                  .toVector
              ),
              (
                scalar.joinedSize(Vector(leftScalar, rightScalar), 4),
                scalar
                  .rowsAt(leftScalar, 0, IArray.from(leftRows.indices))
                  .toVector
              )
            )(_ == _)
            .log("joinedSize and rowsAt")
        )
      )
  }

  /** The group method of a 32-bit native of the standard set. */
  private def jvmIntMethod(name: String, places: Int): GroupMethod =
    com.yang_bo.gezi.jit.NativeBackend.standard
      .natives(com.yang_bo.gezi.jit.NativeName.Function(name))
      .implementation match
      case method: com.yang_bo.gezi.jit.StaticBlockMethod =>
        GroupMethod(
          com.yang_bo.gezi.jit.NativeName.Function(name),
          method,
          Vector.fill(places)(GroupPlace.IntBits),
          Some(com.yang_bo.gezi.jit.JvmIntFamily.identity)
        )
      case other =>
        throw IllegalStateException(
          s"$name has a static block method, not $other"
        )

  private val word: Gen[GroupValue] =
    Gen
      .frequency1(
        3 -> Gen.int(Range.linearFrom(0, Int.MinValue, Int.MaxValue)),
        1 -> Gen.element1(0, 1, -1, Int.MinValue, Int.MaxValue)
      )
      .map(GroupValue.IntBits(com.yang_bo.gezi.jit.JvmIntFamily.identity, _))

  property(
    "a 32-bit native gives the scalar backend's rows, run as a kernel on columns of ints"
  ) {
    for
      rowCount <- Gen.int(Range.linear(0, 6)).forAll
      left <- word.list(Range.singleton(rowCount)).forAll
      right <- word.list(Range.singleton(rowCount)).forAll
    yield
      val rows = left
        .lazyZip(right)
        .map((first, second) => Vector(first, second))
        .toVector
      val (scalarTable, arrayTable) = (
        scalar.table(
          Vector.tabulate(2)(index => scalar.column(rows.map(_(index)))),
          rows.size
        ),
        arrays.table(
          Vector.tabulate(2)(index => arrays.column(rows.map(_(index)))),
          rows.size
        )
      )
      Result.all(
        Vector(
          ("jvm_int_add", 2),
          ("jvm_int_subtract", 2),
          ("jvm_int_multiply", 2),
          ("jvm_int_negate", 1),
          ("jvm_int_equal", 2),
          ("jvm_int_less_than", 2)
        ).toList
          .map((name, places) =>
            val method = jvmIntMethod(name, places)
            val arguments = Vector(0, 1).take(places)
            val found = arrays.called(arrayTable, method, arguments)
            // A sum, difference, product or negation stays a column of ints;
            // a comparison's 0 or 1 a column of truths held as ints.
            val heldAsInts = rowCount == 0 || (found.columns.lastOption match
              case Some(JvmArrayColumn.Ints(_, _)) =>
                !Set("jvm_int_equal", "jvm_int_less_than").contains(name)
              case Some(JvmArrayColumn.Truths(_)) =>
                Set("jvm_int_equal", "jvm_int_less_than").contains(name)
              case _ => false)
            Result
              .diff(
                (arrays.rows(found), heldAsInts),
                (
                  scalar.rows(scalar.called(scalarTable, method, arguments)),
                  true
                )
              )(_ == _)
              .log(name)
          )
      )
  }

  /** A table of one or two columns held as ints: row numbers below 4, then
    * 32-bit words or truths, up to 8 rows, so that duplicates are frequent.
    */
  private val intRows: Gen[Vector[Vector[GroupValue]]] =
    for
      rowCount <- Gen.int(Range.linear(0, 8))
      width <- Gen.int(Range.constant(1, 2))
      words <- Gen.boolean
      // Two families held as a JVM int, so that a join of one family's
      // column with the other's pairs no row.
      family <- Gen.element1(
        com.yang_bo.gezi.jit.JvmIntFamily.identity,
        com.yang_bo.gezi.jit.FamilyIdentity.Codec("jvm_bits_32")
      )
      rows <- Gen
        .int(Range.linear(0, 3))
        .map(GroupValue.Row(_))
        .list(Range.singleton(rowCount))
      others <- (if words then
                   Gen
                     .element1(0, 1, -1, Int.MinValue, Int.MaxValue)
                     .map(GroupValue.IntBits(family, _))
                 else truth).list(Range.singleton(rowCount))
    yield rows
      .lazyZip(others)
      .map((row, other) => Vector(row, other).take(width))
      .toVector

  property(
    "deduplication and joins of int columns run as kernels and give the scalar backend's rows"
  ) {
    for
      leftRows <- intRows.forAll
      rightRows <- intRows.forAll
    yield
      def tables(rows: Vector[Vector[GroupValue]]) =
        val width = rows.headOption.map(_.size).getOrElse(1)
        (
          scalar.table(
            Vector.tabulate(width)(index => scalar.column(rows.map(_(index)))),
            rows.size
          ),
          arrays.table(
            Vector.tabulate(width)(index => arrays.column(rows.map(_(index)))),
            rows.size
          )
        )
      val ((leftScalar, leftArrays), (rightScalar, rightArrays)) =
        (tables(leftRows), tables(rightRows))
      val unique = arrays.unique(leftArrays)
      // A join on the row numbers, and one on the last columns, of words or
      // truth values when both tables have two.
      val key =
        if leftArrays.columns.size == 2 && rightArrays.columns.size == 2 then 1
        else 0
      val joined = arrays.joined(leftArrays, rightArrays, Vector(0), Vector(0))
      val joinedByLast =
        arrays.joined(leftArrays, rightArrays, Vector(key), Vector(key))
      Result.diff(
        (
          arrays.rows(unique),
          rowsAsArrays(unique),
          arrays.rows(joined),
          rowsAsArrays(joined),
          arrays.rows(joinedByLast)
        ),
        (
          scalar.rows(scalar.unique(leftScalar)),
          true,
          scalar.rows(
            scalar.joined(leftScalar, rightScalar, Vector(0), Vector(0))
          ),
          true,
          scalar.rows(
            scalar.joined(leftScalar, rightScalar, Vector(key), Vector(key))
          )
        )
      )(_ == _)
  }

  /** A cell of an argument: a word (`Int.MinValue` among them), a natural, a
    * truth, a row number, or a word of another family, with small bits so that
    * ints of different kinds are often equal as ints.
    */
  private val argumentCell: Gen[GroupValue] = Gen.choice1(
    Gen
      .element1(0, 1, -1, Int.MinValue)
      .map(GroupValue.IntBits(com.yang_bo.gezi.jit.JvmIntFamily.identity, _)),
    natural,
    truth,
    Gen.int(Range.constant(0, 1)).map(GroupValue.Row(_)),
    Gen
      .int(Range.constant(0, 1))
      .map(GroupValue.IntBits(com.yang_bo.gezi.jit.FamilyIdentity.Codec("jvm_bits_32"), _))
  )

  /** The cells of one kind: words, truths, row numbers or the other family's
    * words.
    */
  private val oneKindCells: Gen[Gen[GroupValue]] = Gen.element1(
    Gen
      .element1(0, 1, -1, Int.MinValue)
      .map(GroupValue.IntBits(com.yang_bo.gezi.jit.JvmIntFamily.identity, _)),
    truth,
    Gen.int(Range.constant(0, 1)).map(GroupValue.Row(_)),
    Gen
      .int(Range.constant(0, 1))
      .map(GroupValue.IntBits(com.yang_bo.gezi.jit.FamilyIdentity.Codec("jvm_bits_32"), _))
  )

  /** An argument's relation over `rowCount` rows: for each row a group of up to
    * three cells, empty in some rows; one argument in two holds cells of one
    * kind only, drawn among the kinds held as ints (so that its column is held
    * as ints), the other any cells.
    */
  private def argumentRelation(rowCount: Int): Gen[Vector[(Int, GroupValue)]] =
    for
      oneKind <- Gen.boolean
      kind <- oneKindCells
      groups <- (if oneKind then kind else argumentCell)
        .list(Range.linear(0, 3))
        .list(Range.singleton(rowCount))
    yield groups.toVector.zipWithIndex.flatMap((group, row) =>
      group.map(cell => (row, cell))
    )

  /** Catches a memo that keys a call by its arguments' representation rather
    * than their groups' members (a group held as ints in one column and as
    * values in another, ints of equal bits and other kinds or families, an
    * empty group), that loses a finished call with no result, or that gives
    * back a call's groups out of order: generated relations of one to three
    * arguments over a frame, some rows not asked (as a row whose argument
    * waits), some calls finished with one result and some with none; the second
    * asking, the groups given back and the counts are the scalar backend's.
    */
  property(
    "the memo identifies calls by their arguments' groups and answers as the scalar backend's memo"
  ) {
    for
      rowCount <- Gen.int(Range.linear(1, 6)).forAll
      width <- Gen.int(Range.constant(1, 3)).forAll
      relations <- argumentRelation(rowCount)
        .list(Range.singleton(width))
        .forAll
      skipped <- Gen.int(Range.constant(0, 3)).forAll
      finishedShare <- Gen.int(Range.constant(0, 3)).forAll
    yield
      val recursion = NoFacts.thunkOrInstance(
        com.yang_bo.gezi.ir.Code.Slot(0),
        Vector(com.yang_bo.gezi.ir.Hole.Bound(0)),
        Vector.empty
      )
      // Every row but the skipped-th ones is asked.
      val rows = IArray.from(
        (0 until rowCount).filterNot(row =>
          skipped > 0 && row % (skipped + 1) == skipped
        )
      )
      def runOn(backend: GroupBackend) =
        val tables = relations.toVector.map(pairs =>
          backend.table(
            Vector(
              backend.column(pairs.map((row, _) => GroupValue.Row(row))),
              backend.column(pairs.map(_._2))
            ),
            pairs.size
          )
        )
        val (identified, firstHits, calls) = backend.asked(
          backend.emptyMemo(GroupMemoOption.Mapped),
          recursion,
          rows,
          tables
        )
        // Every finishedShare-th call finishes, every other one of those with
        // its row number times 10 as its one result and the rest with no
        // result, a hit with no row; the others stay unfinished.
        val finishing =
          calls.identities.indices.filter(_ % (finishedShare + 1) == 0).toVector
        val answering = finishing.zipWithIndex.collect {
          case (index, position) if position % 2 == 0 => index
        }
        val results = backend.table(
          Vector(
            backend.column(
              answering.map(index => GroupValue.Row(calls.rows(index)))
            ),
            backend.column(
              answering.map(index => GroupValue.Row(calls.rows(index) * 10))
            )
          ),
          answering.size
        )
        val stored = backend.stored(
          identified,
          recursion,
          IArray.from(finishing.map(calls.identities(_))),
          IArray.from(finishing.map(calls.rows(_))),
          results
        )
        val (_, hits, again) = backend.asked(stored, recursion, rows, tables)
        (
          backend.rows(firstHits),
          calls.rows.toVector,
          calls.identities.toVector.distinct.size,
          backend.rows(hits),
          again.rows.toVector,
          backend
            .keys(
              stored,
              recursion,
              IArray.from(calls.identities.toVector.distinct)
            )
            .map(backend.rows),
          backend.memoSizes(stored)
        )
      Result.diff(runOn(arrays), runOn(scalar))(_ == _)
  }

  /** Catches a call told apart by its column's representation: one site's
    * operand a column of words, another's a column of values mixing one of
    * those words with naturals and with ints of other kinds equal as ints; the
    * word is one call at both sites, each other value its own, as the scalar
    * backend does; a frame of no row asks nothing.
    */
  property(
    "calls of one recursion are identified by their values whatever their columns, as on the scalar backend"
  ) {
    for
      words <- Gen
        .element1(0, 1, -1, Int.MinValue)
        .map(GroupValue.IntBits(com.yang_bo.gezi.jit.JvmIntFamily.identity, _))
        .list(Range.linear(1, 4))
        .forAll
      naturals <- natural.list(Range.linear(1, 4)).forAll
      others <- Gen
        .choice1(
          Gen.boolean.map(GroupValue.Truth(_)),
          Gen.int(Range.constant(0, 1)).map(GroupValue.Row(_)),
          Gen
            .int(Range.constant(0, 1))
            .map(
              GroupValue
                .IntBits(com.yang_bo.gezi.jit.FamilyIdentity.Codec("jvm_bits_32"), _)
            ),
          Gen
            .int(Range.constant(0, 1))
            .map(GroupValue.IntBits(com.yang_bo.gezi.jit.JvmIntFamily.identity, _))
        )
        .list(Range.linear(0, 4))
        .forAll
      wordsFirst <- Gen.boolean.forAll
    yield
      val recursion = NoFacts.thunkOrInstance(
        com.yang_bo.gezi.ir.Code.Slot(0),
        Vector(com.yang_bo.gezi.ir.Hole.Bound(0)),
        Vector.empty
      )
      val mixed = words.toVector.take(1) ++ naturals.toVector ++ others.toVector
      val (first, second) =
        if wordsFirst then (words.toVector, mixed) else (mixed, words.toVector)
      def runOn(backend: GroupBackend) =
        // Each value its own row's group of one.
        def relation(values: Vector[GroupValue]) =
          backend.table(
            Vector(
              backend.column(values.indices.toVector.map(GroupValue.Row(_))),
              backend.column(values)
            ),
            values.size
          )
        def asked(memo: backend.Memo, values: Vector[GroupValue]) =
          backend.asked(
            memo,
            recursion,
            IArray.from(values.indices),
            Vector(relation(values))
          )
        val (afterNoRow, _, noCall) = backend.asked(
          backend.emptyMemo(GroupMemoOption.Mapped),
          recursion,
          IArray.empty[Int],
          Vector(relation(Vector.empty))
        )
        val (afterFirst, _, firstCalls) = asked(afterNoRow, first)
        val (afterSecond, _, secondCalls) = asked(afterFirst, second)
        // The first site's calls finish, each with its row number times 10.
        val results = backend.table(
          Vector(
            backend.column(firstCalls.rows.toVector.map(GroupValue.Row(_))),
            backend.column(
              firstCalls.rows.toVector.map(row => GroupValue.Row(row * 10))
            )
          ),
          firstCalls.rows.length
        )
        val stored = backend.stored(
          afterSecond,
          recursion,
          firstCalls.identities,
          firstCalls.rows,
          results
        )
        val (_, secondHits, secondMisses) = asked(stored, second)
        (
          noCall.rows.length,
          (firstCalls.identities.toVector ++ secondCalls.identities.toVector).distinct.size,
          backend.rows(secondHits),
          secondMisses.rows.toVector
        )
      Result.diff(runOn(arrays), runOn(scalar))(_ == _)
  }

  property(
    "two operands of k distinct values in one frame row join to k² rows, the size read before the join"
  ) {
    for values <- Gen
        .int(Range.linearFrom(0, Int.MinValue, Int.MaxValue))
        .list(Range.linear(0, 12))
        .map(_.distinct.toVector)
        .forAll
    yield
      val k = values.size.toLong
      // The relation of frame row 0 to each value: its operand's group.
      def relation(backend: GroupBackend) =
        backend.unique(
          backend.table(
            Vector(
              backend.column(values.map(_ => GroupValue.Row(0))),
              backend.column(
                values.map(
                  GroupValue.IntBits(com.yang_bo.gezi.jit.JvmIntFamily.identity, _)
                )
              )
            ),
            values.size
          )
        )
      val sizes = Vector[GroupBackend](scalar, arrays).map(backend =>
        backend.joinedSize(Vector(relation(backend), relation(backend)), 1)
      )
      Result.diff(sizes, Vector(k * k, k * k))(_ == _)
  }
