package gezi.narrowblocks.groups

/** A column of the JVM array group backend: row numbers held as one `int[]`
  * (`Rows`), the values of a family held as a JVM `int` as one `int[]`
  * (`Ints`), truth values as one `int[]` of 0 and 1 (`Truths`), all moved by
  * the kernels of `JvmArrayKernels`, or any other values held as the scalar
  * backend holds them (`Values`), whose operations are the scalar backend's. A
  * column of row numbers, of one family's ints or of truth values is always
  * `Rows`, `Ints` or `Truths` once the backend made it
  * (`JvmArrayGroupBackend.column`).
  */
enum JvmArrayColumn:
  case Rows(numbers: IArray[Int])
  case Ints(family: gezi.jit.FamilyIdentity, bits: IArray[Int])
  case Truths(cells: IArray[Int])
  case Values(values: Vector[GroupValue])

  /** The column's cells. */
  def size: Int = this match
    case Rows(numbers)  => numbers.length
    case Ints(_, bits)  => bits.length
    case Truths(cells)  => cells.length
    case Values(values) => values.size

  /** The column's cells as the scalar backend holds them. */
  def asValues: Vector[GroupValue] = this match
    case Rows(numbers)      => numbers.toVector.map(GroupValue.Row(_))
    case Ints(family, bits) => bits.toVector.map(GroupValue.IntBits(family, _))
    case Truths(cells)      =>
      cells.toVector.map(cell => GroupValue.Truth(cell != 0))
    case Values(values) => values

  /** The value at the row. */
  def valueAt(row: Int): GroupValue = this match
    case Rows(numbers)      => GroupValue.Row(numbers(row))
    case Ints(family, bits) => GroupValue.IntBits(family, bits(row))
    case Truths(cells)      => GroupValue.Truth(cells(row) != 0)
    case Values(values)     => values(row)

/** The JVM array group backend: the scalar backend's semantics
  * (`ScalarGroupBackend`, the reference every backend gives the same rows as),
  * with the frames' row numbers and the 32-bit words held as `int[]` and the
  * operations that move rows, the outer product, the numbering, the joins, the
  * concatenations, the projections and the gathers of rows, run as kernels on
  * them (`JvmArrayKernels`), as are the natives of 32-bit words whose methods
  * are the kernels' arithmetic (`gezi.jit.JvmIntNatives`), a constant and a
  * filter's test on a column held as ints. The distinct rows and the joins run
  * as kernels on ranks: a column held as ints is its own ranks, a column of
  * other values ranked by the canonical order, and several columns folded into
  * one rank per row (`unique`, `joined`). Any other operation on values (a test
  * of naturals, another native, a constructor) runs on the scalar backend on
  * its operands' columns alone, read as values there, the other columns left as
  * they are and the rows it keeps taken by a kernel.
  *
  * The memo (`JvmArrayMemo`) keys a recursion's calls by their arguments'
  * groups, each group by its members alone whatever column held them
  * (`ArgumentGroup`): a nonempty group of one kind held as ints as that kind
  * and its ints, any other as its members, so that two calls are one exactly
  * when their groups are. It keeps their results as columns: by the call's
  * identity when a group is held as ints (`ArrayCallKey.ofValues` false), so
  * that no int is read as a value; otherwise in a memo of results by the
  * groups' members, a map or a dense table beside it as the entry's
  * `GroupMemoOption` chose.
  */
object JvmArrayGroupBackend extends GroupBackend:

  type Column = JvmArrayColumn

  type Memo = JvmArrayMemo

  /** The column of the values: `Rows` when they are row numbers, `Ints` when
    * they are 32-bit words, a column of no cell being `Values`.
    */
  def column(values: Vector[GroupValue]): Column =
    val numbers = values.collect { case GroupValue.Row(index) => index }
    val words = values.collect { case GroupValue.IntBits(family, bits) =>
      (family, bits)
    }
    val truths = values.collect { case GroupValue.Truth(truth) =>
      if truth then 1 else 0
    }
    if values.nonEmpty && numbers.size == values.size then
      JvmArrayColumn.Rows(IArray.from(numbers))
    else if values.nonEmpty && words.size == values.size && words
        .map(_._1)
        .distinct
        .size == 1
    then
      words.map(_._1).distinct match
        case Vector(family) =>
          JvmArrayColumn.Ints(family, IArray.from(words.map(_._2)))
        case other =>
          throw IllegalStateException(
            s"a column of ints of one family, not $other"
          )
    else if values.nonEmpty && truths.size == values.size then
      JvmArrayColumn.Truths(IArray.from(truths))
    else JvmArrayColumn.Values(values)

  override def table(
      columns: Vector[Column],
      rowCount: Int
  ): GroupTable[Column] =
    require(
      columns.forall(_.size == rowCount),
      s"every column of a table has its $rowCount rows: ${columns.map(_.size)}"
    )
    GroupTable(columns, rowCount)

  /** The table as the scalar backend holds it. */
  private def asScalar(
      table: GroupTable[Column]
  ): GroupTable[ScalarGroupBackend.Column] =
    ScalarGroupBackend.table(table.columns.map(_.asValues), table.rowCount)

  /** The scalar backend's table as this backend holds it. */
  private def ofScalar(
      table: GroupTable[ScalarGroupBackend.Column]
  ): GroupTable[Column] =
    this.table(table.columns.map(column), table.rowCount)

  /** The column's cells at the rows, in their order. */
  private def taken(column: Column, rows: IArray[Int]): Column = column match
    case JvmArrayColumn.Rows(numbers) =>
      JvmArrayColumn.Rows(JvmArrayKernels.gathered(numbers, rows))
    case JvmArrayColumn.Ints(family, bits) =>
      JvmArrayColumn.Ints(family, JvmArrayKernels.gathered(bits, rows))
    case JvmArrayColumn.Truths(cells) =>
      JvmArrayColumn.Truths(JvmArrayKernels.gathered(cells, rows))
    case JvmArrayColumn.Values(values) => this.column(rows.toVector.map(values))

  private def rowsTaken(
      table: GroupTable[Column],
      rows: IArray[Int]
  ): GroupTable[Column] =
    this.table(table.columns.map(taken(_, rows)), rows.length)

  def emptyMemo(option: GroupMemoOption): Memo =
    JvmArrayMemo(Map.empty, option.empty[JvmArrayColumn])

  /** The row numbers of a table's first column. */
  private def rowNumbers(table: GroupTable[Column]): IArray[Int] =
    rowsAt(table, 0, JvmArrayKernels.iota(table.rowCount))

  /** The results of a finished call, by its key. */
  private def finishedResults(
      memo: Memo,
      recursion: Int,
      calls: ArrayCalls,
      key: ArrayCallKey
  ): Option[Column] =
    if key.ofValues then memo.byValues.get(CallKey(recursion, key.memberValues))
    else calls.identities.get(key).flatMap(calls.finished.get)

  /** Each row's group of an argument's relation (the row number, then a value):
    * the relation deduplicated in the canonical order, by kernels, so that each
    * row's members are one run, in their canonical order.
    */
  private def grouped(relation: GroupTable[Column]): Map[Int, ArgumentGroup] =
    val distinct = unique(relation)
    val rows = rowNumbers(distinct)
    val members = distinct.columns(1)
    val starts = (0 until rows.length)
      .filter(index => index == 0 || rows(index) != rows(index - 1))
      .toVector
    starts
      .lazyZip(starts.drop(1) :+ rows.length)
      .map((start, end) => rows(start) -> ArgumentGroup.of(members, start, end))
      .toMap

  def asked(
      memo: Memo,
      recursion: Int,
      rows: IArray[Int],
      arguments: Vector[GroupTable[Column]]
  ): (Memo, GroupTable[Column], CallsIdentified) =
    val groups = arguments.map(grouped)
    val keys = rows.toVector.map(row =>
      ArrayCallKey(groups.map(_.getOrElse(row, ArgumentGroup.empty)))
    )
    val calls = memo.calls.getOrElse(recursion, ArrayCalls.empty)
    val found = keys.map(finishedResults(memo, recursion, calls, _))
    val hits = found.indices.toVector.collect(index =>
      found(index) match { case Some(results) => (rows(index), results) }
    )
    val misses = found.indices.toVector.filter(found(_).isEmpty)
    val (identified, identities) = misses.foldLeft((calls, Vector.empty[Int])) {
      case ((current, made), index) =>
        current.identities.get(keys(index)) match
          case Some(identity) => (current, made :+ identity)
          case None           =>
            val identity = current.keys.size
            (
              current.copy(
                identities = current.identities.updated(keys(index), identity),
                keys = current.keys :+ keys(index)
              ),
              made :+ identity
            )
    }
    val hitRows = JvmArrayColumn.Rows(
      IArray.concat(
        hits.map((row, results) => JvmArrayKernels.filled(results.size, row))*
      )
    )
    (
      if misses.isEmpty then memo
      else memo.copy(calls = memo.calls.updated(recursion, identified)),
      unique(
        table(
          Vector(hitRows, concatenatedColumns(hits.map(_._2))),
          hitRows.size
        )
      ),
      CallsIdentified(IArray.from(misses.map(rows(_))), IArray.from(identities))
    )

  /** The calls' arguments, one relation per argument, its members the groups'
    * of the identities in order, each tagged with its identity's position.
    */
  def keys(
      memo: Memo,
      recursion: Int,
      identities: IArray[Int]
  ): Vector[GroupTable[Column]] =
    val calls = memo.calls.getOrElse(
      recursion,
      throw IllegalStateException(
        s"no call of the recursion $recursion was asked for"
      )
    )
    val keys = identities.toVector.map(calls.keys)
    val width = calls.keys.headOption.fold(0)(_.groups.size)
    Vector.tabulate(width)(argument =>
      val groups = keys.map(_.groups(argument))
      val positions = JvmArrayColumn.Rows(
        IArray.concat(
          groups.zipWithIndex.map((group, position) =>
            JvmArrayKernels.filled(group.size, position)
          )*
        )
      )
      table(
        Vector(positions, concatenatedColumns(groups.map(_.column))),
        positions.size
      )
    )

  def stored(
      memo: Memo,
      recursion: Int,
      identities: IArray[Int],
      rows: IArray[Int],
      results: GroupTable[Column]
  ): Memo =
    require(
      identities.length == rows.length,
      s"each stored call has one row: ${identities.length} identities, ${rows.length} rows"
    )
    val calls = memo.calls.getOrElse(
      recursion,
      throw IllegalStateException(
        s"no call of the recursion $recursion was asked for"
      )
    )
    // The results' positions sorted by their row numbers, and the run of
    // positions of each row.
    val sortedPairs = JvmArrayKernels.sortedUnique(
      JvmArrayKernels.packed(
        rowNumbers(results),
        0,
        JvmArrayKernels.iota(results.rowCount),
        0
      )
    )
    val (resultRows, positions) = (
      JvmArrayKernels.high(sortedPairs, 0),
      JvmArrayKernels.low(sortedPairs, 0)
    )
    val starts = (0 until resultRows.length)
      .filter(index => index == 0 || resultRows(index) != resultRows(index - 1))
      .toVector
    val runs = starts
      .lazyZip(starts.drop(1) :+ resultRows.length)
      .map((start, end) => resultRows(start) -> (start, end))
      .toMap
    val values = results.columns(1)
    identities.toVector.lazyZip(rows.toVector).foldLeft(memo) {
      case (made, (identity, row)) =>
        val (start, end) = runs.getOrElse(row, (0, 0))
        val slice = taken(values, positions.slice(start, end))
        val key = calls.keys(identity)
        if key.ofValues then
          made.copy(byValues =
            made.byValues.updated(CallKey(recursion, key.memberValues), slice)
          )
        else
          val current = made.calls.getOrElse(recursion, calls)
          made.copy(calls =
            made.calls.updated(
              recursion,
              current.copy(finished = current.finished.updated(identity, slice))
            )
          )
    }

  def memoSizes(memo: Memo): (Int, Int) = memo.sizes

  def emptyTable(columns: Int): GroupTable[Column] =
    table(Vector.fill(columns)(JvmArrayColumn.Values(Vector.empty)), 0)

  /** The join's size by the relations' histograms of row numbers
    * (`JvmArrayKernels.histogram`), only the one number read back; a relation
    * of no row counts nothing at every row (`JvmArrayKernels.filled`), and a
    * relation whose rows are held as values counts on the scalar backend.
    */
  def joinedSize(relations: Vector[GroupTable[Column]], rowCount: Int): Long =
    val counts = relations.map(relation =>
      relation.columns.headOption match
        case Some(JvmArrayColumn.Rows(numbers)) =>
          Some(JvmArrayKernels.histogram(numbers, rowCount))
        case Some(JvmArrayColumn.Values(values)) if values.isEmpty =>
          Some(JvmArrayKernels.filled(rowCount, 0))
        case _ => None
    )
    if counts.forall(_.isDefined) then
      val histograms = counts.flatten
      (0 until rowCount).foldLeft(0L)((sum, row) =>
        sum + histograms.foldLeft(1L)((product, histogram) =>
          product * histogram(row)
        )
      )
    else ScalarGroupBackend.joinedSize(relations.map(asScalar), rowCount)

  def rowsAt(
      table: GroupTable[Column],
      column: Int,
      rows: IArray[Int]
  ): IArray[Int] = table.columns(column) match
    case JvmArrayColumn.Rows(numbers) => JvmArrayKernels.gathered(numbers, rows)
    case other @ (JvmArrayColumn.Ints(_, _) | JvmArrayColumn.Truths(_) |
        JvmArrayColumn.Values(_)) =>
      val values = other.asValues
      rows.map(row =>
        values(row) match
          case GroupValue.Row(index) => index
          case found                 =>
            throw IllegalStateException(s"a column of row numbers holds $found")
      )

  def product(
      left: GroupTable[Column],
      right: GroupTable[Column]
  ): GroupTable[Column] =
    val (leftRows, rightRows) = (
      JvmArrayKernels.repeated(left.rowCount, right.rowCount),
      JvmArrayKernels.tiled(right.rowCount, left.rowCount)
    )
    table(
      left.columns.map(taken(_, leftRows)) ++ right.columns.map(
        taken(_, rightRows)
      ),
      leftRows.length
    )

  /** This backend's elementwise implementations, by the native's implementation
    * name (the backend facts of this backend): each native of 32-bit words
    * (`gezi.jit.JvmIntNatives`) and the kernel that computes it, with its
    * operands' count and whether its values are truth values (a comparison's 0
    * or 1). Every other call runs on the scalar backend, its method called row
    * by row.
    */
  private val kernels: Map[gezi.jit.NativeName, (String, Int, Boolean)] = Map(
    gezi.jit.NativeName.Function("jvm_int_add") -> ("added", 2, false),
    gezi.jit.NativeName
      .Function("jvm_int_subtract") -> ("subtracted", 2, false),
    gezi.jit.NativeName
      .Function("jvm_int_multiply") -> ("multiplied", 2, false),
    gezi.jit.NativeName.Function("jvm_int_negate") -> ("negated", 1, false),
    gezi.jit.NativeName.Function("jvm_int_equal") -> ("equal", 2, true),
    gezi.jit.NativeName.Function("jvm_int_less_than") -> ("lessThan", 2, true)
  )

  def called(
      table: GroupTable[Column],
      method: GroupMethod,
      arguments: Vector[Int]
  ): GroupTable[Column] =
    val operands = arguments.map(table.columns).collect {
      case JvmArrayColumn.Ints(_, bits) => bits
    }
    (kernels.get(method.native), operands) match
      case (Some((name, places, truths)), found)
          if found.size == arguments.size && places == arguments.size =>
        val cells = found match
          case Vector(only) if name == "negated" =>
            JvmArrayKernels.negated(only)
          case Vector(left, right) =>
            JvmArrayKernels.elementwiseOf(name, left, right)
          case other =>
            throw IllegalStateException(
              s"the kernel $name takes $places operands, not ${other.size}"
            )
        val appended =
          if truths then JvmArrayColumn.Truths(cells)
          else
            JvmArrayColumn.Ints(
              method.resultFamily.getOrElse(
                throw IllegalStateException(
                  s"the kernel $name's native names no result family"
                )
              ),
              cells
            )
        this.table(table.columns :+ appended, table.rowCount)
      case _ =>
        appendedThrough(table, arguments)((operands, places) =>
          ScalarGroupBackend.called(operands, method, places)
        )

  def numbered(table: GroupTable[Column]): GroupTable[Column] =
    this.table(
      table.columns :+ JvmArrayColumn.Rows(
        JvmArrayKernels.iota(table.rowCount)
      ),
      table.rowCount
    )

  /** The column's cells as ints, with the flip that orders them as the
    * canonical order does (`JvmArrayKernels.packed`): the sign bit for 32-bit
    * words, ordered unsigned, 0 for row numbers and for truths as 0 or 1; none
    * for a column of other values.
    */
  private def heldAsInts(column: Column): Option[(IArray[Int], Int)] =
    column match
      case JvmArrayColumn.Rows(numbers) => Some((numbers, 0))
      case JvmArrayColumn.Truths(cells) => Some((cells, 0))
      case JvmArrayColumn.Ints(_, bits) =>
        Some((bits, JvmArrayKernels.unsignedFlip))
      case JvmArrayColumn.Values(_) => None

  /** A column of the same kind as `kind`, of the cells given. */
  private def likewise(kind: Column, cells: IArray[Int]): Column = kind match
    case JvmArrayColumn.Rows(_)         => JvmArrayColumn.Rows(cells)
    case JvmArrayColumn.Truths(_)       => JvmArrayColumn.Truths(cells)
    case JvmArrayColumn.Ints(family, _) => JvmArrayColumn.Ints(family, cells)
    case JvmArrayColumn.Values(_)       =>
      throw IllegalStateException("a column of values is held as no ints")

  /** Whether two columns hold values of one kind as ints. */
  private def sameIntKind(first: Column, second: Column): Boolean =
    (first, second) match
      case (JvmArrayColumn.Ints(first, _), JvmArrayColumn.Ints(second, _)) =>
        first == second
      case (JvmArrayColumn.Rows(_), JvmArrayColumn.Rows(_)) |
          (JvmArrayColumn.Truths(_), JvmArrayColumn.Truths(_)) =>
        true
      case _ => false

  /** The join by the kernels: one key held as ints of one kind on both sides is
    * compared as it is; any other keys are ranked over both sides together
    * (`ranks`, `denseRanks`) into one int key per row, equal exactly when the
    * rows' keys are equal. Each side's keys are packed with its row numbers and
    * sorted, merged, and the pairs of rows sorted, the left's rows outer.
    */
  def joined(
      left: GroupTable[Column],
      right: GroupTable[Column],
      leftKeys: Vector[Int],
      rightKeys: Vector[Int]
  ): GroupTable[Column] =
    require(
      leftKeys.size == rightKeys.size,
      s"a join's keys pair up: $leftKeys and $rightKeys"
    )
    val ((leftCells, rightCells), flip) =
      (leftKeys.map(left.columns), rightKeys.map(right.columns)) match
        case (Vector(leftKey), Vector(rightKey))
            if sameIntKind(leftKey, rightKey) =>
          val (leftHeld, keyFlip) = heldAsInts(leftKey).getOrElse(
            throw IllegalStateException("a key of one int kind is held as ints")
          )
          val (rightHeld, _) = heldAsInts(rightKey).getOrElse(
            throw IllegalStateException("a key of one int kind is held as ints")
          )
          ((leftHeld, rightHeld), keyFlip)
        case (leftColumns, rightColumns) =>
          val together = leftColumns
            .lazyZip(rightColumns)
            .map((leftKey, rightKey) =>
              ranks(
                concatenatedColumns(Vector(leftKey, rightKey)),
                left.rowCount + right.rowCount
              )
            )
          val (dense, _) = denseRanks(together, left.rowCount + right.rowCount)
          (
            (
              dense.slice(0, left.rowCount),
              dense.slice(left.rowCount, dense.length)
            ),
            0
          )
    def sortedKeys(cells: IArray[Int]): IArray[Long] =
      JvmArrayKernels.sortedUnique(
        JvmArrayKernels.packed(
          cells,
          flip,
          JvmArrayKernels.iota(cells.length),
          0
        )
      )
    val pairs = JvmArrayKernels.sortedUnique(
      JvmArrayKernels.mergeJoined(sortedKeys(leftCells), sortedKeys(rightCells))
    )
    val (leftRows, rightRows) =
      (JvmArrayKernels.high(pairs, 0), JvmArrayKernels.low(pairs, 0))
    this.table(
      left.columns.map(taken(_, leftRows)) ++ right.columns.map(
        taken(_, rightRows)
      ),
      pairs.length
    )

  /** A column's cells as ints whose order, under the flip given, is the
    * canonical order of its values: a column held as ints as it is; a column of
    * other values (of `rowCount` cells, or none when empty) by each value's
    * rank among its distinct values in the canonical order
    * (`GroupBackend.valueOrdering`), flip 0.
    */
  private def ranks(column: Column, rowCount: Int): (IArray[Int], Int) =
    heldAsInts(column) match
      case Some(held) => held
      case None       =>
        val values = column.asValues
        if values.isEmpty then (IArray.from(Vector.fill(rowCount)(0)), 0)
        else
          val rank = values.distinct
            .sorted(using GroupBackend.valueOrdering)
            .zipWithIndex
            .toMap
          (IArray.from(values.map(rank)), 0)

  /** The rows' ranks among the distinct rows in the canonical order, and how
    * many distinct rows there are, from each column's cells as ints with their
    * flips (`ranks`): the columns folded from the first, each step packing the
    * ranks so far with the next column's cells and ranking the packed keys
    * among their distinct values.
    */
  private def denseRanks(
      columns: Vector[(IArray[Int], Int)],
      rowCount: Int
  ): (IArray[Int], Int) =
    def step(
        first: IArray[Int],
        firstFlip: Int,
        second: IArray[Int],
        secondFlip: Int
    ): (IArray[Int], Int) =
      val keys = JvmArrayKernels.packed(first, firstFlip, second, secondFlip)
      val distinct = JvmArrayKernels.sortedUnique(keys)
      (JvmArrayKernels.ranked(keys, distinct), distinct.length)
    columns.headOption match
      case None =>
        (JvmArrayKernels.filled(rowCount, 0), if rowCount == 0 then 0 else 1)
      case Some((cells, flip)) =>
        columns.drop(1).foldLeft(step(cells, flip, cells, flip)) {
          case ((sofar, _), (next, nextFlip)) => step(sofar, 0, next, nextFlip)
        }

  /** A constant fills a column by a kernel, and a filter's test on a column
    * held as ints is decided by the column's kind, every cell alike; any other
    * operation runs on the scalar backend on its operands' columns alone
    * (`appendedThrough`).
    */
  def computed(
      table: GroupTable[Column],
      operation: GroupOperation,
      arguments: Vector[Int]
  ): GroupTable[Column] =
    (operation, arguments.map(table.columns)) match
      case (_, _) if table.rowCount == 0 =>
        ofScalar(
          ScalarGroupBackend.computed(asScalar(table), operation, arguments)
        )
      case (GroupOperation.Constant(value), Vector()) =>
        val filled = value match
          case GroupValue.Row(index) =>
            JvmArrayColumn.Rows(JvmArrayKernels.filled(table.rowCount, index))
          case GroupValue.IntBits(family, bits) =>
            JvmArrayColumn.Ints(
              family,
              JvmArrayKernels.filled(table.rowCount, bits)
            )
          case GroupValue.Truth(truth) =>
            JvmArrayColumn.Truths(
              JvmArrayKernels.filled(table.rowCount, if truth then 1 else 0)
            )
          case other =>
            JvmArrayColumn.Values(Vector.fill(table.rowCount)(other))
        this.table(table.columns :+ filled, table.rowCount)
      case (
            GroupOperation.Admits(representation),
            Vector(
              operand @ (JvmArrayColumn.Rows(_) | JvmArrayColumn.Ints(_, _) |
              JvmArrayColumn.Truths(_))
            )
          ) =>
        val admitted = (representation, operand) match
          case (
                GroupRepresentation.IntOf(family),
                JvmArrayColumn.Ints(valueFamily, _)
              ) =>
            family == valueFamily
          case (GroupRepresentation.Truth, JvmArrayColumn.Truths(_)) => true
          case _                                                     => false
        this.table(
          table.columns :+ JvmArrayColumn.Truths(
            JvmArrayKernels.filled(table.rowCount, if admitted then 1 else 0)
          ),
          table.rowCount
        )
      case _ =>
        appendedThrough(table, arguments)((operands, places) =>
          ScalarGroupBackend.computed(operands, operation, places)
        )

  /** The table with the column an operation of the scalar backend appends,
    * given only the operands' columns read as values and the row numbers: the
    * rows it keeps taken by a kernel, its column appended as this backend holds
    * it.
    */
  private def appendedThrough(
      table: GroupTable[Column],
      arguments: Vector[Int]
  )(
      operation: (
          GroupTable[ScalarGroupBackend.Column],
          Vector[Int]
      ) => GroupTable[ScalarGroupBackend.Column]
  ): GroupTable[Column] =
    val operands = arguments.map(index =>
      table.columns(index).asValues
    ) :+ JvmArrayKernels.iota(table.rowCount).toVector.map(GroupValue.Row(_))
    val result = operation(
      ScalarGroupBackend.table(operands, table.rowCount),
      arguments.indices.toVector
    )
    val kept = IArray.from(result.columns(arguments.size).map {
      case GroupValue.Row(row) => row
      case other               =>
        throw IllegalStateException(
          s"the row numbers of an operation's operands hold $other"
        )
    })
    this.table(
      table.columns.map(taken(_, kept)) :+ column(result.columns.last),
      kept.length
    )

  /** The columns one after another, held as ints when they are all of one kind
    * held so; a column of no cell is left out.
    */
  private def concatenatedColumns(columns: Vector[Column]): Column =
    columns.filter(_.size > 0) match
      case Vector()     => JvmArrayColumn.Values(Vector.empty)
      case Vector(only) => only
      case nonempty @ (first +: rest) if rest.forall(sameIntKind(first, _)) =>
        likewise(
          first,
          IArray.concat(
            nonempty.map(column =>
              heldAsInts(column)
                .getOrElse(throw IllegalStateException("an int column"))
                ._1
            )*
          )
        )
      case nonempty => column(nonempty.flatMap(_.asValues))

  def concatenated(
      left: GroupTable[Column],
      right: GroupTable[Column]
  ): GroupTable[Column] =
    require(
      left.columns.size == right.columns.size,
      s"concatenated tables have the same columns: ${left.columns.size} and ${right.columns.size}"
    )
    table(
      left.columns.lazyZip(right.columns).map {
        case (JvmArrayColumn.Rows(first), JvmArrayColumn.Rows(second)) =>
          JvmArrayColumn.Rows(JvmArrayKernels.concatenated(first, second))
        case (
              JvmArrayColumn.Ints(firstFamily, first),
              JvmArrayColumn.Ints(secondFamily, second)
            ) if firstFamily == secondFamily =>
          JvmArrayColumn
            .Ints(firstFamily, JvmArrayKernels.concatenated(first, second))
        case (JvmArrayColumn.Truths(first), JvmArrayColumn.Truths(second)) =>
          JvmArrayColumn.Truths(JvmArrayKernels.concatenated(first, second))
        case (first, second) => concatenatedColumns(Vector(first, second))
      },
      left.rowCount + right.rowCount
    )

  def selected(
      table: GroupTable[Column],
      mask: Int
  ): (GroupTable[Column], GroupTable[Column]) = table.columns(mask) match
    case JvmArrayColumn.Truths(cells) =>
      (
        rowsTaken(table, JvmArrayKernels.compressed(cells)),
        rowsTaken(table, JvmArrayKernels.compressedZeros(cells))
      )
    case other => selectedByValues(table, other)

  /** The selection by a mask of truth values the column holds as values. */
  private def selectedByValues(
      table: GroupTable[Column],
      mask: Column
  ): (GroupTable[Column], GroupTable[Column]) =
    val truths = mask.asValues.map {
      case GroupValue.Truth(value) => value
      case other                   =>
        throw IllegalStateException(
          s"a selection's mask is a column of truth values, not $other"
        )
    }
    val (chosen, others) = truths.indices.toVector.partition(truths)
    (
      rowsTaken(table, IArray.from(chosen)),
      rowsTaken(table, IArray.from(others))
    )

  def projected(
      table: GroupTable[Column],
      columns: Vector[Int]
  ): GroupTable[Column] =
    this.table(columns.map(table.columns), table.rowCount)

  /** The distinct rows in the canonical order, by the kernels: each row's rank
    * among the distinct rows (`denseRanks` of the columns' `ranks`), and for
    * each rank the first row that holds it, the columns gathered at those rows.
    */
  def unique(table: GroupTable[Column]): GroupTable[Column] =
    val (dense, count) =
      denseRanks(table.columns.map(ranks(_, table.rowCount)), table.rowCount)
    rowsTaken(table, JvmArrayKernels.firstRows(dense, count))

  def rows(table: GroupTable[Column]): Vector[Vector[GroupValue]] =
    ScalarGroupBackend.rows(asScalar(table))
