package gezi.narrowblocks.groups

import java.lang.invoke.MethodHandle
import java.lang.invoke.MethodHandles
import java.lang.invoke.MethodType
import java.math.BigInteger
import gezi.jit.ConstructedNaturals
import gezi.jit.StaticBlockMethod
import gezi.jit.StaticBlockResult

/** The JVM scalar group backend, the reference semantics of every backend
  * (`GroupBackend`): a column is a vector of values, each operation a walk over
  * its rows, a native called on one row at a time by its static method.
  */
object ScalarGroupBackend extends GroupBackend:

  type Column = Vector[GroupValue]

  /** The calls on the heap, as values (`HeapMemo`). */
  type Memo = HeapMemo

  def column(values: Vector[GroupValue]): Column = values

  def emptyMemo(option: GroupMemoOption): Memo = HeapMemo.empty(option)

  /** Each row's group of an argument's relation, its members distinct and in
    * the canonical order.
    */
  private def groups(
      relation: GroupTable[Column]
  ): Map[Int, Vector[GroupValue]] =
    rows(relation)
      .groupMap(row => GroupProgram.rowIndex(row(0)))(row => row(1))
      .map((row, values) =>
        row -> values.distinct.sorted(using GroupBackend.valueOrdering)
      )

  def asked(
      memo: Memo,
      recursion: Int,
      rows: IArray[Int],
      arguments: Vector[GroupTable[Column]]
  ): (Memo, GroupTable[Column], CallsIdentified) =
    val grouped = arguments.map(groups)
    val (asked, hits, misses) = memo.asked(
      recursion,
      rows.toVector.map(row =>
        row -> grouped.map(_.getOrElse(row, Vector.empty))
      )
    )
    (
      asked,
      unique(
        table(
          Vector(hits.map((row, _) => GroupValue.Row(row)), hits.map(_._2)),
          hits.size
        )
      ),
      CallsIdentified(
        IArray.from(misses.map(_._1)),
        IArray.from(misses.map(_._2))
      )
    )

  def keys(
      memo: Memo,
      recursion: Int,
      identities: IArray[Int]
  ): Vector[GroupTable[Column]] =
    val arguments = memo.arguments(recursion, identities.toVector)
    val width = memo.calls
      .get(recursion)
      .flatMap(_.arguments.headOption)
      .map(_.size)
      .getOrElse(0)
    Vector.tabulate(width)(argument =>
      val pairs = arguments.zipWithIndex.flatMap((groups, position) =>
        groups(argument).map(member => (GroupValue.Row(position), member))
      )
      table(Vector(pairs.map(_._1), pairs.map(_._2)), pairs.size)
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
    val byRow = this
      .rows(results)
      .groupMap(row => GroupProgram.rowIndex(row(0)))(row => row(1))
    memo.stored(
      recursion,
      identities.toVector
        .lazyZip(rows.toVector)
        .map((identity, row) => (identity, byRow.getOrElse(row, Vector.empty)))
    )

  def memoSizes(memo: Memo): (Int, Int) =
    (memo.finished.size, memo.finished.denseSize)

  def emptyTable(columns: Int): GroupTable[Column] =
    table(Vector.fill(columns)(Vector.empty), 0)

  def joinedSize(relations: Vector[GroupTable[Column]], rowCount: Int): Long =
    val counts = relations.map(relation =>
      relation.columns.headOption
        .getOrElse(Vector.empty)
        .groupMapReduce(GroupProgram.rowIndex)(_ => 1L)(_ + _)
    )
    (0 until rowCount)
      .map(row =>
        counts.foldLeft(1L)((product, count) =>
          product * count.getOrElse(row, 0L)
        )
      )
      .sum

  def rowsAt(
      table: GroupTable[Column],
      column: Int,
      rows: IArray[Int]
  ): IArray[Int] =
    rows.map(row => GroupProgram.rowIndex(table.columns(column)(row)))

  override def table(
      columns: Vector[Column],
      rowCount: Int
  ): GroupTable[Column] =
    require(
      columns.forall(_.size == rowCount),
      s"every column of a table has its $rowCount rows: ${columns.map(_.size)}"
    )
    GroupTable(columns, rowCount)

  def product(
      left: GroupTable[Column],
      right: GroupTable[Column]
  ): GroupTable[Column] =
    val rowCount = left.rowCount * right.rowCount
    val leftColumns = left.columns.map(column =>
      column.flatMap(value => Vector.fill(right.rowCount)(value))
    )
    val rightColumns =
      right.columns.map(column => Vector.fill(left.rowCount)(column).flatten)
    table(leftColumns ++ rightColumns, rowCount)

  def called(
      table: GroupTable[Column],
      method: GroupMethod,
      arguments: Vector[Int]
  ): GroupTable[Column] =
    require(
      arguments.forall(index => index >= 0 && index < table.columns.size),
      s"the arguments $arguments are columns of the table"
    )
    require(
      method.places.size == arguments.size,
      s"the method takes ${method.places.size} operands, not ${arguments.size}"
    )
    val handle = method.handle
    val results = (0 until table.rowCount).toVector.map(row =>
      val operands: Vector[AnyRef] = arguments
        .zip(method.places)
        .map((index, place) =>
          (place, table.columns(index)(row)) match
            case (GroupPlace.Natural, GroupValue.Natural(value)) => value
            case (GroupPlace.NaturalList, GroupValue.List(list)) => list.suffix
            case (GroupPlace.IntBits, GroupValue.IntBits(_, bits)) =>
              Integer.valueOf(bits)
            case (_, other) =>
              throw IllegalStateException(
                s"a block calls a static method at a place $place on its values only, not on $other"
              )
        )
      GroupBackend.returned(
        method,
        handle.invokeWithArguments(java.util.List.of(operands*))
      )
    )
    val kept = results.indices.filter(row => results(row).isDefined).toVector
    this.table(
      table.columns.map(column => kept.map(column)) :+ kept.map(row =>
        results(row).getOrElse(
          throw IllegalStateException("a kept row has a value")
        )
      ),
      kept.size
    )

  def numbered(table: GroupTable[Column]): GroupTable[Column] =
    this.table(
      table.columns :+ (0 until table.rowCount).toVector.map(GroupValue.Row(_)),
      table.rowCount
    )

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
    val byKey = (0 until right.rowCount).toVector.groupBy(row =>
      rightKeys.map(index => right.columns(index)(row))
    )
    val pairs = (0 until left.rowCount).toVector.flatMap(row =>
      byKey
        .getOrElse(
          leftKeys.map(index => left.columns(index)(row)),
          Vector.empty
        )
        .map(other => (row, other))
    )
    this.table(
      left.columns.map(column =>
        pairs.map((row, _) => column(row))
      ) ++ right.columns.map(column => pairs.map((_, other) => column(other))),
      pairs.size
    )

  def computed(
      table: GroupTable[Column],
      operation: GroupOperation,
      arguments: Vector[Int]
  ): GroupTable[Column] =
    require(
      arguments.forall(index => index >= 0 && index < table.columns.size),
      s"the arguments $arguments are columns of the table"
    )
    val results = (0 until table.rowCount).toVector.map(row =>
      ScalarGroupBackend.operated(
        operation,
        arguments.map(index => table.columns(index)(row))
      )
    )
    val kept = results.indices.filter(row => results(row).isDefined).toVector
    this.table(
      table.columns.map(column => kept.map(column)) :+ kept.map(row =>
        results(row).getOrElse(
          throw IllegalStateException("a kept row has a value")
        )
      ),
      kept.size
    )

  def concatenated(
      left: GroupTable[Column],
      right: GroupTable[Column]
  ): GroupTable[Column] =
    require(
      left.columns.size == right.columns.size,
      s"concatenated tables have the same columns: ${left.columns.size} and ${right.columns.size}"
    )
    table(
      left.columns.lazyZip(right.columns).map(_ ++ _),
      left.rowCount + right.rowCount
    )

  def selected(
      table: GroupTable[Column],
      mask: Int
  ): (GroupTable[Column], GroupTable[Column]) =
    val truths = table.columns(mask).map {
      case GroupValue.Truth(value) => value
      case other                   =>
        throw IllegalStateException(
          s"a selection's mask is a column of truth values, not $other"
        )
    }
    val (chosen, others) = (0 until table.rowCount).toVector.partition(truths)
    (rowsTaken(table, chosen), rowsTaken(table, others))

  def projected(
      table: GroupTable[Column],
      columns: Vector[Int]
  ): GroupTable[Column] =
    this.table(columns.map(table.columns), table.rowCount)

  def unique(table: GroupTable[Column]): GroupTable[Column] =
    val distinct = rows(table).distinct.sorted(using GroupBackend.rowOrdering)
    this.table(
      table.columns.indices.toVector.map(index => distinct.map(_(index))),
      distinct.size
    )

  def rows(table: GroupTable[Column]): Vector[Vector[GroupValue]] =
    (0 until table.rowCount).toVector.map(row => table.columns.map(_(row)))

  /** The value of the operation on one row's operands, none when it has none
    * there.
    */
  private def operated(
      operation: GroupOperation,
      operands: Vector[GroupValue]
  ): Option[GroupValue] =
    def natural(value: GroupValue): BigInteger = value match
      case GroupValue.Natural(number) => number
      case other                      =>
        throw IllegalStateException(s"$operation reads naturals, not $other")
    def list(value: GroupValue): gezi.jit.NativeValue.ArrayListed = value match
      case GroupValue.List(found) => found
      case other                  =>
        throw IllegalStateException(s"$operation reads lists, not $other")
    (operation, operands) match
      case (GroupOperation.Constant(value), Vector())             => Some(value)
      case (GroupOperation.Admits(representation), Vector(value)) =>
        Some(GroupValue.Truth((representation, value) match
          case (GroupRepresentation.Natural, GroupValue.Natural(_)) => true
          case (GroupRepresentation.Positive, GroupValue.Natural(number)) =>
            number.signum > 0
          case (GroupRepresentation.Truth, GroupValue.Truth(_)) => true
          case (
                GroupRepresentation.IntOf(family),
                GroupValue.IntBits(valueFamily, _)
              ) =>
            family == valueFamily
          case _ => false))
      case (GroupOperation.Zero, Vector(value)) =>
        Some(GroupValue.Truth(natural(value).signum == 0))
      case (GroupOperation.EvenPositive, Vector(value)) =>
        Some(
          GroupValue.Truth(
            natural(value).signum > 0 && !natural(value).testBit(0)
          )
        )
      case (GroupOperation.Odd, Vector(value)) =>
        Some(GroupValue.Truth(natural(value).testBit(0)))
      case (GroupOperation.Half, Vector(value)) =>
        Some(GroupValue.Natural(natural(value).shiftRight(1)))
      case (GroupOperation.Doubled, Vector(value)) =>
        Option.when(natural(value).signum > 0)(
          GroupValue.Natural(natural(value).shiftLeft(1))
        )
      case (GroupOperation.DoubledAndOne, Vector(value)) =>
        Some(
          GroupValue.Natural(natural(value).shiftLeft(1).add(BigInteger.ONE))
        )
      case (GroupOperation.ConstructedAt(constructor), fields) =>
        Some(
          GroupValue.Constructed(
            ConstructedNaturals(constructor, fields.map(natural))
          )
        )
      case (GroupOperation.Empty, Vector(value)) =>
        Some(GroupValue.Truth(list(value).nil))
      case (GroupOperation.Relabelled(kind), Vector(value)) =>
        kind.relabelled(list(value)).map(GroupValue.List(_))
      case (GroupOperation.Head, Vector(value)) =>
        Some(GroupLists.head(list(value)))
      case (GroupOperation.Tail, Vector(value)) =>
        Some(GroupValue.List(GroupLists.tail(list(value))))
      case (GroupOperation.Consed(element, kind), Vector(item, rest)) =>
        val kept: Option[gezi.jit.ArrayItem] = (element, item) match
          case (GroupRepresentation.Natural, GroupValue.Natural(number)) =>
            Some(number)
          case (GroupRepresentation.Positive, GroupValue.Natural(number)) =>
            Option.when(number.signum > 0)(number)
          case (
                GroupRepresentation.IntOf(family),
                GroupValue.IntBits(itemFamily, bits)
              ) if itemFamily == family =>
            Some(bits)
          case _ =>
            throw IllegalStateException(
              s"a cons of $element elements reads ${element}'s values, not $item"
            )
        kept.map(found => GroupValue.List(kind.consed(found, list(rest))))
      case (other, values) =>
        throw IllegalStateException(
          s"no operation $other on ${values.size} operands"
        )

  /** The table of the rows at the indices, in their order. */
  private def rowsTaken(
      table: GroupTable[Column],
      indices: Vector[Int]
  ): GroupTable[Column] =
    this.table(table.columns.map(column => indices.map(column)), indices.size)

  /** The handle of the static method, its parameters of the JVM types of its
    * places and its result of the JVM type of its convention.
    */
  private[groups] def handle(method: GroupMethod): MethodHandle =
    val result = method.method.result match
      case StaticBlockResult.Natural | StaticBlockResult.NaturalOrNoAnswer =>
        classOf[BigInteger]
      case StaticBlockResult.Truth       => java.lang.Boolean.TYPE
      case StaticBlockResult.Constructed => classOf[ConstructedNaturals]
      case StaticBlockResult.NaturalList => classOf[Vector[?]]
      case StaticBlockResult.JvmInt      => java.lang.Integer.TYPE
      case StaticBlockResult.Lattice     => classOf[gezi.jit.NaturalLattice]
    val parameters: Vector[Class[?]] = method.places.map {
      case GroupPlace.Natural     => classOf[BigInteger]
      case GroupPlace.NaturalList => classOf[Vector[?]]
      case GroupPlace.IntBits     => java.lang.Integer.TYPE
    }
    MethodHandles
      .publicLookup()
      .findStatic(
        Class.forName(method.method.className, true, getClass.getClassLoader),
        method.method.methodName,
        MethodType.methodType(result, java.util.List.of(parameters*))
      )
