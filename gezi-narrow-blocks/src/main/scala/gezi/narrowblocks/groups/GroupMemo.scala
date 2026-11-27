package gezi.narrowblocks.groups


/** The finished calls of one run of a group block and their results
  * (`GroupProgram`'s schedule), which exist only for that run, each call's
  * results held as a backend holds them (`Results`: the values, or a column).
  * Every implementation gives the same results for the same calls: they
  * differ only in how a call is found.
  */
trait GroupMemo[Results]:

  /** The results of the call, when it has finished. */
  def get(key: CallKey): Option[Results]

  /** Whether the call has finished. */
  def contains(key: CallKey): Boolean = get(key).isDefined

  /** The memo with the call's results. */
  def updated(key: CallKey, results: Results): GroupMemo[Results]

  /** The finished calls. */
  def size: Int

  /** The finished calls a dense table holds. */
  def denseSize: Int

/** How a group block's run keeps its finished calls: by a persistent map
  * from the call (`Mapped`), or, for the calls whose every argument's group
  * is one list, a dense table of their suffixes within `cells` cells beside
  * the map (`Dense`).
  */
enum GroupMemoOption:
  case Mapped
  case Dense(cells: Long)

  /** The empty memo of a run. */
  def empty[Results]: GroupMemo[Results] = this match
    case Mapped       => MappedMemo[Results](Map.empty)
    case Dense(cells) => DenseMemo[Results](cells, Map.empty, 0, MappedMemo[Results](Map.empty))

/** The finished calls by a persistent map keyed by the call, equal by its
  * recursion and its arguments' groups.
  */
final case class MappedMemo[Results](finished: Map[CallKey, Results]) extends GroupMemo[Results]:
  def get(key: CallKey): Option[Results] = finished.get(key)
  def updated(key: CallKey, results: Results): GroupMemo[Results] = MappedMemo(finished.updated(key, results))
  def size: Int = finished.size
  def denseSize: Int = 0

/** One recursion's dense table: a dimension for each argument, bound to the
  * list whose suffixes it holds and the count of those suffixes, the empty
  * one included; a cell for each combination of suffixes, in an immutable
  * vector, the last dimension innermost.
  */
final case class DenseTable[Results](dimensions: Vector[gezi.jit.ArrayElements], cells: Vector[Option[Results]]):

  /** The cell of the key's arguments, when each is a group of one list
    * that is by its elements a suffix of its dimension's list: in one step
    * when it is held by that list's own elements, else by its hash code and
    * then its elements, so that two calls equal by their arguments find one
    * cell and no other call finds it. A group of other than one member has
    * no cell.
    */
  def cell(arguments: Vector[Vector[GroupValue]]): Option[Int] =
    Option
      .when(arguments.size == dimensions.size)(arguments.zip(dimensions))
      .flatMap(pairs =>
        pairs.foldLeft(Option(0)) {
          case (Some(index), (Vector(GroupValue.List(suffix)), elements)) =>
            DenseTable.start(suffix, elements).map(start => index * (elements.values.size + 1) + start)
          case _ => None
        }
      )

object DenseTable:

  /** Where the suffix starts in the list, when it is one of its suffixes by
    * its elements.
    */
  def start(suffix: gezi.jit.NativeValue.ArrayListed, elements: gezi.jit.ArrayElements): Option[Int] =
    if suffix.elements eq elements then Some(suffix.start)
    else
      val start = elements.values.size - (suffix.elements.values.size - suffix.start)
      Option.when(start >= 0 && suffix == gezi.jit.NativeValue.ArrayListed(elements, start))(start)

/** The finished calls by a dense table per recursion, beside a map: a
  * recursion's table is bound at its first call whose every argument's group
  * is one list, each dimension to that list, when the cells it needs are at
  * most `limit`; a call whose every argument's group is one list that is by
  * its elements a suffix of its dimension's list is found in the table
  * (`DenseTable.cell`),
  * and any other in the map, so that a call is found where it was kept
  * whichever objects hold its arguments. `filled` counts the tables' filled
  * cells.
  */
final case class DenseMemo[Results](limit: Long, tables: Map[Int, DenseTable[Results]], filled: Int, mapped: MappedMemo[Results])
    extends GroupMemo[Results]:

  /** The call's results from its cell, else from the map: a call finished
    * before its recursion's table was bound, or while its lists fitted no
    * table, stays in the map.
    */
  def get(key: CallKey): Option[Results] =
    tables.get(key.recursion).flatMap(table => table.cell(key.arguments).flatMap(table.cells(_))).orElse(mapped.get(key))

  def updated(key: CallKey, results: Results): GroupMemo[Results] =
    val table = tables.get(key.recursion).orElse(DenseMemo.bound[Results](key.arguments, limit))
    table.flatMap(found => found.cell(key.arguments).map(index => (found, index))) match
      case Some((found, index)) =>
        DenseMemo(
          limit,
          tables.updated(key.recursion, found.copy(cells = found.cells.updated(index, Some(results)))),
          if found.cells(index).isEmpty then filled + 1 else filled,
          mapped
        )
      case None => copy(mapped = MappedMemo(mapped.finished.updated(key, results)))

  /** The filled cells and the map's calls. */
  def size: Int = filled + mapped.size
  def denseSize: Int = filled

object DenseMemo:

  /** The table bound to the arguments' lists, when every argument is a list
    * and the cells their suffixes need are at most `limit`, which is at most
    * the cells a vector holds.
    */
  def bound[Results](arguments: Vector[Vector[GroupValue]], limit: Long): Option[DenseTable[Results]] =
    val lists = arguments.collect { case Vector(GroupValue.List(suffix)) => suffix.elements }
    val cells = lists.foldLeft(BigInt(1))((product, elements) => product * (elements.values.size + 1))
    require(limit <= Int.MaxValue, s"a dense table holds at most ${Int.MaxValue} cells, not $limit")
    Option.when(arguments.nonEmpty && lists.size == arguments.size && cells <= limit)(
      DenseTable[Results](lists, Vector.fill(cells.toInt)(None))
    )

/** The calls of one recursion asked for in a run: each call's identity by
  * its arguments' groups, and the groups of each identity in order.
  */
final case class HeapCalls(identities: Map[Vector[Vector[GroupValue]], Int], arguments: Vector[Vector[Vector[GroupValue]]]):

  /** The calls with an identity for each of the arguments' groups, a new one
    * for groups not asked for before, and those identities in order.
    */
  def identified(asked: Vector[Vector[Vector[GroupValue]]]): (HeapCalls, Vector[Int]) =
    asked.foldLeft((this, Vector.empty[Int])) { case ((calls, found), key) =>
      calls.identities.get(key) match
        case Some(identity) => (calls, found :+ identity)
        case None =>
          val identity = calls.arguments.size
          (HeapCalls(calls.identities.updated(key, identity), calls.arguments :+ key), found :+ identity)
    }

object HeapCalls:
  val empty: HeapCalls = HeapCalls(Map.empty, Vector.empty)

/** The memo of a backend that keeps a run's calls on the JVM heap as
  * values (`GroupValue`): the finished calls' results (`GroupMemo`, a map or
  * a dense table beside it, as the entry's data chose) and the calls asked
  * for, by recursion. The scalar backend's memo, and any backend's whose
  * columns read as values.
  */
final case class HeapMemo(finished: GroupMemo[Vector[GroupValue]], calls: Map[Int, HeapCalls]):

  /** For each row asked, given with its arguments' groups: the row with
    * each result of its call when the call has finished, else the row with
    * its call's identity, a new one for groups not asked for before; and the
    * memo with those identities.
    */
  def asked(recursion: Int, rows: Vector[(Int, Vector[Vector[GroupValue]])]): (HeapMemo, Vector[(Int, GroupValue)], Vector[(Int, Int)]) =
    val (hits, misses) = rows.partitionMap((row, groups) =>
      finished.get(CallKey(recursion, groups)) match
        case Some(results) => Left(results.map(value => (row, value)))
        case None          => Right((row, groups))
    )
    val (calls, identities) = this.calls.getOrElse(recursion, HeapCalls.empty).identified(misses.map(_._2))
    (
      if misses.isEmpty then this else copy(calls = this.calls.updated(recursion, calls)),
      hits.flatten,
      misses.map(_._1).zip(identities)
    )

  /** The arguments' groups of the identities' calls. */
  def arguments(recursion: Int, identities: Vector[Int]): Vector[Vector[Vector[GroupValue]]] =
    val calls = this.calls.getOrElse(recursion, throw IllegalStateException(s"no call of the recursion $recursion was asked for"))
    identities.map(calls.arguments)

  /** The memo with the identities' calls finished with the values given. */
  def stored(recursion: Int, results: Vector[(Int, Vector[GroupValue])]): HeapMemo =
    copy(finished = arguments(recursion, results.map(_._1)).lazyZip(results).foldLeft(finished) { case (memo, (key, (_, values))) =>
      memo.updated(CallKey(recursion, key), values)
    })

object HeapMemo:

  /** The memo of a run that has asked for no call, by the option given. */
  def empty(option: GroupMemoOption): HeapMemo = HeapMemo(option.empty[Vector[GroupValue]], Map.empty)
