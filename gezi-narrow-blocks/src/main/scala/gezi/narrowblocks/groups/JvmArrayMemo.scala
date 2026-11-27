package gezi.narrowblocks.groups


/** How a column of the JVM array group backend holds its values as ints:
  * row numbers, values of a family held as a JVM `int` (ordered unsigned, so
  * packed with the sign bit flipped) or truths as 0 or 1.
  */
enum JvmArrayIntKind(val flip: Int):
  case Row extends JvmArrayIntKind(0)
  case Word(family: gezi.jit.FamilyIdentity) extends JvmArrayIntKind(Integer.MIN_VALUE)
  case Truth extends JvmArrayIntKind(0)

  /** The column of this kind holding the cells. */
  def column(cells: IArray[Int]): JvmArrayColumn = this match
    case Row   => JvmArrayColumn.Rows(cells)
    case Word(family) => JvmArrayColumn.Ints(family, cells)
    case Truth => JvmArrayColumn.Truths(cells)

object JvmArrayIntKind:

  /** The kind of a column held as ints, and its cells; none for a column of
    * other values.
    */
  def of(column: JvmArrayColumn): Option[(JvmArrayIntKind, IArray[Int])] = column match
    case JvmArrayColumn.Rows(cells)   => Some((Row, cells))
    case JvmArrayColumn.Ints(family, cells) => Some((Word(family), cells))
    case JvmArrayColumn.Truths(cells) => Some((Truth, cells))
    case JvmArrayColumn.Values(_)     => None

/** One argument's group in a call's key, by its members alone, whatever
  * column held them: a nonempty group whose members are all of one kind held
  * as ints (row numbers, one family's 32-bit words, truth values) as that
  * kind and their ints in the canonical order (`Ints`); any other group, the
  * empty one included, as its members in the canonical order (`Values`). So
  * two groups are one exactly when their members are, as the scalar
  * backend's keys are.
  */
enum ArgumentGroup:
  case Ints(kind: JvmArrayIntKind, cells: scala.collection.immutable.ArraySeq.ofInt)
  case Values(members: Vector[GroupValue])

  /** The group's members. */
  def size: Int = this match
    case Ints(_, cells)   => cells.size
    case Values(members) => members.size

  /** The group's members as a column. */
  def column: JvmArrayColumn = this match
    case Ints(kind, cells) => kind.column(IArray.from(cells))
    case Values(members)   => JvmArrayColumn.Values(members)

object ArgumentGroup:

  /** The empty group. */
  val empty: ArgumentGroup = Values(Vector.empty)

  /** The cells, an immutable array no code writes, as a sequence equal by
    * its contents, without a copy.
    */
  private def wrapped(cells: IArray[Int]): scala.collection.immutable.ArraySeq.ofInt =
    scala.collection.immutable.ArraySeq.ofInt(cells.asInstanceOf[Array[Int]])

  /** The group of a column's cells from `start` to `end`, distinct and in
    * the canonical order.
    */
  def of(column: JvmArrayColumn, start: Int, end: Int): ArgumentGroup =
    JvmArrayIntKind.of(column) match
      case Some((kind, cells)) if end > start => Ints(kind, ArgumentGroup.wrapped(cells.slice(start, end)))
      case Some(_)                            => empty
      case None =>
        val members = (start until end).toVector.map(column.valueAt)
        val ints = members.map {
          case GroupValue.Row(index)            => Some((JvmArrayIntKind.Row, index))
          case GroupValue.IntBits(family, bits) => Some((JvmArrayIntKind.Word(family), bits))
          case GroupValue.Truth(truth)          => Some((JvmArrayIntKind.Truth, if truth then 1 else 0))
          case _                                => None
        }
        ints.flatten.map(_._1).distinct match
          case Vector(kind) if members.nonEmpty && ints.forall(_.isDefined) => Ints(kind, ArgumentGroup.wrapped(IArray.from(ints.flatten.map(_._2))))
          case _                                                             => Values(members)

/** One call's key: each argument's group (`ArgumentGroup`). */
final case class ArrayCallKey(groups: Vector[ArgumentGroup]):

  /** Whether every argument's group is held as values, so that the call's
    * results are kept in the memo of results by the arguments' values.
    */
  def ofValues: Boolean = groups.forall {
    case ArgumentGroup.Values(_)  => true
    case ArgumentGroup.Ints(_, _) => false
  }

  /** The groups' members as values, for a key of values only. */
  def memberValues: Vector[Vector[GroupValue]] = groups.map {
    case ArgumentGroup.Values(members) => members
    case other                         => throw IllegalStateException(s"a key of values only, not $other")
  }

/** The calls of one recursion: the identity of each key, the key of each
  * identity in order, and the results of the finished calls whose key holds
  * an int group, by identity, each the column of its values as the backend
  * held them.
  */
final case class ArrayCalls(identities: Map[ArrayCallKey, Int], keys: Vector[ArrayCallKey], finished: Map[Int, JvmArrayColumn])

object ArrayCalls:
  val empty: ArrayCalls = ArrayCalls(Map.empty, Vector.empty, Map.empty)

/** The memo of the JVM array group backend: each recursion's calls keyed by
  * their arguments' groups, one identity per call (`calls`). A finished
  * call's results are a column: by identity when a group is held as ints
  * (`ArrayCalls`), so that no int is read as a value; in `byValues` when
  * every group is held as values, a map or, for groups that are each one
  * list, a dense table beside it, as the entry's option chose
  * (`GroupMemoOption`), the scalar backend's memo of results with its
  * results held as columns.
  */
final case class JvmArrayMemo(calls: Map[Int, ArrayCalls], byValues: GroupMemo[JvmArrayColumn]):

  /** The finished calls, and those in a dense table. */
  def sizes: (Int, Int) = (calls.values.map(_.finished.size).sum + byValues.size, byValues.denseSize)
