package com.yang_bo.gezi.narrowblocks.groups

import java.math.BigInteger
import com.yang_bo.gezi.ir.NativeSpecializer
import com.yang_bo.gezi.jit.StorageEncodingOperations
import com.yang_bo.gezi.jit.ConstructedNaturals
import com.yang_bo.gezi.jit.StaticBlockMethod
import com.yang_bo.gezi.jit.StaticBlockResult

/** One value of a row of a group program, as the JVM holds it inside a block: a
  * binary natural, a truth value, a value of a declared data family whose
  * fields are naturals, a value of a family held as a JVM `int`, or an array
  * list of naturals or of such values. A block holds no storage inside: it
  * builds the storages of its results at its exit, from these values and the
  * criteria written in the term.
  */
enum GroupValue:
  case Natural(value: BigInteger)
  case Truth(value: Boolean)
  case Constructed(value: ConstructedNaturals)

  /** The number of a row of a frame, which a relation's first column holds: for
    * each row of a frame, the values an expression has there.
    */
  case Row(index: Int)

  /** A list inside a block: the JIT's array list value
    * (`com.yang_bo.gezi.jit.NativeValue.ArrayListed`), raw data and no term, its elements
    * shared with every suffix and, for a list that entered the block, with the
    * storage it entered as, so that a suffix that leaves unchanged is that
    * storage's own suffix. Equal by its elements, whatever holder, as the JIT's
    * values are.
    */
  case List(listed: com.yang_bo.gezi.jit.NativeValue.ArrayListed)

  /** A value of a family its codec holds as a JVM `int`
    * (`com.yang_bo.gezi.jit.JvmPrimitive.Int`), such as the 32-bit words of `jvm_int`: the
    * family, and the bits.
    */
  case IntBits(family: com.yang_bo.gezi.jit.FamilyIdentity, bits: Int)

/** The lists a block makes of one element kind: the operations of the JIT's
  * storage encoding of the configuration the block was compiled for, whose
  * array lists the block's are, and the array list's representation. The
  * operations a list needs read the encoding's facts alone: no term of the
  * configuration is in a list.
  */
final case class GroupListKind[C <: NativeSpecializer & Singleton](
    operations: StorageEncodingOperations[C],
    representation: com.yang_bo.gezi.jit.Representation[Nothing]
):

  require(
    operations.arrayListRepresentations.contains(representation),
    s"the encoding makes no array lists of $representation"
  )

  /** The list of the elements, a new holder. Throws when an element is not of
    * the representation: a native whose declared result is a list of the
    * positive naturals returned a zero.
    */
  def of(values: Vector[com.yang_bo.gezi.jit.ArrayItem]): com.yang_bo.gezi.jit.NativeValue.ArrayListed =
    require(
      operations.holdsEvery(representation, values),
      s"a list of $representation holds only its elements: $values"
    )
    operations.arrayList(representation, values)

  /** The list of the item before the rest, one step, its hash codes known from
    * the rest's. The rest is of the representation: every list of a column that
    * no filter reads is of the column's static representation (the nil
    * constant, a native's result and a cons by the filter written in the term,
    * a filtered list by `Relabelled`, a tail by its list's), so a rest of
    * another is a defect and `arrayConsed` throws.
    */
  def consed(
      item: com.yang_bo.gezi.jit.ArrayItem,
      rest: com.yang_bo.gezi.jit.NativeValue.ArrayListed
  ): com.yang_bo.gezi.jit.NativeValue.ArrayListed =
    operations.arrayConsed(representation, item, rest)

  /** The list under this kind's representation
    * (`StorageEncodingOperations.relabelled`): none when the list is not of it.
    */
  def relabelled(
      listed: com.yang_bo.gezi.jit.NativeValue.ArrayListed
  ): Option[com.yang_bo.gezi.jit.NativeValue.ArrayListed] =
    operations.relabelled(listed, representation)

/** The operations of a block on its lists, each one step on the JIT's array
  * list value.
  */
object GroupLists:

  /** The first element of a nonempty list: a natural, or a family's value held
    * as a JVM `int`, the family the list's elements'.
    */
  def head(listed: com.yang_bo.gezi.jit.NativeValue.ArrayListed): GroupValue =
    listed.elements.values(listed.start) match
      case natural: BigInteger => GroupValue.Natural(natural)
      case bits: Int => GroupValue.IntBits(elementFamily(listed), bits)

  /** The list after the first element, the same holder. */
  def tail(
      listed: com.yang_bo.gezi.jit.NativeValue.ArrayListed
  ): com.yang_bo.gezi.jit.NativeValue.ArrayListed =
    require(!listed.nil, "the empty list has no tail")
    com.yang_bo.gezi.jit.NativeValue.ArrayListed(listed.elements, listed.start + 1)

  /** The family of a list's elements, by which lists of two kinds order. */
  def elementFamily(
      listed: com.yang_bo.gezi.jit.NativeValue.ArrayListed
  ): com.yang_bo.gezi.jit.FamilyIdentity =
    listed.elements.representation match
      case com.yang_bo.gezi.jit.Representation.ArrayListOf(element) =>
        element.familyIdentity
      case other =>
        throw IllegalStateException(s"an array list's elements under $other")

/** An elementwise operation of a group program, which a backend runs on each
  * row of a table (`GroupBackend.computed`), appending its value; a row on
  * which it has none is dropped, and the program then stops the block
  * (`GroupProgram`). Each is named, so that every backend gives its own
  * implementation of it.
  */
enum GroupOperation:

  /** The value, the same on every row: a constant of the block. */
  case Constant(value: GroupValue)

  /** Whether the value is of the representation, a filter's test: a natural, a
    * positive natural, a truth value, a family's value held as a JVM `int`.
    */
  case Admits(representation: GroupRepresentation)

  /** The list under the array lists' filter of elements of the representation,
    * relabelled under it (`StorageEncoding.relabelled`): none when the list is
    * not one of it, so that every list of a column a filter reads is of the
    * filter's representation.
    */
  case Relabelled(kind: GroupListKind[?])

  /** Whether the natural is zero, even and positive, or odd: a branch's tests
    * on a natural (`GroupExpression.Branch`).
    */
  case Zero
  case EvenPositive
  case Odd

  /** The half of a natural, rounded down: a branch's half. */
  case Half

  /** Twice a positive natural, none for zero: the binary naturals' even. */
  case Doubled

  /** Twice a natural and one: the binary naturals' odd. */
  case DoubledAndOne

  /** The value of a declared family at the constructor's position, its fields
    * the naturals of the arguments in order.
    */
  case ConstructedAt(constructor: Int)

  /** Whether the list is empty: a list's branch's test. */
  case Empty

  /** The first element and the suffix after it of a nonempty list: the binders
    * of a list's branch's cons case.
    */
  case Head
  case Tail

  /** The list of an element before a list, of the array lists' filter of
    * elements of the representation, which the list after it is of: none when
    * the element is not of the representation, so that the cons under the
    * positive naturals' criterion keeps only positive heads.
    */
  case Consed(element: GroupRepresentation, kind: GroupListKind[?])

/** How a group block passes an operand to a static method: a natural as a
  * `java.math.BigInteger`, a list of naturals as a
  * `scala.collection.immutable.Vector` of them (`NativePlace.NaturalList`), a
  * value of a family held as a JVM `int` as that `int`.
  */
enum GroupPlace:
  case Natural
  case NaturalList
  case IntBits

/** A native's static method as a group block calls it: the native's
  * implementation name, by which a backend may give its own elementwise
  * implementation (`JvmArrayGroupBackend`'s kernels), the method, and how it
  * takes each of its places.
  */
final case class GroupMethod(
    native: com.yang_bo.gezi.jit.NativeName,
    method: StaticBlockMethod,
    places: Vector[GroupPlace],
    resultFamily: Option[com.yang_bo.gezi.jit.FamilyIdentity] = None,
    resultList: Option[GroupListKind[?]] = None
):

  /** The method's handle, looked up once for the method rather than at every
    * call of a table: a pure function of the method, the lookup a class load
    * and a reflective search.
    */
  lazy val handle: java.lang.invoke.MethodHandle =
    ScalarGroupBackend.handle(this)

/** The row numbers of a frame's rows and the identities of their calls,
  * aligned, as `GroupBackend.asked` reads them back.
  */
final case class CallsIdentified(rows: IArray[Int], identities: IArray[Int]):
  require(
    rows.length == identities.length,
    s"each row has one identity: ${rows.length} rows, ${identities.length} identities"
  )

/** A group program's table: its columns, all of `rowCount` rows, a row one
  * combination of the block's values. A table of no column still has rows: the
  * product of a table with a table of no column and one row is the table
  * itself.
  */
final case class GroupTable[Column](columns: Vector[Column], rowCount: Int):
  require(rowCount >= 0, s"a table's rows are not negative: $rowCount")

/** The backend a group program runs on: how its columns are held and how the
  * program's operations, the outer product, the call of a native row by row,
  * concatenation, selection by a column of truth values and deduplication by
  * rows, run on them. The JVM scalar backend (`ScalarGroupBackend`) is the
  * reference: every other backend gives the same rows for the same program.
  *
  * A backend allocates its columns; a caller passes no buffer. Values enter a
  * table at a block's entry (`column`) and leave it at its exit (`rows`). In
  * between, the program reads back control data only: sizes, row numbers, and
  * the identities of calls (`GroupProgram`).
  *
  * A backend also keeps the finished calls of a run (`Memo`), so that a call's
  * arguments and results stay where the backend holds them: the program finds
  * calls by tables of keys and names a call by an identity the memo gives it.
  */
trait GroupBackend:

  /** A column of values, held as the backend holds them. */
  type Column

  /** The finished calls of one run and the identities of the calls asked for,
    * an immutable value threaded through the run.
    */
  type Memo

  /** The memo of a run that has finished no call, by the option the entry's
    * data chose.
    */
  def emptyMemo(option: GroupMemoOption): Memo

  /** The calls of a recursion at the rows given, a frame's rows none of whose
    * arguments waits: each argument a relation (the frame's row number, then a
    * value), a call's argument being that row's group of values, empty when the
    * relation has no value there. Gives the memo with an identity for each call
    * not finished before, the same for equal groups within a run (the memo
    * keeps each new call's groups under its identity); the relation of each row
    * whose call has finished to that call's results (the row number, then a
    * value); and the rows whose call has not finished with their calls'
    * identities, read back.
    */
  def asked(
      memo: Memo,
      recursion: Int,
      rows: IArray[Int],
      arguments: Vector[GroupTable[Column]]
  ): (Memo, GroupTable[Column], CallsIdentified)

  /** The arguments of the calls of the identities, one relation per argument:
    * the identity's position among `identities`, then each member of the call's
    * group for that argument.
    */
  def keys(
      memo: Memo,
      recursion: Int,
      identities: IArray[Int]
  ): Vector[GroupTable[Column]]

  /** The memo with the calls of the identities finished, each with the values
    * `results` (a relation: the row number, then a value) has at its row in
    * `rows` (aligned with `identities`); a call with no value there has
    * finished with no result.
    */
  def stored(
      memo: Memo,
      recursion: Int,
      identities: IArray[Int],
      rows: IArray[Int],
      results: GroupTable[Column]
  ): Memo

  /** The finished calls the memo holds, and how many of them a dense table
    * holds.
    */
  def memoSizes(memo: Memo): (Int, Int)

  /** A table of no row and `columns` columns. */
  def emptyTable(columns: Int): GroupTable[Column]

  /** The rows a join of the relations by the row number would make, for a frame
    * of `rowCount` rows: for each row, the product of the counts of that row's
    * values in each relation, summed. Only the number is read back.
    */
  def joinedSize(relations: Vector[GroupTable[Column]], rowCount: Int): Long

  /** The row numbers (`GroupValue.Row`) at the column of the rows given, in
    * their order.
    */
  def rowsAt(
      table: GroupTable[Column],
      column: Int,
      rows: IArray[Int]
  ): IArray[Int]

  /** The column of the values given, in order. */
  def column(values: Vector[GroupValue]): Column

  /** The table of the columns, which have the given number of rows. */
  def table(columns: Vector[Column], rowCount: Int): GroupTable[Column] =
    GroupTable(columns, rowCount)

  /** The outer product: each row of `left` beside each row of `right`, the
    * left's rows outer, the columns of `left` then those of `right`.
    */
  def product(
      left: GroupTable[Column],
      right: GroupTable[Column]
  ): GroupTable[Column]

  /** The table with the column of the native's results appended, the native
    * called row by row on the columns `arguments` in order by its static
    * method. A row on which the method answers that the term it is bound to has
    * no normal form (`StaticBlockResult.NaturalOrNoAnswer`) is dropped: it has
    * no value, as a row whose filter does not hold, and the program then stops
    * the block (`GroupProgram`).
    */
  def called(
      table: GroupTable[Column],
      method: GroupMethod,
      arguments: Vector[Int]
  ): GroupTable[Column]

  /** The table with a column appended that numbers its rows from 0
    * (`GroupValue.Row`).
    */
  def numbered(table: GroupTable[Column]): GroupTable[Column]

  /** Each row of `left` beside each row of `right` whose values at `rightKeys`
    * are those of the left row at `leftKeys`, the left's rows outer: the
    * columns of `left` then those of `right`. With the row number as the key,
    * it is the outer product within each row.
    */
  def joined(
      left: GroupTable[Column],
      right: GroupTable[Column],
      leftKeys: Vector[Int],
      rightKeys: Vector[Int]
  ): GroupTable[Column]

  /** The table with the column of the operation's values on the columns
    * `arguments` appended, a row on which it has no value dropped.
    */
  def computed(
      table: GroupTable[Column],
      operation: GroupOperation,
      arguments: Vector[Int]
  ): GroupTable[Column]

  /** The rows of `left` then those of `right`, of the same columns. */
  def concatenated(
      left: GroupTable[Column],
      right: GroupTable[Column]
  ): GroupTable[Column]

  /** The rows whose truth value at the column `mask` is true, and those whose
    * value there is false.
    */
  def selected(
      table: GroupTable[Column],
      mask: Int
  ): (GroupTable[Column], GroupTable[Column])

  /** The table with only the columns given, in their order. */
  def projected(
      table: GroupTable[Column],
      columns: Vector[Int]
  ): GroupTable[Column]

  /** The distinct rows, each once, in the canonical order of rows (`GroupValue`
    * order by kind, then value; a row by its values in order).
    */
  def unique(table: GroupTable[Column]): GroupTable[Column]

  /** The table's rows, read back as values. */
  def rows(table: GroupTable[Column]): Vector[Vector[GroupValue]]

/** The canonical order of values and rows of every backend. */
object GroupBackend:

  /** The order of values: naturals, then truth values, then constructed values,
    * then rows, then lists, then values held as an `int`; each kind by its
    * value, a constructed value by its constructor, then its fields in order, a
    * list by its length, then its elements in order, a value held as an `int`
    * by its family's name, then its bits read unsigned.
    */
  val valueOrdering: Ordering[GroupValue] = Ordering.fromLessThan {
    (left, right) =>
      compared(left, right) < 0
  }

  /** The order of rows: by their values in order, a shorter row first when one
    * is a prefix of the other.
    */
  val rowOrdering: Ordering[Vector[GroupValue]] = Ordering.fromLessThan {
    (left, right) =>
      left
        .lazyZip(right)
        .map(compared)
        .find(_ != 0)
        .map(_ < 0)
        .getOrElse(left.size < right.size)
  }

  private def kind(value: GroupValue): Int = value match
    case GroupValue.Natural(_)     => 0
    case GroupValue.Truth(_)       => 1
    case GroupValue.Constructed(_) => 2
    case GroupValue.Row(_)         => 3
    case GroupValue.List(_)        => 4
    case GroupValue.IntBits(_, _)  => 5

  private def compared(left: GroupValue, right: GroupValue): Int =
    (left, right) match
      case (GroupValue.Natural(first), GroupValue.Natural(second)) =>
        first.compareTo(second)
      case (GroupValue.Truth(first), GroupValue.Truth(second)) =>
        java.lang.Boolean.compare(first, second)
      case (GroupValue.Row(first), GroupValue.Row(second)) =>
        Integer.compare(first, second)
      case (
            GroupValue.IntBits(firstFamily, first),
            GroupValue.IntBits(secondFamily, second)
          ) =>
        if firstFamily != secondFamily then
          firstFamily.shown.compareTo(secondFamily.shown)
        else Integer.compareUnsigned(first, second)
      case (GroupValue.List(first), GroupValue.List(second)) =>
        if first == second then 0
        else
          val (firstFamily, secondFamily) =
            (GroupLists.elementFamily(first), GroupLists.elementFamily(second))
          val (firstValues, secondValues) = (first.suffix, second.suffix)
          if firstFamily != secondFamily then
            firstFamily.shown.compareTo(secondFamily.shown)
          else if firstValues.size != secondValues.size then
            Integer.compare(firstValues.size, secondValues.size)
          else
            firstValues
              .lazyZip(secondValues)
              .map(itemCompared)
              .find(_ != 0)
              .getOrElse(0)
      case (GroupValue.Constructed(first), GroupValue.Constructed(second)) =>
        if first.constructor != second.constructor then
          Integer.compare(first.constructor, second.constructor)
        else
          first.fields
            .lazyZip(second.fields)
            .map((one, other) => one.compareTo(other))
            .find(_ != 0)
            .getOrElse(Integer.compare(first.fields.size, second.fields.size))
      case _ => Integer.compare(kind(left), kind(right))

  /** The order of two elements of lists of one family: naturals by value,
    * 32-bit words unsigned.
    */
  private def itemCompared(
      left: com.yang_bo.gezi.jit.ArrayItem,
      right: com.yang_bo.gezi.jit.ArrayItem
  ): Int = (left, right) match
    case (first: BigInteger, second: BigInteger) => first.compareTo(second)
    case (first: Int, second: Int) => Integer.compareUnsigned(first, second)
    case _                         =>
      throw IllegalStateException(
        s"elements of one family, not $left and $right"
      )

  /** The value a static method returned, as the convention its result names
    * reads it: none for a `NaturalOrNoAnswer` method that answered that there
    * is no normal form. Throws `IllegalStateException` for a returned object of
    * another class than the convention's.
    */
  def returned(called: GroupMethod, result: Any): Option[GroupValue] =
    val (method, resultFamily) = (called.method, called.resultFamily)
    (method.result, result) match
      case (StaticBlockResult.Natural, natural: BigInteger) =>
        Some(GroupValue.Natural(natural))
      case (StaticBlockResult.NaturalOrNoAnswer, natural: BigInteger) =>
        Some(GroupValue.Natural(natural))
      case (StaticBlockResult.NaturalOrNoAnswer, other)
          if Option(other).isEmpty =>
        None
      case (StaticBlockResult.Truth, truth: java.lang.Boolean) =>
        Some(GroupValue.Truth(truth.booleanValue))
      case (StaticBlockResult.Constructed, constructed: ConstructedNaturals) =>
        Some(GroupValue.Constructed(constructed))
      case (StaticBlockResult.JvmInt, bits: java.lang.Integer) =>
        Some(
          GroupValue.IntBits(
            resultFamily.getOrElse(
              throw IllegalStateException(
                s"an int result of ${method.methodName} names no family"
              )
            ),
            bits.intValue
          )
        )
      case (StaticBlockResult.NaturalList, values: Vector[?]) =>
        val kind = called.resultList.getOrElse(
          throw IllegalStateException(
            s"a list result of ${method.methodName} names no list kind"
          )
        )
        Some(GroupValue.List(kind.of(values.map {
          case natural: BigInteger => natural: com.yang_bo.gezi.jit.ArrayItem
          case other               =>
            throw IllegalStateException(
              s"the static method ${method.className}.${method.methodName} returned a list holding $other"
            )
        })))
      case (convention, other) =>
        throw IllegalStateException(
          s"the static method ${method.className}.${method.methodName} returned $other, not a value of $convention"
        )
