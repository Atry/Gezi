package gezi.jit

import gezi.ir.ConstructorIdentity
import gezi.weakhead.ListCase
import gezi.weakhead.ListRepresentation
import gezi.ir.Value
import gezi.weakhead.Values
import scala.annotation.tailrec
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Configured, NativeSpecializer}

/** A node of a value as a key: equal to itself only and hashed by its identity,
  * so that a subvalue the heap shares is one key, found in time independent of
  * its size.
  */
final class Identity(val node: AnyRef):

  override def equals(other: Any): Boolean = other match
    case that: Identity => that.node eq node
    case _              => false

  override def hashCode: Int = System.identityHashCode(node)

/** The values a walk found to hold no case of a decoding
  * (`JitValues.caseWalk`), by identity: the memo of a pure function of the
  * value, whose emptying changes only how many nodes a later walk visits
  * (`CONTRIBUTING.md`, "Tables"). It is kept in two generations, as the
  * instance table is (`InstanceRetention`), so that a long run holds a bounded
  * number of values. A value found in the older generation is brought into the
  * young one with nothing under it visited, so that the root of a structure met
  * in every generation stands for the whole of it.
  */
final case class CaseFreeValues(young: Set[Identity], older: Set[Identity])

object CaseFreeValues:

  /** No value known. */
  val empty: CaseFreeValues = CaseFreeValues(Set.empty, Set.empty)

/** What a walk for a case of a decoding found: the values known afterwards when
  * the walked value holds no case, none when it holds one; and the nodes the
  * walk visited, a cost.
  */
final case class CaseWalk(caseFree: Option[CaseFreeValues], visits: Long)

/** The conversions between the reference's values and the JIT's, each
  * trampolined, so that a deep value costs heap and not JVM stack.
  *
  * SHARING. Each conversion that rebuilds a value threads an immutable map from
  * the nodes already converted, keyed by identity (`Identity`), to their
  * images, so that a subvalue met along several paths is converted once and its
  * image is shared by the paths as the subvalue was: the result has as many
  * distinct nodes as the input, not as many as the input written out as a tree.
  * A value that is a small graph of a large tree (the program of
  * `ReductionMeaningsRepeated` at seed 568201625 and two repetitions: 156
  * distinct nodes, 1.93e10 as a tree) is then converted in time and space
  * linear in its distinct nodes.
  */
object JitValues:

  /** A decode point's head of `x ∥ list_type E` as the array list
    * (`Representation.ArrayListOf`) of `x ∥ array_list E`, the same term by the
    * β rule: the list's cells walked once, on the heap, each item a storage of
    * E's representation and each tail a storage of the list down to its nil,
    * their elements one array; none when a cell is not of that form (an item
    * left as written, a tail not read), the list's head then standing for the
    * term.
    */
  // FIXME: https://github.com/Atry/private-overlay/issues/2228 a cell whose item
  // is a storage of another representation of the element's family (a positive
  // natural under `array_list N`) is not packed, so the JIT reads such a list as
  // cells where the group blocks relabel it as an array list: one term, two
  // representations. To be fixed by relabelling here as the blocks do
  // (`StorageEncoding`'s relabelling), the snapshots' diffs derived first.
  def arrayPacked[C <: NativeSpecializer & Singleton](
      operations: StorageEncodingOperations[C],
      representation: Representation[JitValue[C]],
      element: Representation[JitValue[C]],
      head: JitHead[C]
  )(using C): Option[JitHead[C]] =
    head match
      case JitHead.Represented(
            listRepresentation @ Representation.ListOf(_),
            first
          ) =>
        @scala.annotation.tailrec
        def walked(
            value: NativeValue[JitValue[C]],
            found: Vector[ArrayItem]
        ): Option[Vector[ArrayItem]] = value match
          case NativeValue.Listed(ListRepresentation.Items(0, _)) => Some(found)
          case NativeValue.Listed(ListRepresentation.Cell(item, tail)) =>
            val itemOf: Option[ArrayItem] = operations.storedThrough(item) match
              case Some(JitValue.Stored(natural: BinaryNaturalStorage))
                  if natural.representation == element =>
                Some(natural.natural.bigInteger)
              case Some(JitValue.Stored(word: IntStorage))
                  if word.representation == element =>
                Some(word.bits)
              case _ => None
            (itemOf, operations.storedThrough(tail)) match
              case (Some(read), Some(JitValue.Stored(next)))
                  if next.representation == listRepresentation =>
                walked(StorageOf.nativeValue(next), found :+ read)
              case _ => None
          case _ => None
        walked(first, Vector.empty).flatMap(values =>
          operations.storageOf(
            representation,
            operations.arrayList(representation, values)
          ) match
            case JitValue.Stored(storage) => Some(storage)
            case _                        => None
        )
      case _ => None

  /** Whether a value a decoding gave may hold a case of a decoding, the neutral
    * value a list's or a data family's decoding applies a value to (`ListCase`,
    * `DataCase`). A decoded value stands for the filtered value only when it
    * holds none (`gezi.weakhead.ListCodec`, WHY A DECODED LIST STANDS FOR THE
    * FILTERED VALUE): a value that passes its own case to a constructor's case
    * keeps that neutral value as a field. Each item, unread tail and unread
    * field is walked as a tree within its own `decodingCaseWalkLimit` values,
    * true where a walk does not decide, so that the check of a list costs, as
    * its decoding does, time linear in its items; the cells and the fields are
    * walked with no recursion on the stack.
    */
  def mayHoldDecodingCase[C <: NativeSpecializer & Singleton](
      value: NativeValue[JitValue[C]]
  )(using C): Boolean =
    holdsDecodingCase(List(value), Nil)

  /** The most values the walk of one term in `mayHoldDecodingCase` takes before
    * it answers true: the normal-form reader's own limit for the walk of a
    * plain value (`gezi.weakhead.NormalForms`, 4,096), so that a term is walked
    * as far as the reader would walk it.
    */
  val decodingCaseWalkLimit: Int = 4096

  @tailrec
  private def holdsDecodingCase[C <: NativeSpecializer & Singleton](
      held: List[NativeValue[JitValue[C]]],
      terms: List[JitValue[C]]
  )(using C): Boolean =
    terms match
      case term :: rest =>
        termWalked(List(term), decodingCaseWalkLimit, held) match
          case None        => true
          case Some(found) => holdsDecodingCase(found, rest)
      case Nil =>
        held match
          case Nil           => false
          case value :: rest =>
            value match
              case NativeValue.Listed(ListRepresentation.Items(_, items)) =>
                holdsDecodingCase(rest, items.toList)
              case NativeValue.Listed(ListRepresentation.Cell(item, tail)) =>
                holdsDecodingCase(rest, List(item, tail))
              case NativeValue.Stored(term) =>
                holdsDecodingCase(rest, storedFields(term))
              case NativeValue.Constructed(_, _, fields) =>
                holdsDecodingCase(fields.toList ::: rest, Nil)
              case NativeValue.Unread(term) =>
                holdsDecodingCase(rest, List(term))
              case _ => holdsDecodingCase(rest, Nil)

  /** The walk of one term within the values remaining: `None` where it meets a
    * case of a decoding or spends them, otherwise the held values with the
    * represented values it met added, to be walked each on its own.
    */
  @tailrec
  private def termWalked[C <: NativeSpecializer & Singleton](
      pending: List[JitValue[C]],
      remaining: Int,
      held: List[NativeValue[JitValue[C]]]
  )(using C): Option[List[NativeValue[JitValue[C]]]] =
    pending match
      case Nil                 => Some(held)
      case _ if remaining <= 0 => None
      case value :: rest       =>
        value match
          case JitValue.IrTerm(_) => termWalked(rest, remaining - 1, held)
          case JitValue.Apply(function, argument) =>
            termWalked(function :: argument :: rest, remaining - 1, held)
          case JitValue.Parallel(left, right) =>
            termWalked(left :: right :: rest, remaining - 1, held)
          case JitValue.Choice(members) =>
            termWalked(members.toList ::: rest, remaining - 1, held)
          case JitValue.Thunk(_, _, fillings) =>
            termWalked(fillings.toList ::: rest, remaining - 1, held)
          case JitValue.Represented(_, found) =>
            termWalked(rest, remaining - 1, found :: held)
          case JitValue.Grouped(members) =>
            termWalked(members.toList ::: rest, remaining - 1, held)
          case JitValue.Neutral(variable, arguments) =>
            variable match
              case ListCase(_, _, _) | DataCase(_, _, _, _) => None
              case _                                        =>
                termWalked(arguments.toList ::: rest, remaining - 1, held)

  /** The images of the nodes converted so far, by identity. */
  private type Images[Image] = Map[Identity, Image]

  /** The step's image of the node, read from the images when the node was met
    * before, and otherwise made by the step and recorded.
    */
  private def shared[Node <: AnyRef, Image](node: Node, images: Images[Image])(
      step: (Node, Images[Image]) => TailRec[(Image, Images[Image])]
  ): TailRec[(Image, Images[Image])] =
    images.get(Identity(node)) match
      case Some(found) => done((found, images))
      case None        =>
        tailcall(step(node, images)).map((image, after) =>
          (image, after.updated(Identity(node), image))
        )

  /** The step's images of the nodes in order, the images threaded from one node
    * to the next.
    */
  private def allImages[Node, Image](
      nodes: Vector[Node],
      images: Images[Image]
  )(
      step: (Node, Images[Image]) => TailRec[(Image, Images[Image])]
  ): TailRec[(Vector[Image], Images[Image])] =
    def from(
        index: Int,
        found: Vector[Image],
        current: Images[Image]
    ): TailRec[(Vector[Image], Images[Image])] =
      if index >= nodes.size then done((found, current))
      else
        tailcall(step(nodes(index), current)).flatMap((image, next) =>
          from(index + 1, found :+ image, next)
        )
    from(0, Vector.empty, images)

  /** The step's images of two nodes, the images threaded from the first to the
    * second.
    */
  private def bothImages[Node, Image](
      first: Node,
      second: Node,
      images: Images[Image]
  )(
      step: (Node, Images[Image]) => TailRec[(Image, Images[Image])]
  ): TailRec[((Image, Image), Images[Image])] =
    tailcall(step(first, images)).flatMap((firstImage, afterFirst) =>
      tailcall(step(second, afterFirst)).map((secondImage, afterSecond) =>
        ((firstImage, secondImage), afterSecond)
      )
    )

  /** The run-time value of a field of the representation: the term itself for a
    * field of the family `unread`, the value of the representation otherwise.
    */
  def fieldTerm[C <: NativeSpecializer & Singleton](
      operations: StorageEncodingOperations[C],
      representation: Representation[JitValue[C]],
      value: NativeValue[JitValue[C]]
  )(using C): JitValue[C] = value match
    case NativeValue.Unread(term) => term
    case NativeValue.Stored(term) => term
    case other                    => operations.storageOf(representation, other)

  /** Whether the value holds a case of a decoding (`DataCase`, `ListCase`): a
    * field kept unread that holds one refers to the binder the decoding opened,
    * so that the case would leave the decoding. The walk visits each shared
    * part once and stops at a value `known` holds, so that a run whose state
    * grows by a part at each step visits that part and not the whole state. The
    * values it visited become known only when it found no case.
    */
  def caseWalk[C <: NativeSpecializer & Singleton](
      value: JitValue[C],
      known: CaseFreeValues,
      retention: InstanceRetention
  )(using C): CaseWalk =
    val (seen, visits) =
      walkedForCase(List(value), known.young, known.older, 0L)
    CaseWalk(
      seen.map(young =>
        retention match
          case InstanceRetention.Generations(size) if young.size >= size =>
            CaseFreeValues(Set.empty, young)
          case InstanceRetention.Generations(_) |
              InstanceRetention.NeverDropped =>
            CaseFreeValues(young, known.older)
      ),
      visits
    )

  @tailrec
  private def walkedForCase[C <: NativeSpecializer & Singleton](
      pending: List[JitValue[C]],
      seen: Set[Identity],
      older: Set[Identity],
      visits: Long
  )(using C): (Option[Set[Identity]], Long) = pending match
    case Nil           => (Some(seen), visits)
    case value :: rest =>
      val key = Identity(value.representation)
      if seen.contains(key) then walkedForCase(rest, seen, older, visits)
      else if older.contains(key) then
        walkedForCase(rest, seen + key, older, visits)
      else
        val visited = seen + key
        val counted = visits + 1
        value match
          case JitValue.Neutral(_: DataCase | _: ListCase, _) => (None, counted)
          case JitValue.Neutral(_, arguments)                 =>
            walkedForCase(arguments.toList ++ rest, visited, older, counted)
          case JitValue.Apply(function, argument) =>
            walkedForCase(function :: argument :: rest, visited, older, counted)
          case JitValue.Parallel(left, right) =>
            walkedForCase(left :: right :: rest, visited, older, counted)
          case JitValue.Choice(members) =>
            walkedForCase(members.toList ++ rest, visited, older, counted)
          case JitValue.Thunk(_, _, fillings) =>
            walkedForCase(fillings.toList ++ rest, visited, older, counted)
          case JitValue.Represented(_, native) =>
            walkedForCase(nativeParts(native) ++ rest, visited, older, counted)
          case JitValue.Grouped(members) =>
            walkedForCase(members.toList ++ rest, visited, older, counted)
          case _ => walkedForCase(rest, visited, older, counted)

  /** The run-time values a native value holds. */
  private def nativeParts[C <: NativeSpecializer & Singleton](
      value: NativeValue[JitValue[C]]
  )(using C): List[JitValue[C]] = value match
    case NativeValue.Unread(term)              => List(term)
    case NativeValue.Stored(term)              => storedFields(term)
    case NativeValue.Constructed(_, _, fields) =>
      fields.toList.flatMap(nativeParts)
    case NativeValue.Listed(list) => listParts(list)
    case _                        => Nil

  /** The fields of a declared family's stored value, one layer: the terms its
    * storage holds. Walking the stored term itself would read it as a value of
    * a representation again, whose native value is that term.
    */
  private def storedFields[C <: NativeSpecializer & Singleton](
      term: JitValue[C]
  )(using C): List[JitValue[C]] = term match
    case JitValue.Stored(storage) =>
      StorageOf
        .constructed[C](storage)
        .fold(List.empty[JitValue[C]])(_.fields.toList)
    case _ => Nil

  private def listParts[C <: NativeSpecializer & Singleton](
      list: ListRepresentation[JitValue[C]]
  )(using C): List[JitValue[C]] = list match
    case ListRepresentation.Items(_, items)  => items.toList
    case ListRepresentation.Cell(item, tail) => List(item, tail)
