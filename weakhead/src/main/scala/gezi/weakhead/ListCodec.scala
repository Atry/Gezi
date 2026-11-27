package gezi.weakhead

import gezi.ir.{Configured, NativeSpecializer, Value}

/** A constructor of the lists the codec decodes into and encodes from. */
enum ListConstructor:
  case Nil
  case Cons

/** A case a list is applied to in a decoding: the decoding, the tail depth and
  * the constructor; a neutral value no closed program can name.
  *
  * A neutral value, a free variable (`CONTRIBUTING.md`, "Types live only in the
  * term"), kept as an exception argued here: it stands for a binder of the
  * value read (a Scott value's handler, a constructor's or a define's
  * parameter), opened to read the value's head, as the normal-form reader's
  * `BoundVariable` opens a lambda, whose Scaladoc has the argument. A closed
  * term in its place would not do: a term that is no such value could ignore it
  * and build the reading itself.
  */
final case class ListCase(
    decoding: Decoding,
    level: Int,
    constructor: ListConstructor
) extends NeutralVariable

/** A field of cons the check of the constructors applies cons to. */
enum ListFieldName:
  case Head
  case Tail

/** The fresh fields the check of the constructors applies cons to.
  *
  * A neutral value, a free variable (`CONTRIBUTING.md`, "Types live only in the
  * term"), kept as an exception argued here: it stands for a binder of the
  * value read (a Scott value's handler, a constructor's or a define's
  * parameter), opened to read the value's head, as the normal-form reader's
  * `BoundVariable` opens a lambda, whose Scaladoc has the argument. A closed
  * term in its place would not do: a term that is no such value could ignore it
  * and build the reading itself.
  */
final case class ListField(decoding: Decoding, field: ListFieldName)
    extends NeutralVariable

/** What a head of a value applied to a decoding's cases reads. */
enum ListReading[C <: NativeSpecializer & Singleton]:

  /** The first case with no argument. */
  case Nil()

  /** The second case over two arguments, the head and the tail. */
  case Cons(head: Value[C], tail: Value[C])

  /** Any other head (the Prolog codec's `none`). */
  case NoCase()

/** A value of the representation list(E) (list_codec.pl), over the JIT's
  * run-time values of type Item: `items(Length, Items)`, the items kept as they
  * were given, unevaluated, and its length; or `cell(Item, Tail)`, a list whose
  * tail is not read (A LIST WHOSE TAIL IS NOT READ there).
  */
enum ListRepresentation[+Item]:

  /** The items and their number: a native's whole list, and the empty list a
    * storage holds.
    */
  case Items(length: Int, items: Vector[Item])

  /** One cell, a storage's one layer `cons (item ∥ E) tail ∥ list_type E`: the
    * item and the tail's node as written, never read here. The tail is
    * `t ∥ list_type E` or a storage of the list, the unique spelling, except
    * for a cell cons's native makes under the default construction, whose tail
    * is the term as given.
    *
    * FIXME: that cell's view is not the unique spelling, its tail unfiltered;
    * https://github.com/Atry/private-overlay/issues/2202 kept as main has it,
    * by copy-on-write, and a decode point filters such a tail
    * (`gezi.jit.JitRules.decodePointValue`).
    */
  case Cell(item: Item, tail: Item)

/** A field a value of the representation hands out to a case it is applied to
  * (`eliminatedBranch`).
  */
enum ListElementField[+Item]:

  /** An item filtered by the element, `parallel(Item, Element)`. */
  case Filtered(item: Item, element: Item)

  /** A cell's tail node, handed out as it is. */
  case Node(node: Item)

/** The codec of the representation list(E): the library's lists as host
  * vectors. The port of `gezi/prolog/gezi/list_codec.pl`, a hand-written codec,
  * for the representations the Prolog backend's fact
  * `native_specialization(list)` names, one for each element filter: at a
  * decode point x ∥ list_type E the representation is list(E), E the
  * criterion's argument, a term the codec plants and never reads. The value
  * `Items(n, Vector(i1, ..., in))` stands for cons (i1 ∥ E) (cons (i2 ∥ E) ...
  * nil), nil and cons the terms at the positions 0 and 1 of the `data_family`
  * of the type the knowledge module of the backend specializes to list
  * (`position`). The items are kept as they were given, unevaluated, so a
  * list's head is read only where a consumer reads it, except the values of a
  * fallback point's check, which the check evaluated when the cell was built.
  *
  * FIXME (carried from list_codec.pl:26, following the FIXME at the JIT's
  * https://github.com/Atry/private-overlay/issues/1938 item_outcome/3,
  * jit.pl:1096, carried to its port `gezi.jit.Jit`'s `itemOutcome`): the check
  * of a fallback point runs when its cell is built, so a list holding one is
  * less lazy than the define, and where the check does not end a reading of the
  * list's spine loses its answer.
  *
  * A LIST WHOSE TAIL IS NOT READ, THE ASSUMED SHAPE and A TRUSTED DECLARATION:
  * the Prolog module comment, unchanged (`git show
  * 13db98f8d:lambda_jit/prolog/lambda_jit/list_codec.pl`). A list is a Scott
  * value of two cases: applied to two arguments, nil's value answers the first
  * and cons h t's value the second applied to h and t, as `\n. \c. n` and
  * `\h. \t. \n. \c. c h t` do. DECODING applies a value to the cases of
  * `decodingCases` and reads each head with `caseReading`; the tail is then
  * decoded one level deeper with cases of its own level, the head kept as it
  * is. The codec assumes this one shape of value and decides no type.
  *
  * WHY A DECODED LIST STANDS FOR THE FILTERED VALUE: x ⊑ cons h1 (... (cons hn
  * nil)) by the decoding, provided that no item mentions a case of the
  * decoding. So the decoded list may lose answers of the filtered value and
  * adds none. The decoding itself does not check the proviso: its caller, the
  * JIT's decode point, does (`gezi.jit.JitValues.mayHoldDecodingCase`), and
  * reads the filtered value as a parallel where an item may mention a case.
  *
  * FIXME (2026-11-07, data families declared by facts): the lists' family is
  * now declared by facts (`data_family`,
  * https://github.com/Atry/private-overlay/issues/1940 `data_fields` and
  * `jvm_type(list)` on `list_type`), and the declaration is checked against
  * this codec (`gezi.jit.DeclaredFamilies`), but the lists are still held by
  * this codec of their own rather than by the generic codec every other
  * declared family uses. Whether the generic codec should replace it is a
  * measurement, a JMH reading of both on the lists' readings, not a design
  * given.
  */
object ListCodec:

  /** The two cases a value of the decoding is applied to at the tail depth.
    */
  def decodingCases[C <: NativeSpecializer & Singleton](
      decoding: Decoding,
      level: Int
  )(using C): (Value[C], Value[C]) =
    (
      NeutralValue(
        ListCase(decoding, level, ListConstructor.Nil),
        Vector.empty
      ),
      NeutralValue(
        ListCase(decoding, level, ListConstructor.Cons),
        Vector.empty
      )
    )

  /** What a head of a value applied to the decoding's cases at the level reads.
    */
  def caseReading[C <: NativeSpecializer & Singleton](
      head: Head[C],
      decoding: Decoding,
      level: Int
  )(using
      C
  ): ListReading[C] = head match
    case Head.Neutral(
          ListCase(`decoding`, `level`, ListConstructor.Nil),
          arguments
        ) if arguments.isEmpty =>
      ListReading.Nil()
    case Head.Neutral(
          ListCase(`decoding`, `level`, ListConstructor.Cons),
          Vector(listHead, listTail)
        ) =>
      ListReading.Cons(listHead, listTail)
    case _ => ListReading.NoCase()

  /** The position of the constructor among the cases, by the assumed shape, and
    * so in the `data_family` of a type the codec holds: nil 0, cons 1. A
    * constructor is its position, never a name.
    */
  def position(constructor: ListConstructor): Int = constructor match
    case ListConstructor.Nil  => 0
    case ListConstructor.Cons => 1

  /** The term the list of the representation list(element) stands for, applied
    * to the count of arguments, answers its branch-th argument applied to the
    * fields, by the assumed shape: the empty list answers the first of two
    * arguments with no field; a cell of an item i answers the second applied to
    * i filtered by the element and to its tail's node as it is. The count, the
    * branch and the fields. A whole list of items is never stored
    * (`gezi.jit.RepresentedStorage.apply` makes it into cells).
    */
  def eliminatedBranch[Item](
      element: Item,
      list: ListRepresentation[Item]
  ): (Int, Int, Vector[ListElementField[Item]]) = list match
    case ListRepresentation.Items(0, _)         => (2, 1, Vector.empty)
    case items @ ListRepresentation.Items(_, _) =>
      throw IllegalStateException(
        s"a stored list is the empty list or one cell, not the whole list $items"
      )
    case ListRepresentation.Cell(item, tail) =>
      (
        2,
        2,
        Vector(
          ListElementField.Filtered(item, element),
          ListElementField.Node(tail)
        )
      )

  /** Whether the defines nil and cons have the assumed shape, read under
    * weak_head: every head of nil applied to the cases reads Nil, and every
    * head of cons applied to two fresh fields and then to the cases reads Cons
    * of those two, each with at least one head; `Shape.LimitReached` when a
    * reading runs past its budget. Each reading within `Codecs.shapeStepLimit`
    * steps.
    */
  def constructorsShape[C <: NativeSpecializer & Singleton](
      nil: Configured[C],
      cons: Configured[C]
  )(using
      C,
      gezi.ir.StorageAccess
  ): Shape[ListReading[C]] =
    val (nilCase, consCase) = decodingCases[C](Decoding.Shape, 0)
    val listHead = NeutralValue[C](
      ListField(Decoding.Shape, ListFieldName.Head),
      Vector.empty
    )
    val listTail = NeutralValue[C](
      ListField(Decoding.Shape, ListFieldName.Tail),
      Vector.empty
    )
    val nilReadings = Codecs.readingsWithin(
      Value.Apply(Value.Apply(Value.of(nil), nilCase), consCase),
      ListReading.NoCase[C]()
    )(caseReading(_, Decoding.Shape, 0))
    val consReadings = Codecs.readingsWithin(
      Value.Apply(
        Value.Apply(
          Value.Apply(Value.Apply(Value.of(cons), listHead), listTail),
          nilCase
        ),
        consCase
      ),
      ListReading.NoCase[C]()
    )(caseReading(_, Decoding.Shape, 0))
    Codecs.shapeOf(
      nilReadings,
      consReadings,
      ListReading.Nil[C](),
      ListReading.Cons(listHead, listTail)
    )
