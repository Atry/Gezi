package gezi.weakhead

import gezi.ir.Instruction

/** A constructor of the lists the codec decodes into and encodes from. */
enum ListConstructor:
  case Nil
  case Cons

/** A case a list is applied to in a decoding: the decoding, the tail depth
  * and the constructor; a neutral value no closed program can name.
  *
  * A neutral value, a free variable (`CONTRIBUTING.md`, "Types live only in the term"), kept as an exception argued here:
  * it stands for a
  * binder of the value read (a Scott value's handler, a constructor's or a
  * define's parameter), opened to read the value's head, as the normal-form
  * reader's `BoundVariable` opens a lambda, whose Scaladoc has the argument.
  * A closed term in its place would not do: a term that is no such value
  * could ignore it and build the reading itself.
  */
final case class ListCase(decoding: Decoding, level: Int, constructor: ListConstructor)
    extends NeutralVariable

/** A field of cons the check of the constructors applies cons to. */
enum ListFieldName:
  case Head
  case Tail

/** The fresh fields the check of the constructors applies cons to.
  *
  * A neutral value, a free variable (`CONTRIBUTING.md`, "Types live only in the term"), kept as an exception argued here:
  * it stands for a
  * binder of the value read (a Scott value's handler, a constructor's or a
  * define's parameter), opened to read the value's head, as the normal-form
  * reader's `BoundVariable` opens a lambda, whose Scaladoc has the argument.
  * A closed term in its place would not do: a term that is no such value
  * could ignore it and build the reading itself.
  */
final case class ListField(decoding: Decoding, field: ListFieldName) extends NeutralVariable

/** What a head of a value applied to a decoding's cases reads. */
enum ListReading:

  /** The first case with no argument. */
  case Nil

  /** The second case over two arguments, the head and the tail. */
  case Cons(head: Value, tail: Value)

  /** Any other head (the Prolog codec's `none`). */
  case NoCase

/** A value of the representation list(E) (list_codec.pl), over the JIT's
  * run-time values of type Item: `items(Length, Items)`, the items kept as
  * they were given, unevaluated, and its length; or `cell(Item, Tail)`, a
  * list whose tail is not read (A LIST WHOSE TAIL IS NOT READ there).
  */
enum ListRepresentation[+Item]:

  /** The items and their number. */
  case Items(length: Int, items: Vector[Item])

  /** An item and a tail not read. */
  case Cell(item: Item, tail: ListTail[Item])

/** The tail of a cell: a term nothing has read (`unread(Term)`), or a list
  * of the representation.
  */
enum ListTail[+Item]:
  case Unread(term: Item)
  case Listed(list: ListRepresentation[Item])

/** A field a value of the representation hands out to a case it is applied
  * to (`eliminatedBranch`).
  */
enum ListElementField[+Item]:

  /** An item filtered by the element, `parallel(Item, Element)`. */
  case Filtered(item: Item, element: Item)

  /** A list of the representation list(Element), `represented(list(E), L)`.
    */
  case Represented(element: Item, list: ListRepresentation[Item])

  /** The term of a tail not read, as it was given. */
  case Term(term: Item)

/** The codec of the representation list(E): the library's lists as host
  * vectors. The port of `gezi/prolog/gezi/list_codec.pl`, a
  * hand-written codec, for the representations the Prolog backend's fact
  * `native_specialization(list)` names, one for each element filter: at a
  * decode point x ∥ list_type E the representation is list(E), E the
  * criterion's argument, a term the codec plants and never reads. The value
  * `Items(n, Vector(i1, ..., in))` stands for cons (i1 ∥ E) (cons (i2 ∥ E)
  * ... nil), nil and cons the terms at the positions 0 and 1 of the
  * `data_family` of the type the knowledge module of the backend
  * specializes to list (`position`). The items are kept as they
  * were given, unevaluated, so a list's head is read only where a consumer
  * reads it, except the values of a fallback point's check, which the check
  * evaluated when the cell was built.
  *
  * FIXME (carried from list_codec.pl:26, following the FIXME at the JIT's https://github.com/Atry/private-overlay/issues/1938
  * item_outcome/3, jit.pl:1096, carried to its port
  * `gezi.jit.Jit`'s `itemOutcome`): the check of a fallback
  * point runs when its cell is built, so a list holding one is less lazy
  * than the define, and where the check does not end a reading of the
  * list's spine loses its answer.
  *
  * A LIST WHOSE TAIL IS NOT READ, THE ASSUMED SHAPE and A TRUSTED
  * DECLARATION: the Prolog module comment, unchanged (`git show
  * 13db98f8d:lambda_jit/prolog/lambda_jit/list_codec.pl`). A list is a Scott
  * value of two cases: applied to two arguments, nil's value answers the
  * first and cons h t's value the second applied to h and t, as `\n. \c. n`
  * and `\h. \t. \n. \c. c h t` do. DECODING applies a value to the cases of
  * `decodingCases` and reads each head with `caseReading`; the tail is then
  * decoded one level deeper with cases of its own level, the head kept as it
  * is. The codec assumes this one shape of value and decides no type.
  *
  * WHY A DECODED LIST STANDS FOR THE FILTERED VALUE: the Prolog module
  * comment, unchanged: x ⊑ cons h1 (... (cons hn nil)) by the decoding,
  * provided that no item mentions a case of the decoding, which the decoding
  * does not check.
  *
  * FIXME (carried from list_codec.pl:83, following the FIXME at the JIT's https://github.com/Atry/private-overlay/issues/1939
  * reading_decoded/5, jit.pl:2144, carried to the port of answer_decoded/5,
  * `gezi.jit.Jit`'s `answerDecoded`): an item is
  * kept with no check that it mentions no case of the decoding; a value that
  * passes its own case to its cons case keeps the decoding's neutral value
  * as an item, and the reader throws on it.
  *
  * FIXME (2026-11-07, data families declared by facts): the lists' family is now declared by facts (`data_family`, https://github.com/Atry/private-overlay/issues/1940
  * `data_fields` and `jvm_type(list)` on `list_type`), and the declaration
  * is checked against this codec (`gezi.jit.DeclaredFamilies`), but the
  * lists are still held by this codec of their own rather than by the
  * generic codec every other declared family uses. Whether the generic codec
  * should replace it is a measurement, a JMH reading of both on the lists'
  * readings, not a design given.
  */
object ListCodec:

  /** The two cases a value of the decoding is applied to at the tail depth.
    */
  def decodingCases(decoding: Decoding, level: Int): (Value, Value) =
    (
      Value.Neutral(ListCase(decoding, level, ListConstructor.Nil), Vector.empty),
      Value.Neutral(ListCase(decoding, level, ListConstructor.Cons), Vector.empty)
    )

  /** What a head of a value applied to the decoding's cases at the level
    * reads.
    */
  def caseReading(head: Head, decoding: Decoding, level: Int): ListReading = head match
    case Head.Neutral(ListCase(`decoding`, `level`, ListConstructor.Nil), arguments) if arguments.isEmpty =>
      ListReading.Nil
    case Head.Neutral(ListCase(`decoding`, `level`, ListConstructor.Cons), Vector(listHead, listTail)) =>
      ListReading.Cons(listHead, listTail)
    case _ => ListReading.NoCase

  /** The position of the constructor among the cases, by the assumed shape,
    * and so in the `data_family` of a type the codec holds: nil 0, cons 1.
    * A constructor is its position, never a name.
    */
  def position(constructor: ListConstructor): Int = constructor match
    case ListConstructor.Nil  => 0
    case ListConstructor.Cons => 1

  /** The term the list of the representation list(element) stands for,
    * applied to the count of arguments, answers its branch-th argument
    * applied to the fields, by the assumed shape: the empty list answers the
    * first of two arguments with no field; a list of a first item i answers
    * the second applied to i filtered by the element and to its tail: the
    * rest of the items in the representation, its length one less, for
    * `Items`; for `Cell`, the tail as it was given (`tailField`), read only
    * now that a consumer reads it. The count, the branch and the fields.
    */
  def eliminatedBranch[Item](
      element: Item,
      list: ListRepresentation[Item]
  ): (Int, Int, Vector[ListElementField[Item]]) = list match
    case ListRepresentation.Items(length, items) =>
      assert(length == items.size, s"a list of ${items.size} items says its length is $length")
      if items.isEmpty then (2, 1, Vector.empty)
      else
        (
          2,
          2,
          Vector(
            ListElementField.Filtered(items.head, element),
            ListElementField.Represented(element, ListRepresentation.Items(length - 1, items.tail))
          )
        )
    case ListRepresentation.Cell(item, tail) =>
      (2, 2, Vector(ListElementField.Filtered(item, element), tailField(element, tail)))

  /** The field the tail of a cell of the representation list(element)
    * stands for: the term of a tail not read, and a list of the
    * representation as a represented value.
    */
  def tailField[Item](element: Item, tail: ListTail[Item]): ListElementField[Item] = tail match
    case ListTail.Unread(term) => ListElementField.Term(term)
    case ListTail.Listed(list) => ListElementField.Represented(element, list)

  /** Whether the defines nil and cons have the assumed shape, read under
    * weak_head: every head of nil applied to the cases reads Nil, and every
    * head of cons applied to two fresh fields and then to the cases reads
    * Cons of those two, each with at least one head; `Shape.LimitReached`
    * when a reading runs past its budget. Each reading within
    * `Codecs.shapeStepLimit` steps.
    */
  def constructorsShape(nil: Instruction, cons: Instruction): Shape[ListReading] =
    val (nilCase, consCase) = decodingCases(Decoding.Shape, 0)
    val listHead = Value.Neutral(ListField(Decoding.Shape, ListFieldName.Head), Vector.empty)
    val listTail = Value.Neutral(ListField(Decoding.Shape, ListFieldName.Tail), Vector.empty)
    val nilReadings = Codecs.readingsWithin(
      Value.Apply(Value.Apply(nil, nilCase), consCase),
      ListReading.NoCase
    )(caseReading(_, Decoding.Shape, 0))
    val consReadings = Codecs.readingsWithin(
      Value.Apply(
        Value.Apply(Value.Apply(Value.Apply(cons, listHead), listTail), nilCase),
        consCase
      ),
      ListReading.NoCase
    )(caseReading(_, Decoding.Shape, 0))
    Codecs.shapeOf(nilReadings, consReadings, ListReading.Nil, ListReading.Cons(listHead, listTail))
