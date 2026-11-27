package com.yang_bo.gezi.ir

/** A total order of interned terms by their content, the same in every run: a
  * native storage before a constructor object, two storages by their own order
  * where it orders them (`NativeStorage.precedes`), else by their outermost
  * constructor's position, the terms they hold without their views
  * (`NativeStorage.termChildren`), their classes' names and their texts; two
  * constructor objects by their classes' names, then field by field, a field
  * that is a term by this order, a vector by its length then element by
  * element, an index by its value, a name by its text, any other value by its
  * own fields or its text. A hash code is never read: it is an identity and
  * differs from one run to the next (`ConstructorIdentity`). Zero exactly on
  * two terms of one content, which are one object when both are interned, for
  * every value whose text (the last resort) shows its content.
  *
  * Stack safe: it walks a list of pending pairs, the first difference deciding.
  */
object ContentComparison:

  /** Negative when `left` comes first, zero on one content, positive otherwise.
    */
  def compare(left: Any, right: Any): Int = compared(List((left, right)))

  /** The order as an `Ordering`, for sorting terms. */
  val ordering: Ordering[Any] = (left: Any, right: Any) => compare(left, right)

  @scala.annotation.tailrec
  private def compared(pending: List[(Any, Any)]): Int = pending match
    case Nil                   => 0
    case (left, right) :: rest =>
      step(left, right) match
        case Left(0)        => compared(rest)
        case Left(decision) => decision
        case Right(more)    => compared(more ++ rest)

  private def step(left: Any, right: Any): Either[Int, List[(Any, Any)]] =
    (left, right) match
      case (first: AnyRef, second: AnyRef) if first eq second => Left(0)
      case (first: NativeStorage, second: NativeStorage)      =>
        if first.precedes(second) then Left(-1)
        else if second.precedes(first) then Left(1)
        else
          Right(
            List(
              (first.comparedConstructor, second.comparedConstructor),
              (first.comparedTerms.toVector, second.comparedTerms.toVector),
              (first.getClass.getName, second.getClass.getName),
              // Two storages of different encodings that `precedes` leaves unordered: by the native data their text shows.
              (first.toString, second.toString)
            )
          )
      case (_: NativeStorage, _)                                     => Left(-1)
      case (_, _: NativeStorage)                                     => Left(1)
      case (first: InternedConstructor, second: InternedConstructor) =>
        if first.getClass ne second.getClass then
          Left(first.getClass.getName.compareTo(second.getClass.getName))
        else Right(fieldPairs(first, second))
      case (_: InternedConstructor, _)           => Left(-1)
      case (_, _: InternedConstructor)           => Left(1)
      case (first: Vector[?], second: Vector[?]) =>
        if first.size != second.size then
          Left(Integer.compare(first.size, second.size))
        else Right(first.zip(second).toList)
      case (first: Int, second: Int)   => Left(Integer.compare(first, second))
      case (first: Long, second: Long) =>
        Left(java.lang.Long.compare(first, second))
      case (first: String, second: String)   => Left(first.compareTo(second))
      case (first: Product, second: Product) =>
        if first.getClass ne second.getClass then
          Left(first.getClass.getName.compareTo(second.getClass.getName))
        // Singleton cases of one enum may share a class and have no field.
        else
          Right(
            (first.productPrefix, second.productPrefix) :: fieldPairs(
              first,
              second
            )
          )
      case _ => Left(left.toString.compareTo(right.toString))

  private def fieldPairs(first: Product, second: Product): List[(Any, Any)] =
    (0 until first.productArity).toList.map(index =>
      (first.productElement(index), second.productElement(index))
    )
