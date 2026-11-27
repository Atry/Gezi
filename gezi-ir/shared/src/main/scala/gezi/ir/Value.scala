package gezi.ir

import gezi.ir.Interned.Interned

/** One layer of a reader's value: a layer of the IR or an extension of the readers' own (a neutral value, a suspension,
  * the JIT's sharing cell).
  */
type ValueLayer[+Child] = IrLayer[Child] | ValueExtension[Child]

/** A run-time value of a reader of the configuration `C`: an interned term over the IR's layers and the readers'
  * extensions, every term interned. A term of the IR of `C` is a value as it is (`Value.of`), with no conversion.
  * Invariant in `C`, with no upper bound, as [[Configured]] is, so that the values of two configurations are never
  * mixed: a value is built only by the typed constructions below, which take children of one configuration and build
  * through its native specializer where the result can be a term of the IR.
  */
opaque type Value[C <: NativeSpecializer & Singleton] = Interned[ValueLayer]

/** A value that holds no neutral value: it may hold a suspension, and then it is no term of the IR yet. */
opaque type Closed[C <: NativeSpecializer & Singleton] = Interned[ValueLayer]

/** A value that holds a neutral value at least: the only values a sharing cell holds. */
opaque type Open[C <: NativeSpecializer & Singleton] = Interned[ValueLayer]

object Value:

  /** The term as a value: the same object (injection). */
  def of[C <: NativeSpecializer & Singleton](term: Configured[C])(using C): Value[C] = term.representation

  /** The value as a closed one, when it holds no neutral value: one field read. */
  def closed[C <: NativeSpecializer & Singleton](value: Value[C])(using C): Option[Closed[C]] =
    Option.when(ConstructorIdentity.closed(value))(value)

  /** The value as an open one, when it holds a neutral value: one field read. */
  def open[C <: NativeSpecializer & Singleton](value: Value[C])(using C): Option[Open[C]] =
    Option.when(!ConstructorIdentity.closed(value))(value)

  /** Whether the two values of one configuration are one value. */
  def same[C <: NativeSpecializer & Singleton](left: Value[C], right: Value[C])(using C): Boolean = left eq right

  extension [C <: NativeSpecializer & Singleton](value: Value[C])

    /** The value's one layer, its children values of the same configuration. */
    def layer: ValueLayer[Value[C]] = (value: Interned[ValueLayer]).layer

    /** The object the value is, for the registered readers that interpret it: the same object. */
    def representation: Interned[ValueLayer] = value

  /** The spine of a value ([[gezi.ir.Spine]]): its head and its arguments, read from the flat copy an application
    * stores.
    */
  object Spine:
    def of[C <: NativeSpecializer & Singleton](value: Value[C]): (Value[C], Vector[Value[C]]) =
      gezi.ir.Spine.of[ValueLayer](value)

    def unapplySeq[C <: NativeSpecializer & Singleton](value: Value[C]): Option[(Value[C], Seq[Value[C]])] =
      gezi.ir.Spine.unapplySeq[ValueLayer](value)

  /** The application value built through the specializer in scope, and its parts. */
  object Apply:
    def apply[C <: NativeSpecializer & Singleton](function: Value[C], argument: Value[C])(using specializer: C): Value[C] =
      application(specializer)(function, argument)

    def unapply[C <: NativeSpecializer & Singleton](value: Value[C])(using C): Option[(Value[C], Value[C])] = value.layer match
      case gezi.ir.Apply(function, argument) => Some((function, argument))
      case _                                 => None

  /** The parallel value built through the specializer in scope, and its sides. */
  object Parallel:
    def apply[C <: NativeSpecializer & Singleton](left: Value[C], right: Value[C])(using specializer: C): Value[C] =
      parallel(specializer)(left, right)

    def unapply[C <: NativeSpecializer & Singleton](value: Value[C])(using C): Option[(Value[C], Value[C])] = value.layer match
      case gezi.ir.Parallel(left, right) => Some((left, right))
      case _                             => None

  /** The choice value built through the specializer in scope, and its sides. */
  object Choice:
    def apply[C <: NativeSpecializer & Singleton](left: Value[C], right: Value[C])(using specializer: C): Value[C] =
      choice(specializer)(left, right)

    def unapply[C <: NativeSpecializer & Singleton](value: Value[C])(using C): Option[(Value[C], Value[C])] = value.layer match
      case gezi.ir.Choice(left, right) => Some((left, right))
      case _                           => None

  /** The thunk value, a lambda chain with at least one hole, built through the specializer in scope, and its parts. A
    * code whose holes are all filled is no thunk value but a suspension (the readers' extension), so holes that are
    * none are a defect of the caller.
    */
  object Thunk:
    def apply[C <: NativeSpecializer & Singleton](code: Code, holes: Vector[Hole], fillings: Vector[Value[C]])(using
        specializer: C
    ): Value[C] =
      thunk(specializer)(
        code,
        NonEmptyHoles.of(holes).getOrElse(throw IllegalArgumentException(s"a thunk value of no hole, a suspension: $code")),
        fillings
      )

    def unapply[C <: NativeSpecializer & Singleton](value: Value[C])(using C): Option[(Code, Vector[Hole], Vector[Value[C]])] =
      value.layer match
        case gezi.ir.Thunk(code, holes, fillings) => Some((code, holes, fillings))
        case _                                    => None

  /** The value whose layer this is, a thunk or an extension's layer read off a value of the configuration (a reader's
    * head): the same object, since an interned value is its layer. Sound because no code outside this module can make
    * a thunk layer over values (`NotTerm`), so every such layer came from a value.
    */
  def ofHeadLayer[C <: NativeSpecializer & Singleton](layer: Thunk[Value[C]] | ValueExtension[Value[C]])(using C): Value[C] =
    Interned.ofCanonicalLayer[ValueLayer](layer)

  /** The value of an extension's layer over values of the configuration: interned through the pool, so that an
    * extension equal by content is one object.
    */
  def extension[C <: NativeSpecializer & Singleton](layer: ValueExtension[Value[C]])(using C): Value[C] =
    Interned[ValueLayer](layer)

  /** The application: a term of the IR, built through the specializer, when both sides are; otherwise the layer as a
    * value.
    */
  def application[C <: NativeSpecializer & Singleton](specializer: C)(function: Value[C], argument: Value[C]): Value[C] =
    given C = specializer
    (Closed.configured(function), Closed.configured(argument)) match
      case (Some(left), Some(right)) => of(specializer.application(left, right))
      case _                         => Interned[ValueLayer](gezi.ir.Apply.ofTerms(function, argument))

  /** The binary choice, as `application` builds. */
  def choice[C <: NativeSpecializer & Singleton](specializer: C)(left: Value[C], right: Value[C]): Value[C] =
    given C = specializer
    (Closed.configured(left), Closed.configured(right)) match
      case (Some(leftTerm), Some(rightTerm)) => of(specializer.choice(leftTerm, rightTerm))
      case _                                 => Interned[ValueLayer](gezi.ir.Choice.ofTerms(left, right))

  /** The thunk with at least one hole, as `application` builds. */
  def thunk[C <: NativeSpecializer & Singleton](specializer: C)(
      code: Code,
      holes: NonEmptyHoles,
      fillings: Vector[Value[C]]
  ): Value[C] =
    given C = specializer
    val terms = fillings.flatMap(Closed.configured(_))
    if terms.size == fillings.size then of(specializer.thunk(code, holes, terms))
    else Interned[ValueLayer](gezi.ir.Thunk.ofTerms(code, holes.toVector, fillings))

  /** The thunk's layer, a reader's head: `thunk`'s value read as the layer it is. */
  def thunkLayer[C <: NativeSpecializer & Singleton](specializer: C)(
      code: Code,
      holes: NonEmptyHoles,
      fillings: Vector[Value[C]]
  ): Thunk[Value[C]] =
    // Registered conversion: `thunk` builds a thunk layer, of terms or of values, whose children are this
    // configuration's (https://github.com/Atry/private-overlay/issues/2261, section 8).
    thunk(specializer)(code, holes, fillings).layer.asInstanceOf[Thunk[Value[C]]]

  /** The parallel: specialized by the specializer when both sides are closed (a side holding a suspension included, as
    * a storage may hold one in a field kept as written), its storage the result when it is the unique spelling of one;
    * otherwise, a side being open, the layer as a value, which is the unique spelling of no storage, since a storage is
    * of a closed term.
    */
  def parallel[C <: NativeSpecializer & Singleton](specializer: C)(left: Value[C], right: Value[C]): Value[C] =
    given C = specializer
    (closed(left), closed(right)) match
      case (Some(leftClosed), Some(rightClosed)) => specializer.parallelOfClosed(leftClosed, rightClosed)
      case _                                     => parallelAsWritten(left, right)

  /** The parallel of two values as written, interned: only the specializer calls it, after finding that the parallel
    * is the unique spelling of no storage, and `parallel` above, for an open side.
    */
  private[ir] def parallelAsWritten[C <: NativeSpecializer & Singleton](left: Value[C], right: Value[C])(using C): Value[C] =
    Interned.parallelOfTerms[ValueLayer](left, right)

object Closed:

  /** The closed value as a value: the same object. */
  def value[C <: NativeSpecializer & Singleton](closed: Closed[C])(using C): Value[C] = closed

  /** The closed value as a term of the IR, when it holds no suspension either: one field read. */
  def configured[C <: NativeSpecializer & Singleton](value: Value[C])(using C): Option[Configured[C]] =
    Option.when(ConstructorIdentity.closed(value) && ConstructorIdentity.suspensionFree(value))(
      Configured.built[C](value.asInstanceOf[Instruction])
    )

  /** The term as a closed value: the same object. */
  def of[C <: NativeSpecializer & Singleton](term: Configured[C])(using C): Closed[C] = term.representation

  extension [C <: NativeSpecializer & Singleton](closed: Closed[C])

    /** The closed value's one layer. */
    def layer: ValueLayer[Value[C]] = (closed: Interned[ValueLayer]).layer

object Open:

  /** The open value as a value: the same object. */
  def value[C <: NativeSpecializer & Singleton](open: Open[C])(using C): Value[C] = open
