package com.yang_bo.gezi.ir

import com.yang_bo.gezi.ir.Interned.Interned

/** An instruction inside a pattern, whose node must be in the class. The
  * pattern's own constructor, kept beside the instruction's layers: matching it
  * asks for that instruction's node, which is not matching its layers part by
  * part, so merging the two would change the programs the orientations compile
  * to.
  */
final case class InstructionReference[
    C <: NativeSpecializer & Singleton
] private (instruction: Configured[C])
    extends InternedConstructor:
  override def toString: String = ConstructorIdentity.shown(this)

/** The operations of a pattern, as extensions in the companion of
  * [[InstructionReference]], a constructor of [[PatternLayer]], which puts them
  * in the implicit scope of `Pattern`.
  */
object InstructionReference:

  /** The canonical InstructionReference: a layer that no construction site
    * converts is interned when it is made.
    */
  def apply[C <: NativeSpecializer & Singleton](
      instruction: Configured[C]
  ): InstructionReference[C] =
    Interned.canonicalLayer(new InstructionReference(instruction))

  extension [C <: NativeSpecializer & Singleton](pattern: Pattern[C])
    /** The patterns one layer below, in child order: function then argument,
      * left then right, fillings in order.
      */
    def children: Vector[Pattern[C]] = pattern.layer match
      case Apply(function, argument) => Vector(function, argument)
      case Parallel(left, right)     => Vector(left, right)
      case Choice(left, right)       => Vector(left, right)
      case Thunk(_, _, fillings)     => fillings
      case Metavariable(_) | ClosureMetavariable(_) | InstructionReference(_) =>
        Vector.empty

    /** The code of a pattern that is a thunk (`Pattern.Thunk`). Throws
      * `IllegalStateException` for any other pattern.
      */
    def code: Code = thunkLayer(pattern).code

    /** The holes of a pattern that is a thunk; throws for any other. */
    def holes: Vector[Hole] = thunkLayer(pattern).holes

    /** The fillings of a pattern that is a thunk; throws for any other. */
    def fillings: Vector[Pattern[C]] = thunkLayer(pattern).fillings

  private def thunkLayer[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C]
  ): Thunk[Pattern[C]] = pattern.layer match
    case thunk @ Thunk(_, _, _) => thunk
    case other => throw IllegalStateException(s"the pattern $other is no thunk")

/** One layer of a pattern of a lemma's side: a metavariable; the eta-shaped
  * lambda `\x. M x`, read as the class of M holding a closure state; an
  * instruction, whose node must be in the class; or one layer of the IR over
  * patterns.
  */
type PatternLayer[C <: NativeSpecializer & Singleton, +Child] =
  Metavariable | ClosureMetavariable | InstructionReference[C] | Apply[Child] |
    Parallel[Child] | Choice[Child] | Thunk[Child]

/** A pattern of a lemma's side: an interned term ([[Interned]]) of
  * `PatternLayer`.
  */
type Pattern[C <: NativeSpecializer & Singleton] =
  Interned[[Child] =>> PatternLayer[C, Child]]

/** The constructions and the parts of patterns, each made through the pool. */
object Pattern:

  private def of[C <: NativeSpecializer & Singleton](
      layer: PatternLayer[C, Pattern[C]]
  ): Pattern[C] =
    Interned[[Child] =>> PatternLayer[C, Child]](layer)

  /** A pattern whose layer is a thunk, as its callers name it: the type does
    * not hold the shape, `Pattern.Thunk(...)` matches it.
    */
  type Thunk[C <: NativeSpecializer & Singleton] = Pattern[C]

  /** A metavariable, by its index. */
  object Metavariable:
    def apply[C <: NativeSpecializer & Singleton](index: Int): Pattern[C] = of(
      com.yang_bo.gezi.ir.Metavariable(index)
    )

    def unapply[C <: NativeSpecializer & Singleton](
        pattern: Pattern[C]
    ): Option[Int] = pattern.layer match
      case com.yang_bo.gezi.ir.Metavariable(index) => Some(index)
      case _                           => None

  /** The eta-shaped lambda over the metavariable of the index. */
  object Closure:
    def apply[C <: NativeSpecializer & Singleton](index: Int): Pattern[C] = of(
      ClosureMetavariable(index)
    )

    def unapply[C <: NativeSpecializer & Singleton](
        pattern: Pattern[C]
    ): Option[Int] = pattern.layer match
      case ClosureMetavariable(index) => Some(index)
      case _                          => None

  /** An instruction whose node must be in the class. */
  object InstructionReference:
    def apply[C <: NativeSpecializer & Singleton](
        instruction: Configured[C]
    ): Pattern[C] = of(com.yang_bo.gezi.ir.InstructionReference(instruction))

    def unapply[C <: NativeSpecializer & Singleton](
        pattern: Pattern[C]
    ): Option[Configured[C]] = pattern.layer match
      case com.yang_bo.gezi.ir.InstructionReference(instruction) => Some(instruction)
      case _                                         => None

  /** An application of patterns. */
  object Apply:
    def apply[C <: NativeSpecializer & Singleton](
        function: Pattern[C],
        argument: Pattern[C]
    ): Pattern[C] = of(com.yang_bo.gezi.ir.Apply(function, argument))

    def unapply[C <: NativeSpecializer & Singleton](
        pattern: Pattern[C]
    ): Option[(Pattern[C], Pattern[C])] = pattern.layer match
      case com.yang_bo.gezi.ir.Apply(function, argument) => Some((function, argument))
      case _                                 => None

  /** A parallel of patterns. */
  object Parallel:
    def apply[C <: NativeSpecializer & Singleton](
        left: Pattern[C],
        right: Pattern[C]
    ): Pattern[C] = of(com.yang_bo.gezi.ir.Parallel(left, right))

    def unapply[C <: NativeSpecializer & Singleton](
        pattern: Pattern[C]
    ): Option[(Pattern[C], Pattern[C])] = pattern.layer match
      case com.yang_bo.gezi.ir.Parallel(left, right) => Some((left, right))
      case _                             => None

  /** A binary choice of patterns. */
  object Choice:
    def apply[C <: NativeSpecializer & Singleton](
        left: Pattern[C],
        right: Pattern[C]
    ): Pattern[C] = of(com.yang_bo.gezi.ir.Choice(left, right))

    def unapply[C <: NativeSpecializer & Singleton](
        pattern: Pattern[C]
    ): Option[(Pattern[C], Pattern[C])] = pattern.layer match
      case com.yang_bo.gezi.ir.Choice(left, right) => Some((left, right))
      case _                           => None

  /** A thunk over patterns. */
  object Thunk:
    def apply[C <: NativeSpecializer & Singleton](
        code: Code,
        holes: Vector[Hole],
        fillings: Vector[Pattern[C]]
    ): Pattern[C] =
      of(com.yang_bo.gezi.ir.Thunk(code, holes, fillings))

    def unapply[C <: NativeSpecializer & Singleton](
        pattern: Pattern[C]
    ): Option[(Code, Vector[Hole], Vector[Pattern[C]])] = pattern.layer match
      case com.yang_bo.gezi.ir.Thunk(code, holes, fillings) => Some((code, holes, fillings))
      case _                                    => None

  /** The members of a pattern's right `+` spine ([[ChoiceSpine.members]]). */
  def choiceMembers[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C]
  ): Vector[Pattern[C]] =
    ChoiceSpine.members[Pattern[C]](pattern, Choice.unapply)

  /** The members nested to the right ([[ChoiceSpine.nested]]); none throws. */
  def nestedChoice[C <: NativeSpecializer & Singleton](
      members: Vector[Pattern[C]]
  ): Pattern[C] =
    ChoiceSpine.nested[Pattern[C]](members, Choice(_, _))

/** Which side of a lemma an orientation matches: the left (forward) or the
  * right (backward). A union an instance makes puts the lemma's left side
  * first.
  */
enum Direction:
  case Forward
  case Backward
