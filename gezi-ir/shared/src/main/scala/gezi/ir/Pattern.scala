package gezi.ir

import gezi.ir.Interned.Interned

/** An instruction inside a pattern, whose node must be in the class. The
  * pattern's own constructor, kept beside the instruction's layers: matching it asks
  * for that instruction's node, which is not matching its layers part by
  * part, so merging the two would change the programs the orientations
  * compile to.
  */
final case class InstructionReference(instruction: Instruction):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

/** The operations of a pattern, as extensions in the companion of
  * [[InstructionReference]], a constructor of [[PatternLayer]], which puts them
  * in the implicit scope of `Pattern`.
  */
object InstructionReference:

  extension (pattern: Pattern)
    /** The patterns one layer below, in child order: function then argument,
      * left then right, fillings in order.
      */
    def children: Vector[Pattern] = pattern.layer match
      case Apply(function, argument) => Vector(function, argument)
      case Parallel(left, right)     => Vector(left, right)
      case Choice(left, right)       => Vector(left, right)
      case Thunk(_, _, fillings)     => fillings
      case Metavariable(_) | ClosureMetavariable(_) | InstructionReference(_) => Vector.empty

    /** The code of a pattern that is a thunk (`Pattern.Thunk`). Throws
      * `IllegalStateException` for any other pattern.
      */
    def code: Code = thunkLayer(pattern).code

    /** The holes of a pattern that is a thunk; throws for any other. */
    def holes: Vector[Hole] = thunkLayer(pattern).holes

    /** The fillings of a pattern that is a thunk; throws for any other. */
    def fillings: Vector[Pattern] = thunkLayer(pattern).fillings

  private def thunkLayer(pattern: Pattern): Thunk[Pattern] = pattern.layer match
    case thunk @ Thunk(_, _, _) => thunk
    case other                  => throw IllegalStateException(s"the pattern $other is no thunk")

/** One layer of a pattern of a lemma's side: a metavariable; the eta-shaped
  * lambda `\x. M x`, read as the class of M holding a closure state; an
  * instruction, whose node must be in the class; or one layer of the IR over
  * patterns.
  */
type PatternLayer[+Child] =
  Metavariable | ClosureMetavariable | InstructionReference | Apply[Child] | Parallel[Child] | Choice[Child] |
    Thunk[Child]

/** A pattern of a lemma's side: an interned term ([[Interned]]) of
  * `PatternLayer`.
  */
type Pattern = Interned[PatternLayer]

/** The constructions and the parts of patterns, each made through the pool. */
object Pattern:

  private def of(layer: PatternLayer[Pattern]): Pattern = Interned[PatternLayer](layer)

  /** A pattern whose layer is a thunk, as its callers name it: the type does
    * not hold the shape, `Pattern.Thunk(...)` matches it.
    */
  type Thunk = Pattern

  /** A metavariable, by its index. */
  object Metavariable:
    def apply(index: Int): Pattern = of(gezi.ir.Metavariable(index))

    def unapply(pattern: Pattern): Option[Int] = pattern.layer match
      case gezi.ir.Metavariable(index) => Some(index)
      case _                                => None

  /** The eta-shaped lambda over the metavariable of the index. */
  object Closure:
    def apply(index: Int): Pattern = of(ClosureMetavariable(index))

    def unapply(pattern: Pattern): Option[Int] = pattern.layer match
      case ClosureMetavariable(index) => Some(index)
      case _                          => None

  /** An instruction whose node must be in the class. */
  object InstructionReference:
    def apply(instruction: Instruction): Pattern = of(gezi.ir.InstructionReference(instruction))

    def unapply(pattern: Pattern): Option[Instruction] = pattern.layer match
      case gezi.ir.InstructionReference(instruction) => Some(instruction)
      case _                                              => None

  /** An application of patterns. */
  object Apply:
    def apply(function: Pattern, argument: Pattern): Pattern = of(gezi.ir.Apply(function, argument))

    def unapply(pattern: Pattern): Option[(Pattern, Pattern)] = pattern.layer match
      case gezi.ir.Apply(function, argument) => Some((function, argument))
      case _                                     => None

  /** A parallel of patterns. */
  object Parallel:
    def apply(left: Pattern, right: Pattern): Pattern = of(gezi.ir.Parallel(left, right))

    def unapply(pattern: Pattern): Option[(Pattern, Pattern)] = pattern.layer match
      case gezi.ir.Parallel(left, right) => Some((left, right))
      case _                                 => None

  /** A binary choice of patterns. */
  object Choice:
    def apply(left: Pattern, right: Pattern): Pattern = of(gezi.ir.Choice(left, right))

    def unapply(pattern: Pattern): Option[(Pattern, Pattern)] = pattern.layer match
      case gezi.ir.Choice(left, right) => Some((left, right))
      case _                               => None

  /** A thunk over patterns. */
  object Thunk:
    def apply(code: Code, holes: Vector[Hole], fillings: Vector[Pattern]): Pattern =
      of(gezi.ir.Thunk(code, holes, fillings))

    def unapply(pattern: Pattern): Option[(Code, Vector[Hole], Vector[Pattern])] = pattern.layer match
      case gezi.ir.Thunk(code, holes, fillings) => Some((code, holes, fillings))
      case _                                        => None

  /** The members of a pattern's right `+` spine ([[ChoiceSpine.members]]). */
  def choiceMembers(pattern: Pattern): Vector[Pattern] =
    ChoiceSpine.members[Pattern](pattern, Choice.unapply)

  /** The members nested to the right ([[ChoiceSpine.nested]]); none throws. */
  def nestedChoice(members: Vector[Pattern]): Pattern =
    ChoiceSpine.nested[Pattern](members, Choice(_, _))

/** Which side of a lemma an orientation matches: the left (forward) or the
  * right (backward). A union an instance makes puts the lemma's left side
  * first.
  */
enum Direction:
  case Forward
  case Backward
