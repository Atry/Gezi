package gezi.lemmaencoding.baseline

import gezi.frontend.Defunctionalization
import gezi.ir.Code
import gezi.ir.Instruction
import gezi.ir.Hole
import gezi.ir.Pattern
import gezi.lemmaencoding.EncodedLemma
import gezi.lemmaencoding.LemmaEncoding
import gezi.standardlibrary.LemmaSides
import gezi.standardlibrary.StandardLibraryIndex

/** A pattern as the Prolog front end writes it: a term of the IR with
  * metavariable leaves and the instructions of names as references.
  */
enum LemmaPattern:
  case Metavariable(index: Int)
  case Reference(instruction: Instruction)
  case Apply(function: LemmaPattern, argument: LemmaPattern)
  case Parallel(left: LemmaPattern, right: LemmaPattern)
  case Choice(left: LemmaPattern, right: LemmaPattern)
  case Thunk(code: Code, holes: Vector[Hole], fillings: Vector[LemmaPattern])

  /** The patterns one layer below, in order. */
  def children: Vector[LemmaPattern] = this match
    case Metavariable(_) | Reference(_) => Vector.empty
    case Apply(function, argument)      => Vector(function, argument)
    case Parallel(left, right)          => Vector(left, right)
    case Choice(left, right)            => Vector(left, right)
    case Thunk(_, _, fillings)          => fillings

/** The baseline's encoding of a lemma: its two sides read as patterns, the
  * port of `gezi/prolog/gezi/lemma_patterns.pl`.
  *
  * A lemma side `\x1 ... \xn. B` is the thunk layer whose holes are x1 to
  * xn, read as the code B over the holes' metavariables, Index 0 the
  * outermost binder, and over the fillings, which are closed instructions
  * and so patterns themselves. The metavariables of a lemma are the binders
  * both its sides' instructions open with (`metavariables`), whether a side
  * was written as a name or as its term: when one side's chain of binders is
  * longer, the longer side's other binders are an object lambda, that side's
  * pattern being a thunk pattern. Every closed subterm of a side, the
  * fillings of its thunk and the whole side of a lemma with no metavariable,
  * is a reference to its instruction, its layer not read. A reference
  * matches a class that holds a node filed under its instruction; the
  * orientation compiler files the roots of reference sides in the initial
  * graph (`OrientationCompilation.patternInstructions`), so a node a lemma
  * writes with that layer is the filed node. It reads the lemma's sides only
  * and names no lemma.
  */
object BaselineLemmaEncoding extends LemmaEncoding:

  /** The lemma's patterns of the framework, its closed subterms references. */
  def encoded(index: StandardLibraryIndex, sides: LemmaSides): EncodedLemma =
    val (arity, left, right) = lemmaPatterns(sides)
    EncodedLemma(sides.lemma, arity, subrepoPattern(left), subrepoPattern(right))

  /** The number of the lemma's metavariables and the patterns of its two
    * sides, every closed subterm a reference.
    */
  def lemmaPatterns(sides: LemmaSides): (Int, LemmaPattern, LemmaPattern) =
    val arity = metavariables(sides)
    (arity, sidePattern(sides.left, arity), sidePattern(sides.right, arity))

  /** The number of the lemma's metavariables: the holes both its sides'
    * instructions open with, a side that is no thunk opening with none. The
    * knowledge base gives a lemma its two closed terms only and no number of
    * metavariables, which means nothing of a lemma; the
    * count is the matcher's choice, which changes the subterms matched and
    * never the lemma's meaning. Since the count is read off the side
    * instructions, the eta-equal spellings `f` and `\w. f w` are different
    * encodings the author chooses.
    */
  def metavariables(sides: LemmaSides): Int = binders(sides.left) min binders(sides.right)

  private def binders(side: Instruction): Int = side match
    case Instruction.Thunk(_, holes, _) => holes.size
    case _                              => 0

  /** What a slot of a side holds while its code is read: a pattern, or the
    * placeholder of a binder of the object lambda.
    */
  private enum SlotValue:
    case Value(pattern: LemmaPattern)
    case LambdaHole

  /** The pattern of a side whose first `arity` binders are the lemma's
    * metavariables: its code with each slot replaced by the metavariable or
    * the filling that reads it; with binders left over, the thunk pattern of
    * the object lambda they make, whose fillings are the other slots' values
    * in slot order. A side of no metavariable is closed, the pattern of its
    * instruction.
    */
  private def sidePattern(side: Instruction, arity: Int): LemmaPattern = side match
    case _ if arity == 0 => LemmaPattern.Reference(side)
    case Instruction.Thunk(code, holes, fillings) =>
      val (metavariableHoles, lambdaHoles) = holes.splitAt(arity)
      val holeValues =
        metavariableHoles.indices.map(index => SlotValue.Value(LemmaPattern.Metavariable(index))) ++
          lambdaHoles.map(_ => SlotValue.LambdaHole)
      val environment = Defunctionalization.slotValues(
        holes,
        holeValues.toVector,
        fillings.map(filling => SlotValue.Value(LemmaPattern.Reference(filling)))
      )
      if lambdaHoles.isEmpty then
        codePattern(
          code,
          environment.map {
            case SlotValue.Value(pattern) => pattern
            case SlotValue.LambdaHole =>
              throw IllegalStateException("a lambda hole with no binder left over")
          }
        )
      else
        LemmaPattern.Thunk(
          code,
          lambdaHoles,
          environment.collect { case SlotValue.Value(pattern) => pattern }
        )
    case other => throw IllegalArgumentException(s"a side that is no thunk has no $arity metavariables: $other")

  /** The code with its slots replaced; an inner thunk's fillings are slot
    * references of the enclosing code.
    */
  private def codePattern(code: Code, environment: Vector[LemmaPattern]): LemmaPattern =
    code match
      case Code.Slot(index) => environment(index)
      case Code.Apply(function, argument) =>
        LemmaPattern.Apply(codePattern(function, environment), codePattern(argument, environment))
      case Code.Parallel(left, right) =>
        LemmaPattern.Parallel(codePattern(left, environment), codePattern(right, environment))
      case Code.Choice(left, right) =>
        LemmaPattern.Choice(codePattern(left, environment), codePattern(right, environment))
      case Code.Thunk(inner, holes, fillings) =>
        LemmaPattern.Thunk(inner, holes, fillings.map(codePattern(_, environment)))

  /** The metavariable of an eta-shaped thunk pattern `\x. M x`, M the
    * metavariable: a lambda pattern.
    */
  def lambdaPattern(pattern: LemmaPattern): Option[Int] = pattern match
    case LemmaPattern.Thunk(
          Code.Apply(Code.Slot(function), Code.Slot(hole)),
          Vector(Hole.Bound(boundHole)),
          Vector(LemmaPattern.Metavariable(index))
        ) if boundHole == hole && function != hole =>
      Some(index)
    case _ => None

  /** The metavariables that occur in the pattern, each once, in the order
    * met.
    */
  def mentions(pattern: LemmaPattern): Vector[Int] = (pattern match
    case LemmaPattern.Metavariable(index) => Vector(index)
    case other                           => other.children.flatMap(mentions)
  ).distinct

  /** The pattern has a rigid symbol: an instruction, a thunk, a choice, a
    * parallel, or an application with a rigid side. An arrangement of metavariables alone matches every application.
    */
  def rigid(pattern: LemmaPattern): Boolean = pattern match
    case LemmaPattern.Metavariable(_)     => false
    case LemmaPattern.Apply(function, argument) => rigid(function) || rigid(argument)
    case _                                => true

  /** The pattern of the framework, its codes interned. A lambda pattern
    * stays a thunk pattern: the orientation compiler reads it as a closure.
    */
  def subrepoPattern(pattern: LemmaPattern): Pattern =
    pattern match
      case LemmaPattern.Metavariable(index) => Pattern.Metavariable(index)
      case LemmaPattern.Reference(instruction)   => Pattern.InstructionReference(instruction)
      case LemmaPattern.Apply(function, argument) =>
        Pattern.Apply(subrepoPattern(function), subrepoPattern(argument))
      case LemmaPattern.Parallel(left, right) =>
        Pattern.Parallel(subrepoPattern(left), subrepoPattern(right))
      case LemmaPattern.Choice(left, right) =>
        Pattern.Choice(subrepoPattern(left), subrepoPattern(right))
      case LemmaPattern.Thunk(code, holes, fillings) =>
        Pattern.Thunk(code, holes, fillings.map(subrepoPattern))
