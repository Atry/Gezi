package gezi.strategies

import gezi.ir.Code
import gezi.ir
import gezi.ir.Hole
import gezi.ir.Pattern
import gezi.ir.{Configured, NativeSpecializer}

/** A fold state of a module of a normality degree: each module's states are
  * its own (`NormalityModule`).
  */
trait FoldState

/** A term as the modules of a normality degree read it
  * (`lambda_jit_baseline_term_order`, A TERM): a term of the IR, an instruction
  * a leaf; a lemma side's pattern, whose metavariables
  * are opaque leaves; a hole of a resolved body, an opaque leaf; and, in a
  * layer the extraction builds over its child entries, a child as the leaf of
  * its fold state.
  */
enum OrderTerm[C <: NativeSpecializer & Singleton]:

  /** An instruction of the IR. */
  case Name(instruction: Configured[C])

  /** A metavariable of a lemma side's pattern. */
  case Metavariable[C <: NativeSpecializer & Singleton](index: Int) extends OrderTerm[C]

  /** A hole of a resolved body that no argument filled. */
  case Bound[C <: NativeSpecializer & Singleton](hole: Hole) extends OrderTerm[C]

  /** A child of a layer, read through its fold state at the module, and
    * whether the child's spelling is λf. f as the refinement runs it
    * (`ModuleCost.identityContract`), which no fold state keeps and the
    * reading of a code's curried specialization choice needs
    * (`TermReading.identityContract`).
    */
  case Folded[C <: NativeSpecializer & Singleton](state: FoldState, identityContract: Boolean) extends OrderTerm[C]

  /** A child of a layer that no module prices: a parallel's criterion, or a
    * thunk's filling its code reads only in a criterion or not at all
    * (`ModuleCostModel`, ONE READING
    * OF A LAYER FOR ALL THE MODULES), with its reading at the module
    * (`NormalityModule.reading`) and not its state, so that a module reads
    * what a parent may read of an unpriced child and never its cost
    * (`gezi.extraction.CostModel`, THE CONTRACT). A module whose parents read nothing beyond the
    * rank reads it as an opaque leaf.
    */
  case Unpriced[C <: NativeSpecializer & Singleton](reading: ModuleReading) extends OrderTerm[C]

  /** An application. */
  case Apply(function: OrderTerm[C], argument: OrderTerm[C])

  /** The parallel of a value and a criterion; `specializationRange` when it
    * is the range `F (A ∥ D) ∥ R` of a specialization choice's typed member
    * that the dispatch recognizer accepts (`TermReading.typedMember`), which
    * the refinement turns into a fallback point on the native's own output
    * (`specialization_attraction` counts no unfiltered left there).
    */
  case Parallel(left: OrderTerm[C], right: OrderTerm[C], specializationRange: Boolean)

  /** The choice of the members: of a term, the members of the IR choice's
    * right `+` spine (`ChoiceSpine`), a right side that is a name ending the
    * spine, so that a chain reads as the member list it was before the
    * choice became binary; of a layer over e-graph children, its two sides.
    */
  case Choice(members: Vector[OrderTerm[C]])

  /** A lambda chain: its code, its holes in lambda order and the fillings of
    * its other slots in slot order.
    */
  case Thunk(code: Code, holes: Vector[Hole], fillings: Vector[OrderTerm[C]])

  /** A child of the stored layer of an instruction the index does not define,
    * which the Prolog baseline wrote out in full and no reading looks into:
    * it is no instruction and no layer a reading recognizes. No module folds one.
    */
  case Unfolded(instruction: Configured[C])

/** The conversions into order terms. */
object OrderTerm:

  /** An order term is a node a cost model reads, no term of the IR: a layer over order terms is an ordinary layer,
    * though the leaves `Name` and `Unfolded` hold terms of the configuration.
    */
  given [C <: NativeSpecializer & Singleton]: gezi.ir.NotTerm[OrderTerm[C]] = gezi.ir.NotTerm.granted

  /** The instruction as an order term: an instruction of the names, or an opaque
    * one, a `Name`; any other instruction its layer over the order terms of its
    * parts.
    */
  def of[C <: NativeSpecializer & Singleton](instruction: Configured[C], names: Set[Configured[C]])(using C): OrderTerm[C] =
    if names.contains(instruction) then Name(instruction) else layerOf(instruction, names)

  /** The order term of the instruction's layer, though the instruction be one of the
    * names, its parts read by `of`; an opaque instruction a `Name`.
    */
  def layerOf[C <: NativeSpecializer & Singleton](instruction: Configured[C], names: Set[Configured[C]])(using C): OrderTerm[C] =
    if instruction.opaque then Name(instruction)
    else
      instruction.layer match
        case ir.Apply(function, argument)     => Apply(of(function, names), of(argument, names))
        case ir.Parallel(left, right)         => Parallel(of(left, names), of(right, names), specializationRange = false)
        case ir.Choice(_, _) =>
          val members = gezi.ir.ChoiceSpine.members[Configured[C]](
            instruction,
            current =>
              if !Configured.same(current, instruction) && names.contains(current) then None
              else
                current.layer match
                  case ir.Choice(left, right) => Some((left, right))
                  case _                      => None
          )
          Choice(members.map(of(_, names)))
        case ir.Thunk(code, holes, fillings)  => Thunk(code, holes, fillings.map(of(_, names)))
        case other => throw IllegalStateException(s"$other carries a noinline leaf, no layer an order term reads")

  /** The lemma side's pattern as an order term. A lambda pattern is read as
    * the thunk pattern it is; a closure pattern, which an encoding of a
    * lemma does not give, throws `IllegalArgumentException`.
    */
  def of[C <: NativeSpecializer & Singleton](pattern: Pattern[C]): OrderTerm[C] = pattern match
    case Pattern.Metavariable(index)          => Metavariable[C](index)
    case Pattern.InstructionReference(instruction) => Name(instruction)
    case Pattern.Apply(function, argument)    => Apply(of(function), of(argument))
    case Pattern.Parallel(left, right)        => Parallel(of(left), of(right), specializationRange = false)
    case Pattern.Choice(_, _) => Choice(Pattern.choiceMembers(pattern).map(of))
    case Pattern.Thunk(code, holes, fillings) => Thunk(code, holes, fillings.map(of))
    case Pattern.Closure(index) =>
      throw IllegalArgumentException(s"the closure pattern of the metavariable $index is no lemma side's pattern")

/** Why a module could not read a term or a configuration
  * (`term_order_error(Reason)`).
  */
enum TermOrderErrorReason:

  /** A code's slot beyond the assignment of its thunk. */
  case SlotOutOfRange(slot: Int, assignment: Vector[OrderTerm[?]])

  /** A name no module has. */
  case NotAModule(name: String)

  /** A module named twice in one configuration. */
  case ModuleTwice(name: String)

  /** A module an extraction may not use: its cost does not meet the
    * extraction's contract (`NormalityModule.meetsExtractionContract`).
    */
  case NotForExtraction(name: String)

  /** A term the module does not read: a fold state of another module, or a
    * child of a stored layer.
    */
  case NotATerm(term: OrderTerm[?])

/** A term or a configuration a module could not read. */
final case class TermOrderError(reason: TermOrderErrorReason)
    extends RuntimeException(s"term order error: $reason")
