package gezi.ematching.indexing

import gezi.orientation.Orientation
import gezi.ematching.Building
import gezi.ematching.OrientationPlan
import gezi.ematching.Program
import gezi.ematching.Seed
import gezi.ematching.SeedKey
import gezi.ematching.SeedKind
import gezi.ir.CodeLayer
import gezi.ir.Code
import gezi.ir.Reachability
import gezi.ir.Pattern
import gezi.ir.Spine
import gezi.ir.{Apply, Choice, Parallel, Slot, Thunk}
import gezi.ir.{Configured, NativeSpecializer}

/** The compiler of orientations and codes into a program: the inverted index of
  * seeds, filed by kind and key, and the buildings of the added sides, the
  * shared subterms and the code bodies.
  */
object Indexing:

  /** The program of the orientations, numbered from 0 in order, and of the
    * codes (`Reachability.codesUnder` gives the codes a computation over some
    * terms may meet). Within a kind and a key the seeds are in the order the
    * Prolog baseline asserts its seed clauses: by orientation, then by position
    * in pre-order.
    */
  def program[C <: NativeSpecializer & Singleton](
      orientations: Vector[Orientation[C]],
      codes: Set[Code]
  )(using C): Program[C] =
    require(
      orientations.zipWithIndex.forall((orientation, position) =>
        orientation.index == position
      ),
      s"the orientations are numbered from 0 in order: ${orientations.map(_.index)}"
    )
    val seeds = orientations
      .flatMap(Seeding.seeds)
      .foldLeft(Map.empty[(SeedKind, SeedKey[C]), Vector[Seed[C]]]) {
        case (table, (kindAndKey, seed)) =>
          table.updated(
            kindAndKey,
            table.getOrElse(kindAndKey, Vector.empty) :+ seed
          )
      }
    Program(
      seeds = seeds,
      orientations = orientations.map(plan),
      codes = codes
        .map(identifier => identifier -> codeBuilding[C](identifier.layer))
        .toMap
    )

  /** The codes a saturation of the orientations from the roots may meet: those
    * under the roots, the instructions of the orientations' patterns and the
    * codes of their thunk patterns.
    */
  def codesMet[C <: NativeSpecializer & Singleton](
      orientations: Vector[Orientation[C]],
      roots: Iterable[Configured[C]]
  )(using C): Set[Code] =
    val patterns = orientations.flatMap(orientation =>
      (orientation.matched +: orientation.added +: orientation.shared)
    )
    val parts = patterns.flatMap(patternParts)
    Reachability.codesUnder(
      roots ++ parts.collect { case Left(instruction) => instruction },
      parts.collect { case Right(code) => code }
    )

  /** The instructions (`Left`) and the codes (`Right`) a pattern names. */
  private def patternParts[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C]
  )(using C): Vector[Either[Configured[C], Code]] =
    val own: Vector[Either[Configured[C], Code]] = pattern match
      case Pattern.InstructionReference(instruction) =>
        Vector(Left(instruction))
      case Pattern.Thunk(code, _, _) => Vector(Right(code))
      case _                         => Vector.empty
    own ++ pattern.children.flatMap(patternParts)

  /** What saturation needs of the orientation to apply an instance. */
  def plan[C <: NativeSpecializer & Singleton](
      orientation: Orientation[C]
  ): OrientationPlan[C] = OrientationPlan(
    lemma = orientation.lemma,
    direction = orientation.direction,
    added = building(orientation.added, orientation.functions),
    essential = orientation.essential,
    shared = orientation.shared.map(building(_, Vector.empty))
  )

  /** The building of an added side or a shared subterm (the baseline's
    * `added_built/6`): an application is read by the β rule when its function's
    * spine starts with one of the function metavariables, or when its function
    * is a thunk pattern, a lambda the side writes. A shared subterm is built
    * with no function metavariable, so that only its applications of thunk
    * patterns are read.
    */
  def building[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C],
      functions: Vector[Int]
  ): Building[C] =
    pattern match
      case Pattern.Metavariable(index)               => Building.Value[C](index)
      case Pattern.Closure(index)                    => Building.Value[C](index)
      case Pattern.InstructionReference(instruction) =>
        Building.InstructionNode(instruction)
      case Pattern.Apply(function, argument) =>
        Building.Apply(
          building(function, functions),
          building(argument, functions),
          read = spineMetavariable(function).exists(functions.contains) ||
            isThunk(function)
        )
      case Pattern.Parallel(left, right) =>
        Building.Parallel(building(left, functions), building(right, functions))
      case Pattern.Choice(left, right) =>
        Building.Choice(building(left, functions), building(right, functions))
      case Pattern.Thunk(code, holes, fillings) =>
        Building.Thunk(code, holes, fillings.map(building(_, functions)))

  /** The metavariable at the head of the pattern's spine (the baseline's
    * `pattern_spine_metavariable/2`).
    */
  def spineMetavariable[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C]
  ): Option[Int] = Spine.of(pattern)._1 match
    case Pattern.Metavariable(index) => Some(index)
    case Pattern.Closure(index)      => Some(index)
    case _                           => None

  private def isThunk[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C]
  ): Boolean = pattern match
    case Pattern.Thunk(_, _, _) => true
    case _                      => false

  /** The building of a code's body (the baseline's `code_layer_read/5`): one
    * layer over the buildings of its subcodes, which are referred to, not
    * copied, and read again wherever they occur; a slot is the value the caller
    * gives at its index. An application whose function the code writes as a
    * thunk, a redex such as a let, is read by the β rule, as an added side's
    * application of a thunk pattern is (`building`); one whose function is a
    * slot is not, so a self-application is never unfolded.
    */
  def codeBuilding[C <: NativeSpecializer & Singleton](
      code: CodeLayer[Code]
  ): Building[C] = code match
    case Slot(index)               => Building.Value[C](index)
    case Apply(function, argument) =>
      Building.Apply(
        Building.CodeBody[C](function),
        Building.CodeBody[C](argument),
        read = function.layer match
          case Thunk(_, _, _) => true
          case _              => false
      )
    case Parallel(left, right) =>
      Building.Parallel(Building.CodeBody[C](left), Building.CodeBody[C](right))
    case Choice(left, right) =>
      Building.Choice(Building.CodeBody[C](left), Building.CodeBody[C](right))
    case Thunk(inner, holes, fillings) =>
      Building.Thunk(inner, holes, fillings.map(Building.CodeBody[C](_)))
