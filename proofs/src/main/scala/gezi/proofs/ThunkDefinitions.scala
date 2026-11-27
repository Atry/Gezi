package gezi.proofs

import gezi.ir.Code
import gezi.ir.CodeLayer
import gezi.ir.Hole
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Apply, Choice, Parallel, Slot, Thunk}

/** A constant of a thunk constant's defining term: the code and the holes of a
  * thunk constant are written as a first-order HOL term over these, not spelled
  * into its name. Lean's `Interpretation.signatureOf` reads them by the same
  * names.
  */
enum DefinitionConstant:
  case NumberZero
  case NumberSuccessor
  case CodeSlot
  case CodeApply
  case CodeChoice
  case CodeParallel
  case CodeThunk
  case CodesNil
  case CodesCons
  case HoleSlot
  case HoleIgnored
  case HolesNil
  case HolesCons
  case ThunkOf(arity: Int)

/** A subterm of a thunk constant's defining term, the unit the article stores
  * once and refers to after: a number in unary, a hole, the holes from one of a
  * list on, a code, the codes from one of a list on, or the whole defining term
  * `LambdaJit.Code.thunkOf C H` of a thunk constant with `arity` fillings.
  */
enum DefinitionPart:
  case NumberPart(value: Int)
  case HolePart(hole: Hole)
  case HolesPart(holes: Vector[Hole])
  case CodePart(code: Code)
  case CodesPart(codes: Vector[Code])
  case Defining(code: Code, holes: Vector[Hole], arity: Int)

/** The definitions of thunk constants: a thunk constant of an article is named
  * `LambdaJit.thunk.N`, N the order of its first occurrence in the article from
  * 0, and defined by `defineConst` as `LambdaJit.Code.thunkOf C H`, `C` its
  * code and `H` its holes; a statement numbers its own constants from 0 in the
  * same way. The functions here say how that term is built, one HOL layer at a
  * time, so that the article writer and the HOL terms of statements build the
  * same term.
  */
object ThunkDefinitions:

  /** The name of the thunk constant numbered `number`, its components. */
  def name(number: Int): Vector[String] =
    Vector("LambdaJit", "thunk", number.toString)

  /** The name of a constant of the defining term, its components. */
  def constantName(constant: DefinitionConstant): Vector[String] =
    constant match
      case DefinitionConstant.NumberZero =>
        Vector("LambdaJit", "Number", "zero")
      case DefinitionConstant.NumberSuccessor =>
        Vector("LambdaJit", "Number", "successor")
      case DefinitionConstant.CodeSlot   => Vector("LambdaJit", "Code", "slot")
      case DefinitionConstant.CodeApply  => Vector("LambdaJit", "Code", "apply")
      case DefinitionConstant.CodeChoice =>
        Vector("LambdaJit", "Code", "choice")
      case DefinitionConstant.CodeParallel =>
        Vector("LambdaJit", "Code", "parallel")
      case DefinitionConstant.CodeThunk => Vector("LambdaJit", "Code", "thunk")
      case DefinitionConstant.CodesNil  => Vector("LambdaJit", "Codes", "nil")
      case DefinitionConstant.CodesCons => Vector("LambdaJit", "Codes", "cons")
      case DefinitionConstant.HoleSlot  => Vector("LambdaJit", "Hole", "slot")
      case DefinitionConstant.HoleIgnored =>
        Vector("LambdaJit", "Hole", "ignored")
      case DefinitionConstant.HolesNil   => Vector("LambdaJit", "Holes", "nil")
      case DefinitionConstant.HolesCons  => Vector("LambdaJit", "Holes", "cons")
      case DefinitionConstant.ThunkOf(_) =>
        Vector("LambdaJit", "Code", "thunkOf")

  /** The type of a thunk constant with `arity` fillings, `term → … → term`. */
  def thunkType(arity: Int): HolType =
    (0 until arity).foldLeft[HolType](HolType.Term)((result, _) =>
      HolType.Function(HolType.Term, result)
    )

  private def function(arguments: Vector[HolType], result: HolType): HolType =
    arguments.foldRight(result)(HolType.Function(_, _))

  /** The type of a constant of the defining term: `thunkOf` takes a code and
    * holes to the type of a thunk constant with its arity.
    */
  def constantType(constant: DefinitionConstant): HolType = constant match
    case DefinitionConstant.NumberZero      => HolType.Number
    case DefinitionConstant.NumberSuccessor =>
      function(Vector(HolType.Number), HolType.Number)
    case DefinitionConstant.CodeSlot =>
      function(Vector(HolType.Number), HolType.Code)
    case DefinitionConstant.CodeApply | DefinitionConstant.CodeChoice |
        DefinitionConstant.CodeParallel =>
      function(Vector(HolType.Code, HolType.Code), HolType.Code)
    case DefinitionConstant.CodeThunk =>
      function(Vector(HolType.Code, HolType.Holes, HolType.Codes), HolType.Code)
    case DefinitionConstant.CodesNil  => HolType.Codes
    case DefinitionConstant.CodesCons =>
      function(Vector(HolType.Code, HolType.Codes), HolType.Codes)
    case DefinitionConstant.HoleSlot =>
      function(Vector(HolType.Number), HolType.Hole)
    case DefinitionConstant.HoleIgnored => HolType.Hole
    case DefinitionConstant.HolesNil    => HolType.Holes
    case DefinitionConstant.HolesCons   =>
      function(Vector(HolType.Hole, HolType.Holes), HolType.Holes)
    case DefinitionConstant.ThunkOf(arity) =>
      function(Vector(HolType.Code, HolType.Holes), thunkType(arity))

  /** One HOL layer of a part: its head constant and the parts it is applied to,
    * in order.
    */
  def layer(
      part: DefinitionPart
  ): (DefinitionConstant, Vector[DefinitionPart]) = part match
    case DefinitionPart.NumberPart(0) =>
      (DefinitionConstant.NumberZero, Vector.empty)
    case DefinitionPart.NumberPart(value) =>
      (
        DefinitionConstant.NumberSuccessor,
        Vector(DefinitionPart.NumberPart(value - 1))
      )
    case DefinitionPart.HolePart(Hole.Bound(slot)) =>
      (DefinitionConstant.HoleSlot, Vector(DefinitionPart.NumberPart(slot)))
    case DefinitionPart.HolePart(Hole.Ignored) =>
      (DefinitionConstant.HoleIgnored, Vector.empty)
    case DefinitionPart.HolesPart(holes) =>
      holes.headOption match
        case None        => (DefinitionConstant.HolesNil, Vector.empty)
        case Some(first) =>
          (
            DefinitionConstant.HolesCons,
            Vector(
              DefinitionPart.HolePart(first),
              DefinitionPart.HolesPart(holes.tail)
            )
          )
    case DefinitionPart.CodesPart(codes) =>
      codes.headOption match
        case None        => (DefinitionConstant.CodesNil, Vector.empty)
        case Some(first) =>
          (
            DefinitionConstant.CodesCons,
            Vector(
              DefinitionPart.CodePart(first),
              DefinitionPart.CodesPart(codes.tail)
            )
          )
    case DefinitionPart.CodePart(code) =>
      code.layer match
        case Slot(index) =>
          (
            DefinitionConstant.CodeSlot,
            Vector(DefinitionPart.NumberPart(index))
          )
        case Apply(left, right) =>
          (
            DefinitionConstant.CodeApply,
            Vector(
              DefinitionPart.CodePart(left),
              DefinitionPart.CodePart(right)
            )
          )
        case Choice(left, right) =>
          (
            DefinitionConstant.CodeChoice,
            Vector(
              DefinitionPart.CodePart(left),
              DefinitionPart.CodePart(right)
            )
          )
        case Parallel(left, right) =>
          (
            DefinitionConstant.CodeParallel,
            Vector(
              DefinitionPart.CodePart(left),
              DefinitionPart.CodePart(right)
            )
          )
        case Thunk(inner, holes, fillings) =>
          (
            DefinitionConstant.CodeThunk,
            Vector(
              DefinitionPart.CodePart(inner),
              DefinitionPart.HolesPart(holes),
              DefinitionPart.CodesPart(fillings)
            )
          )
    case DefinitionPart.Defining(code, holes, arity) =>
      (
        DefinitionConstant.ThunkOf(arity),
        Vector(DefinitionPart.CodePart(code), DefinitionPart.HolesPart(holes))
      )

  /** The HOL term of a part, every type in it: the terms of statements and of
    * the judge's manifests, which stand alone. Each part is built once and its
    * term object reused wherever the part recurs, so that the term is a graph
    * as large as the parts' (a subcode the code shares, every number of a unary
    * chain): it stands for the same tree, which a reader that walks it as a
    * tree writes as before, while `HolTermText.sharedText` writes it at the
    * graph's size. Built as a tree, a defining term of one of the judge's
    * points wrote up to 34,028,221 characters even with its types shared, its
    * slots' unary numbers written out at every occurrence (measured
    * 2026-11-22). A trampoline: a code is as deep as a body, and a number is
    * unary.
    */
  def term(part: DefinitionPart, typeTerm: HolType => HolTypeTerm): HolTerm =
    termBuilt(part, typeTerm, Map.empty).result._1

  private def termBuilt(
      part: DefinitionPart,
      typeTerm: HolType => HolTypeTerm,
      built: Map[DefinitionPart, HolTerm]
  ): TailRec[(HolTerm, Map[DefinitionPart, HolTerm])] =
    built.get(part) match
      case Some(found) => done((found, built))
      case None        =>
        val (constant, arguments) = layer(part)
        val head: HolTerm = HolTerm.Constant(
          constantName(constant),
          typeTerm(constantType(constant))
        )
        def applied(
            index: Int,
            function: HolTerm,
            current: Map[DefinitionPart, HolTerm]
        ): TailRec[(HolTerm, Map[DefinitionPart, HolTerm])] =
          if index >= arguments.size then
            done((function, current.updated(part, function)))
          else
            tailcall(termBuilt(arguments(index), typeTerm, current)).flatMap(
              (argument, after) =>
                applied(
                  index + 1,
                  HolTerm.Application(function, argument),
                  after
                )
            )
        applied(0, head, built)

  /** The defining term of the thunk constant of the code and the holes,
    * `LambdaJit.Code.thunkOf C H` at the type of a constant with `arity`
    * fillings.
    */
  def definingTerm(
      code: Code,
      holes: Vector[Hole],
      arity: Int,
      typeTerm: HolType => HolTypeTerm
  ): HolTerm =
    term(DefinitionPart.Defining(code, holes, arity), typeTerm)

  /** A thunk of a code and holes with the number of its constant, numbered in
    * order of first occurrence.
    */
  final case class Numbering(
      entries: Vector[(Code, Vector[Hole])],
      numbers: Map[(Code, Vector[Hole]), Int]
  ):
    /** The number of the thunk, and the numbering with it, a new thunk taking
      * the next number.
      */
    def numbered(code: Code, holes: Vector[Hole]): (Int, Numbering) =
      numbers.get((code, holes)) match
        case Some(number) => (number, this)
        case None         =>
          val number = entries.size
          (
            number,
            Numbering(
              entries :+ (code, holes),
              numbers.updated((code, holes), number)
            )
          )

  object Numbering:
    val empty: Numbering = Numbering(Vector.empty, Map.empty)

  /** HOL terms with the thunks their constants stand for: the constant
    * `LambdaJit.thunk.N` is the thunk of entry N of `definitions`.
    */
  final case class NamedTerms(
      terms: Vector[HolTerm],
      definitions: Vector[(Code, Vector[Hole])]
  )
