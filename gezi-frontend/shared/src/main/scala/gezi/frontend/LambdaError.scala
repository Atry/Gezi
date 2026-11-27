package gezi.frontend

import gezi.ir.Hole

/** A malformed object term, the Prolog front end's `lambda_error(Reason)`.
  * The message names the reason's kind only: a reason may hold a term
  * thousands of levels deep, whose derived `toString` recurses per level.
  */
final case class LambdaError(reason: LambdaErrorReason)
    extends RuntimeException:
  override def getMessage: String = s"lambda_error(${reason.productPrefix})"

/** Why an object term is malformed. */
enum LambdaErrorReason:

  // TODO: UnknownDefine stood here. Its purpose: the error of a HOAS library name the name-to-instruction map did not
  // hold. It named library terms by the HOAS case Term.Define, a free variable (blacklisted) and a table of library
  // files deleted when the library became files reached by paths. Its replacement reads the
  // library terms it needs as members of a fixture file under tests/ by projection, so no name can be unknown.
  // The deleted code: git show 2908bffd5:lambda_jit/frontend/src/main/scala/lambdajit/frontend/LambdaError.scala.

  /** A HOAS variable used outside the abstraction that made it: its level,
    * and the number of abstractions around the place it was used.
    */
  case VariableOutsideItsAbstraction(level: Int, depth: Int)

  /** A term converted to the IR mentions a variable no binder of it binds. */
  case NotClosed(term: DeBruijnTermOf[Any])

  /** A code reads a slot its thunk does not have. */
  case SlotOutOfRange(slot: Int, slotCount: Int)

  /** `Defunctionalization.fillingPosition` asked for a slot that is a hole.
    */
  case SlotIsAHole(slot: Int, holes: Vector[Hole])

  /** The fillings of a thunk are fewer or more than its non-hole slots: its
    * holes and the number of fillings given.
    */
  case FillingsNotMatched(holes: Vector[Hole], fillingCount: Int)
