package gezi.rewritetrace

import gezi.ir.BindingNormalForm
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Instruction
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.Thunk

/** The spelling a trace replays in:
  * every thunk with holes respelled over placeholders
  * (`BindingNormalForm.respelled`), a function of its code, its holes and the
  * number of its fillings. A derivation passes through thunks of other
  * spellings (a lemma's side as stated, the thunk a β step leaves, a residual
  * the e-graph holds unspelled), joined to their spellings by respelling
  * equations; in this spelling those steps are identities and the trace has
  * no command for them, so that no command writes a thunk the front end
  * cannot read back (`TraceText.readBack`) and the replay computes every
  * step's term: the IR is not part of the trace. The
  * writer (`gezi.proofs.RewriteTrace`, through `Conversions`) and the
  * player (`Trace.replayed`) both take their spelling from here.
  *
  * It is not the front end's spelling of the term's readback, in two ways a
  * placeholder hides: (a) a filling that is a lambda at the body of a chain
  * of lambdas, which the front end continues the chain through; (b) equal
  * fillings, which the front end makes one slot. A term the front end made
  * is its own spelling, so a trace's start is the front end's program
  * (`ReplaySpellingLawTest`). A thunk with no hole is left as it is: reading
  * it as its body is a β step, not a spelling (`RewriteTrace`'s plan joins
  * the β rule's step that leaves one to the body equation's step that reads
  * it).
  *
  * Its own recursions are trampolines, as are those of
  * `BindingNormalForm.respelled`, which it calls.
  */
/** The replay's spellings computed so far: a memo of pure functions of their
  * keys, threaded as a value through a computation that spells many terms
  * sharing their subterms, such as the flattening of a proof
  * (`gezi.proofs.RewriteTrace`):
  * the spelling of each term met (`ReplaySpelling.term`), and the respelling
  * and the filling positions (`ReplaySpelling.fillingPositions`) of each
  * code, holes and number of fillings met. Emptying it changes the cost
  * only. Spelling a term costs its layers not yet spelled, each a thunk's
  * respelling the first time its code, holes and number of fillings are met.
  */
final case class Spellings(
    terms: Map[Instruction, Instruction],
    respellings: Map[(Code, Vector[Hole], Int), Option[(Code, Vector[Hole], Vector[Instruction])]],
    fillings: Map[(Code, Vector[Hole], Int), Option[Vector[Vector[Vector[PositionSegment]]]]]
):

  /** The term in the replay's spelling (`ReplaySpelling.term`), with the
    * spellings it computed added.
    */
  def term(instruction: Instruction): (Instruction, Spellings) = ReplaySpelling.spelled(instruction, this).result

  /** `ReplaySpelling.fillingPositions` of the thunk's code, holes and number
    * of fillings, with the result added.
    */
  def fillingPositions(code: Code, holes: Vector[Hole], fillingCount: Int): (Option[Vector[Vector[Vector[PositionSegment]]]], Spellings) =
    fillings.get((code, holes, fillingCount)) match
      case Some(known) => (known, this)
      case None =>
        val computed = ReplaySpelling.fillingPositions(code, holes, fillingCount)
        (computed, copy(fillings = fillings.updated((code, holes, fillingCount), computed)))

  /** The respelling of a thunk of the code and holes over that many
    * placeholders (`BindingNormalForm.respelled`), with the result added.
    */
  def respelling(code: Code, holes: Vector[Hole], fillingCount: Int): (Option[(Code, Vector[Hole], Vector[Instruction])], Spellings) =
    respellings.get((code, holes, fillingCount)) match
      case Some(known) => (known, this)
      case None =>
        val computed = ReplaySpelling.respelling(code, holes, fillingCount)
        (computed, copy(respellings = respellings.updated((code, holes, fillingCount), computed)))

object Spellings:
  val empty: Spellings = Spellings(Map.empty, Map.empty, Map.empty)

object ReplaySpelling:

  /** The term in the replay's spelling. A trampoline: a term is as deep as a
    * program.
    */
  def term(instruction: Instruction): Instruction = Spellings.empty.term(instruction)._1

  /** The spelling of the term and the spellings with those it computed: a
    * term already spelled is looked up, an opaque one is its own spelling,
    * and any other is its layer over its children's spellings, a thunk's
    * respelled.
    */
  private[rewritetrace] def spelled(instruction: Instruction, known: Spellings): TailRec[(Instruction, Spellings)] =
    known.terms.get(instruction) match
      case Some(spelling)                => done((spelling, known))
      case None if instruction.opaque    => done((instruction, known))
      case None =>
        val layer = instruction.layered
        traversedKnown(layer.children, known)((child, current) => tailcall(spelled(child, current))).map((children, after) =>
          val (spelling, afterLayer) = layer match
            case Thunk(code, holes, _) =>
              after.respelling(code, holes, children.size) match
                case (None, afterRespelling) => (Instruction.Thunk(code, holes, children), afterRespelling)
                case (Some((spelledCode, spelledHoles, overPlaceholders)), afterRespelling) =>
                  val values = BindingNormalForm.placeholders(children.size).zip(children).toMap
                  (Instruction.Thunk(spelledCode, spelledHoles, overPlaceholders.map(substituted(_, values))), afterRespelling)
            case other => (Instruction(other.over(children)), after)
          (spelling, afterLayer.copy(terms = afterLayer.terms.updated(instruction, spelling)))
        )

  /** The results of the step on each item, in order, the spellings threaded
    * through, as a trampoline.
    */
  private def traversedKnown[Item, Result](items: Vector[Item], known: Spellings)(
      step: (Item, Spellings) => TailRec[(Result, Spellings)]
  ): TailRec[(Vector[Result], Spellings)] =
    def from(index: Int, results: Vector[Result], current: Spellings): TailRec[(Vector[Result], Spellings)] =
      if index >= items.size then done((results, current))
      else tailcall(step(items(index), current)).flatMap((result, after) => from(index + 1, results :+ result, after))
    from(0, Vector.empty, known)

  /** The front end's spelling of a thunk of the code with holes, its fillings
    * placeholders; none for a thunk with no hole or one that is its own
    * spelling.
    */
  private[rewritetrace] def respelling(code: Code, holes: Vector[Hole], fillingCount: Int): Option[(Code, Vector[Hole], Vector[Instruction])] =
    if holes.isEmpty then None else BindingNormalForm.respelled(code, holes, fillingCount)

  /** The positions of a thunk's fillings in its replay spelling, a function
    * of the code, the holes and the number of fillings: none for a thunk that
    * is its own spelling (`term` leaves it as it is, and the position of a
    * subterm under a filling is the filling's position followed by the
    * subterm's position in the filling); else, for each filling in order, the
    * positions of its placeholder in the spelling of the thunk over
    * placeholders, each followed, in the spelling of the thunk with its
    * fillings, by the subterm's position in the filling's spelling
    * (`positions`). Costs the code's size and the number of fillings.
    */
  def fillingPositions(code: Code, holes: Vector[Hole], fillingCount: Int): Option[Vector[Vector[Vector[PositionSegment]]]] =
    respelling(code, holes, fillingCount).map((spelledCode, spelledHoles, overPlaceholders) =>
      val over = Instruction.Thunk(spelledCode, spelledHoles, overPlaceholders)
      BindingNormalForm.placeholders(fillingCount).map(placeholder =>
        placesOf(over, placeholder).flatMap(found => positions(over, found))
      )
    )

  /** A term over placeholders with each placeholder its value. A
    * trampoline: a respelled filling is as deep as the code it comes from,
    * and a code is as deep as a program's body.
    */
  private def substituted(term: Instruction, values: Map[Instruction, Instruction]): Instruction =
    substitutedStep(term, values).result

  private def substitutedStep(term: Instruction, values: Map[Instruction, Instruction]): TailRec[Instruction] =
    values.get(term) match
      case Some(value)         => done(value)
      case None if term.opaque => done(term)
      case None =>
        val layer = term.layered
        traversed(layer.children)(child => tailcall(substitutedStep(child, values))).map(children => Instruction(layer.over(children)))

  /** The equation with both sides in the replay's spelling (`side`). */
  def statement(statement: Statement): Statement = Statement(side(statement.left), side(statement.right))

  /** A side in the replay's spelling: each thunk layer spelled as `term`
    * spells it, a variable standing for a term already so spelled. A stored
    * instruction is a closed term of the front end or the graph, already so
    * spelled.
    */
  def side(term: StatementTerm): StatementTerm = sideStep(term).result

  private def sideStep(term: StatementTerm): TailRec[StatementTerm] = term match
    case StatementTerm.Variable(_) | StatementTerm.Stored(_) => done(term)
    case StatementTerm.Layered(Thunk(code, holes, fillings)) =>
      traversed(fillings)(filling => tailcall(sideStep(filling))).flatMap(spelledFillings =>
        respelling(code, holes, spelledFillings.size) match
          case None => done(StatementTerm.Layered(Thunk(code, holes, spelledFillings)))
          case Some((spelledCode, spelledHoles, overPlaceholders)) =>
            val values = BindingNormalForm.placeholders(spelledFillings.size).zip(spelledFillings).toMap
            traversed(overPlaceholders)(filling => tailcall(sideOver(filling, values))).map(spelled =>
              StatementTerm.Layered(Thunk(spelledCode, spelledHoles, spelled))
            )
      )
    case StatementTerm.Layered(layer) =>
      traversed(layer.children)(child => tailcall(sideStep(child))).map(children => StatementTerm.Layered(layer.over(children)))

  /** A term over placeholders as a side, each placeholder its side. A
    * trampoline, as `substituted` is.
    */
  private def sideOver(term: Instruction, values: Map[Instruction, StatementTerm]): TailRec[StatementTerm] =
    values.get(term) match
      case Some(value)         => done(value)
      case None if term.opaque => done(StatementTerm.Stored(term))
      case None =>
        val layer = term.layered
        traversed(layer.children)(child => tailcall(sideOver(child, values))).map(children => StatementTerm.Layered(layer.over(children)))

  /** The positions in the term's spelling (`term`) of the subterm at the
    * position of the term: none when the spelling drops it (a filling the
    * code does not read), several when the spelling copies it. A
    * trampoline, the positions found built by appending to the prefix
    * walked: a position is as long as a term is deep.
    */
  def positions(instruction: Instruction, position: Vector[PositionSegment]): Vector[Vector[PositionSegment]] =
    positionsFound(instruction, position, Vector.empty).result

  /** `positions` of the subterm at `prefix`, each found position prefixed. */
  private def positionsFound(
      instruction: Instruction,
      position: Vector[PositionSegment],
      prefix: Vector[PositionSegment]
  ): TailRec[Vector[Vector[PositionSegment]]] =
    position.headOption match
      case None => done(Vector(prefix))
      case Some(segment) =>
        val rest = position.tail
        def descended: TailRec[Vector[Vector[PositionSegment]]] =
          tailcall(positionsFound(Positions.subterm(instruction, Vector(segment)), rest, prefix :+ segment))
        instruction.layered match
          case Thunk(code, holes, fillings) =>
            fillingPositions(code, holes, fillings.size) match
              case None => descended
              case Some(placed) =>
                segment match
                  case PositionSegment.Filling(place) =>
                    traversed(placed(place))(found => tailcall(positionsFound(fillings(place), rest, prefix ++ found)))
                      .map(_.flatten)
                  case other => throw IllegalArgumentException(s"a thunk has no subterm $other")
          case _ => descended

  /** The positions of the leaf in a term over opaque leaves. A trampoline,
    * as `substituted` is, each position built by appending to the path
    * walked.
    */
  private def placesOf(term: Instruction, leaf: Instruction): Vector[Vector[PositionSegment]] =
    def found(at: Instruction, path: Vector[PositionSegment]): TailRec[Vector[Vector[PositionSegment]]] =
      if at == leaf then done(Vector(path))
      else if at.opaque then done(Vector.empty)
      else
        val layer = at.layered
        traversed(layer.children.zip(Positions.roles(layer)))((child, role) => tailcall(found(child, path :+ role))).map(_.flatten)
    found(term, Vector.empty).result

  /** The results of the step on each item, in order, as a trampoline. */
  private def traversed[Item, Result](items: Vector[Item])(step: Item => TailRec[Result]): TailRec[Vector[Result]] =
    def from(index: Int, results: Vector[Result]): TailRec[Vector[Result]] =
      if index >= items.size then done(results)
      else tailcall(step(items(index))).flatMap(result => from(index + 1, results :+ result))
    from(0, Vector.empty)
