package gezi.rewritetrace

import gezi.ir.BindingNormalForm
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.NativeStorage
import gezi.ir.Opaque
import gezi.ir.StorageAccess
import gezi.ir.UriNode
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Apply, Choice, Parallel, Slot, Thunk}
import gezi.ir.{Configured, NativeSpecializer}

/** The spelling a trace replays in: every thunk with holes respelled over
  * placeholders (`BindingNormalForm.respelled`), a function of its code, its
  * holes and the number of its fillings. A derivation passes through thunks of
  * other spellings (a lemma's side as stated, the thunk a β step leaves, a
  * residual the e-graph holds unspelled), joined to their spellings by
  * respelling equations; in this spelling those steps are identities and the
  * trace has no command for them, so that no command writes a thunk the front
  * end cannot read back (`TraceText.readBack`) and the replay computes every
  * step's term: the IR is not part of the trace. The writer
  * (`gezi.proofs.RewriteTrace`, through `Conversions`) and the player
  * (`Trace.replayed`) both take their spelling from here.
  *
  * It is not the front end's spelling of the term's readback, in two ways a
  * placeholder hides: (a) a filling that is a lambda at the body of a chain of
  * lambdas, which the front end continues the chain through; (b) equal
  * fillings, which the front end makes one slot. A term the front end made is
  * its own spelling, so a trace's start is the front end's program
  * (`ReplaySpellingLawTest`). A thunk with no hole is left as it is: reading it
  * as its body is a β step, not a spelling (`RewriteTrace`'s plan joins the β
  * rule's step that leaves one to the body equation's step that reads it).
  *
  * Its own recursions are trampolines, as are those of
  * `BindingNormalForm.respelled`, which it calls.
  */
/** The replay's spellings computed so far: a memo of pure functions of their
  * keys, threaded as a value through a computation that spells many terms
  * sharing their subterms, such as the flattening of a proof
  * (`gezi.proofs.RewriteTrace`): the spelling of each term met
  * (`ReplaySpelling.term`), and the respelling and the filling positions
  * (`ReplaySpelling.fillingPositions`) of each code, holes and number of
  * fillings met. Emptying it changes the cost only. Spelling a term costs its
  * layers not yet spelled, each a thunk's respelling the first time its code,
  * holes and number of fillings are met.
  */
final case class Spellings[C <: NativeSpecializer & Singleton](
    terms: Map[Configured[C], Configured[C]],
    respellings: Map[(Code, Vector[Hole], Int), Option[
      (Code, Vector[Hole], Vector[Code])
    ]],
    fillings: Map[(Code, Vector[Hole], Int), Option[
      Vector[Vector[Vector[PositionSegment]]]
    ]]
):

  /** The term in the replay's spelling (`ReplaySpelling.term`), with the
    * spellings it computed added.
    */
  def term(term: Configured[C])(using C): (Configured[C], Spellings[C]) =
    ReplaySpelling.spelled(term, this).result

  /** `ReplaySpelling.fillingPositions` of the thunk's code, holes and number of
    * fillings, with the result added.
    */
  def fillingPositions(
      code: Code,
      holes: Vector[Hole],
      fillingCount: Int
  ): (Option[Vector[Vector[Vector[PositionSegment]]]], Spellings[C]) =
    fillings.get((code, holes, fillingCount)) match
      case Some(known) => (known, this)
      case None        =>
        val computed =
          ReplaySpelling.fillingPositions(code, holes, fillingCount)
        (
          computed,
          copy(fillings =
            fillings.updated((code, holes, fillingCount), computed)
          )
        )

  /** The respelling of a thunk of the code and holes over that many fillings
    * (`BindingNormalForm.respelled`), with the result added.
    */
  def respelling(
      code: Code,
      holes: Vector[Hole],
      fillingCount: Int
  ): (Option[(Code, Vector[Hole], Vector[Code])], Spellings[C]) =
    respellings.get((code, holes, fillingCount)) match
      case Some(known) => (known, this)
      case None        =>
        val computed = ReplaySpelling.respelling(code, holes, fillingCount)
        (
          computed,
          copy(respellings =
            respellings.updated((code, holes, fillingCount), computed)
          )
        )

object Spellings:
  def empty[C <: NativeSpecializer & Singleton]: Spellings[C] =
    Spellings(Map.empty, Map.empty, Map.empty)

object ReplaySpelling:

  /** The term in the replay's spelling. A trampoline: a term is as deep as a
    * program.
    */
  def term[C <: NativeSpecializer & Singleton](term: Configured[C])(using
      C
  ): Configured[C] = Spellings.empty[C].term(term)._1

  /** The spelling of the term and the spellings with those it computed: a term
    * already spelled is looked up, an opaque one and a storage are their own
    * spellings (a storage is a leaf of its term's layer, its view the spelling
    * its configuration builds), and any other is its layer over its children's
    * spellings built through the configuration, a thunk's respelled: the
    * respelling's fillings, codes over the slots of the thunk's fillings, read
    * at the children's spellings (`NativeSpecializer.instance`).
    */
  private[rewritetrace] def spelled[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      known: Spellings[C]
  )(using
      specializer: C
  ): TailRec[(Configured[C], Spellings[C])] =
    known.terms.get(term) match
      case Some(spelling) => done((spelling, known))
      case None           =>
        term.layer match
          case _: NativeStorage | UriNode(_) | Opaque(_) => done((term, known))
          case layer                                     =>
            val children = layer.children
            traversedKnown(children, known)((child, current) =>
              tailcall(spelled(child, current))
            ).map((spelledChildren, after) =>
              val (spelling, afterLayer) = layer match
                case Thunk(code, holes, _) =>
                  after.respelling(code, holes, spelledChildren.size) match
                    case (None, afterRespelling) =>
                      (
                        Positions.built(
                          Thunk(code, holes, children.indices.toVector),
                          spelledChildren
                        ),
                        afterRespelling
                      )
                    case (
                          Some((spelledCode, spelledHoles, overSlots)),
                          afterRespelling
                        ) =>
                      val fillings = overSlots.map(filling =>
                        specializer.instance(filling, spelledChildren)
                      )
                      (
                        Positions.built(
                          Thunk(
                            spelledCode,
                            spelledHoles,
                            fillings.indices.toVector
                          ),
                          fillings
                        ),
                        afterRespelling
                      )
                case Apply(_, _) =>
                  (Positions.built(Apply(0, 1), spelledChildren), after)
                case Parallel(_, _) =>
                  (Positions.built(Parallel(0, 1), spelledChildren), after)
                case Choice(_, _) =>
                  (Positions.built(Choice(0, 1), spelledChildren), after)
                case other =>
                  throw IllegalStateException(
                    s"no layer of a term spells $other"
                  )
              (
                spelling,
                afterLayer.copy(terms =
                  afterLayer.terms.updated(term, spelling)
                )
              )
            )

  /** The results of the step on each item, in order, the spellings threaded
    * through, as a trampoline.
    */
  private def traversedKnown[Item, Result, C <: NativeSpecializer & Singleton](
      items: Vector[Item],
      known: Spellings[C]
  )(
      step: (Item, Spellings[C]) => TailRec[(Result, Spellings[C])]
  ): TailRec[(Vector[Result], Spellings[C])] =
    def from(
        index: Int,
        results: Vector[Result],
        current: Spellings[C]
    ): TailRec[(Vector[Result], Spellings[C])] =
      if index >= items.size then done((results, current))
      else
        tailcall(step(items(index), current)).flatMap((result, after) =>
          from(index + 1, results :+ result, after)
        )
    from(0, Vector.empty, known)

  /** The front end's spelling of a thunk of the code with holes, its fillings
    * codes over the slots of the thunk's fillings; none for a thunk with no
    * hole or one that is its own spelling.
    */
  private[rewritetrace] def respelling(
      code: Code,
      holes: Vector[Hole],
      fillingCount: Int
  ): Option[(Code, Vector[Hole], Vector[Code])] =
    if holes.isEmpty then None
    else BindingNormalForm.respelled(code, holes, fillingCount)

  /** The positions of a thunk's fillings in its replay spelling, a function of
    * the code, the holes and the number of fillings: none for a thunk that is
    * its own spelling (`term` leaves it as it is, and the position of a subterm
    * under a filling is the filling's position followed by the subterm's
    * position in the filling); else, for each filling in order, the positions
    * of its slot in the spelling's fillings, each followed, in the spelling of
    * the thunk with its fillings, by the subterm's position in the filling's
    * spelling (`positions`). Costs the code's size and the number of fillings.
    */
  def fillingPositions(
      code: Code,
      holes: Vector[Hole],
      fillingCount: Int
  ): Option[Vector[Vector[Vector[PositionSegment]]]] =
    respelling(code, holes, fillingCount).map((_, _, overSlots) =>
      Vector.tabulate(fillingCount)(slot =>
        overSlots.zipWithIndex.flatMap((filling, place) =>
          slotPositions(filling, slot).map(PositionSegment.Filling(place) +: _)
        )
      )
    )

  /** The positions in the replay spelling of the instance of the code of the
    * slot's filling, outermost first in preorder: an inner thunk that is not
    * its own spelling passes on the positions of its fillings in its spelling,
    * as `positions` does. The recursion follows the code's own nesting.
    */
  private def slotPositions(
      code: Code,
      slot: Int
  ): Vector[Vector[PositionSegment]] = code.layer match
    case Slot(index) =>
      if index == slot then Vector(Vector.empty) else Vector.empty
    case Apply(function, argument) =>
      slotPositions(function, slot).map(PositionSegment.Function +: _) ++
        slotPositions(argument, slot).map(PositionSegment.Argument +: _)
    case Parallel(left, right) =>
      slotPositions(left, slot).map(PositionSegment.Left +: _) ++ slotPositions(
        right,
        slot
      ).map(PositionSegment.Right +: _)
    case Choice(left, right) =>
      slotPositions(left, slot).map(PositionSegment.Left +: _) ++ slotPositions(
        right,
        slot
      ).map(PositionSegment.Right +: _)
    case Thunk(inner, innerHoles, fillings) =>
      val placed = fillingPositions(inner, innerHoles, fillings.size)
      fillings.zipWithIndex.flatMap((filling, place) =>
        val prefixes = placed.fold(
          Vector(Vector(PositionSegment.Filling(place): PositionSegment))
        )(_(place))
        prefixes.flatMap(prefix =>
          slotPositions(filling, slot).map(prefix ++ _)
        )
      )

  /** The equation with both sides in the replay's spelling (`side`). */
  def statement[Term](statement: Statement[Term]): Statement[Term] =
    Statement(side(statement.left), side(statement.right))

  /** A side in the replay's spelling: each thunk layer spelled as `term` spells
    * it, a variable standing for a term already so spelled. A stored term is a
    * closed term of the front end or the graph, already so spelled.
    */
  def side[Term](term: StatementTerm[Term]): StatementTerm[Term] = sideStep(
    term
  ).result

  private def sideStep[Term](
      term: StatementTerm[Term]
  ): TailRec[StatementTerm[Term]] = term match
    case StatementTerm.Variable(_) | StatementTerm.Stored(_) => done(term)
    case StatementTerm.Layered(Thunk(code, holes, fillings)) =>
      traversed(fillings)(filling => tailcall(sideStep(filling))).map(
        spelledFillings =>
          respelling(code, holes, spelledFillings.size) match
            case None =>
              StatementTerm.Layered(Thunk(code, holes, spelledFillings))
            case Some((spelledCode, spelledHoles, overSlots)) =>
              StatementTerm.Layered(
                Thunk(
                  spelledCode,
                  spelledHoles,
                  overSlots.map(filling =>
                    BindingNormalForm.fillingMapped(filling, spelledFillings)(
                      StatementTerm.Layered(_)
                    )
                  )
                )
              )
      )
    case StatementTerm.Layered(layer) =>
      traversed(layer.children)(child => tailcall(sideStep(child))).map(
        children => StatementTerm.Layered(layer.over(children))
      )

  /** The positions in the term's spelling (`term`) of the subterm at the
    * position of the term: none when the spelling drops it (a filling the code
    * does not read), several when the spelling copies it. A trampoline, the
    * positions found built by appending to the prefix walked: a position is as
    * long as a term is deep.
    */
  def positions[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      position: Vector[PositionSegment]
  )(using C, StorageAccess): Vector[Vector[PositionSegment]] =
    positionsFound(term, position, Vector.empty).result

  /** `positions` of the subterm at `prefix`, each found position prefixed. */
  private def positionsFound[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      position: Vector[PositionSegment],
      prefix: Vector[PositionSegment]
  )(using C, StorageAccess): TailRec[Vector[Vector[PositionSegment]]] =
    position.headOption match
      case None          => done(Vector(prefix))
      case Some(segment) =>
        val rest = position.tail
        def descended: TailRec[Vector[Vector[PositionSegment]]] =
          tailcall(
            positionsFound(
              Positions.childAt(term, segment),
              rest,
              prefix :+ segment
            )
          )
        term.layer match
          case Thunk(code, holes, fillings) =>
            fillingPositions(code, holes, fillings.size) match
              case None         => descended
              case Some(placed) =>
                segment match
                  case PositionSegment.Filling(place) =>
                    traversed(placed(place))(found =>
                      tailcall(
                        positionsFound(fillings(place), rest, prefix ++ found)
                      )
                    )
                      .map(_.flatten)
                  case other =>
                    throw IllegalArgumentException(
                      s"a thunk has no subterm $other"
                    )
          case _ => descended

  /** The results of the step on each item, in order, as a trampoline. */
  private def traversed[Item, Result](items: Vector[Item])(
      step: Item => TailRec[Result]
  ): TailRec[Vector[Result]] =
    def from(index: Int, results: Vector[Result]): TailRec[Vector[Result]] =
      if index >= items.size then done(results)
      else
        tailcall(step(items(index))).flatMap(result =>
          from(index + 1, results :+ result)
        )
    from(0, Vector.empty)
