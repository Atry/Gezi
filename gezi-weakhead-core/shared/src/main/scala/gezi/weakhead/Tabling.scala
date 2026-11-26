package gezi.weakhead

import scala.collection.immutable.IntMap
import gezi.weakhead.Trampoline.done
import gezi.weakhead.Trampoline.tailcall

/** A set of answers that remembers the order they were first added in, so
  * that a table's answers come out in an order that is a function of the
  * computation (never of hash codes).
  *
  * @param ordered
  *   the answers, each once, in the order they were first added
  * @param members
  *   the same answers as a set
  */
final case class AnswerSet[Answer](ordered: Vector[Answer], members: Set[Answer]):

  /** The set with an answer it does not hold added, last in the order. */
  def appended(answer: Answer): AnswerSet[Answer] = AnswerSet(ordered :+ answer, members + answer)

/** The empty answer set. */
object AnswerSet:
  def empty[Answer]: AnswerSet[Answer] = AnswerSet(Vector.empty, Set.empty)

/** Where a tabled function's completed tables are kept beside the state of
  * the computation that completes them, so that another computation may read
  * them. Only
  * a complete table is kept here, the least fixed point of its key, which a
  * computation may drop and compute again at the cost of time alone; the
  * tables in progress stay in the computation's state (`Tables`), a value no
  * other computation reaches, which is what keeps them from being dropped:
  * the cache service's references are strong or weak, so that what is being
  * computed cannot be dropped and what can be computed again can.
  */
trait CompletedTables[State, Key, Answer]:

  /** The answers of the key's complete table, if one is kept, with what
    * pinning the table in a computation's state changes of that state
    * besides its tables: what the store keeps with the table and the state
    * must hold for as long as it holds the table (the marks of failed checks
    * of a `Packed` reading), or nothing.
    */
  def found(key: Key): Option[(AnswerSet[Answer], State => State)]

  /** The complete tables of a component, its leader and its other members,
    * read from the state's complete tables, kept for other computations.
    * The component is handed as it stands in the state, so that a store
    * that keeps nothing builds nothing.
    */
  def kept(leader: Key, members: Vector[Key], complete: Map[Key, AnswerSet[Answer]]): Unit

/** The completed tables kept nowhere but in the computation's own state. */
object CompletedTables:

  private object Unshared extends CompletedTables[Any, Any, Any]:
    def found(key: Any): Option[(AnswerSet[Any], Any => Any)] = None
    def kept(leader: Any, members: Vector[Any], complete: Map[Any, AnswerSet[Any]]): Unit = ()

  /** Nothing kept beside the state. It holds nothing of any of its types, so the cast holds.
    */
  def unshared[State, Key, Answer]: CompletedTables[State, Key, Answer] =
    Unshared.asInstanceOf[CompletedTables[State, Key, Answer]]

/** Where an incomplete table stands (`Tables`). */
enum TableStatus:

  /** The key's evaluation is in progress, on the stack of calls, under the
    * serial number of its call.
    */
  case OnStack(serial: Int)

  /** The key was evaluated in the current iteration of its component, whose
    * leader is reached from the serial number by `Tables.forwards`.
    */
  case Evaluated(serial: Int)

  /** The key was evaluated in an earlier iteration of its component, whose
    * leader is iterating again: its approximation stands, and the next call
    * evaluates it again.
    */
  case Stale

/** The tables of a tabled function, as a value threaded through the
  * computation (`Tabling`): the complete tables, the answers found so far of
  * the others, and the producers of those, each of which every consumer of
  * its key drives (`Tabling.consumed`), so that a key's evaluation runs once
  * however many consumers read it. Nothing is collected: a producer that no
  * consumer drives any more stays, and the next consumer of its key goes on
  * from where it stopped: never collecting is kept as the simplest option,
  * and which caches to drop is `gezi.hotspot`'s to decide.
  *
  * @param complete
  *   the answers of each key whose table is complete
  * @param open
  *   each key whose table is not complete: where its table stands and the
  *   answers found so far, in the order found, every one an answer of its
  *   key; one entry for both, so that a consumer looks a key up once
  * @param forwards
  *   for the identity of each producer that ended before its component was
  *   complete, the identity of a producer further down the stack its
  *   component depends on
  * @param nextSerial
  *   the next number, for a producer's identity and for its order
  * @param active
  *   the identities of the producers running, the innermost first
  * @param running
  *   the same identities as a set, so that whether a producer runs is found
  *   in constant time: a scan of `active` at every consumer's step took 90%
  *   of the JFR samples of `NormalFormsTest`'s random terms (MEASURED
  *   2026-11-19), its depth being that of the term
  * @param frames
  *   the producers that have not ended, running or not, by identity
  *   (`FrameRecord`)
  */
/** An incomplete table (`Tables.open`): where it stands and the answers
  * found so far, in the order found.
  */
final case class OpenTable[Answer](status: TableStatus, answers: AnswerSet[Answer])

final case class Tables[State, Key, Answer](
    complete: Map[Key, AnswerSet[Answer]],
    open: Map[Key, OpenTable[Answer]],
    forwards: IntMap[Int],
    nextSerial: Int,
    active: List[Int],
    running: IntMap[Unit],
    frames: IntMap[FrameRecord[State, Key, Answer]]
):

  /** Whether a producer runs: an evaluation is in progress in these tables. */
  def inProgress: Boolean = active.nonEmpty

  /** The number of tables held, complete or not. */
  def held: Int = complete.size + open.size

  /** The tables a computation stopped inside leaves for the next one: no
    * producer runs, and every producer is marked dirty, since its record of
    * what it depends on was cut short (`FrameRecord.dirty`). Every answer
    * found is kept.
    */
  def stopped: Tables[State, Key, Answer] =
    copy(active = Nil, running = IntMap.empty, frames = frames.transform((_, record) => record.copy(dirty = true)))

  /** The tables with the producer of the identity running innermost. */
  private[weakhead] def started(identity: Int): Tables[State, Key, Answer] =
    copy(active = identity :: active, running = running.updated(identity, ()))

  /** The tables with the producer of the identity, which must run
    * innermost, no longer running.
    */
  private[weakhead] def finished(identity: Int): Tables[State, Key, Answer] = active match
    case `identity` :: below => copy(active = below, running = running.removed(identity))
    case other => throw IllegalStateException(s"the producer $identity ends or gives an answer while ${other.headOption} runs innermost")

  /** The tables after the producer of the identity, which must run innermost,
    * gave an answer new to its key: the key's answers `answers`, the
    * producer's rest `rest`, and the producer no longer running, in one copy
    * of the tables (`finished`).
    */
  private[weakhead] def answered(
      identity: Int,
      key: Key,
      answers: AnswerSet[Answer],
      rest: Answers[State, Answer]
  ): Tables[State, Key, Answer] = active match
    case `identity` :: below =>
      copy(
        open = open.updated(key, open.getOrElse(key, throw IllegalStateException(s"the running producer $identity's key has no open table")).copy(answers = answers)),
        frames = frames.updated(identity, frame(identity).copy(rest = rest)),
        active = below,
        running = running.removed(identity)
      )
    case other => throw IllegalStateException(s"the producer $identity gives an answer while ${other.headOption} runs innermost")

  /** The producer that leads the component of the producer of the identity. */
  @scala.annotation.tailrec
  private[weakhead] final def leader(identity: Int): Int =
    forwards.get(identity) match
      case Some(next) => leader(next)
      case None       => identity

  /** The record of the producer of the identity, which has not ended. */
  private[weakhead] def frame(identity: Int): FrameRecord[State, Key, Answer] =
    frames.getOrElse(identity, throw IllegalStateException(s"the producer $identity has ended"))

  /** The tables with the record of the producer of the identity changed. */
  private[weakhead] def frameChanged(
      identity: Int,
      change: FrameRecord[State, Key, Answer] => FrameRecord[State, Key, Answer]
  ): Tables[State, Key, Answer] =
    copy(frames = frames.updated(identity, change(frame(identity))))

  /** The number of answers the key has now, complete or found so far. */
  private[weakhead] def answerCount(key: Key): Int =
    complete.get(key).orElse(open.get(key).map(_.answers)).fold(0)(_.ordered.size)

  /** Whether a dependency still holds: its producer has not ended and is in
    * the iteration the dependency was recorded in.
    */
  private[weakhead] def holds(dependency: Dependency): Boolean =
    frames.get(dependency.producer).exists(_.iteration == dependency.iteration)

  /** A dependency on the producer of the identity as it is now. */
  private[weakhead] def dependencyOn(identity: Int): Dependency = Dependency(identity, frame(identity).iteration)

  /** Of two dependencies, the one further down the stack; one that no longer
    * holds is kept, since it makes the depending producer run its body once
    * more (`Tabling.ended`).
    */
  private[weakhead] def earlier(first: Option[Dependency], second: Option[Dependency]): Option[Dependency] =
    (first, second) match
      case (None, _) => second
      case (_, None) => first
      case (Some(one), Some(other)) =>
        if !holds(one) then first
        else if !holds(other) then second
        else if frame(one.producer).order <= frame(other.producer).order then first
        else second

/** A producer's evaluation read the answers found so far of the producer of
  * `producer`, in its iteration `iteration` (`FrameRecord.iteration`).
  */
final case class Dependency(producer: Int, iteration: Int)

/** The empty tables. */
object Tables:
  def empty[State, Key, Answer]: Tables[State, Key, Answer] =
    Tables(Map.empty, Map.empty, IntMap.empty, 0, Nil, IntMap.empty, IntMap.empty)

/** A producer of a key's answers that has not ended (`Tables.frames`).
  *
  * @param key
  *   its key
  * @param order
  *   its place in the depth-first order of the producers, which Tarjan's
  *   lowlinks compare: drawn when it is pushed, and drawn again when a
  *   consumer drives it from above a producer pushed after it
  *   (`Tabling.driven`)
  * @param lowlink
  *   the producer furthest down the stack whose answers found so far its
  *   evaluation read (or that of a producer that joined its component), with
  *   that producer's iteration then, none when it read none but its own; a
  *   producer that has ended since, or run its body again, no longer holds
  *   it (`Tables.holds`), and the answers read may have grown since
  * @param members
  *   the keys evaluated in the current iteration whose component it leads
  * @param reads
  *   the incomplete tables read in the current iteration by the producers
  *   that depend on it, each with the number of answers it had when read
  * @param rest
  *   the rest of its body's answers, from where it was last driven
  * @param dirty
  *   whether what it depends on may not be recorded, a computation having
  *   stopped inside it (`Tables.stopped`); it then runs its body once more
  *   when it ends (`Tabling.ended`) before its table may complete
  * @param iteration
  *   how many times it has run its body again (`Tabling.again`)
  */
final case class FrameRecord[State, Key, Answer](
    key: Key,
    order: Int,
    lowlink: Option[Dependency],
    members: Vector[Key],
    reads: Vector[(Key, Int)],
    rest: Answers[State, Answer],
    dirty: Boolean,
    iteration: Int
)

/** A tabled function: a set-valued function of keys, defined by a body that
  * may call the function on other keys, its own key included, and whose
  * value is the least fixed point of the equations its body states, with
  * every key's answers remembered (the memo). It gives what tablambda's
  * tabling gives (its paper's Algorithms 1 to 3): it halts where that
  * tabling halts, gives the same answers, and computes each key's answers
  * once, the time it takes; that algorithm sets the halting, the number of
  * answers and the time complexity. On an
  * evaluation that re-enters itself it gives the least fixed point (Omega's
  * head set is empty, decided in finite time).
  *
  * The tables (`Tables`) are a value inside the computation's state, which
  * `tables` reads and `withTables` replaces; nothing is mutated and nothing
  * is global. The body must be monotone: given larger answer sets for the
  * keys it calls, it gives a larger answer set (a union of what the answers
  * lead to is).
  *
  * PRODUCERS AND CONSUMERS. A call of a key is a consumer of its answers
  * (`consumed`), which reads them by their place in the order found: the
  * answers found so far, then, when it wants more, the key's producer
  * driven to its next answer, as SLG resolution's consumers read a table's
  * answers while its producer finds them (W. Chen, D. S. Warren, Tabled
  * Evaluation with Delaying for General Logic Programs, J. ACM 1996). A
  * producer is the key's body, and its rest is kept in the tables each time
  * it gives an answer, so that whichever consumer wants more drives it from
  * there: a consumer that stops early (`Answers.exists`) leaves the
  * producer where it is, and a later consumer, of the same evaluation or
  * another, goes on from there rather than evaluating the key again (MEASURED
  * 2026-11-19 on e45454515, where a producer given up was evaluated again
  * from its body: a key of 100 answers of 50 steps each, asked by `exists`
  * for its last answer M times, took M times 5,000 steps). So the table gives
  * every answer the untabled evaluation gives before a stop, each as soon as
  * it is found, a stream, so that tabling never gives fewer answers than no
  * tabling, and no answer found is ever dropped.
  *
  * THE ALGORITHM. A consumer of a key whose table is complete reads it. A
  * consumer of a key whose producer runs (it re-enters its own evaluation)
  * reads the answers found so far and no more, and records the read, with
  * the number of answers read, under the producer that leads the key's
  * component, and that producer in the lowlink of the innermost producer
  * running. Otherwise the consumer reads the answers found so far, and when
  * it wants more, drives the producer of the key, or of the component the
  * key's ended producer joined, to its next answer, a new producer of the
  * key pushed first if it has none. A producer driven from above producers
  * pushed after it is given a new order first, so that the producers running
  * stay in Tarjan's depth-first order. When a producer's body ends:
  *   - dirty, or depending on a producer that has ended or run its body
  *     again since it was read: it runs its body once more, from the answers
  *     found so far, recording what it depends on afresh;
  *   - depending on no producer below it: the producer leads a strongly
  *     connected component of calls (Tarjan's lowlink). If some table read
  *     in the iteration (a read recorded under it) has more answers now than
  *     when it was read, every key of the component is marked stale and the
  *     body runs again (a stale key is evaluated again when it is next
  *     called, from its approximation), giving the consumers only the answers
  *     they have not had; if none has, the approximations are a fixed point
  *     of the equations, and all the component's tables are completed
  *     together;
  *   - depending on a producer below it: its key is marked evaluated, it
  *     forwards to that producer, its members and reads move there, and the
  *     producer that drove it depends on that producer too; a later consumer
  *     of the key reads its answers and, wanting more, drives the producer
  *     its forwards lead to.
  * Starting from no answers, and only ever adding what a monotone body gives
  * from answers below the least fixed point, every approximation stays below
  * the least fixed point, so every answer given is an answer of the key; a
  * component completes only on an iteration none of whose reads grew, a
  * fixed point; so a completed table holds exactly the least fixed point's
  * answers. This is the scheme of SLG resolution's completion of strongly
  * connected components with naive iteration inside a component (the
  * components found as R. Tarjan's depth-first search finds them,
  * Depth-First Search and Linear Graph Algorithms, SIAM J. Comput. 1972).
  *
  * A stop inside the body (a budget run out) stops the call; the tables are
  * left as they were at the stop, and a caller that goes on with them takes
  * `Tables.stopped` first, which a call made while no producer runs does
  * itself.
  *
  * @param tables
  *   the tables in a state
  * @param withTables
  *   the state with its tables replaced
  * @param completedTables
  *   where the state's completed tables are kept beside it
  *   (`CompletedTables`): a key with no table in the state is looked up
  *   there before it is evaluated, and a table found there is put in the
  *   state as complete, with what the store keeps with it
  *   (`CompletedTables.found`), so that the computation holds both for as
  *   long as its state does; a component's tables are kept there when it
  *   completes. A
  *   stopped or incomplete table is never kept there.
  * @param body
  *   the answers of a key, given the function itself to call on keys
  */
final case class Tabling[State, Key, Answer](
    tables: State => Tables[State, Key, Answer],
    withTables: (State, Tables[State, Key, Answer]) => State,
    completedTables: State => CompletedTables[State, Key, Answer],
    body: (Key, Key => Answers[State, Answer]) => Answers[State, Answer]
):

  private type Driven = Trampoline[Computed[State, Unit]]

  /** The answers of the key, each as it is found: a consumer of the key
    * (`call`).
    */
  def answers(key: Key): Answers[State, Answer] = call(key)

  /** The answers of the key, each as it is found: a consumer of the key
    * (`consumed`). Called while no producer runs, the stream leaves
    * `Tables.stopped` at a stop.
    */
  def call(key: Key): Answers[State, Answer] =
    Answers(Computation(state =>
      if tables(state).inProgress then tailcall(consumed(key, 0).pull.run(state))
      else tailcall(outermost(consumed(key, 0)).pull.run(state))
    ))

  private def outermost(stream: Answers[State, Answer]): Answers[State, Answer] =
    Answers(Computation(state =>
      tailcall(stream.pull.run(state)).map {
        case Computed.Done(Some((answer, more)), after) => Computed.Done(Some((answer, outermost(more))), after)
        case Computed.Done(None, after)                 => Computed.Done(None, after)
        case Computed.Stopped(stopped)                  => Computed.Stopped(withTables(stopped, tables(stopped).stopped))
      }
    ))

  /** The key's answers from the one at `index` on (THE ALGORITHM). */
  private def consumed(key: Key, index: Int): Answers[State, Answer] =
    Answers(Computation(state =>
      val current = tables(state)
      current.complete.get(key) match
        case Some(answers) => tailcall(Answers.of[State, Answer](answers.ordered.drop(index)).pull.run(state))
        case None =>
          val table = current.open.get(key)
          val found = table.fold(Vector.empty[Answer])(_.answers.ordered)
          val leading = table.map(_.status) match
            case Some(TableStatus.OnStack(identity))   => Some(identity).filter(current.frames.contains)
            case Some(TableStatus.Evaluated(identity)) => Some(current.leader(identity)).filter(current.frames.contains)
            case Some(TableStatus.Stale) | None        => None
          leading match
            case Some(producer) if current.running.contains(producer) =>
              tailcall(read(state, current, key, producer, found, index).pull.run(state))
            case _ if index < found.size =>
              done(Computed.Done(Some((found(index), consumed(key, index + 1))), state))
            case Some(producer) =>
              tailcall(driven(producer, state)).flatMap {
                case Computed.Done(_, after) => tailcall(consumed(key, index).pull.run(after))
                case Computed.Stopped(stopped) => done(Computed.Stopped(stopped))
              }
            case None =>
              table.fold(completedTables(state).found(key))(_ => None) match
                case Some((kept, restored)) =>
                  val pinned = restored(withTables(state, current.copy(complete = current.complete.updated(key, kept))))
                  tailcall(Answers.of[State, Answer](kept.ordered.drop(index)).pull.run(pinned))
                case None =>
                  val (identity, pushed) = keyPushed(current, key)
                  tailcall(driven(identity, withTables(state, pushed))).flatMap {
                    case Computed.Done(_, after) => tailcall(consumed(key, index).pull.run(after))
                    case Computed.Stopped(stopped) => done(Computed.Stopped(stopped))
                  }
    ))

  /** The answers found so far of a key whose producer runs, from the one at
    * `index` on, the read recorded under the producer that leads its
    * component, and that producer in the lowlink of the innermost producer
    * running.
    */
  private def read(
      state: State,
      current: Tables[State, Key, Answer],
      key: Key,
      producer: Int,
      found: Vector[Answer],
      index: Int
  ): Answers[State, Answer] =
    val reading = current.active.headOption.getOrElse(throw IllegalStateException("a read with no producer running"))
    val recorded = current
      .frameChanged(producer, record => record.copy(reads = record.reads :+ (key -> found.size)))
      .frameChanged(reading, record =>
        if reading == producer then record else record.copy(lowlink = current.earlier(record.lowlink, Some(current.dependencyOn(producer))))
      )
    Answers(Computation.replaced(withTables(state, recorded)).flatMap(_ => Answers.of[State, Answer](found.drop(index)).pull))

  /** The tables with a producer of the key pushed, not yet running. */
  private def keyPushed(current: Tables[State, Key, Answer], key: Key): (Int, Tables[State, Key, Answer]) =
    val identity = current.nextSerial
    val record = FrameRecord[State, Key, Answer](key, identity, None, Vector.empty, Vector.empty, body(key, call), dirty = false, iteration = 0)
    (
      identity,
      current.copy(
        open = current.open.updated(key, OpenTable(TableStatus.OnStack(identity), current.open.get(key).fold(AnswerSet.empty[Answer])(_.answers))),
        nextSerial = identity + 1,
        frames = current.frames.updated(identity, record)
      )
    )

  /** The producer of the identity driven by the innermost producer running,
    * or from outside them, to its next answer new to its key, or to its end.
    * A producer pushed before the one that drives it is given a new order
    * first, so that the producers running stay in depth-first order; what it
    * depends on is recorded by identity (`FrameRecord.lowlink`), so nothing
    * of it is lost, and a dependency on a producer that has ended or run its
    * body again since makes it run its body once more when it ends (`ended`).
    */
  private def driven(identity: Int, state: State): Driven =
    val current = tables(state)
    val record = current.frame(identity)
    val outOfOrder = current.active.headOption.exists(driver => current.frame(driver).order > record.order)
    val installed =
      if outOfOrder then
        current
          .copy(nextSerial = current.nextSerial + 1)
          .started(identity)
          .frameChanged(identity, _.copy(order = current.nextSerial))
      else current.started(identity)
    pulled(identity, withTables(state, installed))

  private def pulled(identity: Int, state: State): Driven =
    pulledFrom(identity, tables(state).frame(identity).rest, state)

  /** The producer of the identity, which runs innermost, pulled from
    * `stream`, the rest of its body, to its next answer new to its key, or
    * to its end. An answer its key already holds is passed over without
    * touching the tables: nothing reads the producer's rest while it runs
    * (a consumer of its key reads its answers, `read`), so the rest is
    * written into its record only where control leaves it, at a new answer
    * and at a stop, where it is the stream whose pull stopped, the rest the
    * record held before.
    */
  private def pulledFrom(identity: Int, stream: Answers[State, Answer], state: State): Driven =
    tailcall(stream.pull.run(state)).flatMap {
      case Computed.Stopped(stopped) =>
        done(Computed.Stopped(withTables(stopped, tables(stopped).frameChanged(identity, _.copy(rest = stream)))))
      case Computed.Done(Some((answer, more)), after) =>
        val current = tables(after)
        val key = current.frame(identity).key
        val found = current.open.get(key).fold(AnswerSet.empty[Answer])(_.answers)
        if found.members.contains(answer) then tailcall(pulledFrom(identity, more, after))
        else
          done(Computed.Done((), withTables(after, current.answered(identity, key, found.appended(answer), more))))
      case Computed.Done(None, after) => ended(identity, after)
    }

  /** The producer's body done: run once more, its component completed, its
    * body run again for the component, or its component joined to one below
    * it (THE ALGORITHM).
    */
  private def ended(identity: Int, after: State): Driven =
    val current = tables(after)
    val record = current.frame(identity)
    val dependency = record.lowlink.filter(_.producer != identity)
    val lost = dependency.exists(!current.holds(_))
    val below = dependency.map(_.producer).filter(producer => current.frames.get(producer).exists(_.order < record.order))
    if record.dirty || lost then tailcall(pulled(identity, withTables(after, current.copy(open = staled(current, record)).frameChanged(identity, _ => again(record)))))
    else
      below match
        case None =>
          if record.reads.forall((key, count) => current.answerCount(key) == count) then
            val completedNow = completed(current, identity, record)
            completedTables(after).kept(record.key, record.members, completedNow.complete)
            done(Computed.Done((), withTables(after, completedNow)))
          else tailcall(pulled(identity, withTables(after, current.copy(open = staled(current, record)).frameChanged(identity, _ => again(record)))))
        case Some(producer) =>
          val forwarded = current
            .copy(
              open = current.open.updated(record.key, OpenTable(TableStatus.Evaluated(identity), current.open.get(record.key).fold(AnswerSet.empty[Answer])(_.answers))),
              forwards = current.forwards.updated(identity, producer),
              frames = current.frames.removed(identity)
            )
            .finished(identity)
            .frameChanged(producer, target => target.copy(members = target.members ++ record.members :+ record.key, reads = target.reads ++ record.reads))
          val driverDepends = forwarded.active.headOption.fold(forwarded)(driver =>
            if driver == producer then forwarded
            else forwarded.frameChanged(driver, driving => driving.copy(lowlink = forwarded.earlier(driving.lowlink, Some(forwarded.dependencyOn(producer)))))
          )
          done(Computed.Done((), withTables(after, driverDepends)))

  /** The producer about to run its body again: no member, no read, nothing
    * depended on, not dirty.
    */
  private def again(record: FrameRecord[State, Key, Answer]): FrameRecord[State, Key, Answer] =
    record.copy(
      lowlink = None,
      members = Vector.empty,
      reads = Vector.empty,
      rest = body(record.key, call),
      dirty = false,
      iteration = record.iteration + 1
    )

  /** The open tables with the producer's members stale, to be evaluated again
    * when next called.
    */
  private def staled(current: Tables[State, Key, Answer], record: FrameRecord[State, Key, Answer]): Map[Key, OpenTable[Answer]] =
    record.members.foldLeft(current.open)((open, member) =>
      open.updated(member, OpenTable(TableStatus.Stale, open.get(member).fold(AnswerSet.empty[Answer])(_.answers)))
    )

  /** The tables with the producer's component completed: its key and its
    * members, each with its answers found. A key completed meanwhile by
    * another evaluation keeps its table, the least fixed point, of which the
    * answers found are a part.
    */
  private def completed(
      current: Tables[State, Key, Answer],
      identity: Int,
      record: FrameRecord[State, Key, Answer]
  ): Tables[State, Key, Answer] =
    val component = record.members :+ record.key
    current.copy(
      complete = component.foldLeft(current.complete)((complete, member) =>
        if complete.contains(member) then complete
        else complete.updated(member, current.open.get(member).fold(AnswerSet.empty[Answer])(_.answers))
      ),
      open = current.open -- component,
      frames = current.frames.removed(identity)
    ).finished(identity)
