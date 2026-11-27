package gezi.narrowblocks.groups

import gezi.ir.{Configured, NativeSpecializer}
import gezi.saturation.StopSignal

/** A call of a recursion within one run of a block: the recursion, by its
  * G, and the group of each of its arguments, its members distinct and in
  * the canonical order (`GroupBackend.valueOrdering`), a single value being
  * a group of one. Within a run a recursion is one G, so the key names one
  * call; a run's results are never read by another.
  */
final case class CallKey(recursion: Int, arguments: Vector[Vector[GroupValue]])

/** A call of a recursion as a run's schedule names it: the recursion, and
  * the identity the backend's memo gave the call's arguments' groups
  * (`GroupBackend.asked`).
  */
final case class CallIdentity(recursion: Int, identity: Int)

/** One run of a block as a group program on a backend: every value a
  * relation, for each row of a frame the values an expression has there,
  * made only by the backend's operations, and a recursion's calls scheduled
  * in rounds of tables.
  *
  * THE RELATIONS. A frame is a table of rows numbered from 0. A single-valued
  * binder (a branch's half, a list's head or tail) is a column of the frame,
  * one value per row; a group-valued binder (a block's parameter, a let's
  * binder, a recursion's parameter) is a relation, for each row its group. A relation's table
  * has the frame's row number in its first column and the value in its
  * second, deduplicated (`unique`). So an occurrence of a group-valued
  * binder reads its row's whole group, each occurrence on its own, and an
  * operation on several operands joins them by the row number (`joined`),
  * the outer product within each row.
  *
  * THE CALLS. A recursion's call at a row is the call on each argument's
  * group in that row, by the β rule: the group is substituted at every read
  * of the parameter in the recursion's body, each read its own member, so
  * the recursion's frame binds each parameter to the call's group, and a
  * call is named by its arguments' groups (an empty group included, the
  * call of an argument with no value). A row in which an argument waits
  * makes no call: its group is not yet the term's.
  *
  * THE ROUNDS. A recursion's call reads its result from the results the run
  * has finished; a row whose call is not finished yet waits on that call,
  * waiting being a property of each row's value: the operations that read
  * it wait in that row, those that do not go on, so that one evaluation
  * collects every call a row misses, and a branch whose condition waits
  * enters no case, so that no call is made that the program would not make.
  * Each round evaluates, as one table per recursion, the calls newly asked
  * for and the waiting tasks (the block's entry, or calls) whose missing
  * calls have all finished; a task's results are kept once no row of it
  * waits. A round with nothing to evaluate while the entry has not finished
  * is a cycle: every waiting task waits on a waiting task, and the block
  * stops with no value.
  *
  * THE BUDGET. Every operation counts the rows it makes before it makes
  * them and reads `stop` first; past the allowance, or at a stop, the run
  * gives the steps it spent and no value. So does a row an operation drops
  * (`keptEvery`), marked as rejected: an outcome of the arguments, not of
  * the block, so the machine does not give the block up for it.
  *
  * THE DATA STAYS IN THE BACKEND. Values enter the backend at the block's
  * entry (`column`, once per parameter) and are read back at its exit
  * (`rows`, once); the memo of finished calls is the backend's (`Memo`),
  * threaded through the run in order: through each round's recursion
  * tables, then its entry, then into the next round. In between the program
  * reads back control data only:
  *
  *  - the sizes of joins (`joinedSize`), before the join is made, and the
  *    row counts of tables;
  *  - the row numbers of a call site's unfinished rows with the identities
  *    of their calls (`asked`), once per call site that has any;
  *  - the parent rows of a case's waiting rows (`rowsAt`), only when the
  *    case has rows that wait.
  *
  * A round's frame for a recursion has a row per call, its parameters the
  * relations of the calls' groups the memo gives back by identity (`keys`),
  * and a task is the entry or a call named by its identity. On a backend whose data lives on a device, each
  * read back is a synchronisation of the device with the host.
  */
private final class GroupProgram[C <: NativeSpecializer & Singleton](block: GroupBlock[C], val backend: GroupBackend, memo: GroupMemoOption, allowance: Long, stop: StopSignal):

  private type Table = GroupTable[backend.Column]

  /** The rows of one evaluation and its binders: each single-valued
    * binder's column, aligned with the rows, and each group-valued binder's
    * relation.
    */
  private final case class Frame(rowCount: Int, singles: Map[Int, backend.Column], groups: Map[Int, Table])

  /** For each row of a frame, the values of an expression (the table, the
    * row number then the value), and the rows that wait, each on the calls
    * it misses.
    */
  private final case class Relation(table: Table, waiting: Map[Int, Set[CallIdentity]])

  /** What the run carries from step to step: the steps spent, the
    * backend's memo, and what the run has read back so far.
    */
  private final case class State(spent: Long, memo: backend.Memo, readBacks: GroupReadBacks)

  /** What a step of the run gives: its value and the state after it, or the
    * steps spent when it stopped.
    */
  private type Step[A] = Either[Stopped, (A, State)]

  /** A task of the schedule: the block's entry, or a recursion's call. */
  private enum Task:
    case Entry
    case Call(call: CallIdentity)

  /** The schedule between rounds: the state (the steps spent and the
    * memo); the finished calls; for each call not finished, the tasks
    * waiting on it, and for each waiting task, how many of its missing calls
    * have not finished; the calls evaluated so far; and what the last round
    * finished and left waiting. A finished call wakes only the tasks waiting
    * on it, so the schedule's work is linear in the calls and the waits.
    */
  private final case class Schedule(
      state: State,
      finished: Set[CallIdentity],
      dependents: Map[CallIdentity, Vector[Task]],
      pending: Map[Task, Int],
      started: Set[CallIdentity],
      finishedNow: Vector[CallIdentity],
      waitingNow: Vector[(Task, Set[CallIdentity])]
  ):
    def spent: Long = state.spent

  /** The run on the arguments' groups. */
  def run(arguments: Vector[Vector[GroupValue]]): GroupOutcome =
    val entry = Frame(1, Map.empty, arguments.zipWithIndex.map((group, parameter) => parameter -> entryRelation(group)).toMap)
    val start = State(0L, backend.emptyMemo(memo), GroupReadBacks.none.copy(entryColumns = arguments.size.toLong))
    rounds(Vector(Task.Entry), entry, Schedule(start, Set.empty, Map.empty, Map.empty, Set.empty, Vector.empty, Vector.empty))

  /** The rounds from the tasks ready now. */
  @scala.annotation.tailrec
  private def rounds(ready: Vector[Task], entry: Frame, schedule: Schedule): GroupOutcome =
    round(ready, entry, schedule) match
      case Left(stopped)                 => outcome(if stopped.rejected then GroupEnd.Rejected else GroupEnd.Stopped, stopped.spent, schedule)
      case Right((Some(results), after)) => outcome(GroupEnd.Finished(results), after.spent, after)
      case Right((None, after)) =>
        val (registered, readyNow, fresh) = after.waitingNow.foldLeft((after, Vector.empty[Task], Vector.empty[CallIdentity])) {
          case ((current, ready, asked), (task, missing)) =>
            // Membership tests, never a set difference with the finished or
            // started calls, which would walk all of them every round.
            val remaining = missing.filterNot(current.finished.contains)
            if remaining.isEmpty then (current, ready :+ task, asked)
            else
              (
                current.copy(
                  dependents = remaining.foldLeft(current.dependents)((made, key) => made.updated(key, made.getOrElse(key, Vector.empty) :+ task)),
                  pending = current.pending.updated(task, remaining.size)
                ),
                ready,
                asked ++ remaining.toVector.filterNot(call => current.started.contains(call) || asked.contains(call))
              )
        }
        val (woken, unblocked) = registered.finishedNow.foldLeft((registered, Vector.empty[Task])) { case ((current, ready), key) =>
          current.dependents.getOrElse(key, Vector.empty).foldLeft((current.copy(dependents = current.dependents - key), ready)) {
            case ((inner, readyInner), task) =>
              val left = inner.pending.getOrElse(task, 0) - 1
              if left == 0 then (inner.copy(pending = inner.pending - task), readyInner :+ task)
              else (inner.copy(pending = inner.pending.updated(task, left)), readyInner)
          }
        }
        val next = readyNow ++ unblocked ++ fresh.map(Task.Call(_))
        if next.isEmpty then outcome(GroupEnd.Stopped, woken.spent, woken)
        else rounds(next, entry, woken.copy(finishedNow = Vector.empty, waitingNow = Vector.empty))

  /** The run's outcome, with the memo's counts of finished calls. */
  private def outcome(ended: GroupEnd, spent: Long, schedule: Schedule): GroupOutcome =
    ended match
      case GroupEnd.Finished(results) => require(results.nonEmpty, "a finished run has a value: every entry is nonempty and every operation that would drop a row stops")
      case GroupEnd.Stopped | GroupEnd.Rejected => ()
    val (finishedCalls, denseCalls) = backend.memoSizes(schedule.state.memo)
    GroupOutcome(ended, spent, finishedCalls, denseCalls, schedule.state.readBacks)

  /** One round: each recursion's ready calls as one table, in the order the
    * recursions are first met, then the entry when it is ready; the entry's
    * results when it finishes.
    */
  private def round(ready: Vector[Task], entry: Frame, schedule: Schedule): Either[Stopped, (Option[Vector[GroupValue]], Schedule)] =
    val calls = ready.collect { case Task.Call(call) => call }
    val counted = schedule.state.copy(readBacks = schedule.state.readBacks.copy(rounds = schedule.state.readBacks.rounds + 1))
    val start: Either[Stopped, Schedule] = Right(schedule.copy(started = schedule.started ++ calls, state = counted))
    val afterCalls = calls.map(_.recursion).distinct.foldLeft(start) { (sofar, recursion) =>
      sofar.flatMap(current => recursionRound(recursion, calls.filter(_.recursion == recursion), current))
    }
    afterCalls.flatMap(current =>
      if !ready.contains(Task.Entry) then Right((None, current))
      else
        evaluated(block.body, entry, None, current.state).map((relation, state) =>
          relation.waiting.get(0) match
            case Some(missing) => (None, current.copy(waitingNow = current.waitingNow :+ (Task.Entry, missing), state = state))
            case None =>
              (
                Some(backend.rows(relation.table).map(row => row(1))),
                current.copy(state = state.copy(readBacks = state.readBacks.copy(exits = state.readBacks.exits + 1)))
              )
        )
    )

  /** The calls of one recursion evaluated as one frame, a row per call, the
    * frame's columns the arguments the memo gives back by identity: the
    * calls whose rows do not wait stored in the memo with their results, the
    * others' missing calls kept.
    */
  private def recursionRound(recursion: Int, calls: Vector[CallIdentity], schedule: Schedule): Either[Stopped, Schedule] =
    val found = block.recursionBodies.lift(recursion).getOrElse(throw IllegalStateException(s"a call of a recursion the block did not compile: $recursion"))
    val arguments = backend.keys(schedule.state.memo, recursion, IArray.from(calls.map(_.identity)))
    require(arguments.size == found.parameters, s"the memo gives back a relation for each of the ${found.parameters} arguments, not ${arguments.size}")
    val frame = Frame(calls.size, Map.empty, arguments.zipWithIndex.map((relation, position) => (position + 1) -> relation).toMap)
    val keyed = schedule.state.copy(readBacks = schedule.state.readBacks.copy(keyTables = schedule.state.readBacks.keyTables + 1))
    evaluated(found.body, frame, Some(recursion), keyed).map((relation, state) =>
      val (waiting, done) = calls.zipWithIndex.partition((_, row) => relation.waiting.contains(row))
      val stored = backend.stored(
        state.memo,
        recursion,
        IArray.from(done.map(_._1.identity)),
        IArray.from(done.map(_._2)),
        relation.table
      )
      schedule.copy(
        state = state.copy(memo = stored),
        finished = schedule.finished ++ done.map(_._1),
        finishedNow = schedule.finishedNow ++ done.map(_._1),
        waitingNow = schedule.waitingNow ++ waiting.map((call, row) => (Task.Call(call), relation.waiting(row)))
      )
    )

  /** The relation of the expression over the frame, within the steps left. */
  private def evaluated(
      expression: GroupExpression[Configured[C]],
      frame: Frame,
      recursion: Option[Int],
      state: State
  ): Step[Relation] =
    def of(inner: GroupExpression[Configured[C]], innerFrame: Frame, before: State): Step[Relation] =
      evaluated(inner, innerFrame, recursion, before)
    expression match
      case GroupExpression.Variable(binder) =>
        frame.singles.get(binder) match
          case Some(column) =>
            made(state, frame.rowCount)(backend.projected(backend.numbered(backend.table(Vector(column), frame.rowCount)), Vector(1, 0)))
              .map((table, after) => (Relation(table, Map.empty), after))
          case None =>
            val group = frame.groups.getOrElse(binder, throw IllegalStateException(s"no value bound to the binder $binder"))
            made(state, group.rowCount)(group).map((table, after) => (Relation(table, Map.empty), after))
      case GroupExpression.Literal(closed) => constantRelation(frame, GroupProgram.constantValue(closed), state)
      case GroupExpression.Value(closed)   => constantRelation(frame, GroupProgram.constantValue(closed), state)
      case GroupExpression.Native(name, arguments) =>
        operands(arguments, frame, of, state).flatMap((joined, waiting, after) =>
          val values = arguments.indices.toVector.map(position => 2 + 2 * position)
          val computed =
            if GroupCompilation.constructors.contains(name) then
              backend.computed(joined, GroupProgram.constructorOperation(name), values)
            else backend.called(joined, block.methods(name), values)
          // A row on which the native has no answer, or a constructor no
          // layer, is no row to drop: the application has no normal form,
          // but a context consuming it can have an answer.
          keptEvery(joined, computed, after).flatMap(_ =>
            made(after, joined.rowCount)(backend.projected(computed, Vector(0, computed.columns.size - 1)))
              .map((table, last) => (Relation(table, waiting), last))
          )
        )
      case GroupExpression.Constructed(_, constructor, _, _, fields) =>
        operands(fields, frame, of, state).flatMap((joined, waiting, after) =>
          val computed = backend.computed(joined, GroupOperation.ConstructedAt(constructor), fields.indices.toVector.map(position => 2 + 2 * position))
          made(after, joined.rowCount)(backend.projected(computed, Vector(0, computed.columns.size - 1)))
            .map((table, last) => (Relation(table, waiting), last))
        )
      // A row the filter rejects is not dropped: the filtered term has no
      // answer of its own, but a context consuming it can have one
      // (`(cons zero nil ∥ array_list P) false (λh t. true)` is true), so the
      // block stops and the reading reads the application: the block itself
      // loses no answer here, while the reading still loses this one at its
      // decode point (a FIXME at `gezi.jit.Jit.readingDecoded`).
      case GroupExpression.Filtered(value, GroupRepresentation.ListOf(element)) =>
        // A list is kept relabelled under the filter, so that the filtered
        // column's lists are of its representation.
        of(value, frame, state).flatMap((relation, after) =>
          val kind = GroupListKind(block.operations, GroupBlockMechanism.listRepresentation(element))
          val relabelled = backend.computed(relation.table, GroupOperation.Relabelled(kind), Vector(1))
          keptEvery(relation.table, relabelled, after).flatMap(_ =>
            made(after, relation.table.rowCount)(backend.projected(relabelled, Vector(0, 2)))
              .map((table, last) => (Relation(table, relation.waiting), last))
          )
        )
      case GroupExpression.Filtered(value, representation) =>
        of(value, frame, state).flatMap((relation, after) =>
          val (admitted, rejected) = backend.selected(backend.computed(relation.table, GroupOperation.Admits(representation), Vector(1)), 2)
          if rejected.rowCount > 0 then Left(Stopped(after.spent, rejected = true))
          else
            made(after, relation.table.rowCount)(backend.projected(admitted, Vector(0, 1)))
              .map((table, last) => (Relation(table, relation.waiting), last))
        )
      case GroupExpression.Branch(scrutinee, zero, evenHalf, even, oddHalf, odd) =>
        of(scrutinee, frame, state).flatMap((tested, after) =>
          val cases = Vector(
            (GroupOperation.Zero, None, zero),
            (GroupOperation.EvenPositive, Some(evenHalf), even),
            (GroupOperation.Odd, Some(oddHalf), odd)
          )
          cases
            .foldLeft(Right((Vector.empty[Relation], after)): Step[Vector[Relation]]) { case (sofar, (test, half, branch)) =>
              sofar.flatMap((done, current) =>
                val chosen = backend.projected(backend.selected(backend.computed(tested.table, test, Vector(1)), 2)._1, Vector(0, 1))
                caseRelation(chosen, half.toVector.map(_ -> GroupOperation.Half), branch, frame, of, current).map((relation, next) => (done :+ relation, next))
              )
            }
            .flatMap((relations, current) => union(relations, tested.waiting, current))
        )
      case GroupExpression.Select(scrutinee, whenTrue, whenFalse) =>
        of(scrutinee, frame, state).flatMap((tested, after) =>
          val (truths, falsities) = backend.selected(tested.table, 1)
          caseRelation(truths, Vector.empty, whenTrue, frame, of, after).flatMap((onTrue, current) =>
            caseRelation(falsities, Vector.empty, whenFalse, frame, of, current).flatMap((onFalse, next) =>
              union(Vector(onTrue, onFalse), tested.waiting, next)
            )
          )
        )
      case GroupExpression.ListBranch(scrutinee, nil, head, tail, cons) =>
        of(scrutinee, frame, state).flatMap((tested, after) =>
          val (empties, nonempty) = backend.selected(backend.computed(tested.table, GroupOperation.Empty, Vector(1)), 2)
          caseRelation(backend.projected(empties, Vector(0, 1)), Vector.empty, nil, frame, of, after).flatMap((onNil, current) =>
            caseRelation(
              backend.projected(nonempty, Vector(0, 1)),
              Vector(head -> GroupOperation.Head, tail -> GroupOperation.Tail),
              cons,
              frame,
              of,
              current
            ).flatMap((onCons, next) => union(Vector(onNil, onCons), tested.waiting, next))
          )
        )
      case GroupExpression.ListConstructed(_, fields, element) =>
        if fields.isEmpty then
          constantRelation(frame, GroupValue.List(GroupListKind(block.operations, GroupBlockMechanism.listRepresentation(element)).of(Vector.empty)), state)
        else
          operands(fields, frame, of, state).flatMap((joined, waiting, after) =>
            val kind = GroupListKind(block.operations, GroupBlockMechanism.listRepresentation(element))
            val computed = backend.computed(joined, GroupOperation.Consed(element, kind), Vector(2, 4))
            // A cons the filter rejects (a zero head under the positive
            // naturals) stops the block, as a filter's rejection does.
            keptEvery(joined, computed, after).flatMap(_ =>
              made(after, joined.rowCount)(backend.projected(computed, Vector(0, computed.columns.size - 1)))
                .map((table, last) => (Relation(table, waiting), last))
            )
          )
      case GroupExpression.Let(binder, value, body) =>
        of(value, frame, state).flatMap((bound, after) =>
          of(body, frame.copy(groups = frame.groups.updated(binder, bound.table)), after).map((relation, last) =>
            (Relation(relation.table, GroupProgram.merged(relation.waiting, bound.waiting)), last)
          )
        )
      case GroupExpression.Choice(left, right) =>
        of(left, frame, state).flatMap((leftRelation, after) =>
          of(right, frame, after).flatMap((rightRelation, current) => union(Vector(leftRelation, rightRelation), Map.empty, current))
        )
      case GroupExpression.RecursionCall(called, arguments) => recursionCall(block.recursionNumber(called), arguments, frame, of, state)
      case GroupExpression.SelfCall(arguments) =>
        recursionCall(recursion.getOrElse(throw IllegalStateException("a self call outside a recursion's body")), arguments, frame, of, state)
      case GroupExpression.Call(_, _) | GroupExpression.PartialApplication(_, _) | GroupExpression.ClosedCode(_, _) =>
        throw IllegalStateException(s"a compiled group block holds no $expression")

  /** The operands' relations joined by the row number: the table's first
    * column the frame's row, then the row number and the value of each
    * operand in order; with the rows any operand waits in. The join's size
    * is asked of the backend, and counted, before the join is made.
    */
  private def operands(
      arguments: Vector[GroupExpression[Configured[C]]],
      frame: Frame,
      of: (GroupExpression[Configured[C]], Frame, State) => Step[Relation],
      state: State
  ): Either[Stopped, (Table, Map[Int, Set[CallIdentity]], State)] =
    arguments
      .foldLeft(Right((Vector.empty[Relation], state)): Step[Vector[Relation]])((sofar, argument) =>
        sofar.flatMap((done, current) => of(argument, frame, current).map((relation, after) => (done :+ relation, after)))
      )
      .flatMap((relations, after) =>
        val rows = backend.numbered(backend.table(Vector.empty, frame.rowCount))
        val size = backend.joinedSize(relations.map(_.table), frame.rowCount)
        made(after, size)(relations.foldLeft(rows)((joined, relation) => backend.joined(joined, relation.table, Vector(0), Vector(0))))
          .map((table, last) =>
            (table, relations.foldLeft(Map.empty[Int, Set[CallIdentity]])((made, relation) => GroupProgram.merged(made, relation.waiting)), last)
          )
      )

  /** The relation of a case of a branch over the rows `chosen` (the frame's
    * row, then the scrutinee's value) selected for it: a frame of those
    * rows, the parent's binders read at each row's parent row and each
    * binder the case binds at the operation's value on the scrutinee's (a
    * natural's half, a list's head and tail), the case evaluated there and
    * joined back to the parent rows. The parent rows of the case's waiting
    * rows are read back, and only when some row waits.
    */
  private def caseRelation(
      chosen: Table,
      bound: Vector[(Int, GroupOperation)],
      branch: GroupExpression[Configured[C]],
      frame: Frame,
      of: (GroupExpression[Configured[C]], Frame, State) => Step[Relation],
      state: State
  ): Step[Relation] =
    if chosen.rowCount == 0 then Right((Relation(backend.emptyTable(2), Map.empty), state))
    else
      // The chosen rows numbered: the parent row, the value, the case's row.
      val numbered = backend.numbered(chosen)
      val parentColumn = (binderColumn: backend.Column) =>
        backend.joined(numbered, backend.numbered(backend.table(Vector(binderColumn), frame.rowCount)), Vector(0), Vector(1)).columns(3)
      val singles = frame.singles.map((binder, column) => binder -> parentColumn(column))
      val groups = frame.groups.map((binder, group) => binder -> backend.projected(backend.joined(numbered, group, Vector(0), Vector(0)), Vector(2, 4)))
      val halves = bound.foldLeft(singles) { case (binders, (binder, operation)) =>
        binders.updated(binder, backend.computed(numbered, operation, Vector(1)).columns(3))
      }
      made(state, chosen.rowCount)(numbered).flatMap((_, after) =>
        of(branch, Frame(chosen.rowCount, halves, groups), after).flatMap((relation, current) =>
          val back = backend.projected(backend.joined(relation.table, numbered, Vector(0), Vector(2)), Vector(2, 1))
          val waitingRows = relation.waiting.keys.toVector.sorted
          val parents =
            if waitingRows.isEmpty then Vector.empty
            else backend.rowsAt(numbered, 0, IArray.from(waitingRows)).toVector
          val read =
            if waitingRows.isEmpty then current
            else
              current.copy(readBacks =
                current.readBacks.copy(parentReads = current.readBacks.parentReads + 1, parentRows = current.readBacks.parentRows + waitingRows.size)
              )
          made(read, back.rowCount)(back).map((table, last) =>
            (
              Relation(
                table,
                waitingRows.lazyZip(parents).foldLeft(Map.empty[Int, Set[CallIdentity]]) { case (made, (row, parent)) =>
                  GroupProgram.merged(made, Map(parent -> relation.waiting(row)))
                }
              ),
              last
            )
          )
        )
      )

  /** The calls of the recursion at each row, on the operands' groups: each
    * operand evaluated on its own, not joined with the others (a join would
    * drop a row whose operand has an empty group); a row in which an operand
    * waits makes no call and waits on what the operand misses; for the
    * others the backend's memo gives the results of each finished call, and
    * an identity for each call that has not finished, on which its row
    * waits.
    */
  private def recursionCall(
      recursion: Int,
      arguments: Vector[GroupExpression[Configured[C]]],
      frame: Frame,
      of: (GroupExpression[Configured[C]], Frame, State) => Step[Relation],
      state: State
  ): Step[Relation] =
    arguments
      .foldLeft(Right((Vector.empty[Relation], state)): Step[Vector[Relation]])((sofar, argument) =>
        sofar.flatMap((done, current) => of(argument, frame, current).map((relation, after) => (done :+ relation, after)))
      )
      .flatMap((relations, after) =>
        val waiting = relations.foldLeft(Map.empty[Int, Set[CallIdentity]])((made, relation) => GroupProgram.merged(made, relation.waiting))
        val rows = IArray.from((0 until frame.rowCount).filterNot(waiting.contains))
        val (asked, answered, calls) = backend.asked(after.memo, recursion, rows, relations.map(_.table))
        val identifiedState =
          if calls.rows.isEmpty then after.copy(memo = asked)
          else
            after.copy(
              memo = asked,
              readBacks = after.readBacks.copy(
                identityCalls = after.readBacks.identityCalls + 1,
                identityPairs = after.readBacks.identityPairs + calls.rows.length
              )
            )
        val missing = calls.rows.toVector.lazyZip(calls.identities.toVector).foldLeft(waiting) { case (made, (row, identity)) =>
          GroupProgram.merged(made, Map(row -> Set(CallIdentity(recursion, identity))))
        }
        made(identifiedState, answered.rowCount.toLong)(answered).map((table, last) => (Relation(table, missing), last))
      )

  /** The relations' rows together, deduplicated, with the rows any of them
    * or `waiting` waits in.
    */
  private def union(relations: Vector[Relation], waiting: Map[Int, Set[CallIdentity]], state: State): Step[Relation] =
    val rows = relations.map(_.table.rowCount.toLong).sum
    made(state, rows)(relations.map(_.table).reduceOption(backend.concatenated).getOrElse(backend.emptyTable(2))).map((table, after) =>
      (Relation(table, relations.map(_.waiting).foldLeft(waiting)(GroupProgram.merged)), after)
    )

  /** The constant at every row of the frame. */
  private def constantRelation(frame: Frame, value: GroupValue, state: State): Step[Relation] =
    made(state, frame.rowCount)(
      backend.projected(backend.computed(backend.numbered(backend.table(Vector.empty, frame.rowCount)), GroupOperation.Constant(value), Vector.empty), Vector(0, 1))
    ).map((table, after) => (Relation(table, Map.empty), after))

  /** Whether an operation kept a row for each of its input's: the run goes
    * on when it did, and stops (the steps spent so far) when a row was
    * dropped, a value the operation rejects or has no normal form for, since
    * a context consuming that value can still have an answer the block would
    * lose.
    */
  private def keptEvery(input: Table, output: Table, state: State): Either[Stopped, Unit] =
    if output.rowCount < input.rowCount then Left(Stopped(state.spent, rejected = true)) else Right(())

  /** The table made, deduplicated, when its `rows` fit in the allowance after
    * the steps spent and no stop is asked for: `make` runs only then.
    */
  private def made(state: State, rows: Long)(make: => Table): Step[Table] =
    if stop.stopRequested || rows > allowance - state.spent then Left(Stopped(state.spent, rejected = false))
    else Right((backend.unique(make), state.copy(spent = state.spent + rows)))

  /** The relation of a block's parameter, the entry's one row to each value
    * of its group: the values enter the backend as one column, and the row
    * number is the constant row 0.
    */
  private def entryRelation(group: Vector[GroupValue]): Table =
    val values = backend.table(Vector(backend.column(group)), group.size)
    backend.unique(backend.projected(backend.computed(values, GroupOperation.Constant(GroupValue.Row(0)), Vector.empty), Vector(1, 0)))

/** Why a run stopped with no value, and the steps spent: a row it would
  * drop (`rejected`, an outcome of the arguments, which another argument may
  * not meet), or its allowance about to run out or a stop asked for.
  */
private final case class Stopped(spent: Long, rejected: Boolean)

/** The parts a group program shares with its compilation. */
private object GroupProgram:

  /** The constant a compiled block reads, a storage of a natural or of a
    * 32-bit word.
    */
  def constantValue[C <: NativeSpecializer & Singleton](closed: Configured[C]): GroupValue =
    GroupCompilation.constant(closed) match
      case Some((_, value)) => value
      case None             => throw IllegalStateException(s"a compiled group block reads constants from storages only, not $closed")

  /** The operation of a binary naturals' constructor of one field. */
  def constructorOperation(name: gezi.jit.NativeName): GroupOperation = name match
    case gezi.jit.BinaryNaturalFamily.evenNative => GroupOperation.Doubled
    case gezi.jit.BinaryNaturalFamily.oddNative  => GroupOperation.DoubledAndOne
    case other                                   => throw IllegalStateException(s"no constructor of one field of the binary naturals is $other")

  /** The rows' waits together. */
  def merged(left: Map[Int, Set[CallIdentity]], right: Map[Int, Set[CallIdentity]]): Map[Int, Set[CallIdentity]] =
    right.foldLeft(left) { case (made, (row, keys)) => made.updated(row, made.getOrElse(row, Set.empty) ++ keys) }

  /** The number a row value holds. */
  def rowIndex(value: GroupValue): Int = value match
    case GroupValue.Row(index) => index
    case other                 => throw IllegalStateException(s"a relation's first column holds rows, not $other")
