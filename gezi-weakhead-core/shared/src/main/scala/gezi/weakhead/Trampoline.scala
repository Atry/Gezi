package gezi.weakhead

import gezi.saturation.StopSignal
import scala.annotation.tailrec

/** A trampolined computation, as `scala.util.control.TailCalls.TailRec`,
  * whose sequencing keeps alive only what is still to run.
  *
  * Why not `TailRec`: its `flatMap` on a sequence `Cont(first, next)` builds
  * the continuation `x => c.next(x).flatMap(f)`, which captures the whole
  * sequence `c` and so its `first` step (the bytecode of Scala 3.10.0's
  * library: `TailRec.flatMap$$anonfun$2(TailCalls$Cont, Function1,
  * Object)`). The first step is a call whose thunk captured the state it was
  * given, and it stays reachable until the continuation runs, long after the
  * step itself ran. In the JIT (`gezi.jit.Jit`) a tabled instance's
  * reading is such a sequence, and an instance read inside the reading of
  * another one keeps the state of every enclosing reading alive. MEASURED
  * 2026-11-07 on main a7ab31421 (the hot ladder's `calls_100000_hot`, direct
  * spelling, read as written by `Jit` with the instance table on, a 1 GB
  * heap, CPUs 2 and 3): `OutOfMemoryError` in three runs, after 88, 37 and
  * 26 s, with JFR's object counts at the last sample before it showing
  * `Object[]` 299 MB, `BitmapIndexedSetNode` 91 MB (the versions of the set
  * of instances being read), `JitRunState` 57 MB, `ReadingState` 47 MB and
  * `TailCalls`' sequences, calls and continuations 118 MB. The same
  * retention was measured on 2026-11-03 in the copy of the JIT in the
  * module contest-modules-wren, where this trampoline first fixed it (read
  * back with `git show c78b37577:lambda_jit/contest-modules-wren`).
  *
  * Here `flatMap` only wraps the computation and its continuation in a
  * sequence, and the trampoline's run keeps the next functions of the
  * sequences it has entered on a stack of its own (`Continuation`), and
  * nothing else: a step that has run is unreachable from what follows it,
  * and a chain of sequences nested to the left, however long, is never
  * composed into nested functions that call each other on the JVM stack
  * (`TrampolineLawTest`; `TailRec`'s eager composition throws
  * `StackOverflowError` on such a chain).
  */
enum Trampoline[+Value]:

  /** The value, computed. */
  case Done(value: Value)

  /** The rest of the computation, to run when the trampoline reaches it. */
  case Call(rest: () => Trampoline[Value])

  /** The first computation, then the next one its value chooses. */
  case Sequence[First, Result](first: Trampoline[First], next: First => Trampoline[Result]) extends Trampoline[Result]

  /** This computation followed by the one its value chooses. */
  def flatMap[Next](continuation: Value => Trampoline[Next]): Trampoline[Next] = this match
    case Done(value) => Call(() => continuation(value))
    case _           => Sequence(this, continuation)

  /** This computation with its value mapped. */
  def map[Next](mapping: Value => Next): Trampoline[Next] =
    flatMap(value => Done(mapping(value)))

  /** The value, the trampoline run to its end. */
  def result: Value = Trampoline.run(this)

  /** The value, the trampoline run to its end, or `stopped` when the signal
    * asks for a stop: the signal is read every `Trampoline.stopCheckBounces`
    * bounces, and on a stop every computation still pending is dropped at
    * once, none of them run. The bounces are the one place every kind of
    * work of a computation passes through, the work no budget charges
    * included (a continuation of a tabled instance's reading, the walk of a
    * key), so the time from a stop to the return is bounded by the time of
    * those bounces and not by the depth of what is pending. MEASURED
    * 2026-11-07 on main 06f58a4e0 (`contest-entries-solo`, the hot ladder's
    * `nested_calls_1000000_hot` direct, the judge's cancel at 60 s), before
    * this check: the budget's reads of the signal (`Budget.charged`) were
    * up to 7.9 s apart, and after the stop was read the reading unwound for
    * 15 s, every pending tabled instance's continuation taking its key out
    * of the instances being read one at a time.
    */
  def resultUnless[Result >: Value](stop: StopSignal, stopped: => Result): Result =
    Trampoline.runUnless[Result](this, stop, stopped, Trampoline.stopCheckBounces)

object Trampoline:

  /** The computation of the expression, deferred to the trampoline. */
  def tailcall[Value](rest: => Trampoline[Value]): Trampoline[Value] = Call(() => rest)

  /** The value, computed. */
  def done[Value](value: Value): Trampoline[Value] = Done(value)

  /** The bounces between two reads of the stop signal in `resultUnless`.
    * MEASURED 2026-11-07 (the nested points of the comment on
    * `resultUnless`, a stop at 60 s, a 3 GB heap, an unloaded machine): at
    * 4,096 the reading returned 1.2 to 4.2 s after the stop, late bounces
    * being expensive (a key's walk, a large key's hash, a clause's
    * compilation); at 64 the 10^6 direct point returned 0.16 s after it,
    * the longest time between two reads 0.67 s. The cost of a read on the
    * hot path is `TrampolineStopBenchmark`'s (jmh-pipeline).
    */
  val stopCheckBounces: Int = 64

  /** What is still to run after the computation the trampoline is at: the
    * next functions of the sequences it has entered, innermost first. A
    * sequence is entered by pushing its next function and going on with its
    * first computation, so no continuation is composed, and the step that has
    * run is unreachable from what follows it, the next functions alone being
    * kept (the reassociation of a sequence nested to the left built a
    * sequence and a composed function at every level).
    */
  private enum Continuation[-From, +To]:
    case Finished[Value]() extends Continuation[Value, Value]
    case Then[From, Middle, To](next: From => Trampoline[Middle], rest: Continuation[Middle, To]) extends Continuation[From, To]

  /** `run`, reading the stop signal when `untilCheck` bounces have passed:
    * the value `stopped` on a requested stop, the computation dropped. Its
    * bounce match repeats `run`'s rather than sharing a step function, so
    * that the hot path allocates nothing per bounce.
    */
  private def runUnless[Value](computation: Trampoline[Value], stop: StopSignal, stopped: => Value, untilCheck: Int): Value =
    runUnlessFrom(computation, Continuation.Finished[Value](), stop, stopped, untilCheck)

  @tailrec private def runUnlessFrom[Current, Value](
      computation: Trampoline[Current],
      continuation: Continuation[Current, Value],
      stop: StopSignal,
      stopped: => Value,
      untilCheck: Int
  ): Value =
    if untilCheck == 0 then
      if stop.stopRequested then stopped
      else runUnlessFrom(computation, continuation, stop, stopped, stopCheckBounces)
    else
      computation match
        case Done(value) =>
          continuation match
            case Continuation.Finished()   => value
            case Continuation.Then(next, rest) => runUnlessFrom(next(value), rest, stop, stopped, untilCheck - 1)
        case Call(rest)            => runUnlessFrom(rest(), continuation, stop, stopped, untilCheck - 1)
        case Sequence(first, next) => runUnlessFrom(first, Continuation.Then(next, continuation), stop, stopped, untilCheck - 1)

  private def run[Value](computation: Trampoline[Value]): Value = runFrom(computation, Continuation.Finished[Value]())

  @tailrec private def runFrom[Current, Value](computation: Trampoline[Current], continuation: Continuation[Current, Value]): Value =
    computation match
      case Done(value) =>
        continuation match
          case Continuation.Finished()       => value
          case Continuation.Then(next, rest) => runFrom(next(value), rest)
      case Call(rest)            => runFrom(rest(), continuation)
      case Sequence(first, next) => runFrom(first, Continuation.Then(next, continuation))
