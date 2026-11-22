package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.jit.JitTesting.instructionOf
import gezi.jit.JitTesting.noFacts
import gezi.jit.JitTesting.randomLatticeApplication
import gezi.hotspot.Retention
import gezi.hotspot.baselines.BaselineCaches
import gezi.standardlibrary.SplitMix
import gezi.weakhead.Computed
import gezi.hotspot.ExpansionSource
import gezi.weakhead.JitState
import gezi.weakhead.Mode
import gezi.weakhead.NoJitState
import gezi.weakhead.NormalForms
import gezi.weakhead.ReadingState
import gezi.weakhead.TableSharing
import gezi.weakhead.Value
import gezi.weakhead.Values

/** The JIT's compiled codes in the cache service:
  * a reading that
  * shares its memos (`TableSharing.Shared`, the strong retention, so that
  * nothing is dropped) from a new JIT state takes, for every code it runs
  * compiled, the very form an earlier reading from another new state wrote
  * there (`CompiledCodes`), and a reading over a cleared service compiles
  * its own. Its purpose is to catch a JIT that does not read the service
  * (the defect this replaced: the codes were written to one namespace and
  * read from the state alone, so the service's lifecycle never reached
  * them) or a namespace that does not hold what was compiled. That a shared
  * form changes no answer is the law of `InstanceTableClearingLawTest`, whose
  * shared cases read through the same service. The inputs are random closed
  * applications with choices and parallels
  * (`JitTesting.randomLatticeApplication`), of sizes 2 to 30.
  */
class CompiledCodesSharingLawTest extends GeneratedProperties:

  private val limit: Long = 20000

  private val terms =
    for
      size <- Gen.int(Range.linear(2, 30))
      seed <- Gen.long(Range.linear(0L, Long.MaxValue))
    yield Values.ofInstruction(instructionOf(randomLatticeApplication(size, SplitMix(seed))._1), Set.empty)

  private val configuration =
    JitConfiguration(noFacts, 10000, PredicatePerCode, ClosureBackend, DispatchMode.NoDispatch, instanceTable = false)

  /** The compiled forms the JIT state holds after reading the value within
    * `limit` from a new state with the sharing given, finished or stopped.
    */
  private def compiled(jit: Jit, value: Value, sharing: TableSharing): Map[gezi.ir.Code, CompiledCode] =
    val state = NormalForms.normalForms(Mode.Jit(jit), value).result(ReadingState.fresh(limit).copy(jitState = NoJitState, sharing = sharing)) match
      case Computed.Done(_, after)  => after.jitState
      case Computed.Stopped(after) => after.jitState
    state match
      case run: JitRunState => run.compiled
      case _: JitState      => Map.empty

  property("a reading from a new state takes the compiled forms an earlier reading left in the shared service") {
    for
      value <- terms.forAll
        .cover(20, "the reading compiles a code", value => compiled(Jit(configuration), value, TableSharing.Local).nonEmpty)
    yield
      val jit = Jit(configuration)
      val sharing = TableSharing.Shared(BaselineCaches.provider(), Retention.Strong, ExpansionSource.fresh())
      val first = compiled(jit, value, sharing)
      val second = compiled(jit, value, sharing)
      val cleared = compiled(jit, value, TableSharing.Shared(BaselineCaches.provider(), Retention.Strong, ExpansionSource.fresh()))
      Result
        .assert(second.forall((code, form) => first.get(code).exists(_ eq form)))
        .log(s"codes the second reading compiled anew: ${second.count((code, form) => !first.get(code).exists(_ eq form))} of ${second.size}")
        .and(Result.assert(cleared.forall((code, form) => !first.get(code).exists(_ eq form))).log("a reading over a new service took a form of the first"))
  }
