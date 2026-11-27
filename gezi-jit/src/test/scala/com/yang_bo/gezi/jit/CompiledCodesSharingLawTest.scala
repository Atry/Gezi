package com.yang_bo.gezi.jit

import com.yang_bo.gezi.frontend.DeBruijnTerm
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.jit.JitTesting.instructionOf
import com.yang_bo.gezi.jit.JitTesting.noFactsEncoding
import com.yang_bo.gezi.jit.JitTesting.randomLatticeApplication
import com.yang_bo.gezi.hotspot.Retention
import com.yang_bo.gezi.hotspot.baselines.BaselineCaches
import com.yang_bo.gezi.standardlibrary.SplitMix
import com.yang_bo.gezi.weakhead.Computed
import com.yang_bo.gezi.hotspot.ExpansionSource
import com.yang_bo.gezi.weakhead.JitState
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.NoJitState
import com.yang_bo.gezi.weakhead.NormalForms
import com.yang_bo.gezi.weakhead.ReadingState
import com.yang_bo.gezi.weakhead.TableSharing
import com.yang_bo.gezi.ir.Value
import com.yang_bo.gezi.weakhead.Values

/** The JIT's compiled codes in the cache service: a reading that shares its
  * memos (`TableSharing.Shared`, the strong retention, so that nothing is
  * dropped) from a new JIT state takes, for every code it runs compiled, the
  * very form an earlier reading from another new state wrote there
  * (`CompiledCodes`), and a reading over a cleared service compiles its own.
  * Its purpose is to catch a JIT that does not read the service (the defect
  * this replaced: the codes were written to one namespace and read from the
  * state alone, so the service's lifecycle never reached them) or a namespace
  * that does not hold what was compiled. That a shared form changes no answer
  * is the law of `InstanceTableClearingLawTest`, whose shared cases read
  * through the same service. The inputs are random closed applications with
  * choices and parallels (`JitTesting.randomLatticeApplication`), of sizes 2 to
  * 30, and in every iteration `(λx. x x) (λy. y)`, whose β step reads the body
  * `x x` as an instance of its code, which the JIT compiles at its first
  * instance (`Jit.untabledInstance`); that its reading compiles a code is
  * asserted, so that the law always has a compiled form to share.
  */
class CompiledCodesSharingLawTest extends GeneratedProperties:

  private val encoding = JitTesting.noFactsEncoding

  private given encoding.type = encoding

  private val limit: Long = 20000

  private val terms =
    for
      size <- Gen.int(Range.linear(2, 30))
      seed <- Gen.long(Range.linear(0L, Long.MaxValue))
    yield Values.ofInstruction(
      instructionOf(randomLatticeApplication(size, SplitMix(seed))._1),
      Set.empty
    )

  private val configuration =
    JitConfiguration[encoding.type](
      encoding,
      10000,
      PredicatePerCode,
      ClosureBackend,
      DispatchMode.NoDispatch,
      instanceTable = false,
      storageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()
    )

  /** The compiled forms the JIT state holds after reading the value within
    * `limit` from a new state with the sharing given, finished or stopped.
    */
  private def compiled(
      jit: Jit[encoding.type],
      value: Value[encoding.type],
      sharing: TableSharing
  ): Map[com.yang_bo.gezi.ir.Code, CompiledCode[?]] =
    val state = NormalForms
      .normalForms(Mode.Jit, value)
      .result(
        ReadingState
          .fresh(limit, jit.readingConfiguration)
          .copy(jitState = NoJitState, sharing = sharing)
      ) match
      case Computed.Done(_, after) => after.jitState
      case Computed.Stopped(after) => after.jitState
    state match
      case run: JitRunState[?] => run.compiled
      case _: JitState[?]      => Map.empty

  /** `(λx. x x) (λy. y)`: the instance of `x x` is compiled. */
  private val selfApplied: Value[encoding.type] =
    Values.ofInstruction(
      instructionOf(
        DeBruijnTerm.Apply(
          DeBruijnTerm.Lambda(
            DeBruijnTerm
              .Apply(DeBruijnTerm.Variable(0), DeBruijnTerm.Variable(0))
          ),
          DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0))
        )
      ),
      Set.empty
    )

  property(
    "a reading from a new state takes the compiled forms an earlier reading left in the shared service"
  ) {
    for value <- terms.forAll
    yield shared(value)
      .and(shared(selfApplied))
      .and(
        Result
          .assert(
            compiled(
              Jit(configuration),
              selfApplied,
              TableSharing.Local
            ).nonEmpty
          )
          .log("(λx. x x) (λy. y) compiled no code")
      )
  }

  /** The law on one value. */
  private def shared(value: Value[encoding.type]): Result =
    val jit = Jit(configuration)
    val sharing = TableSharing.Shared(
      BaselineCaches.provider(),
      Retention.Strong,
      ExpansionSource.fresh()
    )
    val first = compiled(jit, value, sharing)
    val second = compiled(jit, value, sharing)
    val cleared = compiled(
      jit,
      value,
      TableSharing.Shared(
        BaselineCaches.provider(),
        Retention.Strong,
        ExpansionSource.fresh()
      )
    )
    Result
      .assert(second.forall((code, form) => first.get(code).exists(_ eq form)))
      .log(
        s"codes the second reading compiled anew: ${second
            .count((code, form) => !first.get(code).exists(_ eq form))} of ${second.size}"
      )
      .and(
        Result
          .assert(
            cleared.forall((code, form) => !first.get(code).exists(_ eq form))
          )
          .log("a reading over a new service took a form of the first")
      )
