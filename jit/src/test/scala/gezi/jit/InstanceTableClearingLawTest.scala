package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.jit.JitTesting.instructionOf
import gezi.jit.JitTesting.noFactsEncoding
import gezi.jit.JitTesting.sameTerms
import gezi.jit.JitTesting.randomLatticeApplication
import gezi.hotspot.Retention
import gezi.hotspot.baselines.BaselineCaches
import gezi.ir.Configured
import gezi.standardlibrary.SplitMix
import gezi.weakhead.Bounded
import gezi.weakhead.Computed
import gezi.weakhead.EvaluatorTesting
import gezi.hotspot.ExpansionSource
import gezi.weakhead.JitState
import gezi.weakhead.Mode
import gezi.weakhead.NoJitState
import gezi.weakhead.NormalForms
import gezi.weakhead.ReadingState
import gezi.weakhead.TableSharing
import gezi.ir.Value
import gezi.weakhead.Values

/** The clearing law of the instance table (`JitRunState.instanceTables`, CONTRIBUTING.md, "Tables"): emptying the table changes only cost. A term
  * read after other terms, with the table and its costs those readings left,
  * the term itself among them at a drawn place, reads the normal forms it
  * reads from an empty table, whenever both readings finish. Its purpose is
  * to catch an entry that changes an answer: a key that two different
  * instances share (a key that leaves out a filling, or compares one by
  * anything weaker than its equality), or heads kept from a reading the
  * budget stopped. Checked under each retention of the state
  * (`InstanceRetention`): the default generation, generations of one entry,
  * so that nearly every recording drops the old generation and nearly every
  * hit is in the old one, which catches a dropped or promoted entry that
  * changes an answer, and never dropped; and under each with the readings
  * sharing their complete tables in one cache service of each retention
  * (`TableSharing.Shared`),
  * the last reading against one with an empty table and nothing shared, which
  * catches a table kept in the service under a namespace that leaves out an
  * input its heads depend on. The inputs are random closed applications with
  * choices and parallels (`JitTesting.randomLatticeApplication`), of sizes
  * 2 to 30, none to four others read before the last besides itself.
  */
class InstanceTableClearingLawTest extends GeneratedProperties:

  private val limit: Long = 20000

  private val encoding = noFactsEncoding

  private given encoding.type = encoding

  private val terms: Gen[Value[encoding.type]] =
    for
      size <- Gen.int(Range.linear(2, 30))
      seed <- Gen.long(Range.linear(0L, Long.MaxValue))
    yield Values.ofInstruction(instructionOf(randomLatticeApplication(size, SplitMix(seed))._1), Set.empty)

  private val retentions: Vector[(String, InstanceRetention)] =
    Vector(
      ("the default generation", InstanceRetention.Generations(JitConfiguration.defaultInstanceTableGeneration)),
      ("generations of one entry", InstanceRetention.Generations(1)),
      ("never dropped", InstanceRetention.NeverDropped)
    )

  /** Where the readings keep their complete tables: in their state alone, or
    * also in a new cache service of each retention, the same service for
    * every reading of one check.
    */
  private val sharings: Vector[(String, () => TableSharing)] =
    ("kept in the state alone", () => TableSharing.Local) +:
      Retention.values.toVector.map(retention =>
        (s"shared under $retention", () => TableSharing.Shared(BaselineCaches.provider(), retention, ExpansionSource.fresh()))
      )

  /** The normal forms of the value read within `limit` from the JIT state
    * and with the sharing given, and the state the reading left.
    */
  private def read(jit: Jit[encoding.type], value: Value[encoding.type], jitState: JitState[encoding.type], sharing: TableSharing): (Bounded[Vector[Configured[encoding.type]]], JitState[encoding.type]) =
    NormalForms.normalForms(Mode.Jit, value).result(ReadingState.fresh(limit, jit.readingConfiguration).copy(jitState = jitState, sharing = sharing)) match
      case Computed.Done(normalForms, after) => (Bounded.Finished(normalForms.sorted(gezi.ir.ContentComparison.ordering)), after.jitState)
      case Computed.Stopped(after)           => (EvaluatorTesting.stopped(after), after.jitState)

  for
    (retentionName, retention) <- retentions
    (sharingName, sharing) <- sharings
  do
    val configuration = JitConfiguration[encoding.type](
      encoding,
      10000,
      PredicatePerCode,
      ClosureBackend,
      DispatchMode.NoDispatch,
      instanceTable = true,
      instanceRetention = retention,
      storageAccess = gezi.ir.StorageAccess.granted()
    )
    property(s"a term read from a filled instance table reads what it reads from an empty one, under $retentionName, $sharingName") {
      for
        others <- Gen.list(terms, Range.linear(0, 4)).forAll
        last <- terms.forAll
        position <- Gen.int(Range.constant(0, others.size)).forAll
      yield
        val jit = Jit(configuration)
        val shared = sharing()
        val earlier = others.take(position) ++ (last :: others.drop(position))
        val filled = earlier.foldLeft(NoJitState: JitState[encoding.type])((jitState, value) => read(jit, value, jitState, shared)._2)
        (read(jit, last, filled, shared)._1, read(jit, last, NoJitState, TableSharing.Local)._1) match
          case (Bounded.Finished(fromFilled), Bounded.Finished(fromEmpty)) => Result.assert(sameTerms(fromFilled, fromEmpty))
          case _                                                           => Result.success
    }
