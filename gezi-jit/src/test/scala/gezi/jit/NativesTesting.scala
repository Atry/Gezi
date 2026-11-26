package gezi.jit

import gezi.weakhead.BigIntegerCodec
import gezi.weakhead.BooleanCodec
import gezi.weakhead.Bounded
import gezi.weakhead.ListCodec
import gezi.weakhead.ListConstructor
import gezi.weakhead.NaturalConstructor
import gezi.weakhead.Computed
import gezi.weakhead.EvaluatorTesting
import gezi.weakhead.JitState
import gezi.weakhead.Mode
import gezi.weakhead.NoJitState
import gezi.weakhead.NormalForms
import gezi.weakhead.ReadOut
import gezi.weakhead.ReadingState
import gezi.weakhead.Value
import gezi.standardlibrary.LibraryFiles
import gezi.standardlibrary.StandardLibrary
import gezi.ir.Instruction
import gezi.frontend.Term

/** A bounded reading's outcome, the steps it took and the JIT state it left. */
final case class Spent[Result](outcome: Bounded[Result], steps: Long, jitState: JitState)

/** How the reference's read-out by membership ended on a normal form
  * (reference_reads_within/4).
  */
enum Confirmation:
  case Confirmed
  case NotRead
  case Exceeded

/** What the tests of the natives share (the helpers of
  * `gezi/tests/jit_natives.plt` and `saturation_runs.pl`): the native
  * route's library compiled with the backend's knowledge modules, the
  * closure filter_by, bounded readings under
  * the reference and the JIT, and the reference's read-out by membership.
  */
object NativesTesting:

  /** The names of the standard set's codec constructors that the tests
    * count calls of: each its family's representation and its position.
    */
  val zeroNative: NativeName = NativeName.Constructor(BigIntegerFamily.identity, BigIntegerCodec.position(NaturalConstructor.Zero))
  val successorNative: NativeName = NativeName.Constructor(BigIntegerFamily.identity, BigIntegerCodec.position(NaturalConstructor.Successor))
  val trueNative: NativeName = NativeName.Constructor(BooleanFamily.identity, BooleanCodec.position(true))
  val falseNative: NativeName = NativeName.Constructor(BooleanFamily.identity, BooleanCodec.position(false))
  val nilNative: NativeName = NativeName.Constructor(Representation.listFamily, ListCodec.position(ListConstructor.Nil))
  val consNative: NativeName = NativeName.Constructor(Representation.listFamily, ListCodec.position(ListConstructor.Cons))

  /** The file of the native route's knowledge, relative to Gezi's
    * root: the choice of the Prolog backend's preset (its backend and the
    * native typing of the types it represents,
    * `corpora/compiler/prolog_backend_preset.lambdalattice`) with
    * closure_application and occurrence_erasure, which type no native type,
    * the one field of the file's tuple. Native typing is enabled through the
    * preset only.
    */
  val presetsFile: String = "tests/library_fixtures/presets.lambdalattice"

  /** The native route's library with the backend's modules (natives on),
    * checked by the backend: the knowledge of `presetsFile`
    * (`LibraryFiles.compiled`); a test's programs reach the library's terms
    * as members of `JitTesting.libraryTermsFile`, never by name.
    */
  lazy val nativesOn: StandardLibrary =
    LibraryFiles.compiled(presetsFile, Vector(BackendChecks))

  /** The configuration of the library under the budget. */
  def configurationOf(library: StandardLibrary, budget: Int = JitConfiguration.defaultBudget): JitConfiguration =
    JitTesting.configured(BackendFacts.of(library), budget)

  /** filter_by, the closure λt.λx. x ∥ t, which a program applies to a
    * criterion and an operand (jit_natives.plt, FILTER_BY).
    */
  val filterBy: Term = Term.λ(criterion => Term.λ(operand => operand ∥ criterion))

  // TODO: surfaceInstruction and surfaceValue stood here. Their purpose: the IR and the plain value of a closed
  // Prolog surface term over the names of the library's declared files and filter_by (surface_instruction/2). They
  // named library terms by LibraryFiles.namedInstruction and LibraryFiles.declaredDirectories, a free variable
  // (blacklisted) and a table of library files deleted when the library became files reached by paths. Their replacement reads the library terms it needs as members of a fixture file under tests/ by
  // projection and composes them with the HOAS case of a closed instruction. The deleted code:
  // git show 2908bffd5:lambda_jit/jit/src/test/scala/lambdajit/jit/NativesTesting.scala.

  /** The distinct normal forms of the value under the mode, sorted by text,
    * within the limit, from the JIT state given.
    */
  def normalFormsSpent(mode: Mode, value: Value, limit: Long, jitState: JitState = NoJitState): Spent[Vector[Instruction]] =
    NormalForms.normalForms(mode, value).result(ReadingState.fresh(limit).copy(jitState = jitState)) match
      case Computed.Done(normalForms, after) => Spent(Bounded.Finished(normalForms.sortBy(_.toString)), after.budget.spent, after.jitState)
      case Computed.Stopped(after)           => Spent(EvaluatorTesting.stopped(after), after.budget.spent, after.jitState)

  /** The steps a normal-form reading of the natives' tests may take: the
    * Prolog tests read within 10,000,000 inferences; the Scala readings that
    * finish take far fewer steps (the largest measured by the tests is
    * printed by them), and a step is a coarser unit than an inference.
    */
  val normalFormLimit: Long = 2000000

  /** The steps the reference's read-out by membership may take to confirm a
    * normal form the JIT read (the Prolog tests confirmed within 10,000,000
    * inferences). MEASURED 2026-10-31 on the fixtures and the 200 random
    * terms: every confirmation that finishes takes at most a few hundred
    * steps, and the two random terms whose read-out does not finish (a
    * choice whose member false is searched for among the naturals, A CHOICE
    * RESOLUTION) still had not at 300,000 steps, which took 50 seconds each:
    * the read-out of `false ∥ nat_type` builds ever larger naturals, so its
    * steps cost more as it runs. Those terms are confirmed on a choice
    * resolution, so a count far above the finished readings and far below
    * the costly ones serves the check.
    */
  val confirmationLimit: Long = 20000

  /** The reference's read-out by membership under tabling(weak_head) reads
    * the normal form of the value within the limit
    * (reference_reads_within/4).
    */
  def referenceReads(value: Value, normalForm: Instruction, limit: Long): Confirmation =
    NormalForms
      .normalForm(Mode.TablingWeakHead, ReadOut.Membership, value)
      .exists(found => gezi.weakhead.Computation.pure(found == normalForm))
      .result(ReadingState.fresh(limit)) match
      case Computed.Done(true, _)  => Confirmation.Confirmed
      case Computed.Done(false, _) => Confirmation.NotRead
      case Computed.Stopped(_)     => Confirmation.Exceeded

  /** The distinct normal forms the reference's read-out by membership reads
    * of the value under weak_head, sorted by text, within the limit
    * (membership_normal_forms_read/2).
    */
  def membershipNormalForms(value: Value, limit: Long): Bounded[Vector[Instruction]] =
    NormalForms
      .normalForm(Mode.TablingWeakHead, ReadOut.Membership, value)
      .collected
      .result(ReadingState.fresh(limit)) match
      case Computed.Done(found, _) => Bounded.Finished(found.distinct.sortBy(_.toString))
      case Computed.Stopped(after) => EvaluatorTesting.stopped(after)
