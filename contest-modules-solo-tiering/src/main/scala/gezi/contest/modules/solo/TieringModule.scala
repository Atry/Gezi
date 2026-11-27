package gezi.contest.modules.solo

import java.nio.file.Path
import gezi.contest.entry.Defaults
import gezi.contest.entry.EntryDataError
import gezi.contest.entry.ExecutorModule
import gezi.contest.entry.ExecutorModuleInputs
import gezi.hotspot.Executor
import gezi.ir.{Configured, NativeSpecializer, NoFacts, Value}
import gezi.knowledgereading.KnowledgeReading
import gezi.knowledgereading.KnowledgeReadingError
import gezi.narrowblocks.ProgramCompiler

/** The executor module of the tiered executor: the framework's reading executor
  * of the entry's JIT (`Defaults.executor`) for both tiers, the program
  * compiler of the entry's lemma rounds (`ProgramCompiler` of
  * `ExecutorModuleInputs.compilation`), and the policy `InterpretFirst` with
  * the interpretation's steps the entry writes. An entry selects it together
  * with the option that has the executor, not the entry, compile its programs;
  * under the entry's compilation the executor would only ever see compiled
  * programs.
  */
final class TieringModule extends ExecutorModule:

  def selectorFile: Path =
    Path.of("corpora", "modules", "solo_tiering.lambdalattice")

  /** The tiered executor of the inputs. The parameters are a tuple of one
    * field, the interpretation's steps, a non-negative integer of 64 bits (`λs.
    * s n`, n written by the library's integer `from_cbor`). Throws
    * `EntryDataError` for other parameters.
    */
  def executor[C <: NativeSpecializer & Singleton](
      parameters: Configured[NoFacts.type],
      inputs: ExecutorModuleInputs[C]
  ): Executor[C, ?] =
    given NoFacts.type = NoFacts
    val steps =
      try
        KnowledgeReading.run(
          KnowledgeReading.fields(Value.of(parameters), 1).flatMap {
            case Vector(steps) => KnowledgeReading.integer(steps)
            case fields        =>
              throw EntryDataError(
                s"solo's tiering module's parameters have ${fields.size} fields, not 1"
              )
          },
          TieringModule.parametersReadingLimit
        )
      catch
        case KnowledgeReadingError(reason) =>
          throw EntryDataError(s"solo's tiering module's parameters: $reason")
    if steps < 0 || !steps.isValidLong then
      throw EntryDataError(
        s"solo's tiering module's interpretation steps are $steps, not a non-negative integer of 64 bits"
      )
    TieredExecutor[C](
      inputs.jit.configuration.specializer,
      Defaults.executor(inputs.jit, inputs.reading),
      ProgramCompiler(inputs.compilation),
      InterpretFirst(inputs.compilation, steps.toLong)
    )

object TieringModule:

  /** The evaluator steps reading the parameters may take: a tuple of one
    * integer of at most 64 bits, a handful of steps a bit, the limit the
    * framework's test modules read theirs within
    * (`TestModuleParameters.readingLimit`).
    */
  val parametersReadingLimit: Long = 10000L
