package gezi.contest.modules.moore

import java.nio.file.Path
import gezi.contest.entry.Defaults
import gezi.contest.entry.EntryDataError
import gezi.contest.entry.ExecutorModule
import gezi.contest.entry.ExecutorModuleInputs
import gezi.hotspot.Executor
import gezi.ir.{Configured, NativeSpecializer, NoFacts, Pure, Value}
import gezi.knowledgereading.KnowledgeReading
import gezi.knowledgereading.KnowledgeReadingError
import gezi.weakhead.Computation

/** The criteria an FFI program is read by, the module's parameters
  * (`corpora/library/java_ffi/moore_parameters`).
  *
  * @param state
  *   the criterion of one step of a Moore machine
  * @param methodSymbols
  *   the library's function from a method to its symbols
  * @param symbols
  *   the criterion of a method's symbols
  * @param boolean
  *   the criterion of the JVM's boolean
  * @param bits8
  *   the criterion of a value type of 8 bits
  * @param bits16
  *   the criterion of a value type of 16 bits
  * @param bits32
  *   the criterion of a value type of 32 bits
  * @param bits64
  *   the criterion of a value type of 64 bits
  */
final case class MooreCriteria[C <: NativeSpecializer & Singleton](
    state: Configured[C],
    methodSymbols: Configured[C],
    symbols: Configured[C],
    boolean: Configured[C],
    bits8: Configured[C],
    bits16: Configured[C],
    bits32: Configured[C],
    bits64: Configured[C]
)

/** The executor module that runs FFI programs: the framework's
  * reading executor of the entry's JIT (`Defaults.executor`), which reads
  * every other program as it does, and `MooreExecutor` for a Moore machine
  * state. An entry selects it by the constructor `module` of the executors'
  * list, with the parameters of `corpora/library/java_ffi/moore_parameters`,
  * and enables the knowledge `corpora/compiler/java_ffi`, whose data families
  * the criteria name.
  */
final class MooreModule extends ExecutorModule:

  def selectorFile: Path = Path.of("corpora", "modules", "moore.lambdalattice")

  /** The executor of the inputs. Throws `EntryDataError` for parameters that
    * are no tuple of the eight fields of `MooreCriteria`.
    */
  def executor[C <: NativeSpecializer & Singleton](parameters: Configured[NoFacts.type], inputs: ExecutorModuleInputs[C]): Executor[C, ?] =
    given NoFacts.type = NoFacts
    val specializer = inputs.jit.configuration.specializer
    // A criterion is a library term, a pure key, the same under every configuration: read under no facts, then
    // brought into the entry's by `Configured.fromPure`. A criterion that is no pure term is a bad configuration.
    def criterion(term: gezi.ir.Value[NoFacts.type]): Configured[C] =
      Pure
        .of(KnowledgeReading.term(term, Set.empty))
        .map(Configured.fromPure(specializer))
        .getOrElse(throw EntryDataError("the Moore module's criteria are library terms with no parallel"))
    val criteria =
      try
        KnowledgeReading.run(
          KnowledgeReading.fields(Value.of(parameters), 8).flatMap {
            case Vector(state, methodSymbols, symbols, boolean, bits8, bits16, bits32, bits64) =>
              Computation.pure(
                MooreCriteria[C](
                  criterion(state),
                  criterion(methodSymbols),
                  criterion(symbols),
                  criterion(boolean),
                  criterion(bits8),
                  criterion(bits16),
                  criterion(bits32),
                  criterion(bits64)
                )
              )
            case fields => throw EntryDataError(s"the Moore module's parameters have ${fields.size} fields, not 8")
          },
          MooreModule.parametersReadingLimit
        )
      catch case KnowledgeReadingError(reason) => throw EntryDataError(s"the Moore module's parameters: $reason")
    MooreExecutor[C](Defaults.executor(inputs.jit, inputs.reading), inputs.jit, criteria)

object MooreModule:

  /** The evaluator steps reading the parameters may take: a tuple of eight
    * fields, each read to its head, the limit the framework's test modules
    * read theirs within (`TestModuleParameters.readingLimit`).
    */
  val parametersReadingLimit: Long = 10000L
