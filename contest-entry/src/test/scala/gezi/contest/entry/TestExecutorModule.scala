package gezi.contest.entry

import java.nio.file.Path
import gezi.hotspot.Budget
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.Executor
import gezi.hotspot.Progress
import gezi.ir.Instruction
import gezi.knowledgereading.KnowledgeReading
import gezi.knowledgereading.KnowledgeReadingError
import gezi.narrowblocks.ProgramCompilation
import gezi.weakhead.ReadingSuspension

/** The executor module of contest-entry's tests (`ExecutorModuleLawTest`),
  * registered with `java.util.ServiceLoader` in the tests' resources: its
  * selector is the one field of tests/executor_module_fixtures/test_executor,
  * and its executor is the framework's (`Defaults.executor`) carrying the
  * parameter the entry wrote, a tuple of one integer the module reads by
  * structure, and the compilation the framework handed it, so that a test
  * sees which parameters and which compilation reached it.
  */
final class TestExecutorModule extends ExecutorModule:

  def selectorFile: Path = Path.of("tests", "executor_module_fixtures", "test_executor.lambdalattice")

  /** The framework's executor of the inputs, carrying the integer the
    * parameters' one field holds and the inputs' compilation. Throws
    * `EntryDataError` for parameters that are no tuple of one integer.
    */
  def executor(parameters: Instruction, inputs: ExecutorModuleInputs): Executor[?] =
    ParameterCarryingExecutor(
      TestModuleParameters.integer("executor", parameters),
      inputs.compilation,
      Defaults.executor(inputs.jit, inputs.reading)
    )

/** How the test modules of contest-entry's tests (`TestExecutorModule`,
  * `TestExtractorModule`) read the parameters an entry wrote: a tuple of one
  * integer, read by structure.
  */
object TestModuleParameters:

  /** The evaluator steps reading the parameters may take: a tuple of one
    * Scott integer of at most 64 bits, a handful of steps a bit.
    */
  val readingLimit: Long = 10000L

  /** The integer the parameters' one field holds. Throws `EntryDataError`,
    * naming the module's interface, for parameters that are no tuple of one
    * integer.
    */
  def integer(interface: String, parameters: Instruction): BigInt =
    try
      KnowledgeReading.run(
        KnowledgeReading.fields(parameters, 1).flatMap {
          case Vector(field) => KnowledgeReading.integer(field)
          case other         => throw EntryDataError(s"the test $interface's parameters have ${other.size} fields, not one")
        },
        readingLimit
      )
    catch case KnowledgeReadingError(reason) => throw EntryDataError(s"the test $interface's parameters: $reason")

/** The framework's executor with the parameter a module read and the
  * compilation it was handed: every call is the framework executor's, and
  * the executor it returns carries both again.
  */
final case class ParameterCarryingExecutor(parameter: BigInt, compilation: ProgramCompilation, framework: Executor[ReadingSuspension])
    extends Executor[ReadingSuspension]:

  def executed(
      term: Instruction,
      dependencies: ExecutionDependencies,
      budget: Budget
  ): (Executor[ReadingSuspension], ExecutionDependencies, Progress[ReadingSuspension]) =
    val (next, after, progress) = framework.executed(term, dependencies, budget)
    (copy(framework = next), after, progress)

  def resumed(
      suspension: ReadingSuspension,
      dependencies: ExecutionDependencies,
      budget: Budget
  ): (Executor[ReadingSuspension], ExecutionDependencies, Progress[ReadingSuspension]) =
    val (next, after, progress) = framework.resumed(suspension, dependencies, budget)
    (copy(framework = next), after, progress)

  def exported(suspension: ReadingSuspension, dependencies: ExecutionDependencies): (ExecutionDependencies, Option[Instruction]) =
    framework.exported(suspension, dependencies)
