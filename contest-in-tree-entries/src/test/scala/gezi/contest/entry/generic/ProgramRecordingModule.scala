package gezi.contest.entry.generic

import java.nio.file.Path
import gezi.contest.entry.Defaults
import gezi.contest.entry.ExecutorModule
import gezi.contest.entry.ExecutorModuleInputs
import gezi.hotspot.Budget
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.Executor
import gezi.hotspot.Progress
import gezi.ir.Instruction
import gezi.narrowblocks.ProgramCompilation
import gezi.weakhead.ReadingSuspension

/** The executor module of `CompilationPlaceLawTest`, given to the entry's
  * table of modules by the test rather than registered with
  * `java.util.ServiceLoader`: its selector is the one field of
  * tests/executor_module_fixtures/program_recording_executor, it reads no
  * parameter, and its executor is the framework's (`Defaults.executor`)
  * recording the compilation the framework handed it and every program it is
  * given to read, so that a test sees what reached the executor.
  */
final class ProgramRecordingModule extends ExecutorModule:

  def selectorFile: Path = Path.of("tests", "executor_module_fixtures", "program_recording_executor.lambdalattice")

  def executor(parameters: Instruction, inputs: ExecutorModuleInputs): Executor[?] =
    ProgramRecordingExecutor(inputs.compilation, Vector.empty, Defaults.executor(inputs.jit, inputs.reading))

/** The framework's executor with the compilation a module was handed and the
  * programs it was given to read, in order: every call is the framework
  * executor's, and the executor it returns carries both again, the program
  * of an execution added.
  */
final case class ProgramRecordingExecutor(
    compilation: ProgramCompilation,
    received: Vector[Instruction],
    framework: Executor[ReadingSuspension]
) extends Executor[ReadingSuspension]:

  def executed(
      term: Instruction,
      dependencies: ExecutionDependencies,
      budget: Budget
  ): (Executor[ReadingSuspension], ExecutionDependencies, Progress[ReadingSuspension]) =
    val (next, after, progress) = framework.executed(term, dependencies, budget)
    (copy(received = received :+ term, framework = next), after, progress)

  def resumed(
      suspension: ReadingSuspension,
      dependencies: ExecutionDependencies,
      budget: Budget
  ): (Executor[ReadingSuspension], ExecutionDependencies, Progress[ReadingSuspension]) =
    val (next, after, progress) = framework.resumed(suspension, dependencies, budget)
    (copy(framework = next), after, progress)

  def exported(suspension: ReadingSuspension, dependencies: ExecutionDependencies): (ExecutionDependencies, Option[Instruction]) =
    framework.exported(suspension, dependencies)
