package com.yang_bo.gezi.contest.entry.generic

import java.nio.file.Path
import com.yang_bo.gezi.contest.entry.Defaults
import com.yang_bo.gezi.contest.entry.ExecutorModule
import com.yang_bo.gezi.contest.entry.ExecutorModuleInputs
import com.yang_bo.gezi.hotspot.Budget
import com.yang_bo.gezi.hotspot.ExecutionDependencies
import com.yang_bo.gezi.hotspot.Executor
import com.yang_bo.gezi.hotspot.Progress
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NativeSpecializer
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.narrowblocks.ProgramCompilation
import com.yang_bo.gezi.weakhead.ReadingSuspension

/** The executor module of `CompilationPlaceLawTest`, given to the entry's table
  * of modules by the test rather than registered with
  * `java.util.ServiceLoader`: its selector is the one field of
  * tests/executor_module_fixtures/program_recording_executor, it reads no
  * parameter, and its executor is the framework's (`Defaults.executor`)
  * recording the compilation the framework handed it and every program it is
  * given to read, so that a test sees what reached the executor.
  */
final class ProgramRecordingModule extends ExecutorModule:

  def selectorFile: Path = Path.of(
    "tests",
    "executor_module_fixtures",
    "program_recording_executor.lambdalattice"
  )

  def executor[C <: NativeSpecializer & Singleton](
      parameters: Configured[NoFacts.type],
      inputs: ExecutorModuleInputs[C]
  ): Executor[C, ?] =
    ProgramRecordingExecutor(
      inputs.compilation,
      Vector.empty,
      Defaults.executor(inputs.jit, inputs.reading)
    )

/** The framework's executor with the compilation a module was handed and the
  * programs it was given to read, in order: every call is the framework
  * executor's, and the executor it returns carries both again, the program of
  * an execution added.
  */
final case class ProgramRecordingExecutor[C <: NativeSpecializer & Singleton](
    compilation: ProgramCompilation[C],
    received: Vector[Configured[C]],
    framework: Executor[C, ReadingSuspension[C]]
) extends Executor[C, ReadingSuspension[C]]:

  def executed(
      term: Configured[C],
      dependencies: ExecutionDependencies,
      budget: Budget
  ): (
      Executor[C, ReadingSuspension[C]],
      ExecutionDependencies,
      Progress[C, ReadingSuspension[C]]
  ) =
    val (next, after, progress) = framework.executed(term, dependencies, budget)
    (copy(received = received :+ term, framework = next), after, progress)

  def resumed(
      suspension: ReadingSuspension[C],
      dependencies: ExecutionDependencies,
      budget: Budget
  ): (
      Executor[C, ReadingSuspension[C]],
      ExecutionDependencies,
      Progress[C, ReadingSuspension[C]]
  ) =
    val (next, after, progress) =
      framework.resumed(suspension, dependencies, budget)
    (copy(framework = next), after, progress)

  def exported(
      suspension: ReadingSuspension[C],
      dependencies: ExecutionDependencies
  ): (ExecutionDependencies, Option[Configured[C]]) =
    framework.exported(suspension, dependencies)
