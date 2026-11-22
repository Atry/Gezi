package gezi.contest.modules.solo

import gezi.hotspot.ArtifactKey
import gezi.hotspot.Budget
import gezi.hotspot.Cache
import gezi.hotspot.CompilationUnit
import gezi.hotspot.CompilerConfiguration
import gezi.hotspot.Decision
import gezi.hotspot.Spent
import gezi.hotspot.TieringPolicy
import gezi.ir.Instruction
import gezi.narrowblocks.ProgramArtifacts
import gezi.saturation.StopSignal

/** The tiering policy: interpret a program within a few evaluator steps, and compile it with
  * the entry's lemma rounds only when the interpretation does not finish in
  * them; run what is compiled once it is in the cache service.
  *
  * The rounds cost more than the reading on most programs that the
  * interpretation alone finishes, and they are what makes the hot ones run
  * at all: on the published families read at main f11aff827, the better of the
  * two for each point scores about 4.1 above compiling every program, all of
  * whose losses are on programs whose interpretation does not finish
  * (readings of 2026-11-21).
  *
  * The policy reads costs only: the steps spent on the program so far, and
  * whether the cache service holds the program's artifact under the
  * compiler's configuration. It reads the program only as the key of that
  * artifact and as the unit it names to compile.
  *
  * @param configuration
  *   the configuration of the compiler whose artifacts the policy looks up
  *   (`gezi.narrowblocks.ProgramCompiler`'s)
  * @param interpretationSteps
  *   the evaluator steps the interpretation of a program may spend before
  *   the policy compiles it
  */
final case class InterpretFirst(configuration: CompilerConfiguration, interpretationSteps: Long) extends TieringPolicy:
  require(interpretationSteps >= 0, s"the interpretation's steps are not negative: $interpretationSteps")

  /** Run the compiled program when its artifact is in the cache service;
    * else interpret it within the steps left of `interpretationSteps`; else
    * compile it. A decision's budget is the most the policy allows; the
    * tiered executor takes the caller's stop and caps its steps by the
    * caller's (`TieredExecutor`).
    */
  def decided(program: CompilationUnit.Program, spent: Spent, cache: Cache): Decision =
    val compiled = cache.locked(ProgramArtifacts)(_.tryGet(ArtifactKey[Instruction](program, configuration))).isDefined
    if compiled then Decision.RunCompiled(Budget(Long.MaxValue, countedUnits = false, StopSignal.NeverStopped))
    else if spent.steps < interpretationSteps then
      Decision.Interpret(Budget(interpretationSteps - spent.steps, countedUnits = false, StopSignal.NeverStopped))
    else Decision.Compile(Vector(program))
