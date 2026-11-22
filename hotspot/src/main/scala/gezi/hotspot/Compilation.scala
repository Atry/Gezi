package gezi.hotspot

import gezi.ir.Instruction

/** What a compiler compiles and an executor counts: a code, a closure (the instruction of a thunk layer, with its
  * fillings), or a whole program.
  */
enum CompilationUnit:
  case Code(code: gezi.ir.Code)
  case Closure(thunk: Instruction)
  case Program(root: Instruction)

/** The configuration that, with the unit, keys the artifacts a compiler
  * writes: its schedule, budget and refinement, as a value whose equality
  * tells two configurations apart; each compiler gives its own
  * implementation.
  */
trait CompilerConfiguration

/** A compiler of units of a residual term. The
  * compiler takes the types of the unit from the assertions written in the
  * residual term, reading the unit's applications, not the whole term, and
  * writes its artifact into its own namespace of the cache service under
  * `ArtifactKey(unit, configuration)`; `Artifact` is the type of what it
  * writes, so that a lookup gives an `Artifact` with no cast.
  */
trait Compiler[Artifact]:

  /** The configuration that, with the unit, keys the artifacts this
    * compiler writes.
    */
  def configuration: CompilerConfiguration

  /** The unit of the residual compiled: the compiler after it, the dependencies
    * with the artifact written into the cache service, and the cost. The stop
    * is the caller's cancel (the judge's, a fork's), read as an execution's
    * budget reads it (`Budget.stop`): a compilation it stops writes no
    * artifact, since what it would write depends on when it stopped, and
    * reports what it spent.
    */
  def compiled(
      residual: Instruction,
      unit: CompilationUnit,
      dependencies: ExecutionDependencies,
      stop: gezi.saturation.StopSignal
  ): (Compiler[Artifact], ExecutionDependencies, CompilationSpent)

/** The key of a compilation artifact in the cache service: the unit and the
  * compiler's configuration, every input of the compilation (the cache-table
  * rule, `CONTRIBUTING.md`, "Tables"). The artifact's type is part of
  * the key's type.
  */
final case class ArtifactKey[Artifact](unit: CompilationUnit, configuration: CompilerConfiguration)

/** What a compilation cost: the e-graph instances it took. */
final case class CompilationSpent(instances: Long):
  require(instances >= 0, s"a compilation's instances are not negative: $instances")
