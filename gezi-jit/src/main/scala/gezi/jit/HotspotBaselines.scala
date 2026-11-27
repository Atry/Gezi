package gezi.jit

import gezi.hotspot.CacheNamespace
import gezi.hotspot.CompilationSpent
import gezi.hotspot.CompilationUnit
import gezi.hotspot.Compiler
import gezi.hotspot.CompilerConfiguration
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.Retention
import gezi.weakhead.AnswerSet
import gezi.weakhead.ApplicationReading
import gezi.hotspot.ExpansionSource
import gezi.weakhead.KnownExtremes
import gezi.ir.Code
import gezi.ir.{Configured, NativeSpecializer}
import gezi.weakhead.Mode
import gezi.weakhead.NoJitState
import gezi.weakhead.ReadingExecutor

/** The JIT as an executor: the reader of normal forms under `Mode.Jit` of the
  * JIT, starting with no JIT state and keeping the state each execution leaves,
  * its compiled codes among them.
  */
object JitExecutor:
  def of[C <: NativeSpecializer & Singleton](jit: Jit[C]): ReadingExecutor[C] =
    ReadingExecutor(Mode.Jit, jit.readingConfiguration, NoJitState)

/** The namespace of the instance table's complete tables in the cache service:
  * a key is an instance's code and fillings (`TabledInstance`), and the
  * namespace holds every other input its heads depend on, the JIT's
  * configuration, compared by reference as `JitRunState.of` compares it, the
  * known extremes, the application reading and the expansion source, so that
  * two readings share a table only where they would compute the same one. The
  * memo of a pure function of the key under those inputs (`CONTRIBUTING.md`,
  * "Tables", kind 2): a complete table is the least fixed point of the
  * instance's reading, so clearing it changes only cost. The namespace is typed
  * by the configuration `C` and names it by reference, so its native
  * specializer (the configuration's `specializer`) is named by identity: the
  * values it holds are terms of `C` and no reading of another configuration
  * finds them.
  */
final case class CompletedInstanceNamespace[C <: NativeSpecializer & Singleton](
    configuration: JitConfiguration[C],
    extremes: KnownExtremes,
    applications: ApplicationReading,
    source: ExpansionSource,
    override val retention: Retention
) extends CacheNamespace[TabledInstance[C], AnswerSet[JitHead[C]]](
      "jit.completed_instances"
    )

/** The configuration of the JIT's compilation as the key of its artifacts: the
  * JIT's configuration, compared by reference, as `JitRunState.of` compares it
  * (a configuration is built once and passed on), since its generation strategy
  * and backend are what a code is compiled by.
  */
final case class JitCompilation[C <: NativeSpecializer & Singleton](
    configuration: JitConfiguration[C]
) extends CompilerConfiguration

/** The namespace of the JIT's compiled codes in the cache service: a code's
  * closures (`CompiledCode`) by the code, interned, under the JIT's
  * configuration, compared by reference as `JitCompilation` compares it, the
  * memo of a pure function of the code's syntax under the configuration
  * (`CONTRIBUTING.md`, "Tables", kind 2), its references as strong as the
  * retention says: under `Retention.WeakKeys` an entry goes when no one holds
  * the code. A JIT state that holds no compiled form of a code takes the one
  * found here when its reading shares its memos (`TableSharing.Shared`), so
  * that the service's lifecycle reaches the JIT's codes; the state keeps the
  * forms it took (`JitRunState.compiled`), a first level the JIT's compilation
  * budget counts.
  */
final case class CompiledCodes[C <: NativeSpecializer & Singleton](
    configuration: JitConfiguration[C],
    override val retention: Retention
) extends CacheNamespace[Code, CompiledCode[C]]("jit.compiled_codes")

/** The JIT's compilation as a compiler: a code unit compiled by the
  * configuration's generation strategy and backend (`JitRules.compiledCode`,
  * the closure backend by default) and written to `CompiledCodes` of the
  * configuration and the retention, under the code. The JIT compiles codes, so
  * a closure or a program unit is refused. A compilation reads the code's
  * syntax only and takes no e-graph instance. A reading of the JIT that shares
  * its memos under the same retention reads what this compiler writes
  * (`CompiledCodes`).
  *
  * @param jitConfiguration
  *   the configuration whose strategy and backend compile a code
  * @param retention
  *   the retention of the namespace the compiled codes are written to
  */
final case class JitCompiler[C <: NativeSpecializer & Singleton](
    jitConfiguration: JitConfiguration[C],
    retention: Retention
) extends Compiler[C, CompiledCode[C]]:

  def configuration: CompilerConfiguration = JitCompilation(jitConfiguration)

  /** The code unit compiled into the cache service; the residual is not read,
    * since a code's compilation depends on its syntax alone. Throws
    * `IllegalArgumentException` for a closure or a program unit.
    */
  def compiled(
      residual: Configured[C],
      unit: CompilationUnit[C],
      dependencies: ExecutionDependencies,
      stop: gezi.saturation.StopSignal
  ): (Compiler[C, CompiledCode[C]], ExecutionDependencies, CompilationSpent) =
    unit match
      case CompilationUnit.Code(code) =>
        dependencies.cache.locked(CompiledCodes(jitConfiguration, retention))(
          _.getOrElseUpdate(code, JitRules(jitConfiguration).compiledCode(code))
        )
        (this, dependencies, CompilationSpent(0))
      case CompilationUnit.Closure(_) | CompilationUnit.Program(_) =>
        throw IllegalArgumentException(
          s"the JIT compiles code units, not $unit"
        )
