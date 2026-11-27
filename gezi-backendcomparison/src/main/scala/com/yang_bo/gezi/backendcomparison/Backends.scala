package com.yang_bo.gezi.backendcomparison

import com.yang_bo.gezi.ematching.bytecode.BytecodeCompilation
import com.yang_bo.gezi.ematching.closures.ClosureCompilation
import com.yang_bo.gezi.ematching.interpretation.Interpretation
import com.yang_bo.gezi.ematching.Backend

/** The backends the application can run, by the name of their module, and the
  * one it runs when none is named.
  */
object Backends:

  val byName: Vector[(String, Backend)] = Vector(
    "interpretation" -> Interpretation,
    "closure-compilation" -> ClosureCompilation,
    "bytecode-compilation" -> BytecodeCompilation
  )

  val defaultName: String = "closure-compilation"

  def named(name: String): Backend =
    byName
      .collectFirst {
        case (backendName, backend) if backendName == name => backend
      }
      .getOrElse(
        throw IllegalArgumentException(
          s"no backend named $name; the backends are ${byName.map(_._1).mkString(", ")}"
        )
      )
