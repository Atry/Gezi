package gezi.ematching

/** The backend that interprets a program: `Interpretation.compiled` keeps the
  * program as it is, and every match walks the steps of the seeds filed under
  * the delta's key, every building walks its `Building` tree, at the time it
  * runs. It depends on `ematching` alone; `backendcomparison` selects it.
  */
package object interpretation
