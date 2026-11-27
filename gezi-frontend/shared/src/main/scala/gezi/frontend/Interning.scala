package gezi.frontend

import gezi.ir.{Configured, NativeSpecializer}

/** The counted interning of a layer. A term is the canonical object
  * of its layer and a code of its code layer (`gezi.ir.Instruction`), so
  * interning needs no table threaded through.
  */
object Interning:

  /** The application built through the specializer in scope, with the count of one operation, the interning. */
  def applicationInternedCounted[C <: NativeSpecializer & Singleton](function: Configured[C], argument: Configured[C])(using
      specializer: C
  ): Counted[Configured[C]] =
    Counted(specializer.application(function, argument), 1L)
