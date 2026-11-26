package gezi.strategies

import gezi.ir.NativeSpecializer

/** The baseline's modules of a normality degree: the HM baseline's six,
  * rows 1 to 6 of `table`, `weak_redexes` of the breadth rounds, and `specialization_attraction` of
  * the native route's compilation. A caller that runs with them gives this
  * table to the strategy; the framework names none of them.
  */
object BaselineModules:

  def table[C <: NativeSpecializer & Singleton]: Vector[NormalityModule[C]] = Vector(
    FilterAttraction.at[C],
    ChoiceAttraction.at[C],
    KnownConstructorLookups.at[C],
    OrdinaryFilters.at[C],
    InputFilterRepulsion.at[C],
    Compression.at[C],
    WeakRedexes.at[C],
    SpecializationAttraction.at[C]
  )
