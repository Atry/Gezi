package gezi.strategies

/** The baseline's modules of a normality degree: the HM baseline's six,
  * rows 1 to 6 of `table`, `weak_redexes` of the breadth rounds, and `specialization_attraction` of
  * the native route's compilation. A caller that runs with them gives this
  * table to the strategy; the framework names none of them.
  */
object BaselineModules:

  val table: Vector[NormalityModule] = Vector(
    FilterAttraction,
    ChoiceAttraction,
    KnownConstructorLookups,
    OrdinaryFilters,
    InputFilterRepulsion,
    Compression,
    WeakRedexes,
    SpecializationAttraction
  )
