package gezi

/** The fixed-point loop over a compiled program, whichever backend compiled it:
  * [[Saturation]] adds the inputs to the graph, matches the deltas (the
  * orientations that only unite before the others), applies every match in
  * order and works the unions and β steps after every instance, until no delta
  * is left or the budget of instances is reached; the β rule applies only when
  * the round enables it (`gezi.ir.BuiltInRule`). It gives a [[Run]] with its
  * [[End]], and knows no backend and no fixture.
  *
  * The module depends on `ematching` alone; `backendcomparison` depends on it.
  */
package object saturation
