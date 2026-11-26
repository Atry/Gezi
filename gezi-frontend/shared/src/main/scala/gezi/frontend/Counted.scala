package gezi.frontend

/** A result with the deterministic count of the operations that made it: the
  * nodes a walk visited and the layers and codes it interned. The
  * count is returned as a value, never kept in global state; it stands in for
  * the inferences the Prolog front end's tests measured
  * (`hindley_milner_baseline.plt`,
  * `the_front_ends_inferences_an_element_costs_do_not_grow`), so that a walk
  * that visits a node or interns more often than the term's size
  * requires shows in the count.
  */
final case class Counted[+Value](value: Value, operations: Long)
