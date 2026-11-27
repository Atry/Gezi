package gezi.jit

/** How the JIT's state keeps the instance table's complete tables between the
  * instances, the readings and the heads that read them
  * (`JitRunState.instanceTables`): a choice of the entry's data, whose cost it
  * changes and never an answer, a dropped table being read again
  * (CONTRIBUTING.md, "Tables"). The state is the first level; a reading whose
  * `ReadingState.sharing` is shared also keeps complete tables in the cache
  * service, the second level, which this retention does not govern.
  */
enum InstanceRetention:

  /** Two generations: the complete tables are the young one, and when it holds
    * `size` of them it becomes the old one, the old one dropped, so that the
    * state holds at most twice `size`; an instance found in the old one is
    * completed in the young one again, so an instance met in every generation
    * stays.
    */
  case Generations(size: Int)

  /** Every complete table kept for as long as the state lives, never dropped:
    * keeping every table in memory is one of the options.
    */
  case NeverDropped
