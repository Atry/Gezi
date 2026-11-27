package gezi.contest.modules

/** The reusable modules of `contest-modules-solo-tiering`: the tiered executor
  * (`TieredExecutor`), which reads a program by the interpreting executor,
  * compiles it into the cache service, or reads what is compiled, as a tiering
  * policy decides from measured costs; the policy `InterpretFirst`, which
  * interprets within a number of steps and compiles only a program whose
  * interpretation does not finish in them; and the executor module that an
  * entry's data selects them by (`TieringModule`, its selector
  * `corpora/modules/solo_tiering`).
  */
package object solo
