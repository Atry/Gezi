package com.yang_bo.gezi.contest

/** The runner in a contest entry's JVM: [[EntryRunner]] loads the one
  * `EntryProvider` the entry registers with `java.util.ServiceLoader`, writes
  * the ready line and answers the points of its pipe ([[PipeLines]]) with the
  * entry, the main being `contestEntryRunner`, which first installs the seccomp
  * filter that denies the JVM the execution of programs ([[ExecutionFilter]])
  * when the supervisor's sandbox is on. The module depends on `contest-entry`
  * only, so that an entry's JVM, whose classpath is the entry's own and this
  * module's, holds neither `contest-corpora` (the generators and the
  * references) nor `contest-judge`.
  */
package object runner
