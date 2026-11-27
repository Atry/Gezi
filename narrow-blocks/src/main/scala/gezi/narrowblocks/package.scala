package gezi

/** The narrow back end: the narrow grammar's check ([[NarrowBlocks]],
  * [[NarrowKind]]), the compilation of a program's narrow blocks to JVM
  * bytecode ([[NarrowBlockCompilation]]), whose blocks call an entry's natives
  * through `gezi.jit.StaticBlockMethod`, the lemma compilation's round
  * ([[LemmaCompilation]]), and the lemma route ([[LemmaRoute]]), which runs the
  * round, compiles and runs the blocks of its extraction and puts their
  * numerals back into the program, and the baseline compiler of a program unit
  * ([[ProgramCompiler]]), whose artifact is the program an entry reads after
  * its lemma rounds. Moved from a module of the base natives into the
  * framework; every entry and module depends on it
  * (project/EntryProjects.scala). It names no contributed native: an entry
  * hands it its `NativeBackend`.
  */
package object narrowblocks
