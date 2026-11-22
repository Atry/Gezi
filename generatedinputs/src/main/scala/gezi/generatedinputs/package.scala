package gezi

/** The infrastructure of generated test inputs: [[GeneratedProperties]]
  * checks a law with Hedgehog in a munit suite, [[SeededSamples]] draws
  * reproducible samples from a fixed seed, [[SeededSnapshots]] records
  * generated inputs with their outputs in one snapshot, and
  * [[StateMachine]] folds a generated sequence of commands over a system
  * and a model. The generators of a module's own data live in that module's
  * test sources, in this package: closed terms in the higher-order abstract
  * syntax (`HoasGenerators`), their lambdalattice text
  * (`LambdalatticeText`) and inputs with one planted defect
  * (`PlantedDefects`) in `frontend`; library configurations in
  * `standardlibrary`; the programs of the benchmark families in
  * `programfamilies`; stores in `ir`; and orientations in
  * `backendcomparison`.
  *
  * The tests of `standardlibrary` and of the modules above it reach the
  * generators of `frontend` and `standardlibrary` through their test
  * dependencies.
  *
  * The module depends on no module of this build; the tests of every other
  * module depend on it.
  */
package object generatedinputs
