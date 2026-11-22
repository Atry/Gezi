package gezi.programfamilies

import gezi.frontend.Term

/** One item of a configuration: a program of a family at a size, or a
  * coverage program named in place of a size. Its name, `family-size`, is
  * the name of its fixture and of its line in a file of fixed points.
  */
final case class Item(family: String, size: String, program: Term):

  /** `family-size`, as the Prolog exporter named the item's fixture. */
  def name: String = s"$family-$size"

/** A configuration of the program families: its fixture file under Gezi's directory, whose member
  * `knowledge` is the knowledge its library compiles and whose member
  * `enabled` is the knowledge whose lemmas its runs enable, each a term of
  * the file and not a choice the host assembles from paths; the
  * budget of every run in instances; and its items. Native typing and its
  * backend are enabled together as one preset of the module system
  * (`CONTRIBUTING.md`, "Efficiency by design, with native structures"), so a fixture will enable that preset
  * once it is written instead of listing typing knowledge files.
  */
final case class Configuration(
    name: String,
    knowledgeFile: String,
    budget: Int,
    items: Vector[Item]
)

/** The two configurations, as the Prolog exporter of the fixtures built them
  * in its mode `fixtures`.
  */
object Configurations:

  /** The budget of every run, 1,000,000 instances.
    */
  val budget: Int = 1000000

  /** The sizes of a size family, 1, 2, 4, ..., 1024 (`mode_size(fixtures,
    * Size)`).
    */
  val sizes: Vector[Int] = (0 to 10).map(exponent => 1 << exponent).toVector

  private def sizeFamily(family: String, program: Int => Term): Vector[Item] =
    sizes.map(size => Item(family, size.toString, program(size)))

  /** The library and the knowledge of `gezi/tests/hindley_milner_baseline.plt`,
    * `[native_types, hindley_milner_unions]`, compiled and enabled (the
    * fixture `tests/program_family_fixtures/hindley_milner_baseline.lambdalattice`);
    * the families numeral, list, chain, nested and tuple of
    * `fixpoint_verdicts:family_value/3`.
    */
  val hindleyMilnerBaseline: Configuration = Configuration(
    "hindley_milner_baseline",
    "tests/program_family_fixtures/hindley_milner_baseline.lambdalattice",
    budget,
    sizeFamily("numeral", ProgramFamilies.numeral) ++
      sizeFamily("list", ProgramFamilies.listOf(ProgramFamilies.successor(ProgramFamilies.zero), _)) ++
      sizeFamily("chain", ProgramFamilies.chain) ++
      sizeFamily("nested", ProgramFamilies.nested) ++
      sizeFamily("tuple", ProgramFamilies.tuple)
  )

  /** The native route's library (`saturation_runs:native_route_library/1`)
    * and the knowledge of the saturation options of the type-checking round
    * of `native_route_schedule/3`, `[hindley_milner_unions,
    * native_arithmetic_unions]`, as the Prolog cost comparison read them (the fixture `tests/program_family_fixtures/cost_comparison.lambdalattice`);
    * the families numerals, lists and folds of that file's `program/3`, and
    * coverage, every program of `fixpoint_verdicts:coverage_program/3`,
    * named by its first argument.
    */
  val costComparison: Configuration = Configuration(
    "cost_comparison",
    "tests/program_family_fixtures/cost_comparison.lambdalattice",
    budget,
    sizeFamily("numerals", ProgramFamilies.numeral) ++
      sizeFamily("lists", ProgramFamilies.listOf(ProgramFamilies.zero, _)) ++
      sizeFamily("folds", ProgramFamilies.fold) ++
      ProgramFamilies.coverage.map((name, program) => Item("coverage", name, program))
  )

  /** Both configurations. */
  val all: Vector[Configuration] = Vector(hindleyMilnerBaseline, costComparison)
