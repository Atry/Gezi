package com.yang_bo.gezi.generatedinputs

import hedgehog.Gen
import hedgehog.Range
import com.yang_bo.gezi.programfamilies.Configuration
import com.yang_bo.gezi.programfamilies.Configurations
import com.yang_bo.gezi.programfamilies.Item
import com.yang_bo.gezi.programfamilies.ProgramFamilies
import com.yang_bo.gezi.frontend.Term

/** Generators of the programs of the benchmark families over size, for tests of
  * the pipeline on programs other than the fixtures' powers of two.
  */
object ProgramGenerators:

  /** A family of a configuration: its name, as the fixtures name it, and its
    * program at a size.
    */
  final case class Family(
      name: String,
      configuration: Configuration,
      program: Int => Term
  )

  /** The eight size families of the two configurations, as `Configurations`
    * builds their items: numeral, list (of successor zero), chain, nested and
    * tuple of `hindley_milner_baseline`; numerals, lists (of zero) and folds of
    * `cost_comparison`.
    */
  val families: Vector[Family] = Vector(
    Family(
      "numeral",
      Configurations.hindleyMilnerBaseline,
      ProgramFamilies.numeral
    ),
    Family(
      "list",
      Configurations.hindleyMilnerBaseline,
      ProgramFamilies.listOf(ProgramFamilies.successor(ProgramFamilies.zero), _)
    ),
    Family(
      "chain",
      Configurations.hindleyMilnerBaseline,
      ProgramFamilies.chain
    ),
    Family(
      "nested",
      Configurations.hindleyMilnerBaseline,
      ProgramFamilies.nested
    ),
    Family(
      "tuple",
      Configurations.hindleyMilnerBaseline,
      ProgramFamilies.tuple
    ),
    Family("numerals", Configurations.costComparison, ProgramFamilies.numeral),
    Family(
      "lists",
      Configurations.costComparison,
      ProgramFamilies.listOf(ProgramFamilies.zero, _)
    ),
    Family("folds", Configurations.costComparison, ProgramFamilies.fold)
  )

  /** The family of the name. */
  def family(name: String): Family =
    families
      .find(_.name == name)
      .getOrElse(throw IllegalArgumentException(s"no family $name"))

  /** An item of a family at a size from 1 to `maximum`, linear in Hedgehog's
    * size and shrinking towards 1; its name is `family-size`, the fixtures'
    * when the size is a power of two. Size 1 is every family's smallest (a
    * chain and a tuple have at least one lambda and one component).
    */
  def item(family: Family, maximum: Int): Gen[Item] =
    require(maximum >= 1, s"a family's sizes start at 1: $maximum")
    Gen
      .int(Range.linear(1, maximum))
      .map(size => Item(family.name, size.toString, family.program(size)))

  /** An item of any of the eight families at a size from 1 to `maximum`. */
  def anyItem(maximum: Int): Gen[(Family, Item)] =
    for
      chosen <- Gen.element(families.head, families.tail.toList)
      generated <- item(chosen, maximum)
    yield (chosen, generated)
