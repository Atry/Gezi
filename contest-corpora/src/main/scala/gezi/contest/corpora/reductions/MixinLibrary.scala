package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamilies

import gezi.contest.corpora.merges
import gezi.contest.corpora.merges.Hierarchy
import gezi.frontend.Term
import java.nio.file.Path

/** The modules a program under `MixinLibrary.withMixinLibrary` refers to
  * (`merges.LibraryNames`).
  */
type MixinNames = merges.LibraryNames

/** The mixin encoding of inheritance over the hierarchies of the reduction
  * group's families: the merge group's port of
  * `problems/mixin_library` (`merges.MixinLibrary`), its
  * contributions and readers, reached by the hierarchies' names. The
  * hierarchies are the facts `hierarchy/2` of that file and of the families
  * that declare their own, read as data; a hierarchy declared other than
  * once throws where it is used, as the Prolog's `hierarchy_slots/2` does.
  */
final case class MixinLibrary(
    encoding: merges.MixinLibrary,
    hierarchies: Map[String, Vector[Vector[String]]]
):

  /** The hierarchy's one declaration of slots. */
  def slots(hierarchy: String): Vector[String] = hierarchies.getOrElse(hierarchy, Vector.empty) match
    case Vector(declared) => declared
    case declarations =>
      throw IllegalArgumentException(s"the hierarchy $hierarchy has not one declaration: $declarations")

  private def named(hierarchy: String): Hierarchy = Hierarchy(hierarchy, slots(hierarchy))

  /** `\Self. \c1. ... \cW. cm Body` (`self_mixin/5`). */
  def selfMixin(hierarchy: String, slot: String)(body: ProblemTerm => ProblemTerm): ProblemTerm =
    encoding.selfMixin(named(hierarchy), slot, body)

  /** The wrapper of each slot and value (`value_mixin/3`). */
  def valueMixin(hierarchy: String, definitions: (String, ProblemTerm)*): ProblemTerm =
    encoding.valueMixin(named(hierarchy), definitions*)

  /** The slot read from the object (`read_slot/4`). */
  def readSlot(hierarchy: String, slot: String, objectTerm: ProblemTerm): ProblemTerm =
    encoding.readSlot(named(hierarchy), slot, objectTerm)

  /** The read applied to the arguments (`slot_applied/5`). */
  def slotApplied(hierarchy: String, slot: String, objectTerm: ProblemTerm, arguments: ProblemTerm*): ProblemTerm =
    encoding.slotApplied(named(hierarchy), slot, objectTerm, arguments*)

  /** The body under the lets of the module of each library, the libraries'
    * and the given hierarchies each declared once (`with_mixin_library/5`).
    */
  def withMixinLibrary(libraries: Vector[String], hierarchies: Vector[String])(body: MixinNames => ProblemTerm): ProblemTerm =
    (hierarchies ++ libraries.flatMap(encoding.libraryHierarchies)).foreach(slots)
    encoding.withMixinLibrary(libraries, body)

  /** The class read from the library's module (`library_class/4`). */
  def libraryClass(names: MixinNames, library: String, className: String): ProblemTerm =
    encoding.libraryClass(names, library, className)

  /** The class read from the one library of the program that has it
    * (`library_class/3`).
    */
  def libraryClass(names: MixinNames, className: String): ProblemTerm = encoding.libraryClass(names, className)

  /** The natural of the library `natural` (`natural_instance/3`). */
  def naturalInstance(names: MixinNames, count: Int): ProblemTerm = encoding.naturalInstance(names, count)

  /** `{successor, predecessor : Predecessor}` (`successor_class/3`). */
  def successorClass(names: MixinNames, predecessor: ProblemTerm): ProblemTerm = encoding.successorClass(names, predecessor)

  /** The natural of the library `binary` (`binary_instance/3`). */
  def binaryInstance(names: MixinNames, count: BigInt): ProblemTerm = encoding.binaryInstance(names, count)

/** Reading the hierarchies. */
object MixinLibrary:

  /** The mixin library over the hierarchies declared in the family
    * `mixin_library` (its table `hierarchy`, whose rows are the files of
    * `mixin_library/hierarchies` it imports) and in the families given (their
    * tables `contest_mixin_library__hierarchy`), each row one declaration of
    * a name and its slots.
    */
  def read(problems: ProblemFamilies, families: Vector[String]): MixinLibrary =
    val hierarchies = (problems("mixin_library").rows("hierarchy") ++
      families.flatMap(family => problems(family).rows("contest_mixin_library__hierarchy")))
      .map {
        case Vector(name, slots) => (ProblemData.text(name), ProblemData.texts(slots))
        case other               => throw IllegalArgumentException(s"not a hierarchy: $other")
      }
      .groupMap(_._1)(_._2)
    MixinLibrary(merges.MixinLibrary(problems), hierarchies)
