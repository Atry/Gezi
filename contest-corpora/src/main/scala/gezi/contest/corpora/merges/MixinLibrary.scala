package gezi.contest.corpora.merges

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamilies
import gezi.contest.corpora.common.ProblemField

import gezi.frontend.Term
import gezi.frontend.Term.*

/** A hierarchy of the mixin encoding: its name and its slot names, in order;
  * its width is their count, and a slot's position stands for its label
  * (`contest_mixin_library:hierarchy/2`).
  */
final case class Hierarchy(name: String, slots: Vector[String]):

  if slots.distinct.length != slots.length then
    throw IllegalArgumentException(s"the hierarchy $name names a slot twice: $slots")

  /** The number of slots. */
  def width: Int = slots.length

  /** The position of the slot, from 0. Throws when the hierarchy has no such
    * slot.
    */
  def index(slot: String): Int =
    val found = slots.indexOf(slot)
    if found < 0 then throw IllegalArgumentException(s"the hierarchy $name has no slot $slot")
    found

/** A library's module as a program lets it: the library, the hierarchy of
  * its module and the variable the program refers to it by
  * (`module(Library, Hierarchy, Variable)`).
  */
final case class LibraryModule(library: String, hierarchy: Hierarchy, variable: Term)

/** The modules a program under `MixinLibrary.withMixinLibrary` refers to
  * (`names(Modules)`).
  */
final case class LibraryNames(modules: Vector[LibraryModule])

/** The port of the deleted Prolog file
  * (`git show 91b3f11e1^:lambda_jit/corpora/contest_mixin_library.pl`; its data are
  * `problems/mixin_library`): the mixin
  * encoding of inheritance in lambda plus choice, with no label. A wrapper
  * is `\self. \c1. ... \cW. cm b`, slot m defined by b; a mixin, a class and
  * an object are choices of wrappers; reading slot m of an object o is the
  * self-application `o o c1 ... cW`, cm the handler and every other c top,
  * the term of no answer (the FIXME at `readHandled`). A library is a module, an object whose slots are its
  * classes, each file of the library one mixin of the module.
  *
  * The library's hierarchies, its files, its modules and the Booleans are
  * data of the family `gezi/problems/mixin_library` and are read from
  * it; the contributions of the files
  * and the readers are ported here.
  */
final class MixinLibrary(problems: ProblemFamilies):

  private val file = problems("mixin_library")

  /** The hierarchy the file declares under the name (`hierarchy/2`): the
    * one row of the table `hierarchy`, each row a file of
    * `mixin_library/hierarchies` the table imports, whose name field is the
    * name. The name is the host's, which points into the data from outside.
    */
  def hierarchy(name: String): Hierarchy =
    file.rowsWith("hierarchy", Map(0 -> name)) match
      case Vector(fields) => declared(fields)
      case found =>
        throw IllegalArgumentException(s"the hierarchy $name has ${found.length} declarations, not one")

  /** The hierarchy a row of `hierarchy/2` writes: its name, a text, and its
    * slot names, a list of texts.
    */
  private def declared(fields: Vector[ProblemField]): Hierarchy = fields match
    case Vector(name, slots) => Hierarchy(ProblemData.text(name), ProblemData.texts(slots))
    case other => throw IllegalArgumentException(s"a hierarchy row has ${other.size} fields, not two")

  /** The hierarchy of Booleans: church, not, conjunction, equality. */
  val boolean: Hierarchy = hierarchy("boolean")

  /** The hierarchy of unary naturals. */
  val natural: Hierarchy = hierarchy("natural")

  /** The hierarchy of binary naturals. */
  val binary: Hierarchy = hierarchy("binary")

  /** `\t. \f. t`. */
  def trueTerm: Term = file.program("true_term")

  /** `\t. \f. f`. */
  def falseTerm: Term = file.program("false_term")

  private def fileAtoms(predicate: String, library: String): Vector[String] =
    file.rowsWith(predicate, Map(0 -> library)) match
      case Vector(arguments) => ProblemData.texts(arguments(1))
      case found => throw IllegalArgumentException(s"$predicate has ${found.length} facts for $library")

  /** The hierarchy of the library's module (`library_module/2`): the
    * row's second field is the hierarchy row itself, a file of
    * `mixin_library/hierarchies` imported by omega, read as a record of the
    * hierarchy's name and slots (`ProblemData.alternative`), not looked up
    * by a name.
    */
  def libraryModule(library: String): Hierarchy =
    file.rowsWith("library_module", Map(0 -> library)) match
      case Vector(Vector(_, module)) => declared(ProblemData.alternative(module, 1)._2)
      case Vector(fields) =>
        throw IllegalArgumentException(s"the row of library_module for $library has ${fields.size} fields, not two")
      case found =>throw IllegalArgumentException(s"library_module has ${found.length} facts for $library")

  /** The files of the library, in order (`library_files/2`). */
  def libraryFiles(library: String): Vector[String] = fileAtoms("library_files", library)

  /** The hierarchies the library's programs read (`library_hierarchies/2`). */
  def libraryHierarchies(library: String): Vector[String] = fileAtoms("library_hierarchies", library)

  /** `\self. \c1. ... \cW. cm body`, the slot the m-th of the hierarchy and
    * the body a function of self (`self_mixin/5`).
    */
  def selfMixin(hierarchy: Hierarchy, slot: String, body: Term => Term): Term =
    val index = hierarchy.index(slot)
    def handlers(bound: Vector[Term], self: Term): Term =
      if bound.length == hierarchy.width then bound(index)(body(self))
      else λ(handler => handlers(bound :+ handler, self))
    λ(self => handlers(Vector.empty, self))

  /** The wrapper of each `slot -> value` of the definitions, each value
    * reading nothing of self: the wrapper itself for one definition, the
    * choice of them for several (`value_mixin/3`). Throws on none.
    */
  def valueMixin(hierarchy: Hierarchy, definitions: (String, Term)*): Term =
    definitions.map((slot, value) => selfMixin(hierarchy, slot, _ => value)).toVector match
      case Vector()       => throw IllegalArgumentException("a value mixin defines a slot")
      case Vector(single) => single
      case several        => choice(several*)

  /** The slot read from the object, `o o c1 ... cW` with the identity for
    * the slot's handler (`read_slot/4`).
    */
  def readSlot(hierarchy: Hierarchy, slot: String, objectTerm: Term): Term =
    readHandled(hierarchy, slot, objectTerm, λ(value => value))

  /** The read applied to the arguments, with the handler
    * `\v. v a1 ... ak` (`slot_applied/5`). Throws on no argument.
    */
  def slotApplied(hierarchy: Hierarchy, slot: String, objectTerm: Term, arguments: Term*): Term =
    if arguments.isEmpty then throw IllegalArgumentException(s"$slot is applied to no argument")
    readHandled(hierarchy, slot, objectTerm, λ(value => arguments.foldLeft(value)(_(_))))

  /** `o o c1 ... cW`; an object that is not a variable let bound first,
    * `(\o. o o c1 ... cW) Object` (`read_handled/5`).
    *
    * An unhandled slot's handler is top, the term of no answer (`Term.top`).
    *
    * FIXME (2026-11-10, measured with top in place of `{}`, the record of no https://github.com/Atry/private-overlay/issues/1990
    * entries, which the language no longer has): the mixin families read 43
    * to 68 times the steps under weak_head and 21 of their 34 programs that
    * finished within 2,000,000 steps no longer do: `top M` is `top ∥ M`, a
    * parallel head that takes every pending argument and that the reader
    * peels one argument at a time, where `{} M` had no head
    * (three ways forward are open, none decided). The same holds for
    * the failure of `MixinDatalog.guard`.
    */
  private def readHandled(hierarchy: Hierarchy, slot: String, objectTerm: Term, handler: Term): Term =
    val index = hierarchy.index(slot)
    val handlers = (0 until hierarchy.width).map(position => if position == index then handler else Term.top)
    def read(bound: Term): Term = handlers.foldLeft(bound(bound))(_(_))
    objectTerm match
      case Term.BoundVariable(_) => read(objectTerm)
      case _                     => λ(bound => read(bound))(objectTerm)

  /** The body under the lets of the module of each library
    * (`with_mixin_library/5`): the body refers to the modules by the names
    * it is given.
    */
  def withMixinLibrary(libraries: Vector[String], body: LibraryNames => Term): Term =
    def bound(remaining: Vector[String], modules: Vector[LibraryModule]): Term =
      if remaining.isEmpty then body(LibraryNames(modules))
      else
        val library = remaining.head
        val hierarchy = libraryModule(library)
        λ(variable => bound(remaining.tail, modules :+ LibraryModule(library, hierarchy, variable)))(
          choice(libraryFiles(library).map(fileMixin(hierarchy, _))*)
        )
    bound(libraries, Vector.empty)

  /** The library's class read from its module (`library_class/4`). */
  def libraryClass(names: LibraryNames, library: String, className: String): Term =
    names.modules.find(_.library == library) match
      case Some(module) => readSlot(module.hierarchy, className, module.variable)
      case None         => throw IllegalArgumentException(s"the program lets no library $library")

  /** The class of the one library of the program that has it
    * (`library_class/3`).
    */
  def libraryClass(names: LibraryNames, className: String): Term =
    names.modules.filter(_.hierarchy.slots.contains(className)) match
      case Vector(module) => readSlot(module.hierarchy, className, module.variable)
      case found =>
        throw IllegalArgumentException(s"${found.length} libraries of the program have the class $className")

  /** The natural `count` of the library `natural`: zero, or `{successor,
    * predecessor : n}` (`natural_instance/3`).
    */
  def naturalInstance(names: LibraryNames, count: Int): Term =
    require(count >= 0, s"a natural is not negative: $count")
    (1 to count).foldLeft(libraryClass(names, "natural", "zero"))((predecessor, _) =>
      successorClass(names, predecessor)
    )

  /** `{successor, predecessor : predecessor}` (`successor_class/3`). */
  def successorClass(names: LibraryNames, predecessor: Term): Term =
    choice(libraryClass(names, "natural", "successor"), valueMixin(natural, "predecessor" -> predecessor))

  /** `count` of the library `binary`, least significant bit outermost: zero,
    * `{even, half : h}` or `{odd, half_of_predecessor : h}`
    * (`binary_instance/3`).
    */
  def binaryInstance(names: LibraryNames, count: BigInt): Term =
    require(count >= 0, s"a natural is not negative: $count")
    if count == 0 then libraryClass(names, "binary", "zero")
    else
      val half = binaryInstance(names, count / 2)
      if count % 2 == 0 then
        choice(libraryClass(names, "binary", "even"), valueMixin(binary, "half" -> half))
      else
        choice(libraryClass(names, "binary", "odd"), valueMixin(binary, "half_of_predecessor" -> half))

  // ---- the library modules ----

  /** The module mixin of one library file: a wrapper of each class the file
    * contributes to, whose body is the contribution over the module's self
    * (`library_file_mixin/4`).
    */
  private def fileMixin(moduleHierarchy: Hierarchy, fileName: String): Term =
    moduleHierarchy.slots.flatMap(className =>
      contribution(fileName, className).map(body => selfMixin(moduleHierarchy, className, module =>
        body(ModuleContext(moduleHierarchy, module))
      ))
    ) match
      case Vector()       => throw IllegalArgumentException(s"the library file $fileName contributes nothing")
      case Vector(single) => single
      case several        => choice(several*)

  /** The module's hierarchy and its self, which a contribution reads its
    * classes through.
    */
  private final case class ModuleContext(hierarchy: Hierarchy, module: Term):
    def moduleClass(className: String): Term = readSlot(hierarchy, className, module)

  /** The file's contribution to the class, as a function of the module's
    * context (`contribution/4`).
    */
  private def contribution(fileName: String, className: String): Option[ModuleContext => Term] =
    (fileName, className) match
      case ("boolean_data", "true")  => Some(_ => valueMixin(boolean, "church" -> trueTerm))
      case ("boolean_data", "false") => Some(_ => valueMixin(boolean, "church" -> falseTerm))
      case ("boolean_negation", "true") =>
        Some(context => valueMixin(boolean, "not" -> context.moduleClass("false")))
      case ("boolean_negation", "false") =>
        Some(context => valueMixin(boolean, "not" -> context.moduleClass("true")))
      case ("boolean_and", "true") => Some(_ => valueMixin(boolean, "conjunction" -> λ(other => other)))
      case ("boolean_and", "false") =>
        Some(context => valueMixin(boolean, "conjunction" -> λ(_ => context.moduleClass("false"))))
      case ("boolean_equality", "true") => Some(_ => valueMixin(boolean, "equality" -> λ(other => other)))
      case ("boolean_equality", "false") =>
        Some(_ => valueMixin(boolean, "equality" -> λ(other => readSlot(boolean, "not", other))))
      case ("natural_data", "zero") => Some(_ => valueMixin(natural, "scott" -> λ(zero => λ(_ => zero))))
      case ("natural_data", "successor") =>
        Some(_ =>
          selfMixin(natural, "scott", self =>
            λ(_ => λ(successor => successor(readSlot(natural, "scott", readSlot(natural, "predecessor", self)))))
          )
        )
      case ("natural_visitor", "zero") =>
        Some(_ => valueMixin(natural, "accept" -> λ(onZero => λ(_ => onZero))))
      case ("natural_visitor", "successor") =>
        Some(_ =>
          selfMixin(natural, "accept", self =>
            λ(_ => λ(onSuccessor => onSuccessor(readSlot(natural, "predecessor", self))))
          )
        )
      case ("natural_plus", "zero") => Some(_ => valueMixin(natural, "plus" -> λ(addend => addend)))
      case ("natural_plus", "successor") =>
        Some(context =>
          selfMixin(natural, "plus", self =>
            λ(addend =>
              slotApplied(
                natural,
                "plus",
                readSlot(natural, "predecessor", self),
                choice(context.moduleClass("successor"), valueMixin(natural, "predecessor" -> addend))
              )
            )
          )
        )
      case ("natural_equality", "zero") =>
        Some(context =>
          valueMixin(
            natural,
            "equality" -> λ(other =>
              slotApplied(natural, "accept", other, context.moduleClass("true"), λ(_ => context.moduleClass("false")))
            )
          )
        )
      case ("natural_equality", "successor") =>
        Some(context =>
          selfMixin(natural, "equality", self =>
            λ(other =>
              slotApplied(
                natural,
                "accept",
                other,
                context.moduleClass("false"),
                λ(otherPredecessor =>
                  slotApplied(natural, "equality", readSlot(natural, "predecessor", self), otherPredecessor)
                )
              )
            )
          )
        )
      case ("binary_increment", "zero") =>
        Some(context =>
          valueMixin(
            binary,
            "increment" -> binaryFieldClass(context, "odd", "half_of_predecessor", context.moduleClass("zero"))
          )
        )
      case ("binary_increment", "even") =>
        Some(context =>
          selfMixin(binary, "increment", self =>
            binaryFieldClass(context, "odd", "half_of_predecessor", readSlot(binary, "half", self))
          )
        )
      case ("binary_increment", "odd") =>
        Some(context =>
          selfMixin(binary, "increment", self =>
            binaryFieldClass(
              context,
              "even",
              "half",
              readSlot(binary, "increment", readSlot(binary, "half_of_predecessor", self))
            )
          )
        )
      case ("binary_visitor", "zero") =>
        Some(_ => valueMixin(binary, "accept" -> λ(onZero => λ(_ => λ(_ => onZero)))))
      case ("binary_visitor", "even") =>
        Some(_ =>
          selfMixin(binary, "accept", self => λ(_ => λ(onEven => λ(_ => onEven(readSlot(binary, "half", self))))))
        )
      case ("binary_visitor", "odd") =>
        Some(_ =>
          selfMixin(binary, "accept", self =>
            λ(_ => λ(_ => λ(onOdd => onOdd(readSlot(binary, "half_of_predecessor", self)))))
          )
        )
      case ("binary_plus", "zero") => Some(_ => valueMixin(binary, "plus" -> λ(addend => addend)))
      // 2h + 0 = 2h, 2h + 2k = 2(h + k), 2h + 2k + 1 = 2(h + k) + 1.
      case ("binary_plus", "even") =>
        Some(context =>
          selfMixin(binary, "plus", self =>
            λ(addend =>
              slotApplied(
                binary,
                "accept",
                addend,
                self,
                λ(k1 => halfSum(context, "even", "half", readSlot(binary, "half", self), k1)),
                λ(k2 => halfSum(context, "odd", "half_of_predecessor", readSlot(binary, "half", self), k2))
              )
            )
          )
        )
      // 2h + 1 + 0 = 2h + 1, 2h + 1 + 2k = 2(h + k) + 1,
      // 2h + 1 + 2k + 1 = 2((h + k) + 1).
      case ("binary_plus", "odd") =>
        Some(context =>
          selfMixin(binary, "plus", self =>
            λ(addend =>
              slotApplied(
                binary,
                "accept",
                addend,
                self,
                λ(k1 =>
                  halfSum(context, "odd", "half_of_predecessor", readSlot(binary, "half_of_predecessor", self), k1)
                ),
                λ(k2 =>
                  binaryFieldClass(
                    context,
                    "even",
                    "half",
                    readSlot(binary, "increment", slotApplied(binary, "plus", readSlot(binary, "half_of_predecessor", self), k2))
                  )
                )
              )
            )
          )
        )
      case ("binary_equality", "zero") =>
        Some(context =>
          valueMixin(
            binary,
            "equality" -> λ(other =>
              slotApplied(
                binary,
                "accept",
                other,
                context.moduleClass("true"),
                λ(_ => context.moduleClass("false")),
                λ(_ => context.moduleClass("false"))
              )
            )
          )
        )
      case ("binary_equality", "even") =>
        Some(context =>
          selfMixin(binary, "equality", self =>
            λ(other =>
              slotApplied(
                binary,
                "accept",
                other,
                context.moduleClass("false"),
                λ(k => slotApplied(binary, "equality", readSlot(binary, "half", self), k)),
                λ(_ => context.moduleClass("false"))
              )
            )
          )
        )
      case ("binary_equality", "odd") =>
        Some(context =>
          selfMixin(binary, "equality", self =>
            λ(other =>
              slotApplied(
                binary,
                "accept",
                other,
                context.moduleClass("false"),
                λ(_ => context.moduleClass("false")),
                λ(k => slotApplied(binary, "equality", readSlot(binary, "half_of_predecessor", self), k))
              )
            )
          )
        )
      // 0 m = 0; 2h m = h m + h m; (2h + 1) m = (h m + h m) + m, each h m
      // read anew where it is used.
      case ("binary_times", "zero") =>
        Some(context => valueMixin(binary, "times" -> λ(_ => context.moduleClass("zero"))))
      case ("binary_times", "even") =>
        Some(_ => selfMixin(binary, "times", self => λ(multiplicand => doubledHalfProduct(self, "half", multiplicand))))
      case ("binary_times", "odd") =>
        Some(_ =>
          selfMixin(binary, "times", self =>
            λ(multiplicand =>
              slotApplied(binary, "plus", doubledHalfProduct(self, "half_of_predecessor", multiplicand), multiplicand)
            )
          )
        )
      case _ => None

  /** The object `{class, field : half.plus(addendHalf)}` (`half_sum/6`). */
  private def halfSum(context: ModuleContext, className: String, field: String, half: Term, addendHalf: Term): Term =
    binaryFieldClass(context, className, field, slotApplied(binary, "plus", half, addendHalf))

  /** `(h m).plus(h m)`, h self's field, read at each use
    * (`doubled_half_product/4`).
    */
  private def doubledHalfProduct(self: Term, field: String, multiplicand: Term): Term =
    val halfProduct = slotApplied(binary, "times", readSlot(binary, field, self), multiplicand)
    val halfProductAgain = slotApplied(binary, "times", readSlot(binary, field, self), multiplicand)
    slotApplied(binary, "plus", halfProductAgain, halfProduct)

  /** The class `{class, field : value}`, the class read through the module's
    * self (`binary_field_class/5`).
    */
  private def binaryFieldClass(context: ModuleContext, className: String, field: String, value: Term): Term =
    choice(context.moduleClass(className), valueMixin(binary, field -> value))
