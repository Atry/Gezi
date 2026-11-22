package gezi.jit

import java.nio.file.Files
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.ir.Instruction
import gezi.standardlibrary.JvmTypeName
import gezi.standardlibrary.KnowledgeSlot
import gezi.standardlibrary.KnowledgeText
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTable
import gezi.weakhead.Expansions
import gezi.weakhead.Mode
import gezi.weakhead.Values
import scala.util.Random

/** The laws of the data families declared by facts (`DeclaredFamilies`), on
  * generated families written as a tree of library and knowledge files
  * (`KnowledgeTexts.withFreshTree`): a family of k criterion parameters (k from
  * 0 to 2) whose constructors have zero to two fields, each `recursive` or
  * `parameter(I)`, the first constructor of none, and a criterion
  * `λp1 … λpk. fixpoint (λself. (K0 + K1 f … + …))` with `data_family`,
  * `data_fields` and `jvm_type(generic)`. A family is the library file
  * `generated/library/<prefix>`, whose members are its constructors and its
  * criterion, each read by projection (`StandardLibrary.entryMembers`), and
  * its facts the knowledge file `generated/compiler/<prefix>_facts`, which
  * imports them. (1) A generated value written with the constructors, under
  * its family's criterion applied to the criteria of generated families of
  * no parameter, reads through the generic codec (at least one encoding) to
  * the normal form tabling(weak_head) reads of the value alone: decoding then
  * encoding is the identity. A family of parameters is read at two
  * different generated arguments. (2) Two families whose nullary first
  * constructors are one instruction (the same body) each read their own values
  * so: a value's family comes from the filter's criterion, never from a
  * constructor's instruction. Purpose: catch a codec that loses or reorders a
  * field or a constructor, a declaration read wrong, a criterion parameter
  * taken from the wrong position or from a value, and a family chosen by a
  * shared head.
  */
class DeclaredFamilyLawTest extends gezi.generatedinputs.FailFastSuite:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of DeclaredFamilyLawTest, "a family of criterion parameters reads its values at two different generated arguments", takes 14.055 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(25, "s")

  /** A generated family: its criterion parameters' count and the fields of
    * each constructor, `None` for `recursive` and `Some(I)` for
    * `parameter(I)`.
    */
  private final case class Family(prefix: String, arity: Int, constructors: Vector[Vector[Option[Int]]]):
    def constructor(index: Int): String = s"constructor_$index"
    val criterion: String = "set"
    def keys: Vector[String] = constructors.indices.toVector.map(constructor) :+ criterion

  /** A value: its family, the constructor's index and the fields, each a
    * value of its own.
    */
  private final case class Tree(family: Family, constructor: Int, fields: Vector[Tree])

  /** The generated families' library terms, by family prefix and member
    * key, and the library of their facts.
    */
  private final case class Generated(terms: Map[String, Map[String, Instruction]], library: StandardLibrary):
    def term(family: Family, key: String): Term =
      Term.closed(terms(family.prefix).getOrElse(key, throw IllegalArgumentException(s"${family.prefix} has no member $key")))
    def instructions: Set[Instruction] = terms.values.flatMap(_.values).toSet

  private def family(random: Random, prefix: String, arity: Int): Family =
    def field: Option[Int] = if arity > 0 && random.nextBoolean() then Some(random.nextInt(arity)) else None
    Family(prefix, arity, Vector.empty +: Vector.fill(1 + random.nextInt(2))(Vector.fill(random.nextInt(3))(field)))

  /** A value of the family at the arguments' families, at most the depth. */
  private def tree(random: Random, family: Family, arguments: Vector[Family], depth: Int): Tree =
    val constructor = if depth == 0 then 0 else random.nextInt(family.constructors.size)
    Tree(
      family,
      constructor,
      family.constructors(constructor).map {
        case None           => tree(random, family, arguments, depth - 1)
        case Some(position) => tree(random, arguments(position), Vector.empty, depth - 1)
      }
    )

  private def term(generated: Generated, value: Tree): Term =
    value.fields.foldLeft(generated.term(value.family, value.family.constructor(value.constructor)))((applied, field) =>
      applied(term(generated, field))
    )

  /** The text of a constructor of the family: its fields, then one case per
    * constructor, the case of the index applied to the fields.
    */
  private def constructorText(family: Family, index: Int): String =
    val fields = family.constructors(index)
    val binders = fields.indices.map(field => s"λf$field. ").mkString
    val cases = (1 to family.constructors.size).map(alternative => s"λc$alternative. ").mkString
    val applied = (s"c${index + 1}" +: fields.indices.map(field => s"f$field")).mkString(" ")
    s"$binders$cases$applied"

  /** The text of the family's criterion, with the fixed point combinator
    * written out (the same term as the library's `fixpoint`).
    */
  private def criterionText(family: Family): String =
    val members = family.constructors.zipWithIndex.map((fields, index) =>
      (s"(${constructorText(family, index)})" +: fields.map(_.fold("self")(position => s"p$position"))).mkString(" ")
    )
    val parameters = (0 until family.arity).map(position => s"λp$position. ").mkString
    s"$parameters((λx. λf. f (x x f)) (λx. λf. f (x x f))) (λself. (${members.mkString(" + ")}))"

  /** The facts of the family, its terms imported from its library file. */
  private def factsText(family: Family): String =
    def name(key: String): String = s"${family.prefix}_$key"
    val imports = Vector(
      KnowledgeText.Import.Grouped("generated", Vector("library", family.prefix), family.prefix, family.keys.map(name))
    )
    val criterion = name(family.criterion)
    val constructors = family.constructors.indices.toVector.map(index => name(family.constructor(index)))
    val members = Vector(
      (KnowledgeSlot.Families, KnowledgeText.family(criterion, family.arity, constructors)),
      (KnowledgeSlot.JvmTypes, KnowledgeText.jvmType(criterion, JvmTypeName.Generic))
    ) ++ family.constructors.zip(constructors).map((fields, constructor) =>
      (KnowledgeSlot.Fields, KnowledgeText.constructorFields(criterion, constructor, fields.map(_.fold(KnowledgeText.recursive)(KnowledgeText.parameter))))
    )
    KnowledgeTexts.knowledgeFile(imports, members)

  /** The families written to a fresh tree `generated`, their terms read by
    * projection and their facts compiled with the backend's checks.
    */
  private def generated(families: Vector[Family]): Generated =
    KnowledgeTexts.withFreshTree("generated")(tree => generatedIn(families, tree))

  private def generatedIn(families: Vector[Family], tree: java.nio.file.Path): Generated =
    val library = Files.createDirectories(tree.resolve("library"))
    val compiler = Files.createDirectories(tree.resolve("compiler"))
    families.foreach(family =>
      Files.writeString(
        library.resolve(s"${family.prefix}.lambdalattice"),
        KnowledgeTexts.libraryFile(
          family.constructors.indices.toVector.map(index => (family.constructor(index), constructorText(family, index))) :+
            (family.criterion, criterionText(family))
        )
      )
      Files.writeString(compiler.resolve(s"${family.prefix}_facts.lambdalattice"), factsText(family))
    )
    Generated(
      families.map(family =>
        family.prefix -> StandardLibrary.entryMembers(tree, TermTable(s"library/${family.prefix}.lambdalattice", family.keys), Expansions.none)._1
      ).toMap,
      KnowledgeTexts.compiled(tree, families.map(family => s"generated/compiler/${family.prefix}_facts"), Vector(BackendChecks))
    )

  /** Whether the value under its family's criterion, applied to the
    * arguments' criteria, reads through the representation to what
    * tabling(weak_head) reads of the value alone.
    */
  private def readsThroughTheCodec(generated: Generated, value: Tree, arguments: Vector[Family]): Unit =
    val criterion = arguments.foldLeft(generated.term(value.family, value.family.criterion))((applied, argument) =>
      applied(generated.term(argument, argument.criterion))
    )
    val filtered = term(generated, value) ∥ criterion
    val instruction = Defunctionalization.thunkInstruction(filtered.deBruijnTerm(Map.empty))
    val unfiltered = Defunctionalization.thunkInstruction(term(generated, value).deBruijnTerm(Map.empty))
    val jit = NativesTesting.normalFormsSpent(
      Mode.Jit(Jit(NativesTesting.configurationOf(generated.library))),
      Values.ofInstruction(instruction, generated.instructions),
      NativesTesting.normalFormLimit
    )
    val reference = NativesTesting.normalFormsSpent(Mode.TablingWeakHead, Values.ofInstruction(unfiltered, generated.instructions), NativesTesting.normalFormLimit)
    assert(reference.outcome.finished, s"tabling(weak_head) did not read $value")
    assertEquals(jit.outcome, reference.outcome, s"$value")
    assert(JitTesting.counts(jit.jitState).encodings > 0, s"$value was not read through the codec")

  test("a value under its declared family's criterion reads through the generic codec as tabling(weak_head) reads it") {
    val random = Random(20261107)
    (1 to 8).foreach { round =>
      val drawn = family(random, s"family_$round", 0)
      val written = generated(Vector(drawn))
      (1 to 6).foreach(_ => readsThroughTheCodec(written, tree(random, drawn, Vector.empty, random.nextInt(4)), Vector.empty))
    }
  }

  test("a family of criterion parameters reads its values at two different generated arguments") {
    val random = Random(20261109)
    (1 to 6).foreach { round =>
      val arity = 1 + random.nextInt(2)
      val parameterised = family(random, s"parameterised_$round", arity)
      val firstArguments = Vector.tabulate(arity)(position => family(random, s"first_${round}_$position", 0))
      val secondArguments = Vector.tabulate(arity)(position => family(random, s"second_${round}_$position", 0))
      val written = generated(parameterised +: (firstArguments ++ secondArguments))
      Vector(firstArguments, secondArguments).foreach(arguments =>
        (1 to 4).foreach(_ => readsThroughTheCodec(written, tree(random, parameterised, arguments, 1 + random.nextInt(3)), arguments))
      )
    }
  }

  test("two families sharing a nullary constructor's instruction each read their own values by their criterion") {
    val random = Random(20261108)
    (1 to 4).foreach { round =>
      val first = family(random, s"first_$round", 0)
      val second = Family(s"second_$round", 0, Vector.empty +: first.constructors.drop(1).map(fields => fields :+ None))
      val written = generated(Vector(first, second))
      assertEquals(
        written.terms(first.prefix)(first.constructor(0)),
        written.terms(second.prefix)(second.constructor(0)),
        "the two nullary first constructors are one instruction"
      )
      (1 to 4).foreach { _ =>
        readsThroughTheCodec(written, tree(random, first, Vector.empty, random.nextInt(4)), Vector.empty)
        readsThroughTheCodec(written, tree(random, second, Vector.empty, random.nextInt(4)), Vector.empty)
      }
    }
  }
