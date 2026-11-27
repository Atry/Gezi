package gezi.jit

import java.nio.file.Files
import gezi.standardlibrary.JvmTypeName
import gezi.standardlibrary.KnowledgeSlot
import gezi.standardlibrary.KnowledgeText
import gezi.standardlibrary.StandardLibrary
import scala.util.Random

/** The law of a lists' family declared by facts with `jvm_type(list)`
  * (`DeclaredFamilies`): the declaration that describes the framework's list
  * codec as it is (one criterion parameter; nil, at the position 0, of no
  * field; cons, at the position 1, of `parameter(0)` and `recursive`)
  * loads, and every generated mutation of it (the constructors swapped, the
  * arity changed, cons's fields reordered or replaced, nil given a field,
  * the specialization renamed) is rejected when the backend's facts are
  * read. Purpose: catch a reader that accepts a lists' declaration the codec
  * does not hold, which would describe lists one way and hold them another.
  */
class DeclaredListLawTest extends gezi.generatedinputs.FailFastSuite:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of DeclaredListLawTest, "every mutation of the lists' declaration is rejected when the backend's facts are read", takes 10.273 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(20, "s")

  /** The facts of the lists' declaration, as written, or mutated. */
  private final case class Declaration(
      specialization: String,
      arity: Int,
      constructors: Vector[String],
      nilFields: Vector[String],
      consFields: Vector[String]
  )

  private val described = Declaration("list", 1, Vector("nil", "cons"), Vector.empty, Vector("parameter(0)", "recursive"))

  private def mutated(random: Random): Declaration = random.nextInt(5) match
    case 0 => described.copy(constructors = described.constructors.reverse)
    case 1 => described.copy(arity = Vector(0, 2, 3)(random.nextInt(3)))
    case 2 =>
      described.copy(consFields = Vector(
        Vector("recursive", "parameter(0)"),
        Vector("parameter(0)"),
        Vector("parameter(0)", "parameter(0)"),
        Vector("recursive", "recursive")
      )(random.nextInt(4)))
    case 3 => described.copy(nilFields = Vector(Vector("recursive"), Vector("parameter(0)"))(random.nextInt(2)))
    case _ => described.copy(specialization = "other_lists")

  /** The library of nil, cons and a lists' criterion, with the
    * declaration's facts: a tree `generated` written fresh
    * (`KnowledgeTexts.withFreshTree`), the three terms the members of the
    * library file `library/lists` and the facts the knowledge file
    * `compiler/generated_facts`, which imports them.
    */
  private def library(declaration: Declaration): StandardLibrary =
    KnowledgeTexts.withFreshTree("generated")(tree => libraryIn(declaration, tree))

  private def libraryIn(declaration: Declaration, tree: java.nio.file.Path): StandardLibrary =
    Files.writeString(
      Files.createDirectories(tree.resolve("library")).resolve("lists.lambdalattice"),
      KnowledgeTexts.libraryFile(
        Vector(
          "nil" -> "λn. λc. n",
          "cons" -> "λh. λt. λn. λc. c h t",
          "generated_list_type" -> "λe. ((λx. λf. f (x x f)) (λx. λf. f (x x f))) (λl. ((λn. λc. n) + (λh. λt. λn. λc. c h t) e l))"
        )
      )
    )
    val imported = KnowledgeText.Import.Grouped(
      "generated",
      Vector("library", "lists"),
      "lists",
      Vector("nil", "cons", "generated_list_type")
    )
    def criterion(written: String): String = written match
      case "recursive" => KnowledgeText.recursive
      case parameter   => KnowledgeText.parameter(parameter.stripPrefix("parameter(").stripSuffix(")").toInt)
    def fields(constructor: String, written: Vector[String]): (KnowledgeSlot, String) =
      (KnowledgeSlot.Fields, KnowledgeText.constructorFields("generated_list_type", constructor, written.map(criterion)))
    val members = Vector(
      (KnowledgeSlot.Representations, KnowledgeText.named("generated_list_type", declaration.specialization)),
      (KnowledgeSlot.Families, KnowledgeText.family("generated_list_type", declaration.arity, declaration.constructors)),
      fields("nil", declaration.nilFields),
      fields("cons", declaration.consFields),
      (KnowledgeSlot.JvmTypes, KnowledgeText.jvmType("generated_list_type", JvmTypeName.List))
    )
    Files.writeString(
      Files.createDirectories(tree.resolve("compiler")).resolve("generated_facts.lambdalattice"),
      KnowledgeTexts.knowledgeFile(Vector(imported), members)
    )
    KnowledgeTexts.compiled(tree, Vector("generated/compiler/generated_facts"), Vector.empty)

  test("the lists' declaration that describes the codec loads") {
    BackendFacts.of(library(described))
  }

  test("every mutation of the lists' declaration is rejected when the backend's facts are read") {
    val random = Random(20261107)
    (1 to 20).foreach { _ =>
      val declaration = mutated(random)
      intercept[IllegalArgumentException](BackendFacts.of(library(declaration)))
    }
  }
