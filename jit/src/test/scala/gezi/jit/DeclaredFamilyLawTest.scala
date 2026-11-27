package gezi.jit

import java.nio.file.Files
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.frontend.TermOf
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Pure
import gezi.ir.Value
import gezi.standardlibrary.JvmTypeName
import gezi.standardlibrary.KnowledgeSlot
import gezi.standardlibrary.KnowledgeText
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTable
import gezi.weakhead.Expansions
import gezi.weakhead.Mode
import scala.util.Random

/** The laws of the data families declared by facts (`DeclaredFamilies`), on
  * generated families written as a tree of library and knowledge files
  * (`KnowledgeTexts.withFreshTree`): a family of k criterion parameters (k from
  * 0 to 2) whose constructors have zero to two fields, each `recursive` or
  * `parameter(I)`, the first constructor of none, and a criterion
  * `λp1 … λpk. fixpoint (λself. (K0 + K1 f … + …))` with `data_family`,
  * `data_fields` and `jvm_type(generic)`. A family is the library file
  * `generated/library/<prefix>`, whose members are its constructors and its
  * criterion, each read by projection (`StandardLibrary.entryMembers`), and its
  * facts the knowledge file `generated/compiler/<prefix>_facts`, which imports
  * them. (1) A generated value written with the constructors, under its
  * family's criterion applied to the criteria of generated families of no
  * parameter, reads through the generic codec (at least one encoding) to the
  * normal form tabling(weak_head) reads of the value alone: decoding then
  * encoding is the identity. A family of parameters is read at two different
  * generated arguments. (2) Two families whose nullary first constructors are
  * one instruction (the same body) each read their own values so: a value's
  * family comes from the filter's criterion, never from a constructor's
  * instruction. Purpose: catch a codec that loses or reorders a field or a
  * constructor, a declaration read wrong, a criterion parameter taken from the
  * wrong position or from a value, and a family chosen by a shared head.
  */
class DeclaredFamilyLawTest extends gezi.generatedinputs.FailFastSuite:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of DeclaredFamilyLawTest, "a family of criterion parameters reads its values at two different generated arguments", takes 14.055 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(25, "s")

  /** A generated family: its criterion parameters' count and the fields of each
    * constructor, `None` for `recursive` and `Some(I)` for `parameter(I)`; and
    * the fields its criterion writes otherwise than its facts declare, by
    * constructor and field, each a closed criterion's text (none for a family
    * whose criterion is its facts').
    */
  private final case class Family(
      prefix: String,
      arity: Int,
      constructors: Vector[Vector[Option[Int]]],
      misdeclared: Map[(Int, Int), String] = Map.empty,
      filtered: Set[(Int, Int)] = Set.empty,
      unread: Set[(Int, Int)] = Set.empty,
      closedFields: Map[(Int, Int), (Family, Vector[Family])] = Map.empty,
      marker: Option[String] = None,
      fixedPointConstructor: Option[Int] = None
  ):
    def constructor(index: Int): String = s"constructor_$index"
    val criterion: String = "set"
    def keys: Vector[String] =
      constructors.indices.toVector.map(constructor) :+ criterion :++
        (if filtered.isEmpty then Vector.empty
         else Vector(filter)) :++ (if unread.isEmpty then Vector.empty
                                   else Vector(bottom))
    val filter: String = "filter"
    val bottom: String = "bottom"

  /** A value: its family, the constructor's index and the fields, each a value
    * of its own.
    */
  private final case class Tree(
      family: Family,
      constructor: Int,
      fields: Vector[Tree]
  )

  /** The generated families' library terms, by family prefix and member key,
    * and the library of their facts.
    */
  private final case class Generated(
      terms: Map[String, Map[String, Plain]],
      library: StandardLibrary
  ):
    def term(family: Family, key: String): Hoas =
      Term.closed(
        terms(family.prefix).getOrElse(
          key,
          throw IllegalArgumentException(s"${family.prefix} has no member $key")
        )
      )

    /** The native specializer of the facts of the generated library, whose
      * singleton type is the configuration the generated programs are read in.
      */
    lazy val encoding: StorageEncoding = NativesTesting.encodingOf(library)

    /** The generated term of the family's member, crossed into the library's
      * configuration.
      */
    def crossed(family: Family, key: String): Configured[encoding.type] =
      JitTesting.instructionCrossed(encoding)(
        terms(family.prefix).getOrElse(
          key,
          throw IllegalArgumentException(s"${family.prefix} has no member $key")
        )
      )

  /** A closed term of no facts: the generated terms are read from files under
    * no facts and crossed into the encoding that reads them.
    */
  private type Plain = Configured[NoFacts.type]

  /** A closed HOAS term over the terms of no facts. */
  private type Hoas = TermOf[Configured[NoFacts.type]]

  /** The term compiled to one thunk under no facts. */
  private def plain(term: Hoas): Plain =
    Defunctionalization.thunkInstruction[NoFacts.type](
      term.deBruijnTerm(Map.empty)
    )(using NoFacts)

  /** The value of the term under no facts in the encoding's configuration: its
    * parallels converted by the encoding.
    */
  private def valueIn[E <: StorageEncoding & Singleton](
      encoding: E
  )(term: Hoas): Value[E] =
    JitTesting.instructionValue[E](
      JitTesting.instructionCrossed(encoding)(plain(term))
    )(using encoding)

  /** The pure key of a generated criterion, the identity of the family it
    * declares.
    */
  private def identityOf(generated: Generated, family: Family): FamilyIdentity =
    FamilyIdentity.Declared(
      Pure.required(generated.terms(family.prefix)(family.criterion))
    )

  private def family(random: Random, prefix: String, arity: Int): Family =
    def field: Option[Int] = if arity > 0 && random.nextBoolean() then
      Some(random.nextInt(arity))
    else None
    Family(
      prefix,
      arity,
      Vector.empty +: Vector.fill(1 + random.nextInt(2))(
        Vector.fill(random.nextInt(3))(field)
      )
    )

  /** A value of the family at the arguments' families, at most the depth. */
  private def tree(
      random: Random,
      family: Family,
      arguments: Vector[Family],
      depth: Int
  ): Tree =
    val constructor =
      if depth == 0 then 0 else random.nextInt(family.constructors.size)
    Tree(
      family,
      constructor,
      family.constructors(constructor).map {
        case None           => tree(random, family, arguments, depth - 1)
        case Some(position) =>
          tree(random, arguments(position), Vector.empty, depth - 1)
      }
    )

  private def term(generated: Generated, value: Tree): Hoas =
    value.fields.foldLeft(
      generated.term(value.family, value.family.constructor(value.constructor))
    )((applied, field) => applied(term(generated, field)))

  /** The text of a constructor of the family: its fields, then one case per
    * constructor, the case of the index applied to the fields.
    */
  private def constructorText(family: Family, index: Int): String =
    val fields = family.constructors(index)
    val binders = fields.indices.map(field => s"λf$field. ").mkString
    val cases = (1 to family.constructors.size)
      .map(alternative => s"λc$alternative. ")
      .mkString
    val applied = (s"c${index + 1}" +: fields.indices.map(field => s"f$field"))
      .mkString(" ")
    s"$binders$cases$applied"

  /** The text of the family's criterion, with the fixed point combinator
    * written out (the same term as the library's `fixpoint`), under the
    * family's marker when it has one, `λx. (λ"key" v. v) "key" x`, a variable
    * arguments partial function of the key applied to the key and to the
    * combinator, written as the library writes its `$generic`
    * (corpora/library/native_types/markers.lambdalattice).
    */
  private def criterionText(family: Family): String =
    val members = family.constructors.zipWithIndex.map((fields, index) =>
      (s"(${constructorText(family, index)})" +: fields.zipWithIndex.map(
        (field, position) =>
          family.misdeclared.getOrElse(
            (index, position),
            if family.closedFields.contains((index, position)) then
              val (named, arguments) = family.closedFields((index, position))
              s"((${criterionText(named)}) ${arguments.map(argument => s"(${criterionText(argument)})").mkString(" ")})"
            else if family.filtered((index, position)) then s"($filterText)"
            else if family.unread((index, position)) then s"($bottomText)"
            else field.fold("self")(parameter => s"p$parameter")
          )
      )).mkString(" ")
    )
    val parameters =
      (0 until family.arity).map(position => s"λp$position. ").mkString
    val fixpoint = family.marker.fold(fixpointText)(key =>
      s"""((λx. (λ"$key" v. v) "$key" x) $fixpointText)"""
    )
    s"$parameters$fixpoint (λself. (${members.mkString(" + ")}))"

  /** The fixed point combinator written out, Θ. */
  private val fixpointText: String = "((λx. λf. f (x x f)) (λx. λf. f (x x f)))"

  /** A function's range filter over the booleans, `λ_. (true + false)`: by (9)
    * and η, `f ∥ λ_. B = λy. f y ∥ B`. It names no family, so a field it
    * filters is held as `f ∥ F` (`FilteredFamily`). The booleans' choice is
    * finite: a reading of `x ∥ B` reads its two members, where a recursive
    * criterion of no family (the naturals written out) is read as a fold over
    * all its values and does not finish.
    */
  private val filterText: String = "λ_. ((λt. λf. t) + (λt. λf. f))"

  /** Ω, the criterion of a field held as written (the codec `unread`): x ∥ Ω is x.
    */
  private val bottomText: String = "(λx. x x) (λx. x x)"

  /** A field criterion that is a closed term, the third constructor of
    * `field_criteria`, its one item the term.
    */
  private def closedCriterion(term: String): String =
    s"(λ_ _ closed. closed (λn. λc. c ($term) (λn. λc. n)))"

  /** The facts of the family, its terms imported from its library file. */
  private def factsText(family: Family): String =
    def name(key: String): String = s"${family.prefix}_$key"
    val named = family.closedFields.values.toVector
      .flatMap((other, arguments) => other +: arguments)
      .distinctBy(_.prefix)
    val imports =
      (family +: named).map(imported =>
        KnowledgeText.Import.Grouped(
          "generated",
          Vector("library", imported.prefix),
          imported.prefix,
          imported.keys.map(key => s"${imported.prefix}_$key")
        )
      )
    val criterion = name(family.criterion)
    val constructors = family.constructors.indices.toVector.map(index =>
      name(family.constructor(index))
    )
    val members = Vector(
      (
        KnowledgeSlot.Families,
        KnowledgeText.family(criterion, family.arity, constructors)
      ),
      (
        KnowledgeSlot.JvmTypes,
        KnowledgeText.jvmType(criterion, JvmTypeName.Generic)
      )
    ) ++ family.constructors.zip(constructors).zipWithIndex.map {
      case ((fields, constructor), index) =>
        val criteria = fields.zipWithIndex.map((field, position) =>
          if family.closedFields.contains((index, position)) then
            val (other, arguments) = family.closedFields((index, position))
            val items = (other +: arguments)
              .map(item => s"${item.prefix}_${item.criterion}")
            s"(λ_ _ closed. closed ${items.foldRight("(λn. λc. n)")(
                (item, tail) => s"(λn. λc. c ($item) $tail)"
              )})"
          else if family.filtered((index, position)) then
            closedCriterion(name(family.filter))
          else if family.unread((index, position)) then
            closedCriterion(name(family.bottom))
          else field.fold(KnowledgeText.recursive)(KnowledgeText.parameter)
        )
        (
          KnowledgeSlot.Fields,
          KnowledgeText.constructorFields(criterion, constructor, criteria)
        )
    } ++ (if family.unread.isEmpty then Vector.empty
          else
            Vector(
              (
                KnowledgeSlot.Representations,
                KnowledgeText.named(name(family.bottom), "unread")
              ),
              (
                KnowledgeSlot.Families,
                KnowledgeText.family(name(family.bottom), 0, Vector.empty)
              )
            ))
    KnowledgeTexts.knowledgeFile(imports, members)

  /** The families written to a fresh tree `generated`, their terms read by
    * projection and their facts compiled with the backend's checks.
    */
  private def generated(families: Vector[Family]): Generated =
    KnowledgeTexts.withFreshTree("generated")(tree =>
      generatedIn(families, tree)
    )

  private def generatedIn(
      families: Vector[Family],
      tree: java.nio.file.Path
  ): Generated =
    val library = Files.createDirectories(tree.resolve("library"))
    val compiler = Files.createDirectories(tree.resolve("compiler"))
    families.foreach(family =>
      Files.writeString(
        library.resolve(s"${family.prefix}.lambdalattice"),
        KnowledgeTexts.libraryFile(
          family.constructors.indices.toVector.map(index =>
            (
              family.constructor(index),
              if family.fixedPointConstructor.contains(index) then
                s"$fixpointText (λt. ((${constructorText(family, index)}) + t))"
              else constructorText(family, index)
            )
          ) :+
            (family.criterion, criterionText(family)) :++
            (if family.filtered.isEmpty then Vector.empty
             else Vector((family.filter, filterText))) :++
            (if family.unread.isEmpty then Vector.empty
             else Vector((family.bottom, bottomText)))
        )
      )
      Files.writeString(
        compiler.resolve(s"${family.prefix}_facts.lambdalattice"),
        factsText(family)
      )
    )
    Generated(
      families
        .map(family =>
          family.prefix -> StandardLibrary
            .entryMembers(
              tree,
              TermTable(s"library/${family.prefix}.lambdalattice", family.keys),
              Expansions.none
            )
            ._1
        )
        .toMap,
      KnowledgeTexts.compiled(
        tree,
        families.map(family => s"generated/compiler/${family.prefix}_facts"),
        Vector(BackendChecks)
      )
    )

  /** Whether the value under its family's criterion, applied to the arguments'
    * criteria, reads through the representation to what tabling(weak_head)
    * reads of the value alone.
    */
  private def readsThroughTheCodec(
      generated: Generated,
      value: Tree,
      arguments: Vector[Family]
  ): Unit =
    val criterion =
      arguments.foldLeft(generated.term(value.family, value.family.criterion))(
        (applied, argument) =>
          applied(generated.term(argument, argument.criterion))
      )
    val filtered = term(generated, value) ∥ criterion
    val encoding = generated.encoding
    given encoding.type = encoding
    val jit = NativesTesting.normalFormsSpent(
      Jit(NativesTesting.configurationOf(encoding)),
      valueIn(encoding)(filtered),
      NativesTesting.normalFormLimit
    )
    val reference = NativesTesting.normalFormsSpent(
      Mode.TablingWeakHead,
      JitTesting.plainConfiguration(encoding),
      valueIn(encoding)(term(generated, value)),
      NativesTesting.normalFormLimit
    )
    assert(
      reference.outcome.finished,
      s"tabling(weak_head) did not read $value"
    )
    assert(JitTesting.sameOutcomes(jit.outcome, reference.outcome), s"$value")
    assert(
      JitTesting.counts(jit.jitState).encodings > 0,
      s"$value was not read through the codec"
    )

  test(
    "a value under its declared family's criterion reads through the generic codec as tabling(weak_head) reads it"
  ) {
    val random = Random(20261107)
    (1 to 8).foreach { round =>
      val drawn = family(random, s"family_$round", 0)
      val written = generated(Vector(drawn))
      (1 to 6).foreach(_ =>
        readsThroughTheCodec(
          written,
          tree(random, drawn, Vector.empty, random.nextInt(4)),
          Vector.empty
        )
      )
    }
  }

  test(
    "a family of criterion parameters reads its values at two different generated arguments"
  ) {
    val random = Random(20261109)
    (1 to 6).foreach { round =>
      val arity = 1 + random.nextInt(2)
      val parameterised = family(random, s"parameterised_$round", arity)
      val firstArguments = Vector.tabulate(arity)(position =>
        family(random, s"first_${round}_$position", 0)
      )
      val secondArguments = Vector.tabulate(arity)(position =>
        family(random, s"second_${round}_$position", 0)
      )
      val written =
        generated(parameterised +: (firstArguments ++ secondArguments))
      Vector(firstArguments, secondArguments).foreach(arguments =>
        (1 to 4).foreach(_ =>
          readsThroughTheCodec(
            written,
            tree(random, parameterised, arguments, 1 + random.nextInt(3)),
            arguments
          )
        )
      )
    }
  }

  test(
    "two families sharing a nullary constructor's instruction each read their own values by their criterion"
  ) {
    val random = Random(20261108)
    (1 to 4).foreach { round =>
      val first = family(random, s"first_$round", 0)
      val second = Family(
        s"second_$round",
        0,
        Vector.empty +: first.constructors.drop(1).map(fields => fields :+ None)
      )
      val written = generated(Vector(first, second))
      assert(
        Configured.same(
          written.terms(first.prefix)(first.constructor(0)),
          written.terms(second.prefix)(second.constructor(0))
        )(using NoFacts),
        "the two nullary first constructors are one instruction"
      )
      (1 to 4).foreach { _ =>
        readsThroughTheCodec(
          written,
          tree(random, first, Vector.empty, random.nextInt(4)),
          Vector.empty
        )
        readsThroughTheCodec(
          written,
          tree(random, second, Vector.empty, random.nextInt(4)),
          Vector.empty
        )
      }
    }
  }

  /** The law that a declared family's storage made directly from a generated
    * value, `NativeValue.Constructed` and not decoded from a term, reads by the
    * cases of the family's constructors, under the reference reading, the case
    * of the value's own constructor: the view's outermost constructor is the
    * one at the value's index in the family's `data_family`, checked against
    * the constructor texts this test writes (case k of n applied to the fields)
    * and not against the codec. Each case ignores its fields and gives a marker
    * of its own, so the criterion's side of the view reads every marker once
    * and the parallel keeps the value's. Its purpose is to catch a generic
    * codec whose constructor order differs from the declaration's, which a
    * round trip through the codec itself does not see (#2168, the oracle of the
    * views).
    */
  test(
    "a declared family's storage made from a value reads the case of the value's constructor"
  ) {
    def markerTerm(index: Int): Hoas =
      Term.λ(a => Term.λ(b => Term.λ(c => Vector(a, b, c)(index))))
    def ignoring(arity: Int, body: Hoas): Hoas =
      if arity == 0 then body else Term.λ(_ => ignoring(arity - 1, body))
    def nativeValue(
        identity: FamilyIdentity,
        value: Tree
    ): NativeValue[Nothing] =
      NativeValue.Constructed(
        identity,
        value.constructor,
        value.fields.map(nativeValue(identity, _))
      )
    val random = Random(20261125)
    (1 to 6).foreach { round =>
      val drawn = family(random, s"viewed_$round", 0)
      val written = generated(Vector(drawn))
      val encoding = written.encoding
      given encoding.type = encoding
      val identity = identityOf(written, drawn)
      (1 to 4).foreach { _ =>
        val value = tree(random, drawn, Vector.empty, random.nextInt(3))
        val storage = JitTesting.valueOfNative(encoding)(
          Representation.Data(identity, None),
          nativeValue(identity, value)
        )
        val cases = drawn.constructors.zipWithIndex.map((fields, index) =>
          valueIn(encoding)(ignoring(fields.size, markerTerm(index)))
        )
        val read = NativesTesting.normalFormsSpent(
          Mode.TablingWeakHead,
          JitTesting.plainConfiguration(encoding),
          cases.foldLeft(storage)(gezi.ir.Value.Apply(_, _)),
          NativesTesting.normalFormLimit
        )
        val expected = NativesTesting.normalFormsSpent(
          Mode.TablingWeakHead,
          JitTesting.plainConfiguration(encoding),
          valueIn(encoding)(markerTerm(value.constructor)),
          NativesTesting.normalFormLimit
        )
        assert(
          JitTesting.sameOutcomes(read.outcome, expected.outcome),
          s"round $round: $value"
        )
      }
    }
  }

  /** The law of a declared family whose field is filtered by a criterion of no
    * family, a function's range filter `λ_. B` over the booleans
    * (`FilteredFamily`): a value `C g` of it, g a function, read under the
    * family's criterion, hands out its field as `g ∥ λ_. B`, and the field
    * applied to a natural reads, by the JIT and by the reference reading alike,
    * the boolean g gives, and nothing when g gives no boolean. Derived before
    * the run: `(g ∥ λ_. B) k = g k ∥ B`; for g the constant true or false that
    * is g's boolean by (5), B being true + false; for g the identity and k ≥ 1
    * it is `succ^k zero ∥ B`, whose heads (s against t or f) share no normal
    * form, so no answer, where the field without its filter would read the
    * natural; and the JIT decodes the value at least once. And the unique
    * spelling `C (g ∥ λ_. B) ∥ T` converts to the very storage made from the
    * value (field node `g ∥ λ_. B`), while `C g ∥ T`, its field unfiltered,
    * gets none. Its purpose is to catch a field whose filter a decode point
    * drops, which adds answers, and a conversion that gives one term two
    * objects.
    */
  test(
    "a declared family's field filtered by a criterion of no family holds a function and hands it out filtered"
  ) {
    val random = Random(20261126)
    def natural(count: Int): Hoas =
      (1 to count).foldLeft(Term.λ(z => Term.λ(_ => z)): Hoas)((inner, _) =>
        Term.λ(z => Term.λ(s => s(inner)))
      )
    def truth(value: Boolean): Hoas =
      Term.λ(t => Term.λ(f => if value then t else f))
    def constant(value: Boolean): Hoas = Term.λ(_ => truth(value))
    val drawn = Family(
      "filtered_field",
      0,
      Vector(Vector.empty, Vector(None)),
      filtered = Set((1, 0))
    )
    val written = generated(Vector(drawn))
    val encoding = written.encoding
    given encoding.type = encoding
    (1 to 6).foreach { _ =>
      val result = random.nextBoolean()
      val identity = random.nextBoolean()
      val argument =
        if identity then 1 + random.nextInt(2) else random.nextInt(3)
      val criterion = written.term(drawn, drawn.criterion)
      val value = written.term(drawn, drawn.constructor(1))(if identity then
        Term.λ(n => n)
      else constant(result))
      val applied = (value ∥ criterion)(
        Term.λ(_ => Term.λ(_ => Term.λ(c => c)))
      )(Term.λ(field => field(natural(argument))))
      val program = valueIn(encoding)(applied)
      val jit = NativesTesting.normalFormsSpent(
        Jit(NativesTesting.configurationOf(encoding)),
        program,
        NativesTesting.normalFormLimit
      )
      val reference = NativesTesting.normalFormsSpent(
        Mode.TablingWeakHead,
        JitTesting.plainConfiguration(encoding),
        program,
        NativesTesting.normalFormLimit
      )
      val expected =
        if identity then
          gezi.weakhead.Bounded.Finished(
            Vector.empty[Configured[encoding.type]]
          )
        else
          NativesTesting
            .normalFormsSpent(
              Mode.TablingWeakHead,
              JitTesting.plainConfiguration(encoding),
              valueIn(encoding)(truth(result)),
              NativesTesting.normalFormLimit
            )
            .outcome
      assert(expected.finished, s"the expected boolean did not read")
      assert(
        JitTesting.sameOutcomes(jit.outcome, expected),
        s"jit, ${if identity then "identity" else result} on $argument"
      )
      assert(
        JitTesting.sameOutcomes(reference.outcome, expected),
        s"reference, ${if identity then "identity" else result} on $argument"
      )
      assert(
        JitTesting.counts(jit.jitState).decodings > 0,
        "the value was not decoded"
      )
    }
    val identity = identityOf(written, drawn)
    val representation = Representation.Data(identity, None)
    val filter: JitValue[encoding.type] =
      Value.of(written.crossed(drawn, drawn.filter))
    val function: JitValue[encoding.type] =
      valueIn(encoding)(Term.λ(_ => Term.λ(t => Term.λ(_ => t))))
    val constructor: JitValue[encoding.type] =
      Value.of(written.crossed(drawn, drawn.constructor(1)))
    val made = JitTesting.valueOfNative(encoding)(
      representation,
      NativeValue.Constructed(
        identity,
        1,
        Vector(
          NativeValue.Unread(
            JitTesting.parallelOfValues(encoding)(function, filter)
          )
        )
      )
    )
    val converted = JitTesting.parallelOfValues(encoding)(
      JitValue.Apply(
        constructor,
        JitTesting.parallelOfValues(encoding)(function, filter)
      ),
      JitTesting.criterionOf(encoding)(representation)
    )
    assert(Value.same(converted, made), s"$converted, $made")
    val unfiltered = JitTesting.parallelOfValues(encoding)(
      JitValue.Apply(constructor, function),
      JitTesting.criterionOf(encoding)(representation)
    )
    assert(
      JitValue.Stored.unapply(unfiltered).isEmpty,
      s"an unfiltered field got a storage: $unfiltered"
    )
  }

  /** The law of a declared family's field filtered by a criterion of no family,
    * met by a context that reads the type's other constructor: over a family
    * like the filtered-field law's above (`C0`, and `C1 f` with f filtered by F =
    * `λ_. B`, T = `C0 + C1 F`), the program `(C1 g ∥ T) g (λf. f)`, g a
    * generated closed normal form, reads the one normal form g, by the JIT and
    * by the reference reading. Derived before the run by the β rule and the
    * λ-lattice laws: a parallel applied is the parallel of the applications,
    * `(C1 g) g (λf. f) = g` and `T g (λf. f) = g + F`, so the program is
    * `g ∥ (g + F) = (g ∥ g) + (g ∥ F) = g + (g ∥ F)`, which reads g (`g ∥ F`
    * adds g or nothing). Its purpose is to catch a decode point that makes
    * `C1 g ∥ T` the storage `C1 (g ∥ F) ∥ T`, which reads
    * `(g ∥ F) ∥ (g + F) = g ∥ F`, no answer when g is not in F (the identity),
    * a refinement that drops the meeting of the value's case with the type's.
    */
  test(
    "a declared family's value whose field is not written filtered keeps the answer the type's other constructor meets"
  ) {
    val random = Random(20261130)
    val drawn = Family(
      "met_field",
      0,
      Vector(Vector.empty, Vector(None)),
      filtered = Set((1, 0))
    )
    val written = generated(Vector(drawn))
    val encoding = written.encoding
    given encoding.type = encoding
    def truth(value: Boolean): Hoas =
      Term.λ(t => Term.λ(f => if value then t else f))
    def drawnNormalForm(random: Random): Hoas = random.nextInt(4) match
      case 0 => Term.λ(n => n)
      case 1 => Term.λ(_ => Term.λ(b => b))
      case 2 => Term.λ(n => n(n))
      case _ =>
        val result = truth(random.nextBoolean())
        Term.λ(_ => result)
    (1 to 6).foreach { round =>
      val g = drawnNormalForm(random)
      val program = (written.term(drawn, drawn.constructor(1))(g) ∥ written
        .term(drawn, drawn.criterion))(g)(Term.λ(f => f))
      def readByReference(term: Hoas) =
        NativesTesting.normalFormsSpent(
          Mode.TablingWeakHead,
          JitTesting.plainConfiguration(encoding),
          valueIn(encoding)(term),
          NativesTesting.normalFormLimit
        )
      val expected = readByReference(g).outcome
      assert(expected.finished, s"round $round: g did not read")
      val jitRead = NativesTesting.normalFormsSpent(
        Jit(NativesTesting.configurationOf(encoding)),
        valueIn(encoding)(program),
        NativesTesting.normalFormLimit
      )
      assert(
        JitTesting.sameOutcomes(jitRead.outcome, expected),
        s"jit, round $round, g $g"
      )
      assert(
        JitTesting.sameOutcomes(readByReference(program).outcome, expected),
        s"reference, round $round, g $g"
      )
    }
  }

  /** The law that a declared family's storage is one layer of nodes. Over a
    * generated chain of stored layers, each layer built from a value whose
    * fields are the storage below: holds that storage's very object as each
    * field node; is its own value; is taken apart by the family's codec into
    * that very storage, not into a value rebuilt from it; is the very object
    * the conversion of its unique spelling `C s … s ∥ T` gives; and, at the
    * first few layers, the very object made from the whole value built anew,
    * layer by layer; and a chain of 100000 layers is built and taken apart down
    * to its nullary layer, in exactly that many steps, with no recursion on the
    * stack. Derived before the run from the design: every identity holds at
    * every layer. Its purpose is to catch a storage that rebuilds, re-reads or
    * rehashes its fields' layers, which makes a walk over a chain of n layers
    * cost n² or more and its memory n².
    */
  test(
    "a declared family's storage over a stored chain holds the chain's node and is taken apart one layer at a time"
  ) {
    val random = Random(20261127)
    (1 to 3).foreach { round =>
      val drawn = Family(
        s"chain_$round",
        0,
        Vector(Vector.empty, Vector.fill(1 + random.nextInt(2))(None))
      )
      val written = generated(Vector(drawn))
      val encoding = written.encoding
      given encoding.type = encoding
      val identity = identityOf(written, drawn)
      val representation = Representation.Data(identity, None)
      val width = drawn.constructors(1).size
      val constructor: JitValue[encoding.type] =
        Value.of(written.crossed(drawn, drawn.constructor(1)))
      def stored(
          value: NativeValue[JitValue[encoding.type]]
      ): ConstructedStorage[JitValue[encoding.type]] =
        JitTesting.valueOfNative(encoding)(representation, value) match
          case JitValue.Stored(storage) =>
            StorageOf
              .constructed(storage)
              .getOrElse(fail(s"no declared family's storage: $storage"))
          case other => fail(s"no declared family's storage: $other")
      def anew(depth: Int): NativeValue[JitValue[encoding.type]] =
        if depth == 0 then NativeValue.Constructed(identity, 0, Vector.empty)
        else
          NativeValue.Constructed(
            identity,
            1,
            Vector.fill(width)(anew(depth - 1))
          )
      def layerOver(
          below: ConstructedStorage[JitValue[encoding.type]]
      ): ConstructedStorage[JitValue[encoding.type]] =
        stored(
          NativeValue.Constructed(
            identity,
            1,
            Vector.fill(width)(StorageOf.nativeValue(below))
          )
        )
      val length = 1 + random.nextInt(300)
      val chain =
        (1 to length).scanLeft(stored(anew(0)))((below, _) => layerOver(below))
      chain.zip(chain.tail).zipWithIndex.foreach {
        case ((below, layer), index) =>
          assert(
            layer.fields.size == width && layer.fields
              .forall(Value.same(_, StorageOf.value(below))),
            s"round $round, layer ${index + 1}: ${layer.fields}"
          )
          // A declared family's storage stands for its own term: its native value is the storage itself.
          assert(
            StorageOf.nativeValue(layer) match
              case NativeValue.Stored(term) =>
                Value.same(term, StorageOf.value(layer))
              case other => false
            ,
            s"round $round, layer ${index + 1}: its own value"
          )
          val spelled = Vector
            .fill(width)(JitTesting.interned(encoding)(below))
            .foldLeft(constructor)(JitValue.Apply(_, _))
          assert(
            Value.same(
              JitTesting.parallelOfValues(encoding)(
                spelled,
                JitTesting.criterionOf(encoding)(representation)
              ),
              StorageOf.value(layer)
            ),
            s"round $round, layer ${index + 1}: converted"
          )
      }
      (0 to (length min 6)).foreach(depth =>
        assert(
          stored(anew(depth)) eq chain(depth),
          s"round $round, depth $depth: built anew"
        )
      )
      val longLength = 100000
      val long =
        (1 to longLength).foldLeft(chain.head)((below, _) => layerOver(below))
      @scala.annotation.tailrec
      def depthOf(
          storage: ConstructedStorage[JitValue[encoding.type]],
          sofar: Int
      ): Int =
        if storage.constructor == 0 then sofar
        else
          storage.fields.head match
            case JitValue.Stored(first) =>
              depthOf(
                StorageOf
                  .constructed(first)
                  .getOrElse(
                    fail(
                      s"round $round: the field is no declared storage: $first"
                    )
                  ),
                sofar + 1
              )
            case other => fail(s"round $round: the field is no storage: $other")
      assertEquals(
        depthOf(long, 0),
        longLength,
        s"round $round: the long chain"
      )
    }
  }

  /** The law of the decode points of a field filtered by a criterion of no
    * family, `λ_. B` over the booleans, held as `g ∥ F` (`FilteredFamily`), for
    * a field the facts declare filtered and for a field `parameter(0)` at a
    * criterion argument that names no family. A generated function g (a
    * constant boolean, the identity, or a case on zero) is put in the field
    * four ways: `C g ∥ T`, `C (g ∥ F) ∥ T`, `(λx. x ∥ T) (C (g ∥ F))` (the
    * filter met after the field was filtered) and `(λc1 c2. c2 g) ∥ T` (the
    * constructor's body already applied). Derived before the run from
    * `Jit.nativeAppliedHeads`, where a constructor's native runs only when
    * every argument is already written a storage: none of the four calls the
    * native, each is decoded by the cases (`Jit.valueDecoded`); the two whose
    * field is written `g ∥ F` each give one value, the same storage (equal: a
    * head the JIT reads is interned only where it enters a term), whose field
    * node carries F once (∥ is idempotent), for the declared field the one the
    * unique spelling `C (g ∥ F) ∥ T` converts to; the two whose field is g
    * alone give none, read as written (#2163 B1: a generic layer is a storage
    * only when written `C (f ∥ F) ∥ T`, since `C (g ∥ F) ∥ T` is below
    * `C g ∥ T` in ⊑_O); and the field applied to a natural reads, by the JIT,
    * what the reference reading reads. The other site, a constructor's native
    * called on the field's argument (`Jit.representedValues`), is reached only
    * through a native that takes the family's value at a place, or a fallback
    * point's type-filtered constructor, neither of which these generated facts
    * declare; it filters through the same `filteredOnce`. Its purpose is to
    * catch a decode point that piles a filter on a field already filtered (one
    * term, two storages; a filter per update), a site of the two that drops or
    * doubles the filter unseen by the other, and a criterion parameter of no
    * family read otherwise than as written.
    */
  test(
    "both decode points give a filtered field one filter, for a declared field and at a criterion parameter"
  ) {
    val random = Random(20261128)
    def truth(value: Boolean): Hoas =
      Term.λ(t => Term.λ(f => if value then t else f))
    def natural(count: Int): Hoas =
      (1 to count).foldLeft(Term.λ(z => Term.λ(_ => z)): Hoas)((inner, _) =>
        Term.λ(z => Term.λ(s => s(inner)))
      )
    def function(random: Random): Hoas = random.nextInt(3) match
      case 0 =>
        val result = truth(random.nextBoolean())
        Term.λ(_ => result)
      case 1 => Term.λ(n => n)
      case _ =>
        val (onZero, onSuccessor) =
          (truth(random.nextBoolean()), truth(random.nextBoolean()))
        Term.λ(n => n(onZero)(Term.λ(_ => onSuccessor)))
    val filterTerm: Hoas = Term.λ(_ => truth(true) + truth(false))
    val declared = Family(
      "filtered_sites",
      0,
      Vector(Vector.empty, Vector(None)),
      filtered = Set((1, 0))
    )
    val parameterized =
      Family("parameter_sites", 1, Vector(Vector.empty, Vector(Some(0))))
    val written = generated(Vector(declared, parameterized))
    val encoding = written.encoding
    given encoding.type = encoding
    def represented(
        jit: Jit[encoding.type],
        term: Hoas
    ): (Vector[NativeValue[JitValue[encoding.type]]], JitCounts) =
      jit
        .representedHeads(valueIn(encoding)(term))
        .collected
        .result(
          gezi.weakhead.ReadingState
            .fresh(NativesTesting.normalFormLimit, jit.readingConfiguration)
        ) match
        case gezi.weakhead.Computed.Done(values, after) =>
          (values, JitTesting.counts(after.jitState))
        case gezi.weakhead.Computed.Stopped(_) =>
          fail(s"the decode point of $term did not finish")
    def constructedOf(
        value: NativeValue[JitValue[encoding.type]]
    ): ConstructedStorage[JitValue[encoding.type]] = value match
      case NativeValue.Stored(JitValue.Stored(storage)) =>
        StorageOf
          .constructed(storage)
          .getOrElse(fail(s"no declared family's storage: $storage"))
      case other => fail(s"no declared family's storage: $other")
    Vector(declared, parameterized).foreach { family =>
      val identity = identityOf(written, family)
      val (criterion, filter) =
        if family.arity == 0 then
          (
            written.term(family, family.criterion),
            written.term(family, family.filter)
          )
        else (written.term(family, family.criterion)(filterTerm), filterTerm)
      val constructor = written.term(family, family.constructor(1))
      (1 to 4).foreach { round =>
        val g = function(random)
        val programs = Vector(
          constructor(g) ∥ criterion,
          constructor(g ∥ filter) ∥ criterion,
          Term.λ(x => x ∥ criterion)(constructor(g ∥ filter)),
          Term.λ(_ => Term.λ(case1 => case1(g))) ∥ criterion
        )
        val jit = Jit(NativesTesting.configurationOf(encoding))
        val read = programs.map(represented(jit, _))
        val Vector(
          unfilteredRead,
          filteredRead,
          filteredLaterRead,
          appliedRead
        ) = read: @unchecked
        Vector(unfilteredRead, appliedRead).foreach((values, _) =>
          assert(
            values.isEmpty,
            s"${family.prefix}, round $round: a field g alone gave the storages $values"
          )
        )
        val storages = Vector(filteredRead, filteredLaterRead).map {
          case (Vector(value), _) => constructedOf(value)
          case (other, _)         =>
            fail(
              s"${family.prefix}, round $round: the decode point gave $other"
            )
        }
        val first = storages.head
        assert(
          storages.forall(_.sameContent(first)),
          s"${family.prefix}, round $round: $storages"
        )
        val fieldFilter = first.representation match
          case Representation.Data(
                _,
                Some(CriterionParameters(Vector(parameter)))
              ) =>
            FilteredFamily
              .criterionOf(parameter)
              .getOrElse(
                fail(
                  s"${family.prefix}: the parameter $parameter names a family"
                )
              )
          case Representation.Data(_, None) =>
            Value.of(written.crossed(family, family.filter)): JitValue[
              encoding.type
            ]
          case other => fail(s"${family.prefix}: $other")
        first.fields match
          case Vector(node @ JitValue.Parallel(inner, found))
              if Value.same(found, fieldFilter) =>
            assert(
              encoding.operations.filteredAlready(inner, fieldFilter).isEmpty,
              s"${family.prefix}, round $round: two filters in $node"
            )
            if family.arity == 0 then
              val spelled = JitValue.Apply(
                Value.of(written.crossed(family, family.constructor(1))),
                JitTesting.parallelOfValues(encoding)(inner, fieldFilter)
              )
              assert(
                Value.same(
                  JitTesting.parallelOfValues(encoding)(
                    spelled,
                    JitTesting.criterionOf(encoding)(first.representation)
                  ),
                  StorageOf.value(first)
                ),
                s"${family.prefix}, round $round: converted"
              )
          case other =>
            fail(s"${family.prefix}, round $round: the field nodes are $other")
        val constructorNative = NativeName.Constructor(identity, 1)
        // The programs written as a parallel reach the decode point, which decodes. The filter a closure's body applies
        // builds its parallel through the facts' native specializer at run time: for the declared field, the storage itself
        // (`C (g ∥ F) ∥ T` the unique spelling), so that reading decodes nothing; at a criterion parameter, which names
        // no representation of the facts (`StorageEncoding.convertedValue` converts none), the parallel as written,
        // which the decode point decodes. No reading calls the constructor's native.
        read.zipWithIndex.foreach { case ((_, counts), index) =>
          assert(
            counts.callsOf(constructorNative) == 0,
            s"${family.prefix}, round $round, program $index: $counts"
          )
          if index == 2 && family.arity == 0 then
            assertEquals(
              counts.decodings,
              0L,
              s"${family.prefix}, round $round, program $index: $counts"
            )
          else
            assert(
              counts.decodings > 0,
              s"${family.prefix}, round $round, program $index: $counts"
            )
        }
        val argument = random.nextInt(3)
        val applied = (constructor(g) ∥ criterion)(Term.λ(_ => Term.λ(c => c)))(
          Term.λ(field => field(natural(argument)))
        )
        val jitRead = NativesTesting.normalFormsSpent(
          jit,
          valueIn(encoding)(applied),
          NativesTesting.normalFormLimit
        )
        val reference = NativesTesting.normalFormsSpent(
          Mode.TablingWeakHead,
          JitTesting.plainConfiguration(encoding),
          valueIn(encoding)(applied),
          NativesTesting.normalFormLimit
        )
        assert(
          reference.outcome.finished,
          s"${family.prefix}, round $round: the reference did not finish"
        )
        assert(
          JitTesting.sameOutcomes(jitRead.outcome, reference.outcome),
          s"${family.prefix}, round $round, on $argument"
        )
      }
    }
  }

  /** The law of a field held as written (its criterion Ω, the codec `unread`)
    * whose term is a storage: a declared family's storage whose field holds
    * another storage, generated (a chain of the family's own layers below it),
    * takes the field apart as that node unread, not as the storage's value; its
    * view's field is that node; the reader's elimination spells it
    * (`StorageEncoding.spelled`) with that node as its field; and the storage
    * made again under the representation of the field below's family is the
    * same object. Derived before the run: a field of the representation
    * `unread` is a term, whatever its class, so each of these holds. Its
    * purpose is to catch a field mapped by its node's class rather than by its
    * representation, which hands a term held as written out decoded and asks
    * the family `unread`, which has no layer, for one (a throw).
    */
  test(
    "a field held as written whose term is a storage is that node, unread, at every reading of the layer"
  ) {
    val random = Random(20261129)
    val drawn = Family(
      "unread_field",
      0,
      Vector(Vector.empty, Vector(None), Vector(None)),
      unread = Set((2, 0))
    )
    val written = generated(Vector(drawn))
    val encoding = written.encoding
    given encoding.type = encoding
    val identity = identityOf(written, drawn)
    val representation = Representation.Data(identity, None)
    def stored(
        value: NativeValue[JitValue[encoding.type]]
    ): ConstructedStorage[JitValue[encoding.type]] =
      JitTesting.valueOfNative(encoding)(representation, value) match
        case JitValue.Stored(storage) =>
          StorageOf
            .constructed(storage)
            .getOrElse(fail(s"no declared family's storage: $storage"))
        case other => fail(s"no declared family's storage: $other")
    (1 to 6).foreach { round =>
      val depth = random.nextInt(5)
      val inner = (1 to depth).foldLeft(
        stored(NativeValue.Constructed(identity, 0, Vector.empty))
      )((below, _) =>
        stored(
          NativeValue.Constructed(
            identity,
            1,
            Vector(StorageOf.nativeValue(below))
          )
        )
      )
      val innerNode: JitValue[encoding.type] =
        JitTesting.interned(encoding)(inner)
      val outer = stored(
        NativeValue.Constructed(
          identity,
          2,
          Vector(NativeValue.Unread(innerNode))
        )
      )
      assert(
        outer.fields.size == 1 && Value.same(outer.fields.head, innerNode),
        s"round $round: ${outer.fields}"
      )
      // The reader's elimination reads the storage's one-layer view, its field that node as it was written.
      val view = encoding.viewOf(outer)(using gezi.ir.StorageAccess.granted())
      assert(
        Value.of(view.value) match
          case JitValue.Apply(_, field) => Value.same(field, innerNode)
          case other                    => false
        ,
        s"round $round: the view's field"
      )
      assert(
        stored(
          NativeValue
            .Constructed(identity, 2, Vector(NativeValue.Unread(innerNode)))
        ) eq outer,
        s"round $round: made again"
      )
    }
  }
