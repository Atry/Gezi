package com.yang_bo.gezi.generatedinputs

import hedgehog.Gen
import hedgehog.Range
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.Lambdalattice
import com.yang_bo.gezi.frontend.Literals
import com.yang_bo.gezi.standardlibrary.JvmTypeName
import com.yang_bo.gezi.standardlibrary.KnowledgeSlot
import com.yang_bo.gezi.standardlibrary.KnowledgeText
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** Generators of well-formed knowledge, generic and standing alone: the text of
  * a knowledge term of the shape `KnowledgeFileReading` reads, the fixed-width
  * mixin of `KnowledgeSlot`'s groups and slots, each member the Scott tuple of
  * its slot, written by `KnowledgeText`. It imports nothing: every term is a
  * closed term of `HoasGenerators.openTerm` of at most `termNodes` nodes, every
  * name, proof citation, native implementation and representation the trie of a
  * string literal of bounded length, and every integer and every constructor of
  * a published sum written closed.
  *
  * A member's term, which a property, a native or a family binds, is the Scott
  * pair of the member's name and a generated term, `λs. s "name" term`, so that
  * the bound terms are pairwise different: a family's criterion is declared
  * once and its constructors are distinct, as the index requires, and the terms
  * of two knowledges of different labels are disjoint. A lemma's two sides are
  * generated terms as they are.
  *
  * The slots `associative` and `repeller` are never filled: a member of one
  * needs the lemma the combinator property vocabulary gives for it
  * (`CombinatorPropertyVocabulary.justification`), instantiated by the member's
  * term, which a knowledge of generated terms does not have.
  */
object KnowledgeGenerators:

  /** The most nodes of a generated term: a lemma's side or a bound term. */
  val termNodes: Int = 12

  /** The slots a generated knowledge may fill: every slot but the justified
    * properties', `associative` and `repeller`.
    */
  val fillableSlots: Vector[KnowledgeSlot] =
    KnowledgeSlot.values.toVector.filterNot(slot =>
      slot == KnowledgeSlot.Associative || slot == KnowledgeSlot.Repeller
    )

  /** The slots whose members no backend interprets: the lemmas, the leaves and
    * the front end's markers. A knowledge of these slots alone can be given to
    * an executor whose backend checks its natives, codecs and families, which
    * generated names and terms do not implement.
    */
  val slotsNoBackendInterprets: Vector[KnowledgeSlot] = Vector(
    KnowledgeSlot.Lemmas,
    KnowledgeSlot.Leaves,
    KnowledgeSlot.NameMarker,
    KnowledgeSlot.ClosureMarker,
    KnowledgeSlot.TagOrigin,
    KnowledgeSlot.TagNext
  )

  /** The text of a knowledge whose slots are the given ones, each holding from
    * none to `maximumMembers` members as Hedgehog's size grows, and at least
    * one member in all (a knowledge of no member is top, which a text cannot
    * write standing alone). Every name it declares starts with the label, so
    * that two knowledges of different labels declare disjoint names and bind
    * disjoint terms.
    */
  def knowledgeText(
      label: String,
      slots: Vector[KnowledgeSlot],
      maximumMembers: Int
  ): Gen[String] =
    require(
      slots.nonEmpty && slots.forall(fillableSlots.contains),
      s"the slots $slots are not all fillable"
    )
    require(
      maximumMembers >= 1,
      s"a knowledge of at most $maximumMembers members a slot"
    )
    for
      counts <- sequenced(
        slots.map(_ => Gen.int(Range.linear(0, maximumMembers)))
      )
      // The first slot holds a member at least, so that the knowledge is not top.
      written <- sequenced(
        slots.zip(counts).zipWithIndex.map { case ((slot, count), position) =>
          slotMembers(
            s"$label $position",
            slot,
            if position == 0 then count.max(1) else count
          )
        }
      )
    yield
      val members = written.flatten
      KnowledgeText.mixin(
        KnowledgeSlot.values.toVector.map(slot =>
          slot -> members.collect { case (`slot`, member) =>
            KnowledgeText.Member(member)
          }
        )
      )

  /** The knowledge term of a text `knowledgeText` wrote. */
  def term[C <: NativeSpecializer & Singleton](
      text: String
  )(using C): Configured[C] =
    Defunctionalization.thunkInstruction[C](Lambdalattice.term(text))

  /** The members of the slot, each named by the prefix and its position, with
    * the slot each is written in: a member of `fields` comes with the member of
    * `families` that declares its constructor's family.
    */
  private def slotMembers(
      prefix: String,
      slot: KnowledgeSlot,
      count: Int
  ): Gen[Vector[(KnowledgeSlot, String)]] =
    def each(
        member: String => Gen[String]
    ): Gen[Vector[(KnowledgeSlot, String)]] =
      sequenced(
        Vector.tabulate(count)(position =>
          name(s"$prefix.$position").flatMap(member).map(slot -> _)
        )
      )
    def bound(written: String => String): Gen[Vector[(KnowledgeSlot, String)]] =
      each(memberName => boundTerm(memberName).map(written))
    slot match
      case KnowledgeSlot.Lemmas =>
        each(lemmaName =>
          for
            left <- closedTerm
            right <- closedTerm
            proof <- lemmaProof
          yield s"(λs. s ${KnowledgeText.text(lemmaName)} ($left) ($right) $proof)"
        )
      case KnowledgeSlot.Natives | KnowledgeSlot.Representations =>
        each(memberName =>
          boundTerm(memberName).flatMap(term =>
            backendName.map(KnowledgeText.named(term, _))
          )
        )
      case KnowledgeSlot.JvmTypes =>
        each(memberName =>
          for
            term <- boundTerm(memberName)
            jvmType <- Gen
              .int(Range.constant(0, JvmTypeName.values.size - 1))
              .map(JvmTypeName.fromOrdinal)
          yield KnowledgeText.jvmType(term, jvmType)
        )
      case KnowledgeSlot.Families =>
        sequenced(
          Vector.tabulate(count)(position => family(s"$prefix.$position"))
        ).map(_.map(declared => KnowledgeSlot.Families -> declared.text))
      case KnowledgeSlot.Fields =>
        sequenced(
          Vector.tabulate(count)(position => family(s"$prefix.$position"))
        ).flatMap(families =>
          sequenced(
            families.map(declared =>
              for
                constructor <- Gen
                  .int(Range.constant(0, declared.constructors.size - 1))
                  .map(declared.constructors)
                criteria <- fieldCriterion(declared.arity).list(
                  Range.linear(0, 3)
                )
              yield Vector(
                KnowledgeSlot.Families -> declared.text,
                KnowledgeSlot.Fields -> KnowledgeText.constructorFields(
                  declared.criterion,
                  constructor,
                  criteria.toVector
                )
              )
            )
          ).map(_.flatten)
        )
      case KnowledgeSlot.Associative | KnowledgeSlot.Repeller =>
        throw IllegalArgumentException(
          s"a generated knowledge fills no justified property's slot: $slot"
        )
      case _ =>
        bound(term => s"(λk. k $term)")

  /** A family of `families`: its criterion, its arity, its distinct
    * constructors, and the member's text.
    */
  private final case class Family(
      criterion: String,
      arity: Int,
      constructors: Vector[String],
      text: String
  )

  private def family(prefix: String): Gen[Family] =
    for
      familyName <- name(prefix)
      criterion <- boundTerm(familyName)
      arity <- Gen.int(Range.linear(0, 3))
      constructorCount <- Gen.int(Range.linear(1, 4))
      constructors <- sequenced(
        Vector.tabulate(constructorCount)(position =>
          boundTerm(s"$familyName constructor $position")
        )
      )
    yield Family(
      criterion,
      arity,
      constructors,
      s"(λs. s $criterion ${integer(arity)} ${KnowledgeText.scottList(constructors)})"
    )

  /** A field criterion of a family of the arity, written closed: `parameter` of
    * an index below the arity, or `recursive`.
    */
  private def fieldCriterion(arity: Int): Gen[String] =
    if arity == 0 then Gen.constant(KnowledgeText.recursive)
    else
      Gen.frequency1(
        1 -> Gen.constant(KnowledgeText.recursive),
        2 -> Gen
          .int(Range.linear(0, arity - 1))
          .map(index => s"(λparameter _ _. parameter ${integer(index)})")
      )

  /** A lemma's proof, a constructor of `proof_kinds` (`munit`, `md`, `tex`)
    * written closed, of a citation of bounded length.
    */
  private val lemmaProof: Gen[String] =
    for
      alternative <- Gen.int(Range.constant(0, 2))
      citation <- boundedText(Gen.element1('/', '#', '.', '_', '-'), 40)
    yield s"(λmunit md tex. ${Vector("munit", "md", "tex")(alternative)} ${KnowledgeText.text(citation)})"

  /** A native implementation's or a representation's name. */
  private val backendName: Gen[String] = boundedText(Gen.constant('_'), 20)

  /** A name of the prefix and a drawn text of bounded length. */
  private def name(prefix: String): Gen[String] =
    boundedText(Gen.element1(' ', '_', '-'), 24).map(drawn => s"$prefix $drawn")

  /** A text of letters, digits and the extra characters, of at most `maximum`
    * characters.
    */
  private def boundedText(extra: Gen[Char], maximum: Int): Gen[String] =
    Gen.string(
      Gen.frequency1(6 -> Gen.alphaNum, 1 -> extra),
      Range.linear(0, maximum)
    )

  /** The text of a generated closed term of at most `termNodes` nodes. */
  private val closedTerm: Gen[String] =
    HoasGenerators
      .openTerm(0, termNodes)
      .map(open => LambdalatticeText.text(open(Vector.empty)))

  /** The term a member binds: the pair of the member's name and a generated
    * term.
    */
  private def boundTerm(memberName: String): Gen[String] =
    closedTerm.map(term => s"(λs. s ${KnowledgeText.text(memberName)} ($term))")

  /** The library's Scott integer of the natural, written closed. */
  private def integer(value: Int): String =
    s"(${Lambdalattice.text(Literals.integerTerm(BigInt(value)), Map.empty)})"

  /** The values of the generators, drawn in order. */
  private def sequenced[Value](
      generators: Vector[Gen[Value]]
  ): Gen[Vector[Value]] =
    generators.foldLeft(Gen.constant(Vector.empty[Value]))((drawn, next) =>
      drawn.flatMap(values => next.map(values :+ _))
    )
