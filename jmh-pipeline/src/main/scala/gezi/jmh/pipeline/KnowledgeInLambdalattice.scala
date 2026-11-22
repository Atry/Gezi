package gezi.jmh.pipeline

import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.ir.Instruction
import gezi.ir.Reachability
import gezi.standardlibrary.Property
import gezi.standardlibrary.StandardLibraryIndex

/** A slot of the knowledge term's top-level mixin: what its members are. */
enum KnowledgeSlot:

  /** The lemmas, each member a Scott pair `\s. s L R`. */
  case Lemmas

  /** The defines that have the combinator property. */
  case WithProperty(property: Property)

  /** The defines that the native implementation of the name implements. */
  case Implemented(native: String)

/** What a reader of the knowledge gives the index: the lemmas' sides, and
  * the members of each property slot and of each native slot, each in the
  * order of the slots.
  */
final case class KnowledgeRead(
    lemmas: Vector[(Instruction, Instruction)],
    properties: Vector[(Property, Vector[Instruction])],
    natives: Vector[(String, Vector[Instruction])]
):

  /** Each list with its repetitions dropped: what an index built of the
    * reading holds, the knowledge combined with itself k times reading as it
    * once.
    */
  def distinct: KnowledgeRead = KnowledgeRead(
    lemmas.distinct,
    properties.map((property, members) => (property, members.distinct)),
    natives.map((native, members) => (native, members.distinct))
  )

/** The knowledge base of a compiled standard library written as one term,
  * to measure what reading the knowledge as a term on the weak-head evaluator
  * costs against the current reader's load: the top level
  * is a mixin (`gezi.contest.corpora.merges.MixinLibrary`'s encoding, a
  * choice of wrappers `\self. \c1. ... \cW. cm b`), whose slots are the
  * lemmas, each entry of the vocabulary of combinator
  * properties and each native implementation; slot m's wrapper has for its
  * b the choice of the slot's members; a member of a lemma slot is the Scott
  * pair `\s. s L R`. Each define's body and each lemma side is the instruction the
  * current reader (`gezi.standardlibrary.StandardLibrary`) gave it,
  * written in place: the encoding writes a combinator's body into every file that refers to it, and hash consing makes it the
  * define's instruction. The slots are the lemmas, the vocabulary's
  * entries without an argument, the representations of the
  * native specializations the index has, and the natives the index binds:
  * the encoding has the width set by the vocabulary and the native registry on
  * the Scala side, which this measurement stands in for by the index's own.
  */
object KnowledgeInLambdalattice:

  /** The slots of the index's knowledge, in order. */
  def slots(index: StandardLibraryIndex): Vector[KnowledgeSlot] =
    val fixed = Vector(
      Property.Associative,
      Property.Noinline,
      Property.NameMarker,
      Property.ClosureMarker,
      Property.TagOrigin,
      Property.TagNext,
      Property.FirstOrderConstructor
    )
    val specializations = index.combinatorProperties
      .map(_.property)
      .collect { case specialization: Property.NativeSpecialization => specialization }
      .distinct
    Vector(KnowledgeSlot.Lemmas) ++
      (fixed ++ specializations).map(KnowledgeSlot.WithProperty(_)) ++
      index.nativeBound.map(_.native).distinct.map(KnowledgeSlot.Implemented(_))

  /** What the current reader's index holds, as a reader of the knowledge
    * term gives it: the expected reading.
    */
  def expected(index: StandardLibraryIndex): KnowledgeRead =
    val layout = slots(index)
    KnowledgeRead(
      index.lemmaSides.map(sides => (sides.left, sides.right)),
      layout.collect { case KnowledgeSlot.WithProperty(property) => (property, index.withProperty(property)) },
      layout.collect { case KnowledgeSlot.Implemented(native) =>
        (native, index.nativeBound.filter(_.native == native).map(_.instruction))
      }
    )

  /** The members of each slot, in the order of the slots: Scott pairs in a
    * lemma slot, the defines' instructions in the others.
    */
  def members(index: StandardLibraryIndex): Vector[Vector[Instruction]] =
    slots(index).map {
      case KnowledgeSlot.Lemmas =>
        index.lemmaSides.map(sides => pair(sides.left, sides.right))
      case KnowledgeSlot.WithProperty(property) => index.withProperty(property)
      case KnowledgeSlot.Implemented(native) =>
        index.nativeBound.filter(_.native == native).map(_.instruction)
    }

  /** The knowledge term: the choice of the wrapper of each slot that has a
    * member, b the choice of its members ended by top (`noAnswer`),
    * `m1 + (m2 + (… + (mn + top)))`: the IR's choice is binary, and a member
    * that is itself a choice (a define such as `true + false`) is a left
    * side, so that the reader tells it from the chain (`KnowledgeReader`).
    */
  def term(index: StandardLibraryIndex): Instruction =
    val slotMembers = members(index)
    val width = slotMembers.size
    Instruction.Choice.nested(slotMembers.zipWithIndex.collect {
      case (contents, position) if contents.nonEmpty =>
        wrapper(width, position, Instruction.Choice.nested(contents :+ noAnswer))
    })

  /** top (`gezi.frontend.Literals.top`), the term of no answer, which ends
    * a slot's chain of members and fills an unhandled slot.
    */
  lazy val noAnswer: Instruction = Defunctionalization.thunkInstruction(gezi.frontend.Literals.top)

  /** The knowledge term combined with itself `copies` times by `+`: the
    * record's enabling of several files, each one copy.
    */
  def combined(knowledge: Instruction, copies: Int): Instruction =
    require(copies >= 1, s"a knowledge base is combined at least once: $copies")
    Instruction.Choice.nested(Vector.fill(copies)(knowledge))

  /** `\self. \c1. ... \cW. cm b`, m the position, from 0, among the W slots. */
  def wrapper(width: Int, position: Int, body: Instruction): Instruction =
    val handler = DeBruijnTerm.Variable(width - 1 - position)
    val chain = (0 to width).foldLeft(DeBruijnTerm.Apply(handler, DeBruijnTerm.Constant(body)): DeBruijnTerm)(
      (inner, _) => DeBruijnTerm.Lambda(inner)
    )
    Defunctionalization.thunkInstruction(chain)

  /** The Scott pair `\s. s left right`. */
  def pair(left: Instruction, right: Instruction): Instruction =
    Defunctionalization.thunkInstruction(
      DeBruijnTerm.Lambda(
        DeBruijnTerm.Apply(
          DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), DeBruijnTerm.Constant(left)),
          DeBruijnTerm.Constant(right)
        )
      )
    )

  /** The number of instructions under the term, itself included, and of
    * those under the members alone (the lemma sides and the defines): their
    * difference is the encoding's own.
    */
  def sizes(index: StandardLibraryIndex, knowledge: Instruction): (Int, Int) =
    val under = Reachability.instructionsUnder(Vector(knowledge)).size
    val sideAndDefines = index.lemmaSides.flatMap(sides => Vector(sides.left, sides.right)) ++
      index.combinatorProperties.map(_.instruction) ++ index.nativeBound.map(_.instruction)
    (under, Reachability.instructionsUnder(sideAndDefines).size)
