package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.{Configured, NativeSpecializer, NoFacts, Pure, Value}

/** A provider's family of the test, whose constructors' fields are the
  * representations given: a nullary constructor first, then one constructor of
  * the given fields. Its values are never taken apart: `taken` and `built`
  * throw, so a reading that takes one apart fails.
  */
final case class GeneratedProviderFamily(
    name: String,
    fields: Vector[FieldRepresentation]
) extends DataFamily:

  val identity: FamilyIdentity.Codec = FamilyIdentity.Codec(name)

  val parameterFamily: Option[FamilyIdentity] = None

  def constructors[Term](
      parameter: Option[FamilyParameter[Term]]
  ): Vector[DataConstructor] =
    Vector(
      DataConstructor(NativeName.Constructor(identity, 0), Vector.empty),
      DataConstructor(
        NativeName.Constructor(identity, 1),
        fields.map(field => DataField(field))
      )
    )

  def built[Term](
      parameter: Option[FamilyParameter[Term]],
      layer: DataLayer[Term]
  ): NativeValue[Term] =
    throw IllegalStateException(s"a value of $name was built")

  def taken[Term](
      parameter: Option[FamilyParameter[Term]],
      value: NativeValue[Term]
  ): DataLayer[Term] =
    throw IllegalStateException(s"a value of $name was taken apart")

/** A value of a generated family, which nothing takes apart. */
final case class GeneratedProviderValue(family: String)
    extends NativeValue[Nothing]

/** A tree of terms held as written, the value of the test's family
  * `unread_tree`: a leaf, or a node holding a term as written and two subtrees.
  */
enum UnreadTree[+Term] extends NativeValue[Term]:
  case Leaf
  case Node(term: Term, left: UnreadTree[Term], right: UnreadTree[Term])

/** The trees of terms held as written: a leaf, and a node of a field held as
  * written and two fields of the family itself. Its values hold terms, read
  * layer by layer.
  */
object UnreadTreeFamily extends DataFamily:

  val identity: FamilyIdentity.Codec = FamilyIdentity.Codec("unread_tree")

  val parameterFamily: Option[FamilyIdentity] = None

  def constructors[Term](
      parameter: Option[FamilyParameter[Term]]
  ): Vector[DataConstructor] =
    Vector(
      DataConstructor(NativeName.Constructor(identity, 0), Vector.empty),
      DataConstructor(
        NativeName.Constructor(identity, 1),
        Vector(
          DataField.unparameterised(UnreadFamily.identity),
          DataField.unparameterised(identity),
          DataField.unparameterised(identity)
        )
      )
    )

  def built[Term](
      parameter: Option[FamilyParameter[Term]],
      layer: DataLayer[Term]
  ): NativeValue[Term] =
    throw IllegalStateException("an unread tree was built")

  def taken[Term](
      parameter: Option[FamilyParameter[Term]],
      value: NativeValue[Term]
  ): DataLayer[Term] = value match
    case UnreadTree.Leaf                    => DataLayer(0, Vector.empty)
    case UnreadTree.Node(term, left, right) =>
      DataLayer(1, Vector(NativeValue.Unread(term), left, right))
    case other => throw IllegalArgumentException(s"no unread tree: $other")

/** The law of the families that hold no term (`StorageEncoding.holdsNoTerm`) on
  * generated provider families, built by construction as a chain F0 → F1 → … →
  * Fm, each Fi with a field of F(i + 1), and in some a field of F0 at Fm, which
  * closes a cycle; each family's other fields drawn among a natural, a boolean
  * and itself; and a poisoned field (held as written, filtered, of a declared
  * family, or a list, each kind by construction) at a drawn family Fd, or at
  * none. Derived before the run from the chain's construction, not from the
  * walk: Fi reaches exactly F(i) … F(m), and every family when the cycle is
  * closed, so Fi holds no term exactly when no poison is among the families it
  * reaches. A family that holds no term is answered no terms without its value
  * being taken apart (its `taken` throws). Its purpose is to catch a check that
  * calls a family term-free though a field it reaches may hold a term (a walk
  * that stops before the fields, or that leaves a declared family or a list
  * out), and a reading of a term-free value that takes it apart.
  */
class ProviderValueHeldTermsLawTest extends GeneratedProperties:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => NativesTesting.nativesOn)

  /** A field's representation of one representation at every configuration. */
  private def fixed(
      representation: Representation[Nothing]
  ): FieldRepresentation = FieldRepresentation.fixed(representation)

  /** The opaque criterion of the generated filters, a term of each
    * configuration.
    */
  private def criterionIn[C <: NativeSpecializer & Singleton](using
      specializer: C
  ): JitValue[C] =
    Value.of(specializer.opaque("generated filter criterion"))

  /** A poisoned field: the family it names and its representation. */
  private final case class Poison(
      identity: FamilyIdentity,
      field: FieldRepresentation
  )

  /** The criterion of the generated declared family, a pure key under no facts.
    */
  private val declaredCriterion: Pure =
    Pure.required(NoFacts.opaque("generated declared criterion"))

  /** The poisoned field of each kind. */
  private val poisons: Vector[Poison] = Vector(
    Poison(
      UnreadFamily.identity,
      fixed(Representation.Data(UnreadFamily.identity, None))
    ),
    Poison(
      FilteredFamily.identity,
      new FieldRepresentation:
        def apply[C <: NativeSpecializer & Singleton](
            parameter: Option[FamilyParameter[JitValue[C]]]
        )(using C): Representation[JitValue[C]] =
          Representation.Data(
            FilteredFamily.identity,
            Some(FieldFilter(criterionIn[C]))
          )
    ),
    Poison(
      FamilyIdentity.Declared(declaredCriterion),
      fixed(
        Representation.Data(FamilyIdentity.Declared(declaredCriterion), None)
      )
    ),
    Poison(
      Representation.listFamily,
      new FieldRepresentation:
        def apply[C <: NativeSpecializer & Singleton](
            parameter: Option[FamilyParameter[JitValue[C]]]
        )(using C): Representation[JitValue[C]] =
          Representation.ListOf(criterionIn[C])
    )
  )

  /** The other fields: a natural, a boolean, or the family itself. */
  private def plainField(self: FamilyIdentity, draw: Int): FieldRepresentation =
    draw match
      case 0 => fixed(Representation.BigInteger)
      case 1 => fixed(Representation.Truth)
      case _ => fixed(Representation.Data(self, None))

  property(
    "a provider family holds no term exactly when it reaches no poisoned field, and its values are not taken apart"
  ) {
    for
      length <- Gen.int(Range.linear(1, 5)).forAll
      plain <- Gen.int(Range.linear(0, 2)).list(Range.singleton(5)).forAll
      poisonDepth <- Gen.int(Range.linear(0, 4)).forAll
      round <- Gen.long(Range.linear(0L, Long.MaxValue)).forAll
    yield
      val depth = poisonDepth % length
      val chains =
        for
          cycle <- Vector(false, true)
          poison <- None +: poisons.map(Some(_))
        yield
          val names = Vector.tabulate(length)(index =>
            s"generated_${round}_${cycle}_${poison.fold("none")(_.identity.shown)}_$index"
          )
          val families = names.indices.toVector.map { index =>
            val self = FamilyIdentity.Codec(names(index))
            val next =
              if index + 1 < length then
                Vector(
                  fixed(
                    Representation
                      .Data(FamilyIdentity.Codec(names(index + 1)), None)
                  )
                )
              else if cycle then
                Vector(
                  fixed(
                    Representation.Data(FamilyIdentity.Codec(names(0)), None)
                  )
                )
              else Vector.empty
            val poisoned = if index == depth then poison.map(_.field).toVector
            else Vector.empty
            GeneratedProviderFamily(
              names(index),
              plainField(self, plain(index)) +: (next ++ poisoned)
            )
          }
          (cycle, poison, names, families)
      // One backend with every chain of the iteration: the chains share no family.
      val encoding: StorageEncoding =
        BackendFacts
          .of(
            NativesTesting.nativesOn,
            NativeBackend.standard
              .extended(NativeBackend(Map.empty, chains.flatMap(_._4)))
          )
          .storageEncoding
      val operations = encoding.operations
      val checks = chains.toList.map { (cycle, poison, names, _) =>
        val expected = names.indices.toVector.map(index =>
          poison.isEmpty || !(cycle || index <= depth)
        )
        val found = names.indices.toVector.map(index =>
          operations.holdsNoTerm(
            Representation.Data(FamilyIdentity.Codec(names(index)), None)
          )
        )
        val heldOfFree = names.indices.toVector.collect {
          case index if found(index) =>
            operations.heldTerms(
              Representation.Data(FamilyIdentity.Codec(names(index)), None),
              GeneratedProviderValue(names(index))
            )
        }
        Result
          .diff((found, heldOfFree.forall(_.isEmpty)), (expected, true))(_ == _)
          .log(s"length $length, cycle $cycle, poison $poison at $depth")
      }
      Result.all(checks)
  }

  /** The law that a value of a family that may hold terms gives the terms it
    * holds depth first, in the order of its fields, however deep its layers go:
    * a tree of `unread_tree` built by construction along a spine of 20,000 to
    * 40,000 nodes, each spine node's term followed by a small subtree of drawn
    * shape and then the rest of the spine, each term distinct. Derived before
    * the run from the construction, not from the reading: the expected terms
    * are listed as the tree is built, a node's term, then its left subtree's,
    * then its right's. Its purpose is to catch a reading that recurses a frame
    * of the stack a layer (on 0f32fb14b, under the test JVM's default thread
    * stack, such a spine overflowed it), and one that gives the terms in
    * another order, breadth first among them.
    */
  property(
    "a deep value of a family that may hold terms gives its terms depth first in the order of its fields",
    _.copy(testLimit = hedgehog.core.SuccessCount(5))
  ) {
    for
      length <- Gen.int(Range.linear(20000, 40000)).forAll
      shapes <- Gen.int(Range.linear(0, 3)).list(Range.singleton(8)).forAll
    yield
      val encoding: StorageEncoding =
        BackendFacts
          .of(
            NativesTesting.nativesOn,
            NativeBackend.standard
              .extended(NativeBackend(Map.empty, Vector(UnreadTreeFamily)))
          )
          .storageEncoding
      given encoding.type = encoding
      type Term = JitValue[encoding.type]
      def term(name: String): Term =
        Value.of(encoding.opaque(s"unread tree term $name"))
      // A small subtree of the drawn shape at a spine node, with its terms in
      // depth-first order: a leaf, a node over two leaves, a node with a node
      // on its left, or on its right.
      def side(index: Int): (UnreadTree[Term], Vector[Term]) =
        def node(
            name: String,
            left: UnreadTree[Term],
            right: UnreadTree[Term]
        ): UnreadTree[Term] = UnreadTree.Node(term(name), left, right)
        val (first, second) = (s"$index side", s"$index side inner")
        shapes(index % shapes.size) match
          case 0 => (UnreadTree.Leaf, Vector.empty)
          case 1 =>
            (node(first, UnreadTree.Leaf, UnreadTree.Leaf), Vector(term(first)))
          case 2 =>
            (
              node(
                first,
                node(second, UnreadTree.Leaf, UnreadTree.Leaf),
                UnreadTree.Leaf
              ),
              Vector(term(first), term(second))
            )
          case _ =>
            (
              node(
                first,
                UnreadTree.Leaf,
                node(second, UnreadTree.Leaf, UnreadTree.Leaf)
              ),
              Vector(term(first), term(second))
            )
      val (tree, expected) = (0 until length).reverse.foldLeft(
        (UnreadTree.Leaf: UnreadTree[Term], Vector.empty[Term])
      ) { case ((rest, restTerms), index) =>
        val (subtree, subtreeTerms) = side(index)
        (
          UnreadTree.Node(term(s"$index"), subtree, rest),
          (term(s"$index") +: subtreeTerms) ++ restTerms
        )
      }
      val held = encoding.operations.heldTerms(
        Representation.Data(UnreadTreeFamily.identity, None),
        tree
      )
      Result
        .assert(
          held.size == expected.size && held
            .zip(expected)
            .forall((found, wanted) => Value.same(found, wanted))
        )
        .log(s"the terms held: ${held.size}, expected ${expected.size}")
  }
