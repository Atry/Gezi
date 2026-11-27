package gezi.ir

import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.StandInStorages
import gezi.generatedinputs.StoreGenerators

/** Every term is interned (`gezi.ir.Interned`): a term built again from fresh
  * constructor objects, each part built again too and each atom a fresh string,
  * is the very object of the generated term (`eq`). Its purpose is to catch a
  * term made around the pool, and a hash code or an equality of a constructor
  * that is not its content's, either of which gives one content two objects.
  */
class InterningLawTest extends GeneratedProperties:

  /** The code built again from fresh layers. */
  private def rebuiltCode(code: Code): Code = code.layer match
    case Slot(index)               => Code(Slot(index))
    case Apply(function, argument) =>
      Code(Apply(rebuiltCode(function), rebuiltCode(argument)))
    case Parallel(left, right) =>
      Code(Parallel(rebuiltCode(left), rebuiltCode(right)))
    case Choice(left, right) =>
      Code(Choice(rebuiltCode(left), rebuiltCode(right)))
    case Thunk(inner, holes, fillings) =>
      Code(Thunk(rebuiltCode(inner), holes, fillings.map(rebuiltCode)))

  /** The term built again from fresh layers, through the specializer. */
  private def rebuilt(term: StandInStorages.Term): StandInStorages.Term =
    term.layer match
      case Opaque(name) => StandInStorages.opaque(String(name.toCharArray))
      case UriNode(uri) => StandInStorages.uri(java.net.URI(uri.toString))
      case Apply(function, argument) =>
        StandInStorages.application(rebuilt(function), rebuilt(argument))
      case Parallel(left, right) =>
        StandInStorages.parallel(rebuilt(left), rebuilt(right))
      case Choice(left, right) =>
        StandInStorages.choice(rebuilt(left), rebuilt(right))
      case Thunk(code, holes, fillings) =>
        StandInStorages.thunk(
          rebuiltCode(code),
          NonEmptyHoles
            .of(holes)
            .getOrElse(
              throw IllegalStateException(
                s"a generated thunk has no hole: $term"
              )
            ),
          fillings.map(rebuilt)
        )
      case storage: NativeStorage =>
        throw IllegalStateException(
          s"a generated store holds no storage: $storage"
        )

  property("aTermBuiltAgainFromFreshLayersIsTheSameObject") {
    for generated <- StoreGenerators.store.forAll
    yield Result.all(
      generated.instructions.toList.map(instruction =>
        Result
          .assert(
            Configured.same(rebuilt(instruction), instruction)(using
              StandInStorages
            )
          )
          .log(s"rebuilt $instruction")
      ) ++
        generated.codes.toList.map(code =>
          Result.assert(rebuiltCode(code) eq code).log(s"rebuilt code $code")
        )
    )
  }

  /** A layer over class numbers, as the e-graph keys its congruence table by,
    * interned from two fresh objects: one object, so that the table can find a
    * node by the layer's identity.
    */
  property("aLayerOverClassNumbersInternedTwiceIsOneObject") {
    for
      function <- hedgehog.Gen.int(hedgehog.Range.linear(0, 1000)).forAll
      argument <- hedgehog.Gen.int(hedgehog.Range.linear(0, 1000)).forAll
    yield
      val first = Interned.canonicalLayer(Apply(function, argument))
      val second = Interned.canonicalLayer(Apply(function, argument))
      Result
        .assert(first eq second)
        .log(s"Apply($function, $argument) interned twice")
  }

  /** The law that interning a layer reads no field's hash code or equality: a
    * field that throws when asked either, except while the pool interns that
    * field itself, interned under `Apply` and `Thunk` of a generated width, is
    * no obstacle, and the layer made again is the same object. Its purpose is
    * to catch an interning whose cost grows with the term below the layer,
    * which a hash code or an equality read from a field would walk.
    */
  property(
    "interning a layer of a generated width asks no field for its hash code or equality"
  ) {
    for width <- hedgehog.Gen.int(hedgehog.Range.linear(1, 8)).forAll
    yield
      val probes = Vector.tabulate(width)(index =>
        Interned.canonicalLayer(InterningProbe(index))
      )
      def applied: AnyRef = probes.reduceLeft[AnyRef]((function, argument) =>
        Interned.canonicalLayer(Apply.ofTerms(function, argument))
      )
      def thunk: AnyRef = Interned.canonicalLayer(
        Thunk.ofTerms(Code.Slot(0), Vector(Hole.Bound(0)), probes)
      )
      Result.all(
        List(Result.assert(applied eq applied), Result.assert(thunk eq thunk))
      )
  }

/** A field that answers its hash code and equality only while the pool interns
  * it (as the object interned or the one the pool compares it with), and throws
  * otherwise.
  */
final case class InterningProbe(index: Int) extends InternedConstructor:
  override def hashCode: Int =
    if Canonicalization.interning(this) then super.hashCode
    else
      throw IllegalStateException(s"a field's hash code was read: probe $index")
  override def equals(other: Any): Boolean = other match
    case that: AnyRef
        if Canonicalization
          .interning(this) || Canonicalization.interning(that) =>
      super.equals(that)
    case _ =>
      throw IllegalStateException(s"a field's equality was read: probe $index")
