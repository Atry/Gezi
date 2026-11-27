package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The law of combining the natives providers (`NativesProvider.combined`):
  * the providers' natives and families are added to the standard set when
  * no native and no family is named twice, and the combination is refused
  * when one is, in two providers or in a provider and the standard set. Its
  * purpose is to catch one provider's native or family silently replacing
  * another's, which `extended` alone does, in the order the service loader
  * found them. The native names are drawn from a few letters, so that
  * clashes are common, together with a name of the standard set; the
  * families are the test's `natural_pair` or the standard set's booleans.
  */
class NativesProviderLawTest extends GeneratedProperties:

  private val native: Native = Native(Vector.empty, NativePlace.Fixed(Representation.BigInteger), _ => NativeValue.Natural(0))

  private val standardName: String =
    NativeBackend.standard.natives.keys.toVector.collect { case NativeName.Function(found) => found }.sorted.headOption.getOrElse(
      throw IllegalStateException("the standard set has functions")
    )

  private val name: Gen[String] =
    Gen.frequency1(9 -> Gen.element1("a", "b", "c", "d", "e", "f").map("provided_" + _), 1 -> Gen.constant(standardName))

  /** A family: the test's `natural_pair` (`NativeBackendExtensionTest`),
    * which no other set has, or the standard set's booleans.
    */
  private val family: Gen[DataFamily] = Gen.element1(NaturalPairFamily, BooleanFamily)

  private val provider: Gen[NativeBackend] =
    for
      names <- name.list(Range.linear(0, 3))
      families <- family.list(Range.linear(0, 1))
    yield NativeBackend.functions(names.distinct.map(_ -> native).toMap, families.toVector)

  property("providers combine when no name is given twice, and are refused when one is") {
    for providers <- provider.list(Range.linear(0, 3)).forAll
    yield
      val named = NativeBackend.standard.natives.keys.toVector ++ providers.flatMap(_.natives.keys)
      val familyIdentities = NativeBackend.standard.families.map(_.identity) ++ providers.flatMap(_.families.map(_.identity))
      val combined = scala.util.Try(NativesProvider.combined(providers.toVector))
      if named.distinct.size == named.size && familyIdentities.distinct.size == familyIdentities.size then
        Result.diff(
          combined.map(backend => (backend.natives.keySet, backend.families.map(_.identity).toSet)).toOption,
          Some((named.toSet, familyIdentities.toSet))
        )(_ == _)
      else Result.assert(combined.failed.toOption.exists(_.isInstanceOf[IllegalStateException])).log(s"named: $named, families: $familyIdentities")
  }
