package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The law of the families of the JVM's bit tuples (`JvmBitsFamily`): at every
  * width, `built` after `taken` is the identity, and the layer has one field
  * for each bit. Its purpose is to catch a codec that loses a bit, keeps one
  * above the width, or takes a layer of the wrong size.
  */
class JvmBitsFamilyLawTest extends GeneratedProperties:

  private val value: Gen[JvmBits] =
    for
      width <- Gen.elementUnsafe(JvmBitsFamily.widths.toList)
      bits <- Gen.list(Gen.boolean, Range.singleton(java.lang.Long.SIZE))
    yield JvmBitsFamily.masked(width, bits.foldLeft(0L)((sofar, bit) => (sofar << 1) | (if bit then 1L else 0L)))

  property("built after taken is the identity, with one field for each bit") {
    for found <- value.forAll
    yield
      val family = JvmBitsFamily(found.width)
      val layer = family.taken(None, found)
      Result.all(List(Result.diff(family.built(None, layer), found: NativeValue)(_ == _), Result.diff(layer.fields.size, found.width)(_ == _)))
  }
