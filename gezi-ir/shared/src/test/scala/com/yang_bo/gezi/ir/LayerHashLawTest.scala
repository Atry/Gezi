package com.yang_bo.gezi.ir

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.StandInStorages
import com.yang_bo.gezi.generatedinputs.StoreGenerators

/** The laws of the constructors' hash code and equality (`ConstructorIdentity`,
  * `InternedConstructor`), on the instructions of generated stores. Outside the
  * pool an interned object hashes by its identity and is equal only to itself,
  * a layer made again of the same fields is that very object, every constructor
  * but the parallel being interned when it is made, and a parallel made again
  * is another object, the term only once interned (a construction site converts
  * a parallel to a native storage before it interns it); the pool's
  * single-layer hash code reads each constructor field by its identity, so that
  * it is a residue and two layers whose fields are a permutation of each
  * other's, `x y` and `y x`, differ. Its purpose is to catch a hash code or an
  * equality that still walks the content outside the pool, and a single-layer
  * hash that collides on the shapes the IR builds most.
  */
class LayerHashLawTest extends GeneratedProperties:

  property(
    "outside the pool an instruction hashes by its identity, and its layer made again is it, a parallel once interned"
  ) {
    for generated <- StoreGenerators.store.forAll
    yield
      val instructions = generated.instructions.toVector
      Result.all(
        instructions.toList.map(instruction =>
          val layer = instruction.layer
          val again: AnyRef = layer match
            case Apply(function, argument) => Apply.ofTerms(function, argument)
            case Parallel(left, right)     => Parallel.ofTerms(left, right)
            case Choice(left, right)       => Choice.ofTerms(left, right)
            case Thunk(code, holes, fillings) =>
              Thunk.ofTerms(code, holes, fillings)
            case UriNode(uri)           => UriNode(uri)
            case Opaque(name)           => Opaque(name)
            case storage: NativeStorage => storage
          Result
            .assert(
              instruction.## == System.identityHashCode(
                instruction
              ) && (Interned.canonicalLayer(again) eq (layer: AnyRef)) &&
                (layer match
                  case _: Parallel[?] => !(again eq (layer: AnyRef))
                  case _              => again eq (layer: AnyRef))
            )
            .log(s"$instruction")
        )
      )
  }

  /** Two instructions drawn from a generated store, with repetition. */
  private val two: hedgehog.Gen[(StandInStorages.Term, StandInStorages.Term)] =
    for
      generated <- StoreGenerators.store
      first <- Gen.int(Range.linear(0, 1000))
      second <- Gen.int(Range.linear(0, 1000))
    yield
      val instructions = generated.instructions.toVector
      (
        instructions(first % instructions.size),
        instructions(second % instructions.size)
      )

  property(
    "the single-layer hash code is a residue, and x y and y x differ when x and y do"
  ) {
    for (x, y) <- two.forAll
    yield
      val forward = ConstructorIdentity.singleLayerHash(Apply.ofTerms(x, y))
      val backward = ConstructorIdentity.singleLayerHash(Apply.ofTerms(y, x))
      Result.all(
        List(
          Result.assert(
            forward >= 0 && ConstructorIdentity.raw(forward) == forward
          ),
          Result
            .assert(
              Configured.same(x, y)(using
                StandInStorages
              ) || forward != backward
            )
            .log(s"$x and $y")
        )
      )
  }
