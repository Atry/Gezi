package gezi.jit

/** A native implementation that a narrow block may call directly:
  * the binary name of a public class and the
  * name of its public static method, which takes the native's places as
  * `java.math.BigInteger`, the binary naturals' JVM type, a place
  * `NativePlace.NaturalList` as a `scala.collection.immutable.Vector` of them,
  * and returns its result in the JVM convention `result` names. The block compiler emits
  * `invokestatic` on it, so the framework names no contributed native: a native
  * whose implementation is not one of these is not compiled into a block,
  * and the block goes to the general reading.
  *
  * The static method computes what the implementation computes on its
  * argument vector (`StaticBlockMethodLawTest` checks it on generated
  * canonical naturals). It is called only on operands the block already
  * holds as canonical naturals, so it checks nothing of its operands (`CONTRIBUTING.md`, "Types live only in the term").
  */
trait StaticBlockMethod:

  /** The binary name of the public class that holds the method. */
  def className: String

  /** The name of the public static method. */
  def methodName: String

  /** The JVM convention of the method's result: a `BigInteger`, or a JVM
    * `boolean`. It says how the block calls the method, not what the result
    * is: a block reads a boolean only under the filter `∥ boolean_type`
    * written in the term.
    */
  def result: StaticBlockResult = StaticBlockResult.Natural

/** What a narrow block holds of a native's values. */
object StaticBlockMethod:

  /** The representation of every natural a narrow block holds: each is a
    * decoded literal or the result of a native that `resultHeld` admits.
    */
  val blockNatural: Representation = BinaryNaturalNatives.canonical

  /** Whether a block can hold the native's result as the method returns it:
    * a binary natural, canonical or positive, returned as a `BigInteger`, or
    * a truth value returned as a JVM `boolean`.
    */
  def resultHeld(native: Native, method: StaticBlockMethod): Boolean =
    (native.result, method.result) match
      case (NativePlace.Fixed(representation), StaticBlockResult.Natural) =>
        representation == blockNatural || representation == BinaryNaturalNatives.positive
      case (NativePlace.Fixed(Representation.Truth), StaticBlockResult.Truth) => true
      case _                                                                  => false

/** The JVM convention of a static block method's result. */
enum StaticBlockResult:

  /** A `java.math.BigInteger`. */
  case Natural

  /** A JVM `boolean`. */
  case Truth
