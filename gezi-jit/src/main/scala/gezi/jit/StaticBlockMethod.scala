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

  /** The JVM convention of the method's operands: `java.math.BigInteger`s by
    * default, the one convention the narrow blocks call with; the group
    * blocks also call methods of JVM `int`s
    * (`StaticBlockOperands.JvmInts`).
    */
  def operands: StaticBlockOperands = StaticBlockOperands.Naturals

/** The JVM convention of a static block method's operands. */
enum StaticBlockOperands:

  /** Each a `java.math.BigInteger`, a place `NativePlace.NaturalList` a
    * `scala.collection.immutable.Vector` of them.
    */
  case Naturals

  /** Each a JVM `int`, the bits of a value of the family `jvm_int`
    * (`JvmIntNatives`).
    */
  case JvmInts

/** What a narrow block holds of a native's values. */
object StaticBlockMethod:

  /** The representation of every natural a narrow block holds: each is a
    * decoded literal or the result of a native that `resultHeld` admits.
    */
  val blockNatural: Representation[Nothing] = BinaryNaturalNatives.canonical

  /** Whether a block can hold the native's result as the method returns it,
    * the method taking its operands as the blocks pass them
    * (`StaticBlockOperands.Naturals`): a binary natural, canonical or
    * positive, returned as a `BigInteger`, or a truth value returned as a JVM
    * `boolean`.
    */
  def resultHeld(native: Native, method: StaticBlockMethod): Boolean =
    method.operands == StaticBlockOperands.Naturals && ((native.result, method.result) match
      case (NativePlace.Fixed(representation), StaticBlockResult.Natural) =>
        representation == blockNatural || representation == BinaryNaturalNatives.positive
      case (NativePlace.Fixed(Representation.Truth), StaticBlockResult.Truth) => true
      case _                                                                  => false)

/** The JVM convention of a static block method's result. */
enum StaticBlockResult:

  /** A `java.math.BigInteger`. */
  case Natural

  /** A JVM `boolean`. */
  case Truth

  /** A `java.math.BigInteger`, or null when the term the native is bound to
    * is ≃_O `top` on these operands (which a native whose term merely has no
    * normal form there may not claim: such a term can still give an answer in
    * a context that consumes it, as `(n ∥ t) true (λ_. true)` gives true for
    * naturals n ≠ t; such a native returns a `Lattice`). `StaticBlockMethod.resultHeld`
    * admits none of these, so no narrow block's arithmetic reads such a
    * result: the narrow blocks with lists call the method only at a block's
    * root (`gezi.narrowblocks.lists.NarrowBlockCompilation.noAnswerMethod`),
    * and a group block stops on a row on which it has no answer
    * (`gezi.narrowblocks.groups.GroupCompilation.resultHeld`).
    */
  case NaturalOrNoAnswer

  /** A `ConstructedNaturals`, a value of a declared data family. As with
    * `NaturalOrNoAnswer`, `StaticBlockMethod.resultHeld` admits none of these:
    * only the narrow blocks over declared families call the method, and only
    * at a block's root
    * (`gezi.narrowblocks.lists.NarrowBlockCompilation.constructedMethod`).
    */
  case Constructed

  /** A `scala.collection.immutable.Vector` of `java.math.BigInteger`, the
    * elements of a list of naturals, at a native's result place
    * `NativePlace.NaturalList`. As with `NaturalOrNoAnswer`,
    * `StaticBlockMethod.resultHeld` admits none of these: only the group
    * blocks call such a method (`gezi.narrowblocks.groups.GroupCompilation.resultHeld`),
    * and hold the list as the elements of an array list
    * (`gezi.jit.ArrayListStorage` at its exit).
    */
  case NaturalList

  /** A JVM `int`, the bits of a value of the family `jvm_int`
    * (`JvmIntNatives`), whose methods take their operands as `int`s too.
    * `StaticBlockMethod.resultHeld` admits none of these, so no narrow block
    * calls such a method; the group blocks do, by their own admission of the
    * natives of 32-bit words
    * (`gezi.narrowblocks.groups.GroupCompilation.resultHeld`).
    */
  case JvmInt

  /** A `NaturalLattice`, a term over naturals that the term the native is
    * bound to is ≃_O to on these operands. As with `NaturalOrNoAnswer`,
    * `StaticBlockMethod.resultHeld` admits none of these, and the group
    * blocks admit none either: only the narrow blocks with lists call such a
    * method, and only at a block's root
    * (`gezi.narrowblocks.lists.NarrowBlockCompilation.latticeMethod`), the
    * block replaced by the lattice's term.
    */
  case Lattice

/** A term built from canonical binary naturals by the choice and the
  * parallel, the result of a native whose term on its operands may have no
  * normal form and still not be ≃_O `top`: its equation is the native's
  * claim, that the term it is bound to is ≃_O this one, which a block then
  * stands for in the program.
  */
enum NaturalLattice:

  /** A canonical binary natural. */
  case Numeral(value: java.math.BigInteger)

  /** The choice of the members, nested to the right in their order; never
    * empty.
    */
  case Choice(members: Vector[NaturalLattice])

  /** The parallel of the two. */
  case Parallel(left: NaturalLattice, right: NaturalLattice)

/** A value of a declared data family whose fields are naturals: the position
  * of its constructor in the family's `data_family` and its fields in order.
  * It names no family: the block reads that from the filter in the term.
  */
final case class ConstructedNaturals(constructor: Int, fields: Vector[java.math.BigInteger])
