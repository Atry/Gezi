package gezi.jit

import gezi.weakhead.StorageReading
import gezi.ir.Value
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Configured, NativeSpecializer, Pure}

/** The reader's storage option (`gezi.weakhead.StorageReading`) under one
  * backend's facts: a storage of this encoding whose view is the unique
  * spelling is read as the left side of its view, `C ȳ`
  * (`StorageEncoding.spelled`), and a parallel the reader builds is converted
  * by the encoding (`StorageEncoding.parallel`), whose one admission takes
  * instructions only, a storage that is one included. A native the facts bind to a define,
  * whose places and result are fixed representations, is called on an exact
  * application of the define whose arguments have values (`called`). Of one
  * configuration `C`, whose encoding it reads with: a storage it meets is one
  * of `C`'s terms. Its equality is the object's: the cache's namespaces of
  * completed tables are named by the configuration's specializer, so two
  * builds of one library's facts share none.
  */
final class StorageReadingOfFacts[C <: NativeSpecializer & Singleton] private (
    val encoding: StorageEncoding & C,
    natives: Map[JitValue[C], (NativeName, Native)]
) extends StorageReading[C]:

  private given C = encoding

  private val operations: StorageEncodingOperations[C] = encoding.operations

  /** The most parameters of a native the option calls: the bound on the
    * applications `called` strips.
    */
  private val largestArity: Int = natives.values.map(_._2.parameterCount).maxOption.getOrElse(0)

  // The JIT reads a native's arguments by its own machinery (`JitRules`'
  // native values, which evaluate an argument to its heads in the JIT's state
  // and decode points); the reader calls a native only on arguments that
  // already are values, by syntax, so it shares the natives and the encoding
  // and not that machinery, which runs over the JIT's values and state.
  def called(term: Value[C]): (Option[Value[C]], Int) =
    calledOf(term).result

  private def calledOf(term: JitValue[C]): TailRec[(Option[JitValue[C]], Int)] =
    tailcall(ready(term)).flatMap(isReady => if isReady then computed(term) else done((None, 0)))

  /** Whether the term is an exact native application whose arguments have
    * values, read before any native is called, so that no call is made whose
    * result would be dropped.
    */
  private def ready(term: JitValue[C]): TailRec[Boolean] =
    applied(term, Nil, largestArity) match
      case None => done(false)
      case Some((native, arguments)) => argumentsReady(native.parameters.zip(arguments).toList)

  private def argumentsReady(pending: List[(NativePlace, JitValue[C])]): TailRec[Boolean] = pending match
    case Nil => done(true)
    case (NativePlace.Fixed(representation), argument) :: rest =>
      if stored(argument, representation).isDefined then tailcall(argumentsReady(rest))
      else
        tailcall(resultRepresentation(argument)).flatMap {
          case Some(found) if found == representation => tailcall(argumentsReady(rest))
          case _                                     => done(false)
        }
    case (other, _) :: _ => throw IllegalStateException(s"a native the option calls has fixed places only, not $other")

  /** The representation of the result of the exact native application the
    * term is, when its arguments have values.
    */
  private def resultRepresentation(term: JitValue[C]): TailRec[Option[Representation[Nothing]]] =
    applied(term, Nil, largestArity) match
      case None => done(None)
      case Some((native, arguments)) =>
        tailcall(argumentsReady(native.parameters.zip(arguments).toList)).map(isReady =>
          native.result match
            case NativePlace.Fixed(representation) if isReady => Some(representation)
            case _                                             => None
        )

  /** The result of a ready native application, and the natives called. */
  private def computed(term: JitValue[C]): TailRec[(Option[JitValue[C]], Int)] =
    applied(term, Nil, largestArity) match
      case None => throw IllegalStateException(s"a ready term is a native application: $term")
      case Some((native, arguments)) =>
        valuesOf(native.parameters.zip(arguments).toList, Vector.empty, 0).map((values, calls) =>
          native.result match
            case NativePlace.Fixed(representation) =>
              (Some(operations.storageOf(representation, native.implementation(values.map(NativeArgument.Represented(_))))), calls + 1)
            case other => throw IllegalStateException(s"a native the option calls has the fixed result it was chosen for, not $other")
        )

  /** The native the term applies and its arguments, when the term is a
    * define the option calls applied to exactly its parameters; at most
    * `remaining` applications stripped, so that a define that is itself an
    * application is found from the outside.
    */
  @scala.annotation.tailrec
  private def applied(term: JitValue[C], arguments: List[JitValue[C]], remaining: Int): Option[(Native, List[JitValue[C]])] =
    natives.get(term) match
      case Some((_, native)) if native.parameterCount == arguments.size => Some((native, arguments))
      case _ =>
        term match
          case JitValue.Apply(function, argument) if remaining > 0 => applied(function, argument :: arguments, remaining - 1)
          case _                                                   => None

  /** The values of the arguments of a ready application at the places, in
    * order, and the natives called to get them: a storage of the place's
    * representation, or the result of the inner native application.
    */
  private def valuesOf(
      pending: List[(NativePlace, JitValue[C])],
      found: Vector[NativeValue[JitValue[C]]],
      calls: Int
  ): TailRec[(Vector[NativeValue[JitValue[C]]], Int)] =
    pending match
      case Nil => done((found, calls))
      case (NativePlace.Fixed(representation), argument) :: rest =>
        stored(argument, representation) match
          case Some(value) => tailcall(valuesOf(rest, found :+ value, calls))
          case None =>
            tailcall(computed(argument)).flatMap {
              case (Some(result), innerCalls) =>
                stored(result, representation) match
                  case Some(value) => tailcall(valuesOf(rest, found :+ value, calls + innerCalls))
                  case None        => throw IllegalStateException(s"a ready argument's native gave no storage of its place: $result")
              case (None, _) => throw IllegalStateException(s"a ready argument has a value: $argument")
            }
      case (other, _) :: _ => throw IllegalStateException(s"a native the option calls has fixed places only, not $other")

  /** The native data of the storage the node is, when it is one of the representation: a fixed place's
    * representation holds no declared family's value, so the storage's data is its value.
    */
  private def stored(node: JitValue[C], representation: Representation[Nothing]): Option[NativeValue[JitValue[C]]] = node match
    case JitValue.Stored(storage) if storage.representation == representation => Some(StorageOf.nativeValue(storage))
    case _                                                                     => None

/** The reader's storage option of the facts. */
object StorageReadingOfFacts:

  /** The option under the facts: their encoding, and the natives the facts
    * bind to defines that are functions of fixed places with a fixed result
    * (a data family's constructor is the conversion's, not a call).
    */
  def apply[C <: NativeSpecializer & Singleton](encoding: StorageEncoding & C): StorageReadingOfFacts[C] =
    new StorageReadingOfFacts[C](
      encoding,
      callable(encoding.facts).map((define, named) => Value.of(Configured.fromPure[C](encoding)(define))(using encoding) -> named)
    )

  /** The natives callable on storage values under the facts, by the define
    * each is bound to: for each define, the first native the facts bind it
    * to that is a function of fixed places with a fixed result other than a
    * list's (a data family's constructor is the conversion's, not a call).
    * The reader's option and the e-graph's fold (`ConvertedTermConstruction`)
    * both call them on storages, reading the values without their filters,
    * which the unique spelling's premise of each criterion allows: the backend
    * facts' obligation, replayed in the tests, never checked here.
    */
  def callable(facts: BackendFacts): Map[Pure, (NativeName, Native)] =
    facts.natives.toVector
      .flatMap((instruction, bound) =>
        bound.collectFirst {
          case BoundNative(name @ NativeName.Function(_), count) if count > 0 && fixed(facts.nativeBackend.natives(name)) =>
            instruction -> (name, facts.nativeBackend.natives(name))
        }
      )
      .toMap

  /** Whether every place of the native is a fixed representation other than
    * a list's: a list argument would be a cell whose tail is not read, which
    * the structural path does not read on, so a native over lists is left to
    * the JIT.
    */
  private def fixed(native: Native): Boolean =
    (native.parameters :+ native.result).forall {
      case NativePlace.Fixed(Representation.ListOf(_)) => false
      case NativePlace.Fixed(_)                        => true
      case _                                           => false
    }

