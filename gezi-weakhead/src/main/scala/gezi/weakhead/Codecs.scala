package gezi.weakhead

import gezi.standardlibrary.CombinatorProperty
import gezi.standardlibrary.Property
import gezi.standardlibrary.StandardLibraryIndex
import gezi.ir.{Configured, NativeSpecializer, Value}

/** The number of a decoding (the JIT gives each decoding its own, so that a
  * decoding that starts while another is in progress never reads the
  * other's cases), or the decoding of a codec's check of its constructors.
  */
enum Decoding:

  /** The decoding of this number. */
  case Numbered(number: Long)

  /** The check of the constructors' shape (`constructorsShape` of a codec),
    * the Prolog codecs' decoding number `shape`.
    */
  case Shape

/** The readings of the heads of a term a codec checks, or that its reading
  * ran past its budget.
  */
enum CaseReadings[+Reading]:

  /** The distinct readings of the heads, in the order first found. */
  case Read(readings: Vector[Reading])

  /** The reading ran past its budget (the Prolog codecs' `[unread]`): no
    * reading, and no answer about the shape.
    */
  case LimitReached

/** Whether two defines have a codec's assumed shape, or that a check ran past
  * its budget before it could tell. The two readings are the first
  * constructor's and the second's for the codecs here; the generic check of
  * a data family of `jit` (`DataFamily.constructorsShape`), whose
  * family may have any number of constructors, gives the readings found of
  * the first constructor that misfits and the one reading it asks.
  */
enum Shape[+Reading]:

  /** Both readings finished and are what the shape asks. */
  case Fits

  /** Both readings finished, and one is not what the shape asks: the
    * readings found of the first constructor and of the second.
    */
  case Unfit(first: Vector[Reading], second: Vector[Reading])

  /** A reading ran past its budget, so the check gives no answer (the Prolog
    * codecs answered `unfit` with the readings `[unread]`; a stop is no
    * verdict, and no answer is not the same as an evaluation that does not
    * halt); the readings of both constructors.
    */
  case LimitReached(first: CaseReadings[Reading], second: CaseReadings[Reading])

/** What the three codecs share. */
object Codecs:

  /** The steps a codec's check of its constructors may take for one
    * reading. The Prolog codecs read within 1,000,000 inferences, measured
    * there to need 12,024 for concrete_types' zero and successor together
    * and 11,134 for its true and false. The Scala readings of native_types'
    * zero and successor take 14 and 20 steps (`CodecsTest`, measured
    * 2026-10-31); a step is a coarser unit than an inference, so the same
    * number bounds them at least as loosely.
    *
    * FIXME: a codec's check reads on a reading path of its own https://github.com/Atry/private-overlay/issues/2036
    * (`WeakHead.heads(Mode.TablingWeakHead, ...)` from `ReadingState.fresh`), within this fixed budget, which decides
    * whether a family is shape checked. The reading and its budget are to become options of one interface chosen by
    * configuration (entry data and `Defaults`).
    */
  val shapeStepLimit: Long = 1000000

  /** The distinct readings of the parallel sets of the term under
    * tabling(weak_head), in the order of the term's completed table, or `LimitReached` past the budget: a set of
    * one head reads what the head reads, and any other set, which is no case
    * of a constructor, reads `noCase`.
    */
  def readingsWithin[C <: NativeSpecializer & Singleton, Reading](term: Value[C], noCase: Reading)(
      read: Head[C] => Reading
  )(using C, gezi.ir.StorageAccess): CaseReadings[Reading] =
    WeakHead
      .heads(Mode.TablingWeakHead, term)
      .collected
      .result(
        ReadingState.fresh(shapeStepLimit, ReadingConfiguration(summon[C], summon[gezi.ir.StorageAccess]))
      ) match
      case Computed.Done(sets, _) =>
        CaseReadings.Read(
          sets
            .map(set =>
              set.view(summon[C]) match
                case ParallelView.Single(head) => read(head)
                case _                         => noCase
            )
            .distinct
        )
      case Computed.Stopped(_) => CaseReadings.LimitReached

  /** The shape the readings of two constructors give: `LimitReached` when
    * either reading ran past its budget; otherwise `Fits` when each is
    * exactly the one reading expected, `Unfit` with both when not.
    */
  def shapeOf[Reading](
      first: CaseReadings[Reading],
      second: CaseReadings[Reading],
      expectedFirst: Reading,
      expectedSecond: Reading
  ): Shape[Reading] = (first, second) match
    case (CaseReadings.Read(firstReadings), CaseReadings.Read(secondReadings)) =>
      if firstReadings == Vector(expectedFirst) && secondReadings == Vector(expectedSecond) then Shape.Fits
      else Shape.Unfit(firstReadings, secondReadings)
    case _ => Shape.LimitReached(first, second)

  /** Each `data_family` of the index, in the index's order, with the
    * representation the first `native_specialization` of its criterion
    * names: the representation and the terms of the family's constructors,
    * in the order of their cases. A codec's constructor is a position in
    * such a list, never a name, and never a term alone: α-equivalent library
    * files such as zero, true and nil are one term. A family whose criterion has no
    * `native_specialization` gives none. These are backend facts of the
    * knowledge, read by the pure key of the criterion; none is a type.
    */
  def declaredConstructors(index: StandardLibraryIndex[?]): Vector[(String, Vector[gezi.ir.Pure])] =
    val firstSpecialization = index.combinatorProperties
      .collect { case CombinatorProperty(criterion, Property.NativeSpecialization(representation)) => criterion -> representation }
      .foldLeft(Map.empty[gezi.ir.Pure, String]) { case (found, (criterion, representation)) =>
        if found.contains(criterion) then found else found.updated(criterion, representation)
      }
    index.combinatorProperties.collect {
      case CombinatorProperty(criterion, Property.DataFamily(_, constructors)) if firstSpecialization.contains(criterion) =>
        firstSpecialization(criterion) -> constructors
    }
