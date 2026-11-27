package gezi.weakhead

import gezi.frontend.DeBruijnTerm
import gezi.frontend.DeBruijnTermOf
import gezi.frontend.Defunctionalization
import gezi.frontend.Literals
import gezi.ir.ChoiceSpine
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.NativeStorage
import gezi.ir.ScottReading
import gezi.ir.StorageAccess
import gezi.ir.{Configured, NativeSpecializer, Pure, Value}

import scala.annotation.tailrec

/** The Scott ADT values of a program of the configuration `C`, joined by the
  * choice: a right-nested `+` chain (`gezi.ir.ChoiceSpine`) whose every member
  * is a Scott ADT value, or `top` when there is none. A Scott ADT value is a
  * closed term `λc1 … ck. ci v1 … vn`, 1 ≤ i ≤ k, each `vj` a Scott ADT value
  * in turn; a value a storage holds natively (a natural, a word, a list of
  * them) is one, held another way. The Scott ADT values of a program P are
  * those v with P ⊑_O v: Definition 14 stays the meaning, and this is what is
  * observed of P where its normal forms were.
  *
  * The same object as a term of `C` (`withFilters`), the storages left in it as
  * they are, neither expanded nor decoded: read as Scott ADT values (the Scott
  * ADT reading), a storage is its untyped Scott ADT value, its outer `∥ T`
  * dropped, read from its native data (`NativeSpecializer.scottReadingOf`), and
  * a parallel node `v ∥ E` is v. Both are right (≃_O): a storage's unique
  * spelling's premise gives `C ȳ ∥ T ≃_O C ȳ`, and a parallel node `v ∥ E` is
  * one this reading read as v, which `c` could not convert into a storage. A
  * layer that is no storage and no parallel node is the canonical layer of its
  * (k, i, fields), spelled by the front end's rule (`Defunctionalization`) with
  * equal fields, equal as Scott ADT values, sharing one slot.
  *
  * Its only constructions are `of`, `ofNormalForm` and `members`; `withFilters`
  * gives the term back.
  */
opaque type ScottADTChoices[C <: NativeSpecializer & Singleton] = Configured[C]

object ScottADTChoices:

  /** What `of` reads of a program: its Scott ADT values, whether no normal form
    * the reading gave was dropped for being no Scott ADT value
    * (`nothingDropped`), and whether no member came from a choice split under a
    * constructor (a field of more than one member), the split being right for
    * the observation (a constructor is monotone under ⊑_O) but no equation
    * (`noChoiceSplit`). The e-graph equates a closed subterm with its Scott ADT
    * values only when both hold.
    */
  final case class Read[C <: NativeSpecializer & Singleton](
      choices: ScottADTChoices[C],
      nothingDropped: Boolean,
      noChoiceSplit: Boolean
  )

  /** The Scott ADT values of the program read under the mode, the real
    * filtering of the observation: of each normal form the reading gives, only
    * those that are Scott ADT values. A storage that may be handed over whole
    * is a member as it is, its view not read; any other storage is read one
    * layer from its native data and its fields read on; any other value is read
    * to its normal forms (`NormalForms`), which leave such storages in place. A
    * stop of the reading's budget is the computation's stop: no
    * `ScottADTChoices`.
    */
  def of[C <: NativeSpecializer & Singleton](mode: Mode, program: Value[C])(
      using C
  ): Computation[ReadingState[C], Read[C]] =
    Computation
      .state[ReadingState[C]]
      .flatMap(state =>
        given StorageAccess = state.storageAccess
        found(mode, program).map(read =>
          Read(
            chain(distinct(read.members)),
            read.nothingDropped,
            read.noChoiceSplit
          )
        )
      )

  /** The Scott ADT values among normal forms a reading already gave (an
    * executor's), with no reading: those of the forms that are Scott ADT
    * values, deduplicated; nothing dropped when every form is one; no choice
    * split known only when there is at most one form, since forms read apart do
    * not say whether a choice under a constructor gave them.
    */
  def ofNormalForms[C <: NativeSpecializer & Singleton](
      forms: Vector[Configured[C]]
  )(using C, StorageAccess): Read[C] =
    val scott = forms.filter(scottShaped(_, storagesAllowed = true))
    Read(chain(distinct(scott)), scott.size == forms.size, forms.size <= 1)

  /** The Scott ADT values a term given as text is (a judgment's candidate, the
    * judge's reference): the term itself, a choice of Scott ADT values with no
    * parallel and no storage in it, a normal form already in the front end's
    * spelling; none for any other term.
    */
  def ofNormalForm[C <: NativeSpecializer & Singleton](
      term: Configured[C]
  )(using C, StorageAccess): Option[ScottADTChoices[C]] =
    Option.when(
      Configured.same(term, empty[C]) || memberTerms(term).forall(
        scottShaped(_, storagesAllowed = false)
      )
    )(term)

  /** The members, each a `ScottADTChoices` of one: the members of the chain, a
    * group of storages at the top of a member given as its members, from their
    * native data.
    */
  def members[C <: NativeSpecializer & Singleton](
      choices: ScottADTChoices[C]
  )(using C, StorageAccess): Vector[ScottADTChoices[C]] =
    memberTerms(choices)

  /** The Scott ADT values as a term of `C`: the same object. No-op at run time;
    * for the meaning, every storage and every parallel node of the chain has
    * its filter back, which is right (≃_O) as the reading says.
    */
  def withFilters[C <: NativeSpecializer & Singleton](
      choices: ScottADTChoices[C]
  ): Configured[C] = choices

  /** Whether the two are the same set of Scott ADT values: each member of one
    * equal to a member of the other, two members compared as untyped Scott ADT
    * values (`memberSame`), never by writing text and never by converting a
    * storage.
    */
  def same[C <: NativeSpecializer & Singleton](
      left: ScottADTChoices[C],
      right: ScottADTChoices[C]
  )(using C, StorageAccess): Boolean =
    val leftMembers = memberTerms(left)
    val rightMembers = memberTerms(right)
    leftMembers.forall(member => rightMembers.exists(memberSame(member, _))) &&
    rightMembers.forall(member => leftMembers.exists(memberSame(member, _)))

  /** No Scott ADT value: the framework's `top`, the one spelling of the empty
    * set.
    */
  def empty[C <: NativeSpecializer & Singleton](using
      specializer: C
  ): ScottADTChoices[C] = Configured.fromPure(specializer)(topPure)

  private lazy val topPure: Pure = Defunctionalization.pure(Literals.top)

  // ---- the reading ----

  /** Members read so far, with the two flags of `Read`. */
  private final case class Found[C <: NativeSpecializer & Singleton](
      members: Vector[Configured[C]],
      nothingDropped: Boolean,
      noChoiceSplit: Boolean
  )

  private def combined[C <: NativeSpecializer & Singleton](
      parts: Vector[Found[C]]
  ): Found[C] =
    Found(
      parts.flatMap(_.members),
      parts.forall(_.nothingDropped),
      parts.forall(_.noChoiceSplit)
    )

  private def found[C <: NativeSpecializer & Singleton](
      mode: Mode,
      value: Value[C]
  )(using
      specializer: C,
      access: StorageAccess
  ): Computation[ReadingState[C], Found[C]] =
    OpenNormalForm.storedWhole(value) match
      case Some(whole) => Computation.pure(Found(Vector(whole), true, true))
      case None        =>
        storageOf(value) match
          case Some((term, storage)) =>
            (specializer: C).scottReadingOf(storage) match
              case ScottReading.Members(groupMembers) =>
                Computation
                  .traversed(groupMembers)(member =>
                    found(mode, Value.of(member))
                  )
                  .map(combined)
              case ScottReading.Layer(cases, chosen, fields) =>
                Computation
                  .traversed(fields)(field => found(mode, Value.of(field)))
                  .map(fieldsFound =>
                    Found(
                      product(fieldsFound.map(_.members))
                        .map(layerTerm(cases, chosen, _)),
                      fieldsFound.forall(_.nothingDropped),
                      fieldsFound.forall(field =>
                        field.noChoiceSplit && field.members.size <= 1
                      )
                    )
                  )
          case None =>
            WeakHead
              .heads(mode, value)
              .collected
              .flatMap(sets =>
                Computation.traversed(sets)(setFound(mode, _)).map(combined)
              )

  /** The Scott ADT values of one parallel set: the Scott ADT values among the
    * normal forms of its value. The empty set, a least term's, is read as no
    * member, as its normal forms are (the FIXME at `NormalForms.setRead`), and
    * so reports a member dropped; a set whose value reads several normal forms
    * reports a split, a choice under its head's binders.
    */
  private def setFound[C <: NativeSpecializer & Singleton](
      mode: Mode,
      set: ParallelSet[C]
  )(using
      specializer: C,
      access: StorageAccess
  ): Computation[ReadingState[C], Found[C]] =
    set.value(specializer) match
      case None           => Computation.pure(Found(Vector.empty, false, true))
      case Some(setValue) =>
        NormalForms
          .normalForms(mode, setValue)
          .map(forms =>
            val scott = forms.filter(scottShaped(_, storagesAllowed = true))
            Found(scott, scott.size == forms.size, forms.size <= 1)
          )

  /** The term and the storage the value is, when it is a closed storage. */
  private def storageOf[C <: NativeSpecializer & Singleton](
      value: Value[C]
  )(using C): Option[(Configured[C], NativeStorage)] =
    gezi.ir.Closed
      .configured(value)
      .flatMap(term =>
        (term.representation: AnyRef) match
          case storage: NativeStorage => Some((term, storage))
          case _                      => None
      )

  /** Every choice of one member of each field, in order. */
  private def product[Member](
      fields: Vector[Vector[Member]]
  ): Vector[Vector[Member]] =
    fields.foldLeft(Vector(Vector.empty[Member]))((sofar, field) =>
      sofar.flatMap(chosen => field.map(chosen :+ _))
    )

  /** The canonical layer `λc1 … ck. ci f1 … fn` of the cases, the chosen case
    * (from 0) and the fields, spelled by the front end's rule, which makes
    * equal fields one slot: a field equal as a Scott ADT value to an earlier
    * one is replaced by that one first, so that a storage field and a pure
    * field of one value share a slot, as the spelling of the value written
    * purely would.
    */
  private def layerTerm[C <: NativeSpecializer & Singleton](
      cases: Int,
      chosen: Int,
      fields: Vector[Configured[C]]
  )(using
      C,
      StorageAccess
  ): Configured[C] =
    val representatives =
      fields.foldLeft(Vector.empty[Configured[C]])((sofar, field) =>
        sofar :+ sofar.find(memberSame(_, field)).getOrElse(field)
      )
    val body = representatives.foldLeft(
      DeBruijnTerm.Variable[Configured[C]](cases - 1 - chosen)
    )((function, field) =>
      DeBruijnTerm.Apply(function, DeBruijnTerm.Constant(field))
    )
    Defunctionalization.thunkInstruction[C](
      (0 until cases).foldLeft(body: DeBruijnTermOf[Configured[C]])(
        (inner, _) => DeBruijnTerm.Lambda(inner)
      )
    )

  /** The chain of the members, nested to the right; `empty` for none. */
  private def chain[C <: NativeSpecializer & Singleton](
      members: Vector[Configured[C]]
  )(using specializer: C): ScottADTChoices[C] =
    if members.isEmpty then empty[C]
    else ChoiceSpine.nested[Configured[C]](members, specializer.choice(_, _))

  // ---- reading members as untyped Scott ADT values ----

  /** The members of the chain, a group of storages among them given as its
    * members.
    */
  private def memberTerms[C <: NativeSpecializer & Singleton](
      choices: Configured[C]
  )(using
      specializer: C,
      access: StorageAccess
  ): Vector[Configured[C]] =
    if Configured.same(choices, empty[C]) then Vector.empty
    else
      ChoiceSpine
        .members[Configured[C]](
          choices,
          term =>
            term.layer match
              case gezi.ir.Choice(left, right) => Some((left, right))
              case _                           => None
        )
        .flatMap(member =>
          (member.representation: AnyRef) match
            case storage: NativeStorage =>
              (specializer: C).scottReadingOf(storage) match
                case ScottReading.Members(groupMembers) => groupMembers
                case ScottReading.Layer(_, _, _)        => Vector(member)
            case _ => Vector(member)
        )

  /** The one layer `λc1 … ck. ci f1 … fn` of a member read as an untyped Scott
    * ADT value: a storage's from its native data, a parallel node's left
    * side's, a canonical layer's from its code; none for a term of no such
    * shape.
    */
  @tailrec
  private def layerOf[C <: NativeSpecializer & Singleton](
      term: Configured[C]
  )(using
      specializer: C,
      access: StorageAccess
  ): Option[ScottReading.Layer[Configured[C]]] =
    (term.representation: AnyRef) match
      case storage: NativeStorage =>
        (specializer: C).scottReadingOf(storage) match
          case layer @ ScottReading.Layer(_, _, _) => Some(layer)
          case ScottReading.Members(_)             => None
      case _ =>
        term.layer match
          case gezi.ir.Parallel(left, _)            => layerOf(left)
          case gezi.ir.Thunk(code, holes, fillings) =>
            canonicalLayer(code, holes, fillings)
          case _ => None

  /** The (k, i, fields) of a thunk `λc1 … ck. ci f1 … fn` as the front end
    * spells it: its k holes, the one hole its body applies, and each argument a
    * slot that a filling fills.
    */
  private def canonicalLayer[C <: NativeSpecializer & Singleton](
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[Configured[C]]
  ): Option[ScottReading.Layer[Configured[C]]] =
    val bound = holes.collect { case Hole.Bound(slot) => slot }.toSet
    val filled = (0 until bound.size + fillings.size)
      .filterNot(bound.contains)
      .zip(fillings)
      .toMap
    @tailrec
    def spine(current: Code, arguments: List[Code]): (Code, List[Code]) =
      current match
        case Code.Apply(function, argument) =>
          spine(function, argument :: arguments)
        case other => (other, arguments)
    spine(code, Nil) match
      case (Code.Slot(head), arguments) =>
        val chosen = holes.indexOf(Hole.Bound(head))
        val fields = arguments.map {
          case Code.Slot(slot) => filled.get(slot)
          case _               => None
        }
        Option.when(chosen >= 0 && fields.forall(_.isDefined))(
          ScottReading.Layer(holes.size, chosen, fields.flatten.toVector)
        )
      case _ => None

  /** Whether the term is one Scott ADT value, every field in turn: walked on
    * the heap, each node once, a storage handed over whole taken as one with no
    * field read. A storage counts only when `storagesAllowed` (a normal form
    * leaves only storages handed over whole); a parallel node, which only `of`
    * leaves, never in a term given as text.
    */
  private def scottShaped[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      storagesAllowed: Boolean
  )(using
      C,
      StorageAccess
  ): Boolean =
    @tailrec
    def walked(
        pending: List[Configured[C]],
        seen: Set[Configured[C]]
    ): Boolean = pending match
      case Nil                                 => true
      case next :: rest if seen.contains(next) => walked(rest, seen)
      case next :: rest                        =>
        val storage = (next.representation: AnyRef) match
          case found: NativeStorage => Some(found)
          case _                    => None
        if storage.isDefined && !storagesAllowed then false
        // A storage handed over whole is a Scott ADT value by the backend's facts' obligation: no field of it is read.
        else if storage.exists(_.handedOverWhole) then walked(rest, seen + next)
        else
          next.layer match
            case gezi.ir.Parallel(_, _) if !storagesAllowed => false
            case _                                          =>
              layerOf(next) match
                case Some(layer) =>
                  walked(layer.fields.toList ::: rest, seen + next)
                case None => false
    walked(List(term), Set.empty)

  /** Whether the two members are one untyped Scott ADT value: one object, or of
    * the same case of the same number of cases with equal fields, compared
    * pairwise on the heap, a pair met again taken as equal (each pair is a
    * finite value's, so a mismatch is found wherever it is).
    */
  private def memberSame[C <: NativeSpecializer & Singleton](
      left: Configured[C],
      right: Configured[C]
  )(using
      C,
      StorageAccess
  ): Boolean =
    @tailrec
    def compared(
        pending: List[(Configured[C], Configured[C])],
        assumed: Set[(Configured[C], Configured[C])]
    ): Boolean =
      pending match
        case Nil => true
        case (first, second) :: rest
            if Configured
              .same(first, second) || assumed.contains((first, second)) =>
          compared(rest, assumed)
        case (first, second) :: rest =>
          (layerOf(first), layerOf(second)) match
            case (Some(one), Some(other))
                if one.cases == other.cases && one.chosen == other.chosen && one.fields.size == other.fields.size =>
              compared(
                one.fields.zip(other.fields).toList ::: rest,
                assumed + ((first, second))
              )
            case _ => false
    compared(List((left, right)), Set.empty)

  /** The structural hash of a member, consistent with `memberSame`: the cases,
    * the chosen case and the fields' hashes, computed bottom up on the heap
    * with each node hashed once.
    */
  private def memberHash[C <: NativeSpecializer & Singleton](
      member: Configured[C]
  )(using C, StorageAccess): Int =
    @tailrec
    def hashed(
        pending: List[Either[Configured[C], Configured[C]]],
        known: Map[Configured[C], Int]
    ): Map[Configured[C], Int] =
      pending match
        case Nil                                        => known
        case Left(next) :: rest if known.contains(next) => hashed(rest, known)
        case Left(next) :: rest                         =>
          val fields = layerOf(next).fold(Vector.empty[Configured[C]])(_.fields)
          hashed(fields.toList.map(Left(_)) ::: Right(next) :: rest, known)
        case Right(next) :: rest =>
          val layer = layerOf(next)
          val code = layer.fold(0)(found =>
            found.fields.foldLeft(31 * found.cases + found.chosen)(
              (sofar, field) => 31 * sofar + known(field)
            )
          )
          hashed(rest, known.updated(next, code))
    hashed(List(Left(member)), Map.empty)(member)

  /** The members with no two equal as Scott ADT values, the first of each kept,
    * grouped by `memberHash` first so that only members of one hash are
    * compared.
    */
  private def distinct[C <: NativeSpecializer & Singleton](
      members: Vector[Configured[C]]
  )(using C, StorageAccess): Vector[Configured[C]] =
    members
      .foldLeft(
        (Vector.empty[Configured[C]], Map.empty[Int, Vector[Configured[C]]])
      ) { case ((kept, byHash), member) =>
        val code = memberHash(member)
        val bucket = byHash.getOrElse(code, Vector.empty)
        if bucket.exists(memberSame(_, member)) then (kept, byHash)
        else (kept :+ member, byHash.updated(code, bucket :+ member))
      }
      ._1
