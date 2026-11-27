package com.yang_bo.gezi.jit

import com.yang_bo.gezi.weakhead.Computed
import com.yang_bo.gezi.weakhead.Head
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.ReadingState
import com.yang_bo.gezi.ir.{Closed, Configured, Pure}
import com.yang_bo.gezi.weakhead.WeakHead

/** The test's checker of the premise of the unique spelling's pattern theorem
  * (`docs/design/gezi-set-equations-proofs.md`, section 23) on a backend's
  * facts: a backend's obligation, which the readers of a storage's native data
  * rely on when they read a storage as `C ȳ`, dropping its `∥ T`, checked here
  * on every registered criterion and never judged at run time (the host decides
  * nothing by it). For every criterion T a storage is converted under
  * (`StorageEncoding.converts`) and each constructor C of its family, with the
  * field criteria F̄ the facts give (`StorageEncoding.criterionOf` of each
  * field's representation), ⟦T⟧ ⊑ ⟦C F̄⟧, which ⊢ T = C F̄ + R gives and all
  * the theorem's proof uses (its step 1); for a family with a finite value
  * parameter, per constructor (`parameterizedMembers`), a constructor its
  * criterion does not hold being no layer of it.
  *
  * The check reads T by the tabled weak head and `C F̄` by head β
  * (`constructedHead`), and asks that the one head `C F̄` reaches be the one
  * head of one of T's parallel sets: the same code and holes, each pair of
  * fillings the same term (a head `λx̄. f x̄`, the x̄ not in f, is read as f's
  * heads by the η rule, so that a criterion written η-expanded, as the FFI's
  * are, shows the premise its contraction does). A set the tabled reading lists
  * is above T even where the reading is not exact, ⟦T⟧ ⊑ ⟦S⟧, while the head
  * `C F̄` reaches is equal to it by ⊢_{βη}
  * (`docs/design/gezi-set-equations-proofs.md`, sections 22.4 and 23.1): a
  * premise shown this way holds. `C F̄` is not read by tabling, which would
  * list for a constructor written as a fixed point `Θ (λt. K + t)` the head of
  * K though ⟦C⟧ = ⊥.
  *
  * Two fillings are the same term when they are one term or meet within
  * `headSteps` steps of head β each (`headReducts`): each step an instance of
  * the β rule as the e-graph and the trace apply it (`Statements.fill`,
  * `Statements.betaBody`), the first term spelled as the front end spells it,
  * and every term contracted by the η rule, compared by identity: a reduct of T
  * that comes again on T's own reduction, the `Θ G` its fixed point unrolls to,
  * meets the define's term this way, its fold. So every pair accepted is equal
  * by ⊢_{βη} and ≃_O. A pair equal but not seen to meet within the steps, and a
  * constructor whose head is not reached within the bound of a reading, are not
  * shown, and the test fails. The step bound is derived, not measured
  * (`headSteps`). The lists' criterion is sampled at a few elements: each
  * converted family's criterion, the term of nil and a list of lists. A
  * declared family that takes parameters is checked at the parameters a
  * criterion gives it (`nonMembersAt`).
  *
  * The representations it lists (`stored`, `declared`) are of finitely many
  * parameters; the fixed-width words, whose width takes every size, are checked
  * once for every width by `member` with the width a fresh opaque constant
  * (`UniqueSpellingPremiseTest`).
  */
final class UniqueSpellingPremiseCheck[E <: StorageEncoding & Singleton](
    val encoding: E,
    headSteps: Int
):

  private val facts: BackendFacts = encoding.facts

  private given E = encoding

  private given com.yang_bo.gezi.ir.StorageAccess = UniqueSpellingPremiseCheck.storageAccess

  private val operations: StorageEncodingOperations[E] = encoding.operations

  private type Value = com.yang_bo.gezi.ir.Value[E]

  private type Term = Configured[E]

  /** The configuration the criteria are read under: the facts' native
    * specializer and the test's capability.
    */
  private val configuration: com.yang_bo.gezi.weakhead.ReadingConfiguration[E] =
    com.yang_bo.gezi.weakhead.ReadingConfiguration[E](
      encoding,
      UniqueSpellingPremiseCheck.storageAccess
    )

  /** A pure key of the facts as a value of the configuration. */
  private def pureValue(key: Pure): JitValue[E] =
    com.yang_bo.gezi.ir.Value.of(Configured.fromPure(encoding)(key))

  /** The bound of the readings of one criterion's heads, its first reading and
    * those of its η contractions together (`headSets`), and of the head β of
    * one constructor applied to its fields (`constructedHead`): the criteria's
    * and the applied constructors' heads are a few hundred steps each; a
    * criterion or a constructor whose heads are not reached within it is
    * refused.
    */
  private val limit: Long = 20000

  /** Each parallel set's heads of the term, in order, a set of one head
    * `λx̄. f x̄` (the x̄ not in f) replaced by f's sets; none when the readings
    * do not finish within the limit, which bounds them together: each
    * contraction is read under what the readings before it left, so that a head
    * that contracts to a term whose head contracts again, as
    * `Θ (λt. λx. t x)`'s one head `λx. (Θ g) x` contracts to `Θ g`, ends when
    * the limit is spent. A criterion whose readings each fit the limit but not
    * together is refused: a limit for each reading would let a criterion of
    * many contractions cost the square of the limit.
    */
  private def headSets(term: Value): Option[Vector[Vector[Head[E]]]] =
    // Each item is a set already read, or a term to read whose sets stand in
    // its place; the loop keeps the order of the sets and none of its own
    // calls on the stack, since each reading of a contraction may spend only a
    // few of the limit's steps. Each reading is charged at least one step, so
    // the loop ends within the limit whatever the term.
    @scala.annotation.tailrec
    def read(
        pending: List[Either[Vector[Head[E]], Value]],
        found: Vector[Vector[Head[E]]],
        left: Long
    ): Option[Vector[Vector[Head[E]]]] =
      pending match
        case Nil                        => Some(found)
        case Left(set) :: rest          => read(rest, found :+ set, left)
        case Right(_) :: _ if left <= 0 => None
        case Right(next) :: rest        =>
          WeakHead
            .heads(Mode.TablingWeakHead, next)
            .collected
            .result(ReadingState.fresh(left, configuration)) match
            case Computed.Done(sets, state) =>
              val items = sets.toList.map(_.heads).map {
                case set @ Vector(Head.Lambda(code, holes, fillings)) =>
                  etaContracted(code, holes, fillings)
                    .fold[Either[Vector[Head[E]], Value]](Left(set))(Right(_))
                case set => Left(set)
              }
              read(
                items ::: rest,
                found,
                left - math.max(1L, state.budget.spent)
              )
            case Computed.Stopped(_) => None
    read(List(Right(term)), Vector.empty, limit)

  /** The term f of a head `λx̄. f x̄`, by the η rule: the code applies one slot
    * that holds a filling, not a hole, to the holes' slots in order, each hole
    * bound; none for any other head.
    */
  private def etaContracted(
      code: com.yang_bo.gezi.ir.Code,
      holes: Vector[com.yang_bo.gezi.ir.Hole],
      fillings: Vector[Value]
  ): Option[Value] =
    val (function, arguments) = com.yang_bo.gezi.ir.Spine.of(code)
    val holeSlots = holes.collect { case com.yang_bo.gezi.ir.Hole.Bound(slot) => slot }
    val argumentSlots = arguments.flatMap(argument =>
      argument.layer match
        case com.yang_bo.gezi.ir.Slot(slot) => Vector(slot)
        case _                  => Vector.empty
    )
    function.layer match
      case com.yang_bo.gezi.ir.Slot(slot)
          if holeSlots.size == holes.size && holeSlots.nonEmpty && argumentSlots == holeSlots && arguments.size == holeSlots.size &&
            !holeSlots.contains(slot) =>
        com.yang_bo.gezi.frontend.Defunctionalization
          .slotValues(
            holes,
            holes.map(_ => Option.empty[Value]),
            fillings.map(Some(_))
          )
          .lift(slot)
          .flatten
      case _ => None

  /** Whether the two fillings are shown to be one term: the same term, or terms
    * whose head β reducts within `headSteps` steps meet (`headReducts`); a
    * value of the reader's own, no instruction, is the same only as itself.
    */
  private def same(first: Value, second: Value): Boolean =
    com.yang_bo.gezi.ir.Value.same(first, second) || ((
      instructionOf(first),
      instructionOf(second)
    ) match
      case (Some(firstTerm), Some(secondTerm)) =>
        val reached = headReducts(firstTerm).toSet
        headReducts(secondTerm).exists(reached.contains)
      case _ => false)

  private def instructionOf(value: Value): Option[Term] =
    Closed.configured(value)

  /** The closed term, its spelling (`comparable`) and the head β reducts of
    * that spelling, in order: at most `headSteps` steps of β, stopping where a
    * term has no head redex or a reduct comes again. A reduct is the term the β
    * rule's instance makes, contracted by the η rule where it is a thunk
    * `λx̄. f x̄`, and is not spelled again: spelling is a walk of the whole
    * term, so spelling every reduct would cost the steps times the term's size,
    * where the steps alone cost the size of each redex. Two reducts equal only
    * up to their spelling are not seen to meet, and the pair is refused.
    */
  private def headReducts(start: Term): Vector[Term] =
    @scala.annotation.tailrec
    def walked(term: Term, found: Vector[Term], steps: Int): Vector[Term] =
      val reached = found :+ term
      if steps >= headSteps then reached
      else
        headStep(term).map(etaContractedWhile) match
          case Some(reduct) if !reached.exists(Configured.same(_, reduct)) =>
            walked(reduct, reached, steps + 1)
          case _ => reached
    val spelled = comparable(start)
    if Configured.same(spelled, start) then walked(start, Vector.empty, 0)
    else walked(spelled, Vector(start), 0)

  /** The head the closed term reaches by head β (`headStep`), each reduct
    * contracted by the η rule, within `limit` steps, the bound of a reading of
    * heads, since head β of a constructor applied to its fields is
    * deterministic, each step the size of its redex, and the bound only stops a
    * term that reduces without end, such as `Θ (λt. t)`: the thunk with holes
    * where no head redex is left; none for a term that reaches none within the
    * steps, or that ends at another layer (a choice, a parallel, a storage, a
    * URI node). Every step is an instance of the β rule, so the term is equal
    * to its head by ⊢_{βη}.
    */
  private def constructedHead(term: Term): Option[Head[E]] =
    @scala.annotation.tailrec
    def walked(current: Term, steps: Long): Option[Head[E]] =
      headStep(current).map(etaContractedWhile) match
        case Some(reduct) =>
          if steps >= limit then None else walked(reduct, steps + 1)
        case None =>
          layerOf(current) match
            case Some(com.yang_bo.gezi.ir.Thunk(code, holes, fillings)) if holes.nonEmpty =>
              Some(Head.Lambda[E](code, holes, fillings.map(com.yang_bo.gezi.ir.Value.of)))
            case _ => None
    walked(etaContractedWhile(term), 0)

  /** The term spelled as the front end spells a closed term
    * (`BindingNormalForm.spelled`), contracted by the η rule while it is a
    * thunk `λx̄. f x̄` with the x̄ not in f, each contraction spelled again: a
    * term spelled in a reader's own way may hold f as an application of two
    * fillings, which only its spelling makes one filling. A storage is compared
    * as it is.
    */
  private def comparable(term: Term): Term =
    if com.yang_bo.gezi.ir.NativeStorage.stored(term.representation) then term
    else
      val spelled = com.yang_bo.gezi.ir.BindingNormalForm.spelled(term)
      etaContraction(spelled) match
        case Some(contracted) => comparable(contracted)
        case None             => spelled

  /** The term contracted by the η rule while it is a thunk `λx̄. f x̄`. */
  @scala.annotation.tailrec
  private def etaContractedWhile(term: Term): Term =
    etaContraction(term) match
      case Some(contracted) => etaContractedWhile(contracted)
      case None             => term

  private def etaContraction(term: Term): Option[Term] =
    layerOf(term) match
      case Some(com.yang_bo.gezi.ir.Thunk(code, holes, fillings)) =>
        etaContracted(code, holes, fillings.map(com.yang_bo.gezi.ir.Value.of))
          .flatMap(instructionOf)
      case _ => None

  /** The term's layer, none for a storage, a URI node or an opaque leaf, which
    * head β does not enter.
    */
  private def layerOf(term: Term): Option[com.yang_bo.gezi.ir.IrLayer[Term]] =
    if com.yang_bo.gezi.ir.NativeStorage.stored(term.representation) then None
    else
      term.layer match
        case com.yang_bo.gezi.ir.UriNode(_) | com.yang_bo.gezi.ir.Opaque(_) => None
        case layer                                  => Some(layer)

  /** One step of head β: the redex at the head of the term's spine, a thunk
    * applied to its first argument, contracted by the β rule as the e-graph and
    * the trace apply it (`Statements.fill`, or `Statements.betaBody` for the
    * last hole), the spine's other arguments kept; none when the head is no
    * thunk with a hole. It enters no λ, which would open a binder, and no
    * branch of a choice or a parallel.
    */
  private def headStep(term: Term): Option[Term] =
    layerOf(term) match
      case Some(com.yang_bo.gezi.ir.Apply(function, argument)) =>
        layerOf(function) match
          case Some(com.yang_bo.gezi.ir.Thunk(code, holes, _)) if holes.nonEmpty =>
            val rule =
              if holes.size == 1 then
                com.yang_bo.gezi.rewritetrace.Statements.betaBody(code, holes)
              else com.yang_bo.gezi.rewritetrace.Statements.fill(code, holes)
            val bindings = com.yang_bo.gezi.rewritetrace.Statements
              .matchedBindings(rule.left, term)
              .getOrElse(
                throw IllegalStateException(
                  s"the β rule of the thunk at the head does not match its application: $term"
                )
              )
            Some(com.yang_bo.gezi.rewritetrace.Statements.instance(rule.right, bindings))
          case Some(com.yang_bo.gezi.ir.Apply(_, _)) =>
            headStep(function).map(encoding.application(_, argument))
          case _ => None
      case _ => None

  /** A closed lambda in the front end's spelling (`BindingNormalForm.spelled`:
    * every closed subterm, written in the code or held as a filling, a
    * filling), so that two lambdas that are one term spelled two ways have one
    * code; none for a lambda holding a value of the reader's own, no
    * instruction.
    */
  private def canonicalLambda(
      code: com.yang_bo.gezi.ir.Code,
      holes: Vector[com.yang_bo.gezi.ir.Hole],
      fillings: Vector[Value]
  ): Option[(com.yang_bo.gezi.ir.Code, Vector[com.yang_bo.gezi.ir.Hole], Vector[Value])] =
    val asTerms = fillings.map(instructionOf)
    Option
      .when(asTerms.forall(_.isDefined))(
        com.yang_bo.gezi.ir.BindingNormalForm
          .spelled(encoding.thunkOrInstance(code, holes, asTerms.flatten))
          .layer
      )
      .collect {
        case com.yang_bo.gezi.ir.Thunk(spelledCode, spelledHoles, spelledFillings) =>
          (spelledCode, spelledHoles, spelledFillings.map(com.yang_bo.gezi.ir.Value.of))
      }

  private def sameSet(
      first: Vector[Head[E]],
      second: Vector[Head[E]]
  ): Boolean =
    first.size == second.size && first.zip(second).forall {
      case (
            Head.Lambda(firstCode, firstHoles, firstFillings),
            Head.Lambda(secondCode, secondHoles, secondFillings)
          ) =>
        def alike(
            first: (com.yang_bo.gezi.ir.Code, Vector[com.yang_bo.gezi.ir.Hole], Vector[Value]),
            second: (com.yang_bo.gezi.ir.Code, Vector[com.yang_bo.gezi.ir.Hole], Vector[Value])
        ): Boolean =
          first._1 == second._1 && first._2 == second._2 && first._3.size == second._3.size &&
            first._3.zip(second._3).forall(same)
        alike(
          (firstCode, firstHoles, firstFillings),
          (secondCode, secondHoles, secondFillings)
        ) ||
        ((
          canonicalLambda(firstCode, firstHoles, firstFillings),
          canonicalLambda(secondCode, secondHoles, secondFillings)
        ) match
          case (Some(first), Some(second)) => alike(first, second)
          case _                           => false)
      case (firstHead, secondHead) => firstHead == secondHead
    }

  /** Whether `C F̄` is shown to be one member of T's unfolding: it reads to one
    * parallel set, the same as one of T's.
    */
  def member(
      criterion: JitValue[E],
      constructor: JitValue[E],
      fieldCriteria: Vector[JitValue[E]]
  ): Boolean =
    memberOfSets(headSets(criterion), constructor, fieldCriteria)

  /** `member`, T's parallel sets read already, so that the constructors of one
    * criterion read them once: the head `C F̄` reaches by head β
    * (`constructedHead`) is the one head of one of T's sets.
    */
  private def memberOfSets(
      criterionSets: Option[Vector[Vector[Head[E]]]],
      constructor: JitValue[E],
      fieldCriteria: Vector[JitValue[E]]
  ): Boolean =
    val applied = fieldCriteria.foldLeft(constructor)(JitValue.Apply(_, _))
    (instructionOf(applied).flatMap(constructedHead), criterionSets) match
      case (Some(head), Some(sets)) => sets.exists(sameSet(_, Vector(head)))
      case _                        => false

  /** Whether each constructor of each representation of a family with a finite
    * value parameter (`StorageEncoding.parameterizedRepresentations`) is shown
    * to be a member of its criterion's unfolding, the premise of section 23 for
    * that constructor alone. A constructor the criterion does not hold (zero
    * under the positive naturals) is no member. The backend judges a
    * constructor by its fact (`DataFamily.excluded`), which the check compares
    * with what it shows (`parameterizedDisagreements`).
    */
  lazy val parameterizedMembers
      : Map[(Representation[JitValue[E]], Int), Boolean] =
    operations.parameterizedRepresentations.values.toVector
      .flatMap(representation =>
        val criterionSets = headSets(operations.criterionOf(representation))
        constructorsAndFields(representation).zipWithIndex.map {
          case ((constructor, fields), index) =>
            (representation, index) -> memberOfSets(
              criterionSets,
              constructor,
              fields
            )
        }
      )
      .toMap

  /** The constructors of the representations of `parameterizedMembers` whose
    * premise disagrees with the backend's fact: shown a member though the
    * backend excludes it, or not shown though the backend admits it. Empty when
    * the two rules decide every constructor alike, the condition under which a
    * native's storage and a converted one stand for one term.
    */
  lazy val parameterizedDisagreements: Vector[String] =
    parameterizedMembers.toVector
      .sortBy((key, _) => (key._1.toString, key._2))
      .collect {
        case (
              (
                representation @ Representation.Data(identity, parameter),
                index
              ),
              member
            )
            if member == facts.nativeBackend
              .family(identity)
              .exists(_.excluded(parameter, index)) =>
          s"constructor $index of ${identity.shown} under ${operations.criterionOf(representation)}: premise ${
              if member then "shown" else "not shown"
            }, the backend ${if member then "excludes" else "admits"} it"
      }

  /** Every representation of no value parameter the conversion stores under the
    * facts (those of a finite value parameter are checked per constructor,
    * `parameterizedMembers`): each converted family, and, when the facts
    * convert lists, the lists of each family's criterion, of the term of nil
    * and of the lists of the first of these, a list's criterion being one for
    * every element; and the array lists of every element representation the
    * encoding makes them of.
    */
  lazy val stored: Vector[Representation[JitValue[E]]] =
    val families = operations.convertedFamilies.toVector
      .sortBy(_.shown)
      .map(Representation.Data(_, None))
    val lists =
      if operations.convertsLists then
        val flat =
          (families.map(operations.criterionOf) :+ pureValue(facts.nil))
            .map(Representation.ListOf(_))
        flat :+ Representation.ListOf(operations.criterionOf(flat.head))
      else Vector.empty
    families ++ lists ++ operations.arrayListRepresentations

  /** Every declared family of the facts (`DeclaredFamily`) that takes no
    * parameter, and every declared family a field of one of these names through
    * a closed criterion, at the parameters the criterion gives, transitively
    * (`reached`): the representations whose fields the JIT hands out as the
    * facts declare them whatever criterion a program writes. A family that
    * takes parameters is checked besides at the parameters a criterion a
    * program writes gives it (`nonMembersAt`).
    */
  lazy val declared: Vector[Representation[JitValue[E]]] =
    reached(
      facts.nativeBackend.families
        .collect {
          case family: DeclaredFamily if family.criterionArity == 0 => family
        }
        .sortBy(_.identity.shown)
        .map(family => Representation.Data(family.identity, None))
    )

  /** The representations with every declared family's representation their
    * fields name, transitively, each once: the fields of a declared family are
    * fixed by its facts at the parameters it is given, a closed field's
    * parameters being read from closed criteria, so the set is finite.
    */
  private def reached(
      representations: Vector[Representation[JitValue[E]]]
  ): Vector[Representation[JitValue[E]]] =
    @scala.annotation.tailrec
    def walked(
        pending: List[Representation[JitValue[E]]],
        found: Vector[Representation[JitValue[E]]]
    ): Vector[Representation[JitValue[E]]] = pending match
      case Nil                                                      => found
      case representation :: rest if found.contains(representation) =>
        walked(rest, found)
      case (representation @ Representation.Data(
            identity,
            parameter
          )) :: rest =>
        val named = facts.nativeBackend
          .family(identity)
          .toList
          .flatMap(family =>
            family
              .constructors(parameter)
              .flatMap(_.fields.map(_.representation(parameter)))
          )
          .collect {
            case field @ Representation.Data(FamilyIdentity.Declared(_), _) =>
              field
          }
        walked(named ::: rest, found :+ representation)
      case representation :: rest => walked(rest, found :+ representation)
    walked(representations.toList, Vector.empty)

  /** The constructors of the representation, each with its field criteria as
    * the facts give them.
    */
  private def constructorsAndFields(
      representation: Representation[JitValue[E]]
  ): Vector[(JitValue[E], Vector[JitValue[E]])] =
    representation match
      case Representation.ListOf(element) =>
        Vector(
          pureValue(facts.nil) -> Vector.empty,
          pureValue(facts.cons) -> Vector(
            element,
            operations.criterionOf(representation)
          )
        )
      case Representation.ArrayListOf(element) =>
        Vector(
          pureValue(facts.nil) -> Vector.empty,
          pureValue(facts.cons) -> Vector(
            operations.criterionOf(element),
            operations.criterionOf(representation)
          )
        )
      case Representation.Data(identity, parameter) =>
        val family = facts.nativeBackend
          .family(identity)
          .getOrElse(
            throw IllegalStateException(s"no family ${identity.shown}")
          )
        family
          .constructors(parameter)
          .map(constructor =>
            pureValue(
              facts.constructorDefine(constructor.native)
            ) -> constructor.fields.map(field =>
              operations.criterionOf(field.representation(parameter))
            )
          )

  /** The constructors, named by their representation and position, not shown to
    * be members of their criterion's unfolding: empty when the premise is shown
    * for every stored representation.
    */
  lazy val nonMembers: Vector[String] = nonMembersOf(stored)

  /** The constructors of the declared families of no parameter not shown to be
    * members of their criterion's unfolding: empty when the premise is shown
    * for every one, the condition under which the JIT hands out their fields as
    * the facts declare them.
    */
  lazy val declaredNonMembers: Vector[String] = nonMembersOf(declared)

  /** The constructors of the representation, at its parameters, and of the
    * declared families its fields name, transitively, not shown to be members
    * of their criterion's unfolding. The criterion checked is the one the facts
    * rebuild from the representation (`StorageEncoding.criterionOf`): where a
    * parameter's family is named by several criteria, that it stands for the
    * one the program wrote rests on the codec's facts, as every decoding of
    * that family does.
    */
  def nonMembersAt(
      representation: Representation[JitValue[E]]
  ): Vector[String] = nonMembersOf(reached(Vector(representation)))

  private def nonMembersOf(
      representations: Vector[Representation[JitValue[E]]]
  ): Vector[String] =
    representations.flatMap(representation =>
      val criterion = operations.criterionOf(representation)
      val criterionSets = headSets(criterion)
      constructorsAndFields(representation).zipWithIndex.collect {
        case ((constructor, fields), index)
            if !memberOfSets(criterionSets, constructor, fields) =>
          s"constructor $index of ${representation.familyIdentity.shown} under $criterion"
      }
    )

object UniqueSpellingPremiseCheck:

  /** The capability the check reads the criteria with, granted as a test sets
    * up.
    */
  val storageAccess: com.yang_bo.gezi.ir.StorageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()

  /** The check on the encoding's facts with the step bound `headSteps`. */
  def apply[E <: StorageEncoding & Singleton](
      encoding: E
  ): UniqueSpellingPremiseCheck[E] =
    new UniqueSpellingPremiseCheck[E](encoding, headSteps)

  /** The steps of head β a filling is given to meet another, and a constructor
    * applied to its fields to reach its head, derived from the library's
    * criteria and constructors: a marker `$generic` is a variable arguments
    * partial function of its key's CBOR bits, 0x68 and 8 bytes, 72 bits, each
    * bit three steps (the bit's thunk filled, the Scott boolean filled, its
    * body taken), so `nat_type` and `binary_set P` reach their fixed point
    * `A A G …` in 1 + 216 + 1 = 218 steps (the marker's `λx`, as
    * corpora/library/native_types/markers.lambdalattice writes it, and the
    * final `λv. v` one each), `list_type E` in one more for `λe`, 219, and
    * `array_list E`, under the marker `$array` (0x66 and 6 bytes, 56 bits), in
    * 1 + 168 + 1 + 219 = 389. (A constructor under `$constructor`, 0x6c and 12
    * bytes, 104 bits, reaches its body in 1 + 312 + 1 = 314 steps and its head
    * in one more a field, under the bound of a reading, `constructedHead`.) The
    * FFI's declared lists meet in one step after their η contraction and their
    * pair fixed points in none.
    */
  val headSteps: Int = 389
