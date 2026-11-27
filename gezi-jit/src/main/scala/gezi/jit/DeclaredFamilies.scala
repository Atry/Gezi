package gezi.jit

import gezi.standardlibrary.CombinatorProperty
import gezi.standardlibrary.FieldCriterion
import gezi.standardlibrary.JvmTypeName
import gezi.standardlibrary.Property
import gezi.standardlibrary.StandardLibraryIndex
import gezi.weakhead.ListCodec
import gezi.weakhead.ListConstructor
import gezi.weakhead.Shape
import gezi.ir.{Configured, NativeSpecializer, NoFacts, Pure}
import gezi.ir.Value

/** A data family declared by facts (the vocabulary's backend entries
  * `data_family`, `data_fields` and `jvm_type(generic)`): its values are held as the framework's generic
  * constructed value (`NativeValue.Constructed`), a constructor's index and
  * its fields, built and taken by this one codec for every declared family.
  * The family's identity is its criterion's term
  * (`FamilyIdentity.Declared`),
  * so it has no representation, no `native_specialization`, of its own; its
  * constructors are the library terms `data_family` lists, in the order of
  * their cases, each with the fields the criterion's
  * `data_fields(Constructor, Fields)` gives for its position, and the
  * native each is encoded with is the framework's constructor native of the
  * family's identity and the constructor's position (`NativeName.Constructor`),
  * its term the one at that position
  * (`BackendFacts.bindings`).
  *
  * A family of Arity > 0 takes its parameters as criteria: a filter
  * `x ∥ C @ P1 @ … @ Pk` names them, the JIT reads the representation each
  * Pi names from the filter as written (`CriterionParameters`),
  * and a field `parameter(I)` is held in the representation of the I-th.
  * They are never read from a value.
  */
final case class DeclaredFamily(criterion: Pure, arity: Int, declaredConstructors: Vector[DataConstructor]) extends DataFamily:

  val identity: FamilyIdentity = FamilyIdentity.Declared(criterion)

  val parameterFamily: Option[FamilyIdentity] = None

  override def criterionArity: Int = arity

  def constructors[Term](parameter: Option[FamilyParameter[Term]]): Vector[DataConstructor] = declaredConstructors

  def built[Term](parameter: Option[FamilyParameter[Term]], layer: DataLayer[Term]): NativeValue[Term] =
    if !declaredConstructors.indices.contains(layer.constructor) || declaredConstructors(layer.constructor).fields.size != layer.fields.size then
      throw IllegalArgumentException(s"no layer of ${identity.shown}: $layer")
    NativeValue.Constructed(identity, layer.constructor, layer.fields)

  def taken[Term](parameter: Option[FamilyParameter[Term]], value: NativeValue[Term]): DataLayer[Term] = value match
    case DeclaredValue(family, constructor, fields) if family == identity => DataLayer(constructor, fields)
    case other => throw IllegalArgumentException(s"no value of ${identity.shown}: $other")

/** A value of a declared family built as native data (`NativeValue.Constructed`), as its family, its constructor's
  * index and its fields' values, one layer. A value stored as a term (`NativeValue.Stored`, a `ConstructedStorage`) is
  * none: its fields' values are its configuration's reading (`StorageEncodingOperations.fieldValues`), which the
  * caller, holding the configuration, takes first.
  */
object DeclaredValue:
  def unapply[Term](value: NativeValue[Term]): Option[(FamilyIdentity, Int, Vector[NativeValue[Term]])] = value match
    case NativeValue.Constructed(family, constructor, fields) => Some((family, constructor, fields))
    case _ => None

/** The data families the index declares by facts, and what the backend
  * needs to run them: their codecs and the natives their constructors are
  * encoded with. Read from the index's combinator properties alone; no
  * family is named in Scala.
  */
object DeclaredFamilies:

  /** The declared families of the index: every criterion with
    * `jvm_type(generic)` and a `data_family(Arity, Constructors)`, the
    * criterion a declared library file and the family's identity
    * (`FamilyIdentity.Declared`), each constructor's fields what
    * `data_fields` on the criterion gives for its position (none when it
    * gives none), every field `parameter(I)` with I < Arity, `recursive`, or
    * a closed criterion: the family its head names (a declared family's
    * criterion or a term with a `native_specialization`) at the
    * representations its arguments name, each an argument's family or the
    * filter the argument is when it names none; a closed criterion whose
    * head names no family is the filter of the field (`FilteredFamily`).
    * Throws `IllegalArgumentException` on a `parameter(I)` with I not below
    * Arity, a defect of the knowledge file.
    */
  def families(index: StandardLibraryIndex[?]): Vector[DeclaredFamily] = declarations(index).map(_._1)

  /** Each `data_family` of the index whose criterion has
    * `jvm_type(generic)`, in the index's order, with the identity of the
    * family it declares: the terms of the family's constructors, in the
    * order of their cases (`BackendFacts.bindings`).
    */
  def constructorTerms(index: StandardLibraryIndex[?]): Vector[(FamilyIdentity, Vector[Pure])] =
    index.combinatorProperties.collect {
      case CombinatorProperty(criterion, Property.DataFamily(_, constructors)) if generic(index, criterion) =>
        FamilyIdentity.Declared(criterion) -> constructors
    }

  /** Each declared family with its constructors' terms, in order. */
  private def declarations(index: StandardLibraryIndex[?]): Vector[(DeclaredFamily, Vector[Pure])] =
    index.combinatorProperties
      .collect { case CombinatorProperty(criterion, Property.JvmType(JvmTypeName.Generic)) => criterion }
      .distinct
      .map(criterion =>
        val identity = FamilyIdentity.Declared(criterion)
        val (arity, instructions) =
          propertiesOf(index, criterion).collectFirst { case Property.DataFamily(arity, constructors) => (arity, constructors) }.getOrElse(
            throw IllegalArgumentException(s"${identity.shown} has jvm_type(generic) and no data_family")
          )
        val family = DeclaredFamily(
          criterion,
          arity,
          instructions.indices.toVector.map(position =>
            val fields =
              propertiesOf(index, criterion).collectFirst { case Property.DataFields(`position`, found) => found }.getOrElse(Vector.empty)
            DataConstructor(NativeName.Constructor(identity, position), fields.map(field => fieldOf(index, identity, arity, field)))
          )
        )
        (family, instructions)
      )

  /** The backend with the declared families of the index and their
    * constructors' natives added: each constructor's native takes its
    * fields at their families and gives the constructed value. Every
    * declared family's constructors are checked to have the Scott shape
    * (`DataFamily.constructorsShape`, read under weak_head), and a family
    * whose constructors do not fit throws `IllegalArgumentException`.
    *
    * FIXME (2026-11-07): the shape is checked here, when the backend's facts https://github.com/Atry/private-overlay/issues/1929
    * are read, and not by the library compiler's checks (`BackendChecks`),
    * whose interface (`LibraryBackend.checked`) is handed natives and native
    * specializations only. Candidate fix: hand it the data entries too.
    */
  def extended(index: StandardLibraryIndex[?], backend: NativeBackend): NativeBackend =
    listDeclarationsChecked(index)
    val declared = declarations(index)
    // The facts are built before any configuration has a specializer, so the shape is read under no facts, where a
    // pure key is its own spelling.
    given NoFacts.type = NoFacts
    given gezi.ir.StorageAccess = gezi.weakhead.ReadingConfiguration.withoutFacts.storageAccess
    declared.foreach((family, instructions) =>
      family.constructorsShape[NoFacts.type](None, instructions.map(Configured.fromPure(NoFacts))) match
        case Shape.Fits => ()
        case other      => throw IllegalArgumentException(s"the constructors of ${family.identity.shown} are not of the Scott shape: $other")
    )
    val families = declared.map(_._1)
    backend.extended(NativeBackend(families.flatMap(constructorNatives).toMap, families))

  /** Checks every criterion with `jvm_type(list)` against the framework's
    * list codec (`ListCodec`), which holds those lists: the criterion's
    * `native_specialization` is the codec's family, it takes one criterion
    * parameter (the element's), it has two constructors, nil at the
    * position 0 of no field and cons at the position 1 of the fields
    * `parameter(0)` and `recursive` (`ListCodec.position`); the terms at
    * those positions are the codec's constructors (`BackendFacts.bindings`).
    * A declaration that disagrees throws `IllegalArgumentException`: the
    * codec, not the declaration, decides how a list is held, so the
    * declaration may only describe it.
    */
  private def listDeclarationsChecked(index: StandardLibraryIndex[?]): Unit =
    val nilPosition = ListCodec.position(ListConstructor.Nil)
    val consPosition = ListCodec.position(ListConstructor.Cons)
    index.combinatorProperties
      .collect { case CombinatorProperty(criterion, Property.JvmType(JvmTypeName.List)) => criterion }
      .distinct
      .foreach(criterion =>
        val properties = propertiesOf(index, criterion)
        def disagrees(reason: String): Nothing =
          throw IllegalArgumentException(s"a criterion of jvm_type(list) that disagrees with the list codec: $reason")
        if !specialization(index, criterion).contains(Representation.listFamily.name) then
          disagrees(s"its native_specialization is not ${Representation.listFamily.name}")
        properties.collectFirst { case Property.DataFamily(arity, constructors) => (arity, constructors) } match
          case Some((1, constructors)) if constructors.size == 2 =>
            val fields = properties.collect { case Property.DataFields(position, found) => position -> found }.toMap
            if fields.getOrElse(nilPosition, Vector.empty).nonEmpty then
              disagrees(s"the constructor $nilPosition, ${constructors(nilPosition)}, has fields")
            if fields.get(consPosition) != Some(Vector(FieldCriterion.Parameter(0), FieldCriterion.Recursive)) then
              disagrees(s"the fields of the constructor $consPosition, ${constructors(consPosition)}, are not [parameter(0), recursive]")
          case other => disagrees(s"its data_family is not data_family(1, [Nil, Cons]): $other")
      )

  /** The natives of a declared family's constructors: their fields' places
    * and their result's are at the call's parameter, and no native gives its
    * result's parameter from its operands, so the JIT calls one only where a
    * decoding point reads the
    * family from a filter written in the term. THIS IS THE SITE that keeps a
    * value's family from being concluded from the value: a constructor's
    * term may be one instruction with another family's (hash consing of equal
    * bodies), and a native called bottom-up on its represented fields would
    * name the first family bound to that instruction.
    */
  private def constructorNatives(family: DeclaredFamily): Vector[(NativeName, Native)] =
    family.declaredConstructors.zipWithIndex.map((constructor, index) =>
      constructor.native -> new Native(
        constructor.fields.map(field => NativePlace.OfParameter(field.representation)),
        NativePlace.Parameter(family.identity),
        new NativeImplementation:
          def apply[C <: NativeSpecializer & Singleton](arguments: Vector[NativeArgument[JitValue[C]]])(using
              C
          ): NativeValue[JitValue[C]] =
            family.built(
              None,
              DataLayer(
                index,
                arguments.map {
                  case NativeArgument.Represented(value) => value
                  case other => throw IllegalArgumentException(s"a field of ${constructor.native} that is not a native value: $other")
                }
              )
            )
        ,
        _ => true,
        None
      )
    )

  /** The field of a criterion, its representation a function of the
    * layer's parameter: the I-th criterion parameter for `parameter(I)`, the
    * family at the layer's parameters for `recursive`, and for a closed
    * criterion the family its head names, at the representations its
    * arguments name (`familyOf`), or, when its head names none, the filter
    * the criterion applied to its arguments is (`FilteredFamily`).
    *
    * A decode point of `x ∥ T` hands out a field as these field criteria F
    * filter it (`f ∥ F`, or its family's value) and its elimination drops
    * `∥ T`, which needs `⊢ T = C F̄ + R`. A JIT refuses, when it is made, facts
    * for which it is not shown of a declared family of no parameter or of one
    * a field of such a family names through a closed criterion, transitively
    * (`BackendFacts.declaredFamiliesNotShown`); and a decode point refuses a
    * criterion that gives a family parameters at which it is not shown
    * (`JitRules.premiseShown`). The check is a sound approximation of the
    * premise: a refusal may be of facts that hold but are not shown within
    * its depth.
    */
  private def fieldOf(index: StandardLibraryIndex[?], family: FamilyIdentity, arity: Int, field: FieldCriterion): DataField =
    field match
      case FieldCriterion.Parameter(position) if position < arity =>
        DataField(new FieldRepresentation:
          def apply[C <: NativeSpecializer & Singleton](parameter: Option[FamilyParameter[JitValue[C]]])(using
              C
          ): Representation[JitValue[C]] = parameter match
            case Some(CriterionParameters(criteria)) if criteria.size == arity => criteria(position)
            case other => throw IllegalArgumentException(s"no criterion parameters of ${family.shown}: $other")
        )
      case FieldCriterion.Parameter(position) =>
        throw IllegalArgumentException(s"a field parameter($position) of ${family.shown}, which takes $arity parameters")
      case FieldCriterion.Recursive =>
        DataField(new FieldRepresentation:
          def apply[C <: NativeSpecializer & Singleton](parameter: Option[FamilyParameter[JitValue[C]]])(using
              C
          ): Representation[JitValue[C]] = Representation.Data(family, parameter)
        )
      case FieldCriterion.Closed(criterion, arguments) =>
        familyOf(index, criterion) match
          case Some(found) if arguments.isEmpty => DataField(FieldRepresentation.fixed(Representation.Data(found, None)))
          case Some(found) =>
            DataField(new FieldRepresentation:
              def apply[C <: NativeSpecializer & Singleton](parameter: Option[FamilyParameter[JitValue[C]]])(using
                  C
              ): Representation[JitValue[C]] =
                Representation.Data(found, Some(CriterionParameters(arguments.map(argument => criterionRepresentation[C](index, argument)))))
            )
          case None =>
            // The filter the criterion applied to its arguments spells, a pure term since its parts are.
            val filter = arguments.foldLeft(criterion)(Pure.application)
            DataField(new FieldRepresentation:
              def apply[C <: NativeSpecializer & Singleton](parameter: Option[FamilyParameter[JitValue[C]]])(using
                  specializer: C
              ): Representation[JitValue[C]] = FilteredFamily.of(Value.of(Configured.fromPure(specializer)(filter)))
            )

  /** The family a term of a field criterion names: the family the term
    * declares when it has `jvm_type(generic)` (`FamilyIdentity.Declared`),
    * otherwise the codec its first `native_specialization` names
    * (`FamilyIdentity.Codec`); none for a term that names no family, whose
    * field is filtered by it (`FilteredFamily`).
    */
  private def familyOf(index: StandardLibraryIndex[?], criterion: Pure): Option[FamilyIdentity] =
    if generic(index, criterion) then Some(FamilyIdentity.Declared(criterion))
    else specialization(index, criterion).map(FamilyIdentity.Codec(_))

  /** The representation an argument of a field's criterion names: its
    * family's, or the filter it is when it names none.
    */
  private def criterionRepresentation[C <: NativeSpecializer & Singleton](index: StandardLibraryIndex[?], argument: Pure)(using
      specializer: C
  ): Representation[JitValue[C]] =
    familyOf(index, argument)
      .map(Representation.Data(_, None))
      .getOrElse(FilteredFamily.of(Value.of(Configured.fromPure(specializer)(argument))))

  /** Whether the term has `jvm_type(generic)`, the criterion of a declared
    * family.
    */
  private def generic(index: StandardLibraryIndex[?], criterion: Pure): Boolean =
    index.combinatorProperties.contains(CombinatorProperty(criterion, Property.JvmType(JvmTypeName.Generic)))

  /** The first `native_specialization` of the term. */
  private def specialization(index: StandardLibraryIndex[?], instruction: Pure): Option[String] =
    propertiesOf(index, instruction).collectFirst { case Property.NativeSpecialization(name) => name }

  private def propertiesOf(index: StandardLibraryIndex[?], instruction: Pure): Vector[Property] =
    index.combinatorProperties.collect { case CombinatorProperty(`instruction`, property) => property }
