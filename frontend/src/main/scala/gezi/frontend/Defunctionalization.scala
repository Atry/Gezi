package gezi.frontend

import gezi.ir.Code
import gezi.ir.Configured
import gezi.ir.Instruction
import gezi.ir.Hole
import gezi.ir.NativeSpecializer
import gezi.ir.NoFacts
import gezi.ir.NonEmptyHoles
import gezi.ir.Pure
import gezi.locations.BinderOrigin
import gezi.locations.Location
import gezi.locations.SourceMap
import scala.annotation.tailrec
import scala.util.hashing.MurmurHash3
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** The front end's last step: closed de Bruijn terms to the thunk IR, and back.
  * The port of `gezi/prolog/gezi/defunctionalization.pl`.
  *
  * The terms are locally nameless (`DeBruijnTerm`). A free name is an error of
  * the conversion (`thunkInstruction` of a term alone), as it is of reading a
  * text (`FreeNames.Rejected`). The conversion given names is the rare case
  * that free names are allowed in (`FreeNames`): it looks each free name up in
  * the names as it annotates the term, in the walk the conversion makes anyway,
  * and nothing after it sees a name.
  *
  * The IR has no binder. A lambda chain is a thunk: a code, the body over slots
  * in which the binders and the hoisted maximal closed subterms are numbered
  * alike by first occurrence; the holes, the binders' slots in lambda order;
  * and the fillings, the other slots' values. Partial application fills the
  * first hole. A choice and a parallel compile structurally, their parts over
  * the same slots. A reference to a library name is the bare instruction of its
  * layer (D1 of `lean/README.md`, "Design decisions"). A lambda body stays a
  * thunk's code: the front end translates no body into combinators.
  *
  * FIXME (2026-10-10, link (i) of D6 and D3 of `lean/README.md`, "Design
  * decisions", https://github.com/Atry/private-overlay/issues/1561; carried
  * from defunctionalization.pl): Lean proves link (i) for its own definition of
  * this conversion (module Defunctionalization of gezi/lean,
  * `thunkInstruction`, with `readbackThunkInstruction`: the readback of the
  * finite term is δ(Term)), not for this code. That this code, every
  * instruction replaced by the finite term of its layer, gives the finite term
  * Lean's `thunkInstruction` gives is not proved: the two are separate
  * implementations of the same clauses. The Prolog conversion was compared with
  * Lean's on 2026-10-10 (tests/defunctionalization_agreement.plt: 300 random
  * source programs, the 31 defines of the prelude and 300 random closed terms,
  * all agreeing, each of three mutations failing); this port is compared the
  * same way by `DefunctionalizationAgreementTest` of Gezi's `standardlibrary`
  * module (300 random source programs, the prelude's defines and 300 random
  * closed terms, all agreeing), which samples and does not prove. The statement
  * is on readbacks because the instruction is in general not Lean's
  * `defunctionalize` of δ(Term): a constant's define converts to its own
  * instruction, which the program written with the define's term in place need
  * not give. Candidate fixes: Lean's definition compiled and run in place of
  * this code; or a check of each run by the kernel, the run carrying its source
  * program and the defines' terms into Lean.
  *
  * TODO (https://github.com/Atry/private-overlay/issues/1526; carried from
  * defunctionalization.pl): the comparison on the defines of the old HM
  * baseline's library and the kernel's check of X2, the source program of its
  * type-checking runs, stood beside the Prolog conversion; the same check on
  * the source program of a type-checking run of the new HM baseline stands here
  * once those runs exist. The deleted checks read back with
  * `git show a66f8d948:lambda_jit/tests/opentheory_article.plt` and
  * `git show a66f8d948:lambda_jit/lean/LambdaJit/TypeCheckingRunSourceFixtures.lean`.
  */
object Defunctionalization:

  /** The thunk IR of a closed de Bruijn term. A `Constant` becomes the bare
    * instruction it holds. A chain of abstractions `\x1 ... \xk. B`, B no
    * abstraction, is one `Instruction.Thunk`: its code is B with its binders
    * and its maximal closed subterms (equal ones once) replaced by slots,
    * numbered by first occurrence in preorder; its holes list for x1 to xk the
    * slot of each, or `Hole.Ignored` when B does not read it; its fillings are
    * the other slots' values in slot order, each the IR of a closed subterm. A
    * chain inside B that is not closed is an inner `CodeIdentifier.Thunk` whose
    * fillings are slot references of the enclosing body, allocated at the inner
    * thunk's position in its slot order. So a thunk holds no closed subterm and
    * no distinction between an argument and a capture: `\z.\s. s zero` and
    * `\z.\s. s one` are both
    * `thunk(apply(slot(0), slot(1)), [ignored, 0], [N])`. A chain whose body B
    * is a constant whose layer is a thunk with holes is folded into that thunk,
    * its binders put before the thunk's holes as ignored ones: `\x. zero`, zero
    * being `\a.\b. a`, is `thunk(slot(0), [ignored, 0, ignored], [])`, the
    * instruction of the literal `\x.\a.\b. a`, so that a name and the literal
    * term it equals are one instruction. Lean's `thunkInstruction` folds the
    * same way and proves that the fold keeps the readback (`foldedReadback`).
    * Throws `LambdaError` with `NotClosed` when the term is not closed, and
    * `LambdalatticeMalformed` with `UnboundName` for a free name
    * (`DeBruijnTerm.Free`), which a term converted with no names may not hold.
    *
    * FIXME (2026-11-16): this spelling and `gezi.ir.BindingNormalForm.spelled`,
    * https://github.com/Atry/private-overlay/issues/1985 the spelling half of
    * the binding normal form that the higher-order saturator and the trace's
    * conversions call, are two implementations of one rule, kept in agreement
    * only by `BindingNormalFormSpellingLawTest` (frontend's tests: the front
    * end's instruction is `spelled` of itself, and `spelled` of an evaluator's
    * instruction is `Respelling.respelled`'s). Switch this conversion's
    * spelling half to call `spelled`, then delete the second implementation
    * here; the law first stays to check the switch.
    */
  def thunkInstruction[C <: NativeSpecializer & Singleton](
      term: DeBruijnTermOf[Configured[C]]
  )(using C): Configured[C] =
    thunkInstructionCounted(term, Map.empty).value

  /** `thunkInstruction` of a locally nameless term, each free name
    * (`DeBruijnTerm.Free`) looked up in the names as the walk that annotates
    * the term meets it and converted as the constant of its instruction: a
    * library name a lambdalattice text read with `FreeNames.Allowed` refers to.
    * Free names are blacklisted (`FreeNames`): no new call gives names before
    * its design has been discussed. Throws `LambdalatticeMalformed` with
    * `UnboundName` for a free name the names lack, and the errors of
    * `thunkInstruction`.
    */
  def thunkInstruction[C <: NativeSpecializer & Singleton](
      term: DeBruijnTermOf[Configured[C]],
      names: Map[String, Configured[C]]
  )(using C): Configured[C] =
    thunkInstructionCounted(term, names).value

  /** The pure term of a closed term with no constant, built with no facts: a
    * framework constant (`top`, `bottom`) or a fact's key. Throws
    * `IllegalArgumentException` when the term holds a parallel layer at the
    * level of instructions, which a pure term may not, and the errors of
    * `thunkInstruction`.
    */
  def pure(term: DeBruijnTerm): Pure =
    val built = thunkInstruction[NoFacts.type](term)(using NoFacts)
    Pure
      .of(built)
      .getOrElse(
        throw IllegalArgumentException(
          s"a term with a parallel layer is no pure term: $term"
        )
      )

  /** `thunkInstruction` with the count of its operations: one for each node
    * each of its walks visits (the annotation, the conversion, the codes of the
    * bodies and the lambdas of each chain), one for each slot looked up or
    * allocated, and one for each binder whose hole is read off. A slot lookup
    * counts one however long the comparison of two equal closed subterms
    * (`SlotSource.Closed`) takes: that comparison is not counted. Each layer
    * and code is interned as its node is converted, within the operation that
    * counts the node.
    */
  def thunkInstructionCounted[C <: NativeSpecializer & Singleton](
      term: DeBruijnTermOf[Configured[C]]
  )(using
      C
  ): Counted[Configured[C]] =
    thunkInstructionCounted(term, Map.empty)

  /** `thunkInstructionCounted` of a locally nameless term, its free names
    * looked up in the names as `thunkInstruction` looks them up.
    */
  def thunkInstructionCounted[C <: NativeSpecializer & Singleton](
      term: DeBruijnTermOf[Configured[C]],
      names: Map[String, Configured[C]]
  )(using specializer: C): Counted[Configured[C]] =
    val conversion = Conversion[C](specializer)
    val (root, annotations) = conversion.annotated(term, names, None).result
    if root.annotation.looseness != 0 then
      throw LambdaError(LambdaErrorReason.NotClosed(term))
    val (instruction, _, conversions) = conversion.converted(root).result
    Counted(instruction, annotations + conversions)

  /** What a slot of a mixin's body reads: one of its selves, or a closed
    * instruction, which is a filling of the mixin's thunk.
    */
  private enum MixinRead[+Term]:
    case Self(index: Int) extends MixinRead[Nothing]
    case Held(term: Term)

  /** `thunkInstruction` of the mixin
    * `λd1. … λdn. (λ"k1". U1 d1 … dn) + … + (λ"kp". Up d1 … dn)`: the same
    * interned instruction, built from the keys' bits with none of the
    * conversion's walks. A member's code holds its entry in a slot, so it
    * depends only on the bits of its key and the number of selves. For at least
    * one self and two members, none of whose entries is `top`: a single
    * member's first bit joins the chain of the selves, and an entry that is
    * `top` shares the slot of the misses, both of which `thunkInstruction`
    * spells. Throws `IllegalArgumentException` otherwise.
    *
    * Slots are numbered at their first occurrence, as `bodyThunk` numbers them.
    * A bit's chain reads its argument in slot 0 and then the body's reads, the
    * entry and the selves in that order, with `top` among them: a bit of 1,
    * `λb. b K top`, reads K's slots first and leaves `top` where K has it, or
    * last when K has none; a bit of 0, `λb. b top K`, reads `top` first. So a
    * chain's slots are determined by where `top` stands, and the codes and
    * fillings for each position are made once.
    *
    * FIXME (https://github.com/Atry/private-overlay/issues/1985): this is one
    * more implementation of the spelling rule, for this shape of term, kept in
    * agreement with `thunkInstruction` only by `MixinInstructionLawTest`.
    */
  def mixinInstruction[C <: NativeSpecializer & Singleton](
      members: Vector[(Literal, Configured[C])],
      selves: Int
  )(using
      specializer: C
  ): Configured[C] =
    val topInstruction: Configured[C] =
      Configured.fromPure(specializer)(topPure)
    if selves < 1 then
      throw IllegalArgumentException(s"a mixin of no self: $selves")
    if members.size < 2 then
      throw IllegalArgumentException(
        s"a mixin of fewer than two members: ${members.size}"
      )
    if members.exists(member => Configured.same(member._2, topInstruction)) then
      throw IllegalArgumentException("a mixin with an entry that is top")
    val bodyReads = selves + 1
    val slotCodes = Vector.tabulate(bodyReads + 2)(Code.Slot(_))
    val boundArgument = Vector(Hole.Bound(0))
    def bodyFrom(first: Int): Code =
      (1 until bodyReads).foldLeft(slotCodes(first))((function, position) =>
        Code.Apply(function, slotCodes(first + position))
      )
    val bodyUnderOne = bodyFrom(1)
    val bodyUnderZero = bodyFrom(2)
    val fillingsUnderOne = slotCodes.slice(1, bodyReads + 2)
    val fillingsUnderZero = Vector.tabulate(bodyReads + 1)(top =>
      Vector.tabulate(bodyReads + 1)(position =>
        slotCodes(if position < top then position + 2
        else if position == top then 1
        else position + 1)
      )
    )
    def bitCode(isOne: Boolean, rest: Code, miss: Code): Code =
      Code.Apply(
        Code.Apply(slotCodes(0), if isOne then rest else miss),
        if isOne then miss else rest
      )

    /** The code of the first bit's chain and where `top` stands among the slots
      * after its argument.
      */
    def memberChain(bits: Vector[Boolean]): (Code, Int) =
      val last =
        if bits.last then
          (bitCode(true, bodyUnderOne, slotCodes(bodyReads + 1)), bodyReads)
        else (bitCode(false, bodyUnderZero, slotCodes(1)), 0)
      bits.init.foldRight(last) { case (isOne, (inner, top)) =>
        if isOne then
          (
            bitCode(
              true,
              Code.Thunk(inner, boundArgument, fillingsUnderOne),
              slotCodes(top + 1)
            ),
            top
          )
        else
          (
            bitCode(
              false,
              Code.Thunk(inner, boundArgument, fillingsUnderZero(top)),
              slotCodes(1)
            ),
            0
          )
      }
    def memberRead(
        position: Int,
        top: Int,
        entry: Configured[C]
    ): MixinRead[Configured[C]] =
      if position == top then MixinRead.Held(topInstruction)
      else
        val bodyPosition = if position < top then position else position - 1
        if bodyPosition == 0 then MixinRead.Held(entry)
        else MixinRead.Self(selves - bodyPosition)
    val (sources, numbers, memberCodes) =
      members.foldLeft(
        (
          Vector.empty[MixinRead[Configured[C]]],
          Map.empty[MixinRead[Configured[C]], Int],
          Vector.empty[Code]
        )
      ) { case ((sources, numbers, codes), (literal, entry)) =>
        val (chain, top) = memberChain(Literals.bits(literal))
        val read = Vector.tabulate(bodyReads + 1)(memberRead(_, top, entry))
        val added = read.filterNot(numbers.contains)
        val numbered =
          numbers ++ added.zip(sources.size until sources.size + added.size)
        val fillings = read.map(source =>
          Code.Slot(
            numbered.getOrElse(
              source,
              throw IllegalStateException(
                s"a member's read has no slot: $source"
              )
            )
          )
        )
        (
          sources ++ added,
          numbered,
          codes :+ Code.Thunk(chain, Vector(Hole.Bound(0)), fillings)
        )
      }
    val holes = (selves - 1 to 0 by -1).toVector.map(index =>
      Hole.Bound(
        numbers.getOrElse(
          MixinRead.Self(index),
          throw IllegalStateException(s"no member reads the self $index")
        )
      )
    )
    specializer.thunk(
      Code.Choice.nested(memberCodes),
      NonEmptyHoles
        .of(holes)
        .getOrElse(throw IllegalStateException("a mixin of no self")),
      sources.collect { case MixinRead.Held(instruction) => instruction }
    )

  /** `thunkInstruction` of a closed term read with its spans
    * (`Lambdalattice.located`, `Lambdalattice.locatedInScope`) from the file of
    * the URI, with the source map of the instruction's occurrence
    * (`gezi.locations.SourceMap`): each place the locations of the nodes it was
    * converted from, a code's slot the occurrence of the variable it reads or
    * the whole map of the occurrence of the closed subterm it reads, a filling
    * the occurrences of every closed subterm its slot stands for, merged (equal
    * subterms of one body take one slot), so that the readback
    * (`locatedInstructionTerm`) gives each occurrence its own locations and
    * binder names. The instruction is the one `thunkInstruction` gives. Throws
    * the errors of `thunkInstruction`.
    */
  def locatedThunkInstruction[C <: NativeSpecializer & Singleton](
      term: DeBruijnTermOf[Configured[C]],
      spans: SyntaxSpans,
      uri: java.net.URI
  )(using specializer: C): (Configured[C], SourceMap) =
    val conversion = Conversion[C](specializer)
    val (root, _) =
      conversion.annotated(term, Map.empty, Some(Place(uri, spans))).result
    if root.annotation.looseness != 0 then
      throw LambdaError(LambdaErrorReason.NotClosed(term))
    val (instruction, map, _) = conversion.converted(root).result
    (instruction, map)

  /** The value of a binding `(λt. t V) λm. BODY` contracted
    * (`bindingsContracted`): V's instruction, and the source map of V's
    * occurrence in the text when it was read with its locations.
    */
  final case class ContractedBinding[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      map: SourceMap
  )

  /** A term whose bindings are contracted (`locatedBindingsContracted`): the
    * instruction of the body, each binding's name standing for its value's
    * instruction, the source map of the body's occurrence, in which each
    * occurrence of a binding's name is a leaf at that occurrence's locations,
    * and the bindings, outermost first, each with the map of its value's
    * occurrence. A value is located once, in its own map, however often the
    * body names it, so that the maps together are as large as the text and not
    * as the tree the bindings share, as the printer gives each shared
    * instruction its map once (`locatedInstructionTerm`'s stops). Each is an
    * input of `gezi.provenance.Provenance.of`.
    */
  final case class BindingsContracted[C <: NativeSpecializer & Singleton](
      body: Configured[C],
      map: SourceMap,
      bindings: Vector[ContractedBinding[C]]
  )

  /** The instruction of a term under `enclosingBinders` abstractions of no
    * value, a binder the term may not read, its first `bindings` bindings
    * `(λt. t V) λm. BODY` contracted, the shape in which the printer binds the
    * closed instructions a text refers to more than once (`ReadableText`): each
    * value V converted with each earlier binding's name standing for its
    * instruction, then BODY with each name standing for its value's. So the
    * instruction is the one the printer printed, and reading is linear in the
    * text, while converting the text as it is keeps every binding a β-redex
    * whose code passes every name it still needs to each thunk below, quadratic
    * in the number of bindings. The reason when the term does not start with
    * `bindings` bindings; throws `LambdaError` with `NotClosed` when a value or
    * the body reads a binder of no value.
    */
  def bindingsContracted[C <: NativeSpecializer & Singleton](
      term: DeBruijnTermOf[Configured[C]],
      bindings: Int,
      enclosingBinders: Int
  )(using C): Either[String, Configured[C]] =
    contractedFrom(
      term,
      None,
      bindings,
      Vector.fill(enclosingBinders)(None),
      Vector.empty
    ).map(_.body)

  /** `bindingsContracted` of a term read with its spans
    * (`Lambdalattice.located`) from the file of the URI, with no binder around
    * it: the body's instruction and the source maps of the body and of each
    * value (`BindingsContracted`), whose instructions are those of
    * `bindingsContracted`. Throws as `bindingsContracted` does.
    */
  def locatedBindingsContracted[C <: NativeSpecializer & Singleton](
      term: DeBruijnTermOf[Configured[C]],
      spans: SyntaxSpans,
      uri: java.net.URI,
      bindings: Int
  )(using C): Either[String, BindingsContracted[C]] =
    contractedFrom(
      term,
      Some(Place(uri, spans)),
      bindings,
      Vector.empty,
      Vector.empty
    )

  /** The term contracted from its next binding on, under binders whose values
    * `environment` gives, innermost first, and the bindings already contracted.
    */
  @tailrec
  private def contractedFrom[C <: NativeSpecializer & Singleton](
      term: DeBruijnTermOf[Configured[C]],
      place: Option[Place],
      bindings: Int,
      environment: Vector[Option[DeBruijnTermOf[Configured[C]]]],
      contracted: Vector[ContractedBinding[C]]
  )(using C): Either[String, BindingsContracted[C]] =
    if bindings == 0 then
      val (body, map) = substitutedConverted(term, place, environment)
      Right(BindingsContracted(body, map, contracted))
    else
      term match
        case DeBruijnTerm.Apply(
              DeBruijnTerm.Lambda(
                DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), value)
              ),
              DeBruijnTerm.Lambda(body)
            ) =>
          val (bound, map) = substitutedConverted(
            value,
            place.map(_.child(0).child(0).child(1)),
            None +: environment
          )
          contractedFrom(
            body,
            place.map(_.child(1).child(0)),
            bindings - 1,
            Some(standing(bound)) +: environment,
            contracted :+ ContractedBinding(bound, map)
          )
        case _ =>
          Left(
            s"$bindings bindings (λt. t V) λm. BODY are not at the term's start"
          )

  /** The instruction and the source map of a term, each variable of a binder
    * with a value replaced by the value. A replaced variable's place takes the
    * variable's locations for every node of the value written there.
    */
  private def substitutedConverted[C <: NativeSpecializer & Singleton](
      term: DeBruijnTermOf[Configured[C]],
      place: Option[Place],
      environment: Vector[Option[DeBruijnTermOf[Configured[C]]]]
  )(using specializer: C): (Configured[C], SourceMap) =
    val conversion = Conversion[C](specializer)
    val (substitutedTerm, substitutedSpans) =
      substituted(term, place.map(_.spans), 0, environment).result
    val substitutedPlace = place
      .zip(substitutedSpans)
      .map((outer, spans) => outer.copy(spans = spans))
    val (root, _) =
      conversion.annotated(substitutedTerm, Map.empty, substitutedPlace).result
    if root.annotation.looseness != 0 then
      throw LambdaError(LambdaErrorReason.NotClosed(substitutedTerm))
    val (instruction, map, _) = conversion.converted(root).result
    (instruction, map)

  /** The term a binding's name stands for in the text after it: the constant of
    * its instruction; top's own term for top, which the printer writes in
    * place, as its term, inside the literals of the text (`ReadableText`,
    * LITERALS), so that the reader gives every top of a body one slot, as the
    * readback of the instruction does.
    */
  private def standing[C <: NativeSpecializer & Singleton](
      instruction: Configured[C]
  )(using
      specializer: C
  ): DeBruijnTermOf[Configured[C]] =
    if Configured.same(instruction, Configured.fromPure(specializer)(topPure))
    then Literals.top
    else DeBruijnTerm.Constant(instruction)

  /** The pure term of top, the same object under every configuration: it holds
    * no parallel of instructions.
    */
  private lazy val topPure: Pure = pure(Literals.top)

  /** The term at `depth` abstractions inside the enclosing binders, each
    * variable of an enclosing binder with a value replaced by the value, a
    * closed term, and each of a binder of no value read as one outside the
    * term, so that the term is not closed; with its spans, when it has any, in
    * the substituted term's shape: a replaced variable's spans those of a
    * construct (`SyntaxSpans.Generated`) at the variable's span, every node of
    * the value written there located at it.
    */
  private def substituted[K](
      term: DeBruijnTermOf[K],
      spans: Option[SyntaxSpans],
      depth: Int,
      environment: Vector[Option[DeBruijnTermOf[K]]]
  ): TailRec[(DeBruijnTermOf[K], Option[SyntaxSpans])] =
    def rebuilt(children: Vector[Option[SyntaxSpans]]): Option[SyntaxSpans] =
      spans.map(written =>
        SyntaxSpans.Written(
          written.span,
          written.parentheses,
          children.flatten,
          written.nodeBinder
        )
      )
    def below(position: Int): Option[SyntaxSpans] = spans.map(_.child(position))
    term match
      case DeBruijnTerm.Variable(index) if index >= depth =>
        environment.lift(index - depth).flatten match
          case Some(value) =>
            done(
              (
                value,
                spans.map(written =>
                  SyntaxSpans.Generated(
                    written.span,
                    written.parentheses,
                    Vector.empty,
                    Vector.empty
                  )
                )
              )
            )
          case None => done((DeBruijnTerm.Variable(depth), spans))
      case DeBruijnTerm.Lambda(body) =>
        tailcall(substituted(body, below(0), depth + 1, environment)).map(
          (bodySubstituted, bodySpans) =>
            (DeBruijnTerm.Lambda(bodySubstituted), rebuilt(Vector(bodySpans)))
        )
      case DeBruijnTerm.Apply(function, argument) =>
        for
          (functionSubstituted, functionSpans) <- tailcall(
            substituted(function, below(0), depth, environment)
          )
          (argumentSubstituted, argumentSpans) <- tailcall(
            substituted(argument, below(1), depth, environment)
          )
        yield (
          DeBruijnTerm.Apply(functionSubstituted, argumentSubstituted),
          rebuilt(Vector(functionSpans, argumentSpans))
        )
      case DeBruijnTerm.Choice(left, right) =>
        for
          (leftSubstituted, leftSpans) <- tailcall(
            substituted(left, below(0), depth, environment)
          )
          (rightSubstituted, rightSpans) <- tailcall(
            substituted(right, below(1), depth, environment)
          )
        yield (
          DeBruijnTerm.Choice(leftSubstituted, rightSubstituted),
          rebuilt(Vector(leftSpans, rightSpans))
        )
      case DeBruijnTerm.Parallel(left, right) =>
        for
          (leftSubstituted, leftSpans) <- tailcall(
            substituted(left, below(0), depth, environment)
          )
          (rightSubstituted, rightSpans) <- tailcall(
            substituted(right, below(1), depth, environment)
          )
        yield (
          DeBruijnTerm.Parallel(leftSubstituted, rightSubstituted),
          rebuilt(Vector(leftSpans, rightSpans))
        )
      case other => done((other, spans))

  /** The closed de Bruijn term of a closed instruction: a thunk becomes its
    * chain of abstractions, whose body reads a hole's slot as the binder's
    * variable and a filled slot as the term of its filling, shifted under the
    * binders; every instruction under it is written out by its layer, an
    * instruction met twice written out twice, and an opaque instruction, whose
    * layer is not known, becomes a `Constant`. `thunkInstruction` gives back
    * the instruction. Throws `LambdaError` with `SlotOutOfRange` for a code
    * that reads a slot its thunk does not have, and with `FillingsNotMatched`
    * when a thunk's fillings are fewer than its non-hole slots.
    */
  def instructionTerm[C <: NativeSpecializer & Singleton](
      instruction: Configured[C]
  )(using C): DeBruijnTermOf[Configured[C]] =
    Readback[C](None)
      .termOf(instruction, SourceMap.unlocated, Set.empty)
      .result
      .term

  /** `instructionTerm` read as a formatter reads it, each native storage
    * through its view `v ∥ T`, the sides in turn
    * (`Lambdalattice.closedTextViewed`): the term's readback with no storage
    * left, written as text and never built.
    */
  def instructionTermViewed[C <: NativeSpecializer & Singleton](
      instruction: Configured[C]
  )(using
      C,
      gezi.ir.StorageAccess
  ): DeBruijnTermOf[Configured[C]] =
    Readback[C](Some(summon[gezi.ir.StorageAccess]))
      .termOf(instruction, SourceMap.unlocated, Set.empty)
      .result
      .term

  /** `instructionTerm`, with each instruction of `stops` under the root written
    * as a `Constant` rather than by its layer: the term of a closed instruction
    * whose shared parts a printer names (`ReadableText`).
    */
  def instructionTerm[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      stops: Set[Configured[C]]
  )(using C): DeBruijnTermOf[Configured[C]] =
    Readback[C](None)
      .termOf(instruction, SourceMap.unlocated, stops - instruction)
      .result
      .term

  /** `instructionTerm` with stops, read with the map of an occurrence of the
    * instruction: the term, its source map in the term's shape (`TermMap`), and
    * the map of each stop met under the root, the maps of all its occurrences
    * merged.
    */
  def locatedInstructionTerm[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      map: SourceMap,
      stops: Set[Configured[C]]
  )(using
      C
  ): (DeBruijnTermOf[Configured[C]], TermMap, Map[Configured[C], SourceMap]) =
    val read =
      Readback[C](None).termOf(instruction, map, stops - instruction).result
    (read.term, read.map, read.stopMaps)

  /** The map of `target` from the map of `source`, two instructions with one
    * readback (`instructionTerm`), such as a thunk and its respelling
    * (`gezi.ir.BindingNormalForm.respelled`): each place of the target takes
    * the locations and binder origins of the node of the readback it is, a
    * filling the merged maps of the nodes where it is read; a place of the
    * target whose instruction is the source's at that place takes the source's
    * map of it, read back no further (`ReadMap`). Throws
    * `IllegalArgumentException` where the two readbacks differ in shape.
    */
  def relocatedMap[C <: NativeSpecializer & Singleton](
      source: Configured[C],
      sourceMap: SourceMap,
      target: Configured[C]
  )(using C): SourceMap =
    val readback = Readback[C](None)
    readback
      .instructionMapOf(target, readback.ReadMap.Pending(source, sourceMap))
      .result

  /** The map of an instruction's readback, in the readback's shape: the
    * `TermMap` of `locatedInstructionTerm` with no stops.
    */
  def readbackMap[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      map: SourceMap
  )(using C): TermMap =
    Readback[C](None).termOf(instruction, map, Set.empty).result.map

  /** The map of an instruction from the map of its readback, as `relocatedMap`
    * reads it. Throws `IllegalArgumentException` where the instruction's
    * readback has another shape than the map.
    */
  def mapOfReadback[C <: NativeSpecializer & Singleton](
      target: Configured[C],
      termMap: TermMap
  )(using C): SourceMap =
    val readback = Readback[C](None)
    readback.instructionMapOf(target, readback.ReadMap.Read(termMap)).result

  /** The instruction of an abstraction's body whose bound variable is the
    * argument, an instruction that stays a constant: `(λx. B) A` contracted by
    * one β step on the readback (`instructionTerm`) and converted back
    * (`thunkInstruction`). For a term whose first abstraction binds a
    * combinator, such as a side of a justifying lemma of the standard library's
    * vocabulary of combinator properties, instantiated by the combinator's
    * instruction. Throws `IllegalArgumentException` when the instruction is no
    * abstraction.
    */
  def bodyInstantiated[C <: NativeSpecializer & Singleton](
      abstraction: Configured[C],
      argument: Configured[C]
  )(using
      C
  ): Configured[C] =
    instructionTerm(abstraction) match
      case DeBruijnTerm.Lambda(body) =>
        thunkInstruction(
          instantiatedFrom[Configured[C]](
            body,
            0,
            DeBruijnTerm.Constant(argument)
          ).result
        )
      case other =>
        throw IllegalArgumentException(s"no abstraction to instantiate: $other")

  /** The position, from 0, of the slot among the filled slots of a thunk whose
    * holes are given: the fillings of a thunk are the values of its non-hole
    * slots in slot order. Throws `LambdaError` with `SlotIsAHole` when the slot
    * is a hole.
    */
  def fillingPosition(holes: Vector[Hole], slot: Int): Int =
    if holes.contains(Hole.Bound(slot)) then
      throw LambdaError(LambdaErrorReason.SlotIsAHole(slot, holes))
    (0 until slot).count(candidate => !holes.contains(Hole.Bound(candidate)))

  /** What each slot of a thunk holds, by slot from 0: the slot of the binder at
    * position P of the holes (lambda order, ignored binders counted) holds the
    * P-th hole value, and every other slot the next filling. Throws
    * `LambdaError` with `FillingsNotMatched` when the fillings are fewer or
    * more than the non-hole slots.
    */
  def slotValues[Value](
      holes: Vector[Hole],
      holeValues: Vector[Value],
      fillings: Vector[Value]
  ): Vector[Value] =
    require(
      holeValues.size == holes.size,
      s"${holeValues.size} hole values for ${holes.size} holes"
    )
    val boundSlots = holes.collect { case Hole.Bound(slot) => slot }
    val slotCount = boundSlots.size + fillings.size
    // Each bound slot one of the slots, no two holes binding one slot: else
    // the fillings are not as many as the slots no hole binds.
    if boundSlots.distinct.size != boundSlots.size || boundSlots.exists(
        _ >= slotCount
      )
    then
      throw LambdaError(
        LambdaErrorReason.FillingsNotMatched(holes, fillings.size)
      )
    // One value per slot, made at once: a thunk of a respelled β body has
    // over a hundred slots, and the dynamic program over codes reads them at
    // every evaluation.
    // A thunk has a few holes, so each slot looks its hole up among them
    // without a table, by index, with no iterator made per slot (an
    // iterator per slot was 5.5 GB of a 17.6 GB extraction, JFR).
    Vector.tabulate(slotCount)(slot =>
      holePosition(holes, slot, 0) match
        case -1 => fillings(slot - boundSlotsBelow(boundSlots, slot, 0, 0))
        case position => holeValues(position)
    )

  /** The position of the first hole that binds the slot, from `position` on; -1
    * when none does.
    */
  @tailrec
  private def holePosition(holes: Vector[Hole], slot: Int, position: Int): Int =
    if position >= holes.size then -1
    else
      holes(position) match
        case Hole.Bound(bound) if bound == slot => position
        case _ => holePosition(holes, slot, position + 1)

  /** `found` and the number of bound slots below the slot, from `index` on. */
  @tailrec
  private def boundSlotsBelow(
      boundSlots: Vector[Int],
      slot: Int,
      index: Int,
      found: Int
  ): Int =
    if index >= boundSlots.size then found
    else
      boundSlotsBelow(
        boundSlots,
        slot,
        index + 1,
        if boundSlots(index) < slot then found + 1 else found
      )

  // ---- the conversion ----

  /** Where the walk that annotates a term stands in the spans it was read with:
    * the file's URI and the spans of the node, or nowhere.
    */
  private final case class Place(uri: java.net.URI, spans: SyntaxSpans):
    def child(position: Int): Place = Place(uri, spans.child(position))

    def locations: Set[Location] = Set(Location.Source(uri, spans.span))

    /** The origin of the node's binder, when it is an abstraction the reader
      * gave one.
      */
    def binder: Set[BinderOrigin] = spans.nodeBinder.toSet.map {
      case SpelledBinder.Named(name, span) =>
        BinderOrigin.Written(name, Location.Source(uri, span))
      case SpelledBinder.LiteralBit(literal, bit, span) =>
        BinderOrigin.LiteralBit(
          literal.bytes.toVector,
          bit,
          Location.Source(uri, span)
        )
      case SpelledBinder.Enclosing(name) => BinderOrigin.Enclosing(name)
    }

  /** The map of the part at the position, none where the map locates nothing
    * below its place.
    */
  private def childMap(map: SourceMap, position: Int): SourceMap =
    map.children.lift(position).getOrElse(SourceMap.unlocated)

  /** The conversion of de Bruijn terms whose constants are terms of the
    * configuration `C` into terms of `C`, built through its native specializer:
    * every layer the conversion makes goes through `specializer`, so the result
    * is a term of `C` by its construction, with no test at run time.
    */
  private final class Conversion[C <: NativeSpecializer & Singleton](
      val specializer: C
  ):

    /** A term of the configuration. */
    type Term = Configured[C]

    /** The thunk a constant is, when it is a thunk with holes: its code, holes
      * and fillings.
      */
    private object ConstantThunk:
      def unapply(constant: Term): Option[(Code, Vector[Hole], Vector[Term])] =
        constant.layer match
          case gezi.ir.Thunk(code, holes, fillings) if holes.nonEmpty =>
            Some((code, holes, fillings))
          case _ => None

    /** The holes of a chain of binders, one at least, since a chain is of one
      * abstraction at least.
      */
    private def chainHoles(holes: Vector[Hole]): NonEmptyHoles =
      NonEmptyHoles
        .of(holes)
        .getOrElse(throw IllegalStateException("a chain of no binder"))

    /** What the conversion asks of a subterm at each node: the subterm, each
      * free name the constant of its instruction (`resolvedTerm`); its
      * looseness, the least number of enclosing binders under which it is
      * closed (`closed_under(Term, Depth)` holds exactly when the looseness is
      * at most Depth; a negative index makes it unbounded); and its structural
      * hash, with which closed subterms are compared before their terms are
      * (Prolog's `==`). Looseness and hash are computed once, bottom up, so
      * that asking whether each node of a body is closed is not quadratic, as
      * `closed_under/2` called at each node is, and a closed subterm is hashed
      * in constant time. And the node's source locations, none for a term not
      * read with its spans (`locatedThunkInstruction`); no comparison reads
      * them (`SlotSource.Closed`), so they change no slot and no instruction.
      */
    final case class Annotation(
        term: DeBruijnTermOf[Term],
        looseness: Int,
        hash: Int,
        locations: Set[Location],
        binder: Set[BinderOrigin]
    )

    /** A de Bruijn term with the annotation of each node. Never compared with
      * `==`, which would recurse per level: closed subterms are compared by
      * their annotations' hashes and terms.
      */
    enum Node:
      def annotation: Annotation
      case Variable(annotation: Annotation, index: Int)
      case Lambda(annotation: Annotation, body: Node)
      case Apply(annotation: Annotation, function: Node, argument: Node)
      case Constant(annotation: Annotation, instruction: Term)
      case Choice(annotation: Annotation, left: Node, right: Node)
      case Parallel(annotation: Annotation, left: Node, right: Node)

    private val unbounded: Int = Int.MaxValue

    /** The annotated term, each free name the constant of its instruction in
      * the names, and the count of the nodes the walk visited.
      */
    def annotated(
        term: DeBruijnTermOf[Term],
        names: Map[String, Term],
        place: Option[Place]
    ): TailRec[(Node, Long)] =
      annotatedSharing(term, names, place, Map.empty).map((node, visits, _) =>
        (node, visits)
      )

    /** `annotated`, given the closed compound subterms annotated so far and
      * giving them back with this term's. A term is interned, so a closed
      * subterm written at many places is one key, and with no spans its
      * annotation depends on nothing around it: it is read once, as the `top`
      * at every bit of a literal binder is, and a later occurrence counts one
      * visit. A term read with its spans keeps a node for each occurrence,
      * whose locations differ.
      */
    private def annotatedSharing(
        term: DeBruijnTermOf[Term],
        names: Map[String, Term],
        place: Option[Place],
        known: Map[DeBruijnTermOf[Term], Node]
    ): TailRec[(Node, Long, Map[DeBruijnTermOf[Term], Node])] =
      known.get(term) match
        case Some(node) => done((node, 1L, known))
        case None       => annotatedAnew(term, names, place, known)

    /** The node of a term no earlier occurrence annotated, one case for each
      * constructor, since this runs for every node of every term read. The term
      * an annotation holds has each free name the constant of its instruction
      * in the names: closed subterms are compared by it (`SlotSource.Closed`),
      * so that two free names of one instruction take one slot, as the
      * constants of that instruction do, and a term converts with the names as
      * it converts with its free names replaced by those constants
      * (`FreeNameConversionLawTest`). A term with no free name under it is
      * itself, not a copy, and a self-application `M M` keeps its function and
      * argument one term.
      */
    private def annotatedAnew(
        term: DeBruijnTermOf[Term],
        names: Map[String, Term],
        place: Option[Place],
        known: Map[DeBruijnTermOf[Term], Node]
    ): TailRec[(Node, Long, Map[DeBruijnTermOf[Term], Node])] =
      def annotation(
          resolved: DeBruijnTermOf[Term],
          looseness: Int,
          hash: Int
      ): Annotation =
        Annotation(
          resolved,
          looseness,
          hash,
          place.fold(Set.empty)(_.locations),
          place.fold(Set.empty)(_.binder)
        )
      def hashOf(constructor: Int, holding: Int, parts: Int): Int =
        MurmurHash3.mix(MurmurHash3.mix(constructor, holding), parts)
      def remembered(
          node: Node,
          visits: Long,
          after: Map[DeBruijnTermOf[Term], Node]
      ): (Node, Long, Map[DeBruijnTermOf[Term], Node]) =
        (
          node,
          visits,
          if place.isEmpty && node.annotation.looseness == 0 then
            after.updated(term, node)
          else after
        )
      def pair(
          left: DeBruijnTermOf[Term],
          right: DeBruijnTermOf[Term],
          constructor: Int,
          rebuilt: (
              DeBruijnTermOf[Term],
              DeBruijnTermOf[Term]
          ) => DeBruijnTermOf[Term],
          made: (Annotation, Node, Node) => Node
      ): TailRec[(Node, Long, Map[DeBruijnTermOf[Term], Node])] =
        tailcall(annotatedSharing(left, names, place.map(_.child(0)), known))
          .flatMap((leftNode, leftVisits, afterLeft) =>
            tailcall(
              annotatedSharing(right, names, place.map(_.child(1)), afterLeft)
            ).map((rightNode, rightVisits, afterRight) =>
              val hash = MurmurHash3.mix(
                MurmurHash3
                  .mix(hashOf(constructor, 0, 2), leftNode.annotation.hash),
                rightNode.annotation.hash
              )
              val resolved =
                if (leftNode.annotation.term eq left) && (rightNode.annotation.term eq right)
                then term
                else
                  rebuilt(leftNode.annotation.term, rightNode.annotation.term)
              val looseness = math.max(
                leftNode.annotation.looseness,
                rightNode.annotation.looseness
              )
              remembered(
                made(
                  annotation(resolved, looseness, hash),
                  leftNode,
                  rightNode
                ),
                leftVisits + rightVisits + 1,
                afterRight
              )
            )
          )
      term.layer match
        case gezi.frontend.Variable(index) =>
          done(
            (
              Node.Variable(
                annotation(
                  term,
                  if index < 0 then unbounded else index + 1,
                  hashOf(1, index, 0)
                ),
                index
              ),
              1L,
              known
            )
          )
        case gezi.frontend.Constant(instruction) =>
          done(
            (
              Node.Constant(
                annotation(term, 0, hashOf(2, instruction.hashCode, 0)),
                instruction
              ),
              1L,
              known
            )
          )
        case gezi.frontend.Free(name) =>
          val instruction = namedInstruction(name, names)
          done(
            (
              Node.Constant(
                annotation(
                  DeBruijnTerm.Constant(instruction),
                  0,
                  hashOf(2, instruction.hashCode, 0)
                ),
                instruction
              ),
              1L,
              known
            )
          )
        case gezi.frontend.Lambda(body) =>
          tailcall(annotatedSharing(body, names, place.map(_.child(0)), known))
            .map((bodyNode, visits, after) =>
              val hash =
                MurmurHash3.mix(hashOf(3, 0, 1), bodyNode.annotation.hash)
              val resolved = if bodyNode.annotation.term eq body then term
              else DeBruijnTerm.Lambda(bodyNode.annotation.term)
              val bodyLooseness = bodyNode.annotation.looseness
              val looseness = if bodyLooseness == unbounded then unbounded
              else math.max(0, bodyLooseness - 1)
              remembered(
                Node.Lambda(annotation(resolved, looseness, hash), bodyNode),
                visits + 1,
                after
              )
            )
        case gezi.ir.Apply(function, argument) =>
          pair(
            function,
            argument,
            4,
            (resolvedFunction, resolvedArgument) =>
              DeBruijnTerm.Apply(
                resolvedFunction,
                if function eq argument then resolvedFunction
                else resolvedArgument
              ),
            Node.Apply(_, _, _)
          )
        case gezi.ir.Choice(left, right) =>
          pair(left, right, 5, DeBruijnTerm.Choice(_, _), Node.Choice(_, _, _))
        case gezi.ir.Parallel(left, right) =>
          pair(
            left,
            right,
            6,
            DeBruijnTerm.Parallel(_, _),
            Node.Parallel(_, _, _)
          )

    /** The instruction of a free name in the names; throws
      * `LambdalatticeMalformed` with `UnboundName` when they lack it.
      */
    private def namedInstruction(name: String, names: Map[String, Term]): Term =
      names.getOrElse(
        name,
        throw LambdalatticeMalformed(LambdalatticeProblem.UnboundName(name))
      )

    /** What a slot of a body reads: the chain's variable of a de Bruijn index
      * at the body, a variable of the context outside the chain, or a maximal
      * closed subterm, the first node met of the equal ones.
      */
    private sealed trait SlotSource

    private object SlotSource:
      final case class Bound(index: Int) extends SlotSource
      final case class Free(index: Int) extends SlotSource

      /** Equal to another closed subterm exactly when their terms are equal;
        * hashed by the annotation's hash.
        */
      final case class Closed(node: Node) extends SlotSource:
        override def hashCode: Int = node.annotation.hash
        override def equals(other: Any): Boolean = other match
          case Closed(that) =>
            that.annotation.hash == node.annotation.hash &&
            that.annotation.term == node.annotation.term
          case _ => false

    /** The slots of a body: what each reads, in order of first occurrence; the
      * slot of each, indexed only above `Slots.scannedSources` sources (a chain
      * per bit of a literal binder has few, and building an index for each was
      * a fifth of the allocation of converting a directory); and the count of
      * the operations of the walk that allocates them so far
      * (`thunkInstructionCounted`).
      */
    private final case class Slots(
        sources: Vector[SlotSource],
        numbers: Map[SlotSource, Int],
        operations: Long,
        occurrences: Map[Int, Vector[Occurrence]]
    ):

      /** The slot of the source, none when it has no slot yet. */
      def numberOf(source: SlotSource): Option[Int] =
        @tailrec
        def scanned(index: Int): Option[Int] =
          if index == sources.size then None
          else if sources(index) == source then Some(index)
          else scanned(index + 1)
        if sources.size > Slots.scannedSources then numbers.get(source)
        else scanned(0)

      /** The slots with the sources, none of which has a slot, after the
        * others. Counts no operation.
        */
      def joined(added: Vector[SlotSource]): Slots =
        val all = sources ++ added
        val indexed =
          if all.size <= Slots.scannedSources then Map.empty[SlotSource, Int]
          else if sources.size <= Slots.scannedSources then
            all.zipWithIndex.toMap
          else numbers ++ added.zip(sources.size until all.size)
        assert(
          all.size <= Slots.scannedSources || indexed.size == all.size,
          s"a source given two slots: $added"
        )
        copy(sources = all, numbers = indexed)

      /** The slot of the source, appended when new, and the slots after. */
      def slotOf(source: SlotSource): (Int, Slots) =
        numberOf(source) match
          case Some(index) => (index, counted(1))
          case None        => (sources.size, joined(Vector(source)).counted(1))

      /** The slots with the closed occurrences recorded as occurrences of the
        * slot, after the ones recorded before: a filling's source map merges
        * those of every occurrence its slot stands for. Counts no operation.
        */
      def occurred(slot: Int, found: Vector[Occurrence]): Slots =
        if found.isEmpty then this
        else
          copy(occurrences =
            occurrences.updated(
              slot,
              occurrences.getOrElse(slot, Vector.empty) ++ found
            )
          )

      /** The slots with `more` operations counted. */
      def counted(more: Long): Slots = copy(operations = operations + more)

      /** For the binders of a chain of `count`, outermost first (de Bruijn
        * index count - 1 down to 0 at the body), the slot each reads, or
        * ignored.
        */
      def holes(count: Int): Vector[Hole] =
        (count - 1 to 0 by -1).toVector.map(index =>
          numberOf(SlotSource.Bound(index)) match
            case Some(slot) => Hole.Bound(slot)
            case None       => Hole.Ignored
        )

    private object Slots:
      val empty: Slots = Slots(Vector.empty, Map.empty, 0, Map.empty)

      /** The most sources a body's slots are scanned for rather than indexed:
        * the size of a `Vector`'s first block, a bound on the scan's cost.
        */
      val scannedSources: Int = 32

      /** Whether no two of the sources are equal, from the pair of the indices
        * `first` and `second` on, allocating nothing.
        */
      @tailrec
      def pairwiseDistinct(
          sources: Vector[SlotSource],
          first: Int,
          second: Int
      ): Boolean =
        if first >= sources.size then true
        else if second >= sources.size then
          pairwiseDistinct(sources, first + 1, first + 2)
        else
          sources(first) != sources(second) && pairwiseDistinct(
            sources,
            first,
            second + 1
          )

    /** An occurrence of a closed subterm that a slot reads: its node and, for a
      * located node, its conversion (`converted`), whose map the slot's place
      * in the code map holds, so that each occurrence keeps its own locations
      * and binder names, and which the filling's map merges with the others'.
      */
    private final case class Occurrence(
        node: Node,
        conversion: Option[(Term, SourceMap, Long)]
    )

    /** The source of a variable of de Bruijn index `index` in a body of a chain
      * of `count` binders.
      */
    private def variableSource(index: Int, count: Int): SlotSource =
      if index < count then SlotSource.Bound(index)
      else SlotSource.Free(index - count)

    /** The origins of the binders of the first `count` abstractions of the
      * chain, in lambda order; none when no abstraction of them has one.
      */
    private def chainBinders(
        node: Node,
        count: Int
    ): Vector[Set[BinderOrigin]] =
      @tailrec
      def collected(
          current: Node,
          found: Vector[Set[BinderOrigin]]
      ): Vector[Set[BinderOrigin]] = current match
        case Node.Lambda(annotation, body) if found.size < count =>
          collected(body, found :+ annotation.binder)
        case _ => found
      val binders = collected(node, Vector.empty)
      if binders.forall(_.isEmpty) then Vector.empty else binders

    /** The chain of abstractions at the node: their number and the body under
      * them, which is no abstraction.
      */
    @tailrec
    private def chain(node: Node, count: Int): (Int, Node) = node match
      case Node.Lambda(_, body) => chain(body, count + 1)
      case _                    => (count, node)

    /** The IR of a closed subterm, the source map of its occurrence, and the
      * count of the operations: the nodes visited, the lambdas of each chain,
      * and the operations of each chain's body (`bodyThunk`) and of reading off
      * its holes. A constant's place, and that of a chain folded into a
      * constant's thunk, locates nothing below it.
      */
    def converted(node: Node): TailRec[(Term, SourceMap, Long)] = node match
      case Node.Constant(annotation, instruction) =>
        done((instruction, SourceMap.leaf(annotation.locations), 1L))
      case Node.Apply(annotation, function, argument) =>
        for
          (functionInstruction, functionMap, functionOperations) <- tailcall(
            converted(function)
          )
          (argumentInstruction, argumentMap, argumentOperations) <- tailcall(
            converted(argument)
          )
        yield (
          specializer.application(functionInstruction, argumentInstruction),
          SourceMap.pair(annotation.locations, functionMap, argumentMap),
          functionOperations + argumentOperations + 1
        )
      case Node.Choice(annotation, left, right) =>
        for
          (leftInstruction, leftMap, leftOperations) <- tailcall(
            converted(left)
          )
          (rightInstruction, rightMap, rightOperations) <- tailcall(
            converted(right)
          )
        yield (
          specializer.choice(leftInstruction, rightInstruction),
          SourceMap.pair(annotation.locations, leftMap, rightMap),
          leftOperations + rightOperations + 1
        )
      case Node.Parallel(annotation, left, right) =>
        for
          (leftInstruction, leftMap, leftOperations) <- tailcall(
            converted(left)
          )
          (rightInstruction, rightMap, rightOperations) <- tailcall(
            converted(right)
          )
        yield (
          specializer.parallel(leftInstruction, rightInstruction),
          SourceMap.pair(annotation.locations, leftMap, rightMap),
          leftOperations + rightOperations + 1
        )
      case Node.Lambda(annotation, _) =>
        chain(node, 0) match
          case (
                count,
                Node.Constant(constant, ConstantThunk(code, holes, fillings))
              ) =>
            done(
              (
                specializer.thunk(
                  code,
                  NonEmptyHoles(
                    Hole.Ignored,
                    Vector.fill(count - 1)(Hole.Ignored) ++ holes
                  ),
                  fillings
                ),
                SourceMap.leaf(annotation.locations ++ constant.locations),
                count + 2L
              )
            )
          case (count, body) =>
            chainConverted(
              annotation.locations,
              chainBinders(node, count),
              count,
              body
            )
      case Node.Variable(_, index) =>
        throw IllegalStateException(
          s"a closed term has no variable outside a chain, found $index"
        )

    /** The thunk of a chain of `count` binders whose body is `body`, no
      * abstraction and no name of a thunk with holes, the source map of its
      * occurrence (the chain's locations, the code's map, and each filling's
      * map merged over the located occurrences its slot stands for), and the
      * count of its operations, which the maps of the further occurrences add
      * nothing to. The code's map keeps the map of each occurrence at its
      * slot's place only for a slot of several located occurrences; the place
      * of a slot read at one is a leaf at its locations (`readOnceLeaves`),
      * since the filling's map is then that occurrence's map.
      */
    private def chainConverted(
        locations: Set[Location],
        binders: Vector[Set[BinderOrigin]],
        count: Int,
        body: Node
    ): TailRec[(Term, SourceMap, Long)] =
      for
        (code, codeMap, slots) <- tailcall(bodyThunk(body, count, Slots.empty))
        fillings <- Trampoline.indexed(slots.sources)((source, slot) =>
          source match
            case SlotSource.Closed(closed) =>
              val occurrences = slots.occurrences.getOrElse(slot, Vector.empty)
              val further = occurrences
                .filter(occurrence => occurrence.node ne closed)
                .flatMap(_.conversion)
                .map(_._2)
              occurrences.find(_.node eq closed).flatMap(_.conversion) match
                case Some((instruction, map, operations)) =>
                  done(
                    Some(
                      (
                        instruction,
                        further.foldLeft(map)(_.merged(_)),
                        operations
                      )
                    )
                  )
                case None =>
                  tailcall(converted(closed)).map(
                    (instruction, map, operations) =>
                      Some(
                        (
                          instruction,
                          further.foldLeft(map)(_.merged(_)),
                          operations
                        )
                      )
                  )
            case SlotSource.Bound(_)    => done(None)
            case SlotSource.Free(index) =>
              throw IllegalStateException(
                s"a closed chain's body reads the outer variable $index"
              )
        )
        keptMap <-
          if codeMap.bare then done(codeMap)
          else
            val readOnce = slots.sources.indices
              .filter(slot =>
                slots.sources(slot) match
                  case SlotSource.Closed(_) =>
                    slots.occurrences
                      .getOrElse(slot, Vector.empty)
                      .count(_.conversion.isDefined) <= 1
                  case _ => false
              )
              .toSet
            tailcall(readOnceLeaves(code, codeMap, readOnce))
      yield
        val filled = fillings.flatten
        (
          specializer.thunk(
            code,
            chainHoles(slots.holes(count)),
            filled.map(_._1)
          ),
          SourceMap.of(locations, Some(keptMap), filled.map(_._2), binders),
          filled.map(_._3).sum + slots.operations + count + count + 1
        )

    /** The code's map with the place of each slot of `readOnce` a leaf at its
      * locations, in the code and in its inner codes, whose slots that an inner
      * filling hands up as a slot of the code are of `readOnce` when that slot
      * is. A closed subterm the body writes once is then located by its
      * filling's map alone, where the map of its occurrence would otherwise
      * stand a second time: nested n deep, a map holding each level twice
      * spells 2^n places, and every walk of it (`SourceMap.merged`, equality)
      * would take as long.
      */
    private def readOnceLeaves(
        code: Code,
        map: SourceMap,
        readOnce: Set[Int]
    ): TailRec[SourceMap] =
      if map.bare then done(map)
      else
        code match
          case Code.Slot(index) =>
            done(if readOnce(index) then SourceMap.leaf(map.locations) else map)
          case Code.Apply(left, right) =>
            readOncePair(left, right, map, readOnce)
          case Code.Choice(left, right) =>
            readOncePair(left, right, map, readOnce)
          case Code.Parallel(left, right) =>
            readOncePair(left, right, map, readOnce)
          case Code.Thunk(inner, holes, fillings) =>
            val innerReadOnce = slotValues(
              holes,
              holes.map(_ => false),
              fillings.map {
                case Code.Slot(slot) => readOnce(slot)
                case _               => false
              }
            ).zipWithIndex.collect { case (true, slot) => slot }.toSet
            for
              innerMap <- map.code.fold(done(Option.empty[SourceMap]))(
                innerCode =>
                  tailcall(readOnceLeaves(inner, innerCode, innerReadOnce)).map(
                    Some(_)
                  )
              )
              fillingMaps <- Trampoline.indexed(map.children)(
                (fillingMap, index) =>
                  fillings
                    .lift(index)
                    .fold(done(fillingMap))(filling =>
                      readOnceLeaves(filling, fillingMap, readOnce)
                    )
              )
            yield map.copy(code = innerMap, children = fillingMaps)

    /** `readOnceLeaves` of the two parts of an application, a choice or a
      * parallel.
      */
    private def readOncePair(
        left: Code,
        right: Code,
        map: SourceMap,
        readOnce: Set[Int]
    ): TailRec[SourceMap] =
      for
        leftMap <- tailcall(readOnceLeaves(left, childMap(map, 0), readOnce))
        rightMap <- tailcall(readOnceLeaves(right, childMap(map, 1), readOnce))
      yield map.copy(children = Vector(leftMap, rightMap))

    /** The code of a subterm of the body of a chain of `count` binders, its
      * source map (a slot's place a leaf at the occurrence of the variable it
      * reads, or the whole map of the occurrence of the closed subterm it
      * reads; an inner thunk's fillings unlocated), and the slots after it,
      * which count one more operation for each node visited and record each
      * located closed subterm as an occurrence of its slot, with its
      * conversion.
      */
    private def bodyThunk(
        node: Node,
        count: Int,
        entered: Slots
    ): TailRec[(Code, SourceMap, Slots)] =
      val slots = entered.counted(1)
      node match
        case Node.Variable(annotation, index) =>
          val (slot, after) = slots.slotOf(variableSource(index, count))
          done((Code.Slot(slot), SourceMap.leaf(annotation.locations), after))
        case _ if node.annotation.looseness == 0 =>
          val (slot, after) = slots.slotOf(SlotSource.Closed(node))
          // An unlocated occurrence is not recorded: it has no conversion for
          // the filling's map to merge, so `chainConverted` would read nothing
          // from it, while recording it carried every occurrence of a closed
          // subterm through each enclosing chain (`innerFillings`), the
          // occurrences times the depth: on an exchange line of 7,947 literal
          // binders, chains nested up to 996 deep, the conversion took 42.9 s
          // with them and 24.9 s without (measured 2026-11-21 on two cores,
          // one run each).
          if node.annotation.locations.isEmpty then
            done((Code.Slot(slot), SourceMap.unlocated, after))
          else
            tailcall(converted(node)).map(conversion =>
              (
                Code.Slot(slot),
                conversion._2,
                after.occurred(slot, Vector(Occurrence(node, Some(conversion))))
              )
            )
        case Node.Apply(annotation, function, argument) =>
          for
            (functionCode, functionMap, afterFunction) <- tailcall(
              bodyThunk(function, count, slots)
            )
            (argumentCode, argumentMap, afterArgument) <- tailcall(
              bodyThunk(argument, count, afterFunction)
            )
          yield (
            Code.Apply(functionCode, argumentCode),
            SourceMap.pair(annotation.locations, functionMap, argumentMap),
            afterArgument
          )
        case Node.Choice(annotation, left, right) =>
          for
            (leftCode, leftMap, afterLeft) <- tailcall(
              bodyThunk(left, count, slots)
            )
            (rightCode, rightMap, afterRight) <- tailcall(
              bodyThunk(right, count, afterLeft)
            )
          yield (
            Code.Choice(leftCode, rightCode),
            SourceMap.pair(annotation.locations, leftMap, rightMap),
            afterRight
          )
        case Node.Parallel(annotation, left, right) =>
          for
            (leftCode, leftMap, afterLeft) <- tailcall(
              bodyThunk(left, count, slots)
            )
            (rightCode, rightMap, afterRight) <- tailcall(
              bodyThunk(right, count, afterLeft)
            )
          yield (
            Code.Parallel(leftCode, rightCode),
            SourceMap.pair(annotation.locations, leftMap, rightMap),
            afterRight
          )
        case Node.Lambda(annotation, _) =>
          val (innerCount, innerBody) = chain(node, 0)
          tailcall(bodyThunk(innerBody, innerCount, Slots.empty)).map(
            (innerCode, innerMap, innerSlots) =>
              val (fillings, after) = innerFillings(innerSlots, count, slots)
              (
                Code.Thunk(innerCode, innerSlots.holes(innerCount), fillings),
                SourceMap.of(
                  annotation.locations,
                  Some(innerMap),
                  fillings.map(_ => SourceMap.unlocated),
                  chainBinders(node, innerCount)
                ),
                after.counted(innerSlots.operations + innerCount + innerCount)
              )
          )
        case Node.Constant(_, _) =>
          throw IllegalStateException("a constant is closed and takes a slot")

    /** What the non-hole slots of an inner chain read, as slot references of
      * the enclosing body of `count` binders, and the enclosing slots after
      * them: a closed subterm is a slot of the enclosing body too, its
      * occurrences in the inner chain recorded as occurrences of that slot; the
      * inner chain's outer variable of an index is the enclosing body's
      * variable of that index, bound by the enclosing chain when below `count`
      * and outer again otherwise. Each of the inner slots counts one operation.
      *
      * The inner chain's sources are distinct and so are what they read here,
      * so those new to the enclosing body join it at once rather than one
      * update each: a literal binder is a chain per bit, whose slots include
      * every variable its body reads.
      *
      * FIXME (https://github.com/Atry/private-overlay/issues/1875): a located
      * reading still carries each located occurrence of a closed subterm
      * through every enclosing chain, appending it to the enclosing slot's
      * occurrences at each level, so its cost is the occurrences times the
      * depth of the chains above them (derived from the code, not measured): a
      * file whose literal binders nest deep pays it in its source map.
      * Candidate: keep each slot's occurrences as a tree of the inner chains'
      * occurrences, merged once where the filling's map is built.
      */
    private def innerFillings(
        innerSlots: Slots,
        count: Int,
        slots: Slots
    ): (Vector[Code], Slots) =
      val read = innerSlots.sources.collect {
        case closed: SlotSource.Closed => closed
        case SlotSource.Free(index)    => variableSource(index, count)
      }
      // Above `Slots.scannedSources` the index checks this (`Slots.joined`).
      assert(
        read.size > Slots.scannedSources || Slots.pairwiseDistinct(read, 0, 1),
        s"an inner chain's sources read one enclosing source twice: $read"
      )
      val joined = slots
        .joined(read.filter(slots.numberOf(_).isEmpty))
        .counted(innerSlots.sources.size)
      def number(source: SlotSource): Int =
        joined
          .numberOf(source)
          .getOrElse(
            throw IllegalStateException(
              s"an inner chain's source has no slot: $source"
            )
          )
      val after = innerSlots.occurrences.foldLeft(joined) {
        case (current, (innerSlot, found)) =>
          innerSlots.sources(innerSlot) match
            case closed: SlotSource.Closed =>
              current.occurred(number(closed), found)
            case other =>
              throw IllegalStateException(
                s"only a closed subterm has occurrences, found $other"
              )
      }
      (read.map(source => Code.Slot(number(source))), after)

  // ---- the readback ----

  /** The readback of terms of the configuration `C` into de Bruijn terms whose
    * constants are terms of `C`: every part read through the term's own layer,
    * so that the parts are terms of `C` by their type, a storage or an opaque
    * term a constant, its view never taken apart.
    */
  /** The readback of terms of the configuration. With the capability `viewing`,
    * a formatter's, a native storage is read through its view `v ∥ T` as the
    * parallel it stands for, each side in turn, so that the text written of the
    * readback is the term's text; with none, a storage is a constant, its view
    * never taken apart.
    */
  private final class Readback[C <: NativeSpecializer & Singleton](
      viewing: Option[gezi.ir.StorageAccess]
  )(using specializer: C):

    /** A term of the configuration. */
    type Term = Configured[C]

    private object TermApply:
      def unapply(term: Term): Option[(Term, Term)] = term.layer match
        case gezi.ir.Apply(function, argument) => Some((function, argument))
        case _                                 => None

    private object TermChoice:
      def unapply(term: Term): Option[(Term, Term)] = term.layer match
        case gezi.ir.Choice(left, right) => Some((left, right))
        case _                           => None

    private object TermParallel:
      def unapply(term: Term): Option[(Term, Term)] = term.layer match
        case gezi.ir.Parallel(left, right) => Some((left, right))
        case _                             => None

    private object TermThunk:
      def unapply(term: Term): Option[(Code, Vector[Hole], Vector[Term])] =
        term.layer match
          case gezi.ir.Thunk(code, holes, fillings) =>
            Some((code, holes, fillings))
          case _ => None

    /** A part of the readback: its de Bruijn term, the term's source map, and
      * the map of each stop met under it.
      */
    final case class ReadBack(
        term: DeBruijnTermOf[Term],
        map: TermMap,
        stopMaps: Map[Term, SourceMap]
    )

    def termOf(
        instruction: Term,
        map: SourceMap,
        stops: Set[Term]
    ): TailRec[ReadBack] =
      instruction match
        // A formatter's readback reads a native storage through its one-layer view, the parallel it stands for.
        case viewed
            if viewing.isDefined && gezi.ir.NativeStorage.stored(
              viewed.representation
            ) && !stops.contains(viewed) =>
          viewed.layer match
            case storage: gezi.ir.NativeStorage =>
              val view = (specializer: C).viewOf(storage)(using
                viewing.getOrElse(throw IllegalStateException("no capability"))
              )
              pairOf(view.value, view.criterion, map, stops)((left, right) =>
                DeBruijnTerm.Parallel(left, right)
              )
            case other =>
              throw IllegalStateException(
                s"a stored term whose layer is no storage: $other"
              )
        // A native storage is a leaf of its term's layer, read back as a constant: its view is never taken apart here.
        case opaque
            if opaque.representation.opaque || stops.contains(
              opaque
            ) || gezi.ir.NativeStorage.stored(opaque.representation) =>
          done(
            ReadBack(
              DeBruijnTerm.Constant(opaque),
              if map.locations.isEmpty then TermMap.Unknown
              else TermMap.Leaf(map.locations),
              if stops.contains(opaque) then Map(opaque -> map) else Map.empty
            )
          )
        case TermApply(function, argument) =>
          pairOf(function, argument, map, stops)((left, right) =>
            DeBruijnTerm.Apply(left, right)
          )
        case TermChoice(left, right) =>
          pairOf(left, right, map, stops)((leftTerm, rightTerm) =>
            DeBruijnTerm.Choice(leftTerm, rightTerm)
          )
        case TermParallel(left, right) =>
          pairOf(left, right, map, stops)((leftTerm, rightTerm) =>
            DeBruijnTerm.Parallel(leftTerm, rightTerm)
          )
        case TermThunk(code, holes, fillings) =>
          Trampoline
            .indexed(fillings)((filling, index) =>
              termOf(filling, childMap(map, index), stops)
            )
            .flatMap(fillingParts =>
              thunkTerm(
                code,
                map,
                holes,
                fillingParts
                  .lazyZip(fillings)
                  .map((part, filling) =>
                    SlotRead(part.term, Some(part.map), Some(filling))
                  ),
                stops
              )
                .map((term, termMap) =>
                  ReadBack(
                    term,
                    termMap,
                    fillingParts.foldLeft(Map.empty[Term, SourceMap])(
                      (found, part) => joinedStops(found, part.stopMaps)
                    )
                  )
                )
            )

    /** The readback of the two parts of an application, a choice or a parallel,
      * joined by `joined`.
      */
    private def pairOf(
        left: Term,
        right: Term,
        map: SourceMap,
        stops: Set[Term]
    )(
        joined: (DeBruijnTermOf[Term], DeBruijnTermOf[Term]) => DeBruijnTermOf[
          Term
        ]
    ): TailRec[ReadBack] =
      for
        leftPart <- tailcall(termOf(left, childMap(map, 0), stops))
        rightPart <- tailcall(termOf(right, childMap(map, 1), stops))
      yield ReadBack(
        joined(leftPart.term, rightPart.term),
        TermMap.Pair(map.locations, leftPart.map, rightPart.map),
        joinedStops(leftPart.stopMaps, rightPart.stopMaps)
      )

    /** The maps of the stops met in two parts, a stop met in both taking the
      * map of both occurrences, the left one's merged with the right one's. The
      * smaller map is folded into the larger, so that joining the parts of a
      * term of n stops costs O(n log n) updates whatever its shape: a list's
      * spine nests to the right, and folding the right part each time costs
      * O(n^2) on a list of n cells.
      */
    private def joinedStops(
        left: Map[Term, SourceMap],
        right: Map[Term, SourceMap]
    ): Map[Term, SourceMap] =
      if left.size >= right.size then
        right.foldLeft(left) { case (found, (stop, map)) =>
          found.updated(stop, found.get(stop).fold(map)(_.merged(map)))
        }
      else
        left.foldLeft(right) { case (found, (stop, map)) =>
          found.updated(stop, found.get(stop).fold(map)(map.merged(_)))
        }

    /** What a code's slot reads back to: its term; its map, none for a hole,
      * whose variable the code's map locates; and the instruction of the
      * filling it reads, none for a hole and for an inner thunk's filling that
      * is no slot.
      */
    private final case class SlotRead(
        term: DeBruijnTermOf[Term],
        map: Option[TermMap],
        filling: Option[Term]
    )

    /** The chain of abstractions of a thunk whose fillings read the terms
      * given, at the depth outside the chain, and its source map: the first
      * abstraction located by the thunk's place, each with its binder's
      * origins, the body by the code's map. A hole's slot reads its variable, a
      * filled slot what the filling reads back to.
      */
    private def thunkTerm(
        code: Code,
        map: SourceMap,
        holes: Vector[Hole],
        fillings: Vector[SlotRead],
        stops: Set[Term]
    ): TailRec[(DeBruijnTermOf[Term], TermMap)] =
      val count = holes.size
      val holeValues = Vector.tabulate(count)(position =>
        SlotRead(DeBruijnTerm.Variable(count - 1 - position), None, None)
      )
      for
        // A read of an instruction's filling is a closed term, which shifting
        // leaves as it is; shifted, it was walked again at every level of a
        // chain of nested thunks, quadratic in the depth: a variable arguments
        // partial function of the key of a marker spelled as a tag nests one
        // level per bit (measured 2026-11-19, shiftedFrom 2,247 of TrapJudgmentsLawTest's 10,221 samples).
        shifted <- Trampoline.traversed(fillings)(filling =>
          if filling.filling.isDefined then done(filling)
          else
            shiftedFrom(filling.term, 0, count).map(shiftedTerm =>
              filling.copy(term = shiftedTerm)
            )
        )
        (body, bodyMap) <- tailcall(
          codeTermOf(
            code,
            map.code.getOrElse(SourceMap.unlocated),
            slotValues(holes, holeValues, shifted),
            stops
          )
        )
      yield (
        (0 until count).foldLeft(body)((wrapped, _) =>
          DeBruijnTerm.Lambda(wrapped)
        ),
        (count - 1 to 0 by -1).foldLeft(bodyMap)((wrapped, position) =>
          TermMap.Abstraction(
            if position == 0 then map.locations else Set.empty,
            map.binders.lift(position).getOrElse(Set.empty),
            wrapped
          )
        )
      )

    /** The term of a code and its map. A slot whose place in the code's map
      * holds the map of its own occurrence, which the located conversion gives
      * each closed subterm a slot stands for, reads its filling with that map,
      * which the located conversion keeps only for a closed subterm written
      * more than once (`chainConverted`); another slot takes the filling's map,
      * the occurrences of the filling merged, and a hole's slot its place's
      * locations. An inner thunk's filling that is a slot hands the slot's read
      * down as it is, so that the inner code's place of it decides, as the
      * code's own would.
      */
    private def codeTermOf(
        code: Code,
        map: SourceMap,
        slots: Vector[SlotRead],
        stops: Set[Term]
    ): TailRec[(DeBruijnTermOf[Term], TermMap)] = code match
      case Code.Slot(index) =>
        val SlotRead(term, filled, filling) = slotRead(slots, index)
        filling match
          case Some(instruction) if !map.bare =>
            tailcall(termOf(instruction, map, stops)).map(read =>
              (term, read.map)
            )
          case _ => done((term, filled.getOrElse(TermMap.Leaf(map.locations))))
      case Code.Apply(function, argument) =>
        codePairOf(function, argument, map, slots, stops)(
          DeBruijnTerm.Apply(_, _)
        )
      case Code.Choice(left, right) =>
        codePairOf(left, right, map, slots, stops)(DeBruijnTerm.Choice(_, _))
      case Code.Parallel(left, right) =>
        codePairOf(left, right, map, slots, stops)(DeBruijnTerm.Parallel(_, _))
      case Code.Thunk(inner, holes, fillings) =>
        Trampoline
          .indexed(fillings)((filling, index) =>
            filling match
              case Code.Slot(slot) => done(slotRead(slots, slot))
              case _               =>
                codeTermOf(filling, childMap(map, index), slots, stops)
                  .map((term, termMap) => SlotRead(term, Some(termMap), None))
          )
          .flatMap(fillingReads =>
            thunkTerm(inner, map, holes, fillingReads, stops)
          )

    private def slotRead(slots: Vector[SlotRead], index: Int): SlotRead =
      if index >= 0 && index < slots.size then slots(index)
      else
        throw LambdaError(LambdaErrorReason.SlotOutOfRange(index, slots.size))

    /** `pairOf` for the parts of a code. */
    private def codePairOf(
        left: Code,
        right: Code,
        map: SourceMap,
        slots: Vector[SlotRead],
        stops: Set[Term]
    )(
        joined: (DeBruijnTermOf[Term], DeBruijnTermOf[Term]) => DeBruijnTermOf[
          Term
        ]
    ): TailRec[(DeBruijnTermOf[Term], TermMap)] =
      for
        (leftTerm, leftMap) <- tailcall(
          codeTermOf(left, childMap(map, 0), slots, stops)
        )
        (rightTerm, rightMap) <- tailcall(
          codeTermOf(right, childMap(map, 1), slots, stops)
        )
      yield (
        joined(leftTerm, rightTerm),
        TermMap.Pair(map.locations, leftMap, rightMap)
      )

    // ---- relocation: the map of another spelling of a term ----

    /** A part of a readback's map as relocation reads it: a node of a map
      * already read (`Read`), an instruction with the map of its occurrence not
      * yet read back (`Pending`), or a node read (`Node`). Relocation reads a
      * pending instruction one layer at a time, and only where the target
      * spells it otherwise: where the target has the same instruction, the
      * place takes the occurrence's map as it is. So relocating a respelling
      * costs the parts the two spellings do not share, not the readback of the
      * whole term, whose tree repeats every shared part (measured 2026-11-19 on
      * `contest-entries-wren`'s calls_1000_hot direct point in
      * `EntryTracesTest`: the readback took 3,187 of the test's 10,646
      * samples).
      */
    enum ReadMap:
      case Read(map: TermMap)
      case Pending(instruction: Term, map: SourceMap)
      case Node(node: ReadNode)

    /** The head of a `ReadMap`, as `TermMap`'s nodes, its parts `ReadMap`s. */
    enum ReadNode:
      case Unknown
      case Abstraction(
          locations: Set[Location],
          origins: Set[BinderOrigin],
          body: ReadMap
      )
      case Pair(locations: Set[Location], left: ReadMap, right: ReadMap)
      case Leaf(locations: Set[Location])

    /** The head node of the map, a pending instruction read back one layer
      * (`layerRead`) as often as its head is pending.
      */
    @tailrec
    private def node(read: ReadMap): ReadNode = read match
      case ReadMap.Node(head) => head
      case ReadMap.Read(map)  =>
        map match
          case TermMap.Unknown                               => ReadNode.Unknown
          case TermMap.Abstraction(locations, origins, body) =>
            ReadNode.Abstraction(locations, origins, ReadMap.Read(body))
          case TermMap.Pair(locations, left, right) =>
            ReadNode.Pair(locations, ReadMap.Read(left), ReadMap.Read(right))
          case TermMap.Leaf(locations) => ReadNode.Leaf(locations)
      case ReadMap.Pending(instruction, map) =>
        node(layerRead(instruction, map))

    /** The locations of the head node of the map. */
    private def nodeLocations(read: ReadMap): Set[Location] = node(read) match
      case ReadNode.Unknown                      => Set.empty
      case ReadNode.Abstraction(locations, _, _) => locations
      case ReadNode.Pair(locations, _, _)        => locations
      case ReadNode.Leaf(locations)              => locations

    /** The map of the instruction's readback (`termOf`) one layer deep: its
      * parts, and a thunk's fillings, pending.
      */
    private def layerRead(instruction: Term, map: SourceMap): ReadMap =
      instruction match
        case opaque if opaque.representation.opaque =>
          ReadMap.Node(if map.locations.isEmpty then ReadNode.Unknown
          else ReadNode.Leaf(map.locations))
        case TermApply(function, argument) =>
          pendingPair(function, argument, map)
        case TermChoice(left, right)          => pendingPair(left, right, map)
        case TermParallel(left, right)        => pendingPair(left, right, map)
        case TermThunk(code, holes, fillings) =>
          thunkRead(
            code,
            map,
            holes,
            fillings.zipWithIndex.map((filling, index) =>
              Some(ReadMap.Pending(filling, childMap(map, index)))
            )
          ).result

    private def pendingPair(left: Term, right: Term, map: SourceMap): ReadMap =
      ReadMap.Node(
        ReadNode.Pair(
          map.locations,
          ReadMap.Pending(left, childMap(map, 0)),
          ReadMap.Pending(right, childMap(map, 1))
        )
      )

    /** `thunkTerm`'s map, the fillings' maps given, none for a filling that
      * reads a hole of the code around, whose place locates it.
      */
    private def thunkRead(
        code: Code,
        map: SourceMap,
        holes: Vector[Hole],
        fillings: Vector[Option[ReadMap]]
    ): TailRec[ReadMap] =
      val count = holes.size
      tailcall(
        codeRead(
          code,
          map.code.getOrElse(SourceMap.unlocated),
          slotValues(holes, Vector.fill(count)(None), fillings)
        )
      )
        .map(body =>
          (count - 1 to 0 by -1).foldLeft(body)((wrapped, position) =>
            ReadMap.Node(
              ReadNode.Abstraction(
                if position == 0 then map.locations else Set.empty,
                map.binders.lift(position).getOrElse(Set.empty),
                wrapped
              )
            )
          )
        )

    /** `codeTermOf`'s map, each slot's map given, none for a hole; a slot whose
      * place holds the map of its own occurrence reads its filling with that
      * map, and an inner thunk's filling that is a slot hands the slot's map
      * down as it is, as `codeTermOf` does.
      */
    private def codeRead(
        code: Code,
        map: SourceMap,
        slots: Vector[Option[ReadMap]]
    ): TailRec[ReadMap] = code match
      case Code.Slot(index) =>
        done(slotMap(slots, index) match
          case Some(ReadMap.Pending(filling, _)) if !map.bare =>
            ReadMap.Pending(filling, map)
          case Some(read) => read
          case None       => ReadMap.Node(ReadNode.Leaf(map.locations)))
      case Code.Apply(function, argument) =>
        codePairRead(function, argument, map, slots)
      case Code.Choice(left, right)   => codePairRead(left, right, map, slots)
      case Code.Parallel(left, right) => codePairRead(left, right, map, slots)
      case Code.Thunk(inner, holes, fillings) =>
        Trampoline
          .indexed(fillings)((filling, index) =>
            filling match
              case Code.Slot(slot) => done(slotMap(slots, slot))
              case _               =>
                codeRead(filling, childMap(map, index), slots).map(Some(_))
          )
          .flatMap(fillingReads => thunkRead(inner, map, holes, fillingReads))

    private def slotMap(
        slots: Vector[Option[ReadMap]],
        index: Int
    ): Option[ReadMap] =
      if index >= 0 && index < slots.size then slots(index)
      else
        throw LambdaError(LambdaErrorReason.SlotOutOfRange(index, slots.size))

    private def codePairRead(
        left: Code,
        right: Code,
        map: SourceMap,
        slots: Vector[Option[ReadMap]]
    ): TailRec[ReadMap] =
      for
        leftRead <- tailcall(codeRead(left, childMap(map, 0), slots))
        rightRead <- tailcall(codeRead(right, childMap(map, 1), slots))
      yield ReadMap.Node(ReadNode.Pair(map.locations, leftRead, rightRead))

    /** The map of an instruction from the source map of its readback: each
      * place takes the locations of its node, a thunk's binders the origins of
      * its chain's abstractions, a filling the maps of the nodes where its code
      * reads it, merged; a place whose instruction is the pending one there
      * takes the pending occurrence's map. Throws `IllegalArgumentException`
      * where the instruction's readback has another shape than the map.
      */
    def instructionMapOf(instruction: Term, read: ReadMap): TailRec[SourceMap] =
      read match
        case ReadMap.Pending(source, map)
            if Configured.same(source, instruction) =>
          done(map)
        case _ =>
          instruction match
            case opaque if opaque.representation.opaque =>
              done(SourceMap.leaf(nodeLocations(read)))
            case TermApply(function, argument) =>
              instructionPairMap(function, argument, read)
            case TermChoice(left, right) =>
              instructionPairMap(left, right, read)
            case TermParallel(left, right) =>
              instructionPairMap(left, right, read)
            case TermThunk(code, holes, fillings) =>
              val (locations, origins, body) = chainOpened(read, holes.size)
              val kinds = slotValues(
                holes,
                Vector.fill(holes.size)(None),
                fillings.indices.map(Some(_)).toVector
              )
              for
                (codeMap, reads) <- tailcall(codeMapOf(code, body, kinds))
                fillingMaps <- Trampoline.indexed(fillings)((filling, index) =>
                  Trampoline
                    .traversed(readMaps(reads, index))(read =>
                      instructionMapOf(filling, read)
                    )
                    .map(
                      _.reduceOption(_.merged(_)).getOrElse(SourceMap.unlocated)
                    )
                )
              yield SourceMap(locations, Some(codeMap), fillingMaps, origins)

    private def instructionPairMap(
        left: Term,
        right: Term,
        read: ReadMap
    ): TailRec[SourceMap] =
      val (locations, leftMap, rightMap) = pairOpened(read)
      for
        leftPlace <- tailcall(instructionMapOf(left, leftMap))
        rightPlace <- tailcall(instructionMapOf(right, rightMap))
      yield SourceMap(
        locations,
        None,
        Vector(leftPlace, rightPlace),
        Vector.empty
      )

    /** The map of a code from the source map of its readback, and the nodes
      * where it reads each filling of the thunk around it, by the filling's
      * position (`kinds`: each slot's filling, none for a hole).
      */
    private def codeMapOf(
        code: Code,
        read: ReadMap,
        kinds: Vector[Option[Int]]
    ): TailRec[(SourceMap, Vector[(Int, ReadMap)])] =
      code match
        case Code.Slot(index) =>
          done(
            (
              SourceMap.leaf(nodeLocations(read)),
              kinds.lift(index).flatten.toVector.map((_, read))
            )
          )
        case Code.Apply(function, argument) =>
          codePairMap(function, argument, read, kinds)
        case Code.Choice(left, right)   => codePairMap(left, right, read, kinds)
        case Code.Parallel(left, right) => codePairMap(left, right, read, kinds)
        case Code.Thunk(inner, holes, fillings) =>
          val (locations, origins, body) = chainOpened(read, holes.size)
          val innerKinds = slotValues(
            holes,
            Vector.fill(holes.size)(None),
            fillings.indices.map(Some(_)).toVector
          )
          for
            (innerMap, innerReads) <- tailcall(
              codeMapOf(inner, body, innerKinds)
            )
            fillingParts <- Trampoline.indexed(fillings)((filling, index) =>
              Trampoline
                .traversed(readMaps(innerReads, index))(read =>
                  codeMapOf(filling, read, kinds)
                )
                .map(parts =>
                  (
                    parts
                      .map(_._1)
                      .reduceOption(_.merged(_))
                      .getOrElse(SourceMap.unlocated),
                    parts.flatMap(_._2)
                  )
                )
            )
          yield (
            SourceMap(
              locations,
              Some(innerMap),
              fillingParts.map(_._1),
              origins
            ),
            fillingParts.flatMap(_._2)
          )

    private def codePairMap(
        left: Code,
        right: Code,
        read: ReadMap,
        kinds: Vector[Option[Int]]
    ): TailRec[(SourceMap, Vector[(Int, ReadMap)])] =
      val (locations, leftMap, rightMap) = pairOpened(read)
      for
        (leftPlace, leftReads) <- tailcall(codeMapOf(left, leftMap, kinds))
        (rightPlace, rightReads) <- tailcall(codeMapOf(right, rightMap, kinds))
      yield (
        SourceMap(locations, None, Vector(leftPlace, rightPlace), Vector.empty),
        leftReads ++ rightReads
      )

    /** The maps of the nodes where a filling is read, each node once: a filling
      * read twice is read at one map, made once by the readback.
      */
    private def readMaps(
        reads: Vector[(Int, ReadMap)],
        filling: Int
    ): Vector[ReadMap] =
      reads.foldLeft(Vector.empty[ReadMap]) { case (kept, (index, read)) =>
        if index == filling && !kept.exists(sameRead(_, read)) then kept :+ read
        else kept
      }

    /** The two maps are one node of the readback: one object, or the wrappers
      * of one node of a map already read.
      */
    private def sameRead(first: ReadMap, second: ReadMap): Boolean =
      (first, second) match
        case (ReadMap.Read(left), ReadMap.Read(right)) => left eq right
        case _                                         => first eq second

    /** The locations of a chain of `count` abstractions, its binders' origins
      * (none when no binder has one) and the map of its body.
      */
    private def chainOpened(
        read: ReadMap,
        count: Int
    ): (Set[Location], Vector[Set[BinderOrigin]], ReadMap) =
      @tailrec
      def opened(
          current: ReadMap,
          origins: Vector[Set[BinderOrigin]]
      ): (Vector[Set[BinderOrigin]], ReadMap) =
        if origins.size == count then (origins, current)
        else
          node(current) match
            case ReadNode.Abstraction(_, binder, body) =>
              opened(body, origins :+ binder)
            case ReadNode.Unknown =>
              opened(ReadMap.Node(ReadNode.Unknown), origins :+ Set.empty)
            case other =>
              throw IllegalArgumentException(
                s"a chain of $count abstractions read back as $other"
              )
      val (origins, body) = opened(read, Vector.empty)
      (
        nodeLocations(read),
        if origins.forall(_.isEmpty) then Vector.empty else origins,
        body
      )

    /** The locations of a node of two parts and the maps of the parts. */
    private def pairOpened(read: ReadMap): (Set[Location], ReadMap, ReadMap) =
      node(read) match
        case ReadNode.Pair(locations, left, right) => (locations, left, right)
        case ReadNode.Unknown                      =>
          (
            Set.empty,
            ReadMap.Node(ReadNode.Unknown),
            ReadMap.Node(ReadNode.Unknown)
          )
        case other =>
          throw IllegalArgumentException(
            s"a node of two parts read back as $other"
          )

    /** The term with every variable free at `depth` made `count` deeper. */
    private[frontend] def shiftedFrom(
        term: DeBruijnTermOf[Term],
        depth: Int,
        count: Int
    ): TailRec[DeBruijnTermOf[Term]] = term match
      case DeBruijnTerm.Variable(index) =>
        done(
          DeBruijnTerm.Variable(if index >= depth then index + count else index)
        )
      case DeBruijnTerm.Constant(_) | DeBruijnTerm.Free(_) => done(term)
      case DeBruijnTerm.Apply(function, argument)          =>
        for
          functionShifted <- tailcall(shiftedFrom(function, depth, count))
          argumentShifted <- tailcall(shiftedFrom(argument, depth, count))
        yield DeBruijnTerm.Apply(functionShifted, argumentShifted)
      case DeBruijnTerm.Lambda(body) =>
        tailcall(shiftedFrom(body, depth + 1, count))
          .map(DeBruijnTerm.Lambda(_))
      case DeBruijnTerm.Choice(left, right) =>
        for
          leftShifted <- tailcall(shiftedFrom(left, depth, count))
          rightShifted <- tailcall(shiftedFrom(right, depth, count))
        yield DeBruijnTerm.Choice(leftShifted, rightShifted)
      case DeBruijnTerm.Parallel(left, right) =>
        for
          leftShifted <- tailcall(shiftedFrom(left, depth, count))
          rightShifted <- tailcall(shiftedFrom(right, depth, count))
        yield DeBruijnTerm.Parallel(leftShifted, rightShifted)

  /** The term with the variable bound at `depth` (counted at the term's own
    * depth) replaced by the closed value, and the variables bound outside it
    * made one shallower: the body of an abstraction instantiated by its
    * argument, a step of β on the readback.
    */
  private[frontend] def instantiatedFrom[K](
      term: DeBruijnTermOf[K],
      depth: Int,
      value: DeBruijnTermOf[K]
  ): TailRec[DeBruijnTermOf[K]] = term match
    case DeBruijnTerm.Variable(index) =>
      done(if index == depth then value
      else if index > depth then DeBruijnTerm.Variable[K](index - 1)
      else term)
    case DeBruijnTerm.Constant(_) | DeBruijnTerm.Free(_) => done(term)
    case DeBruijnTerm.Apply(function, argument)          =>
      for
        functionInstantiated <- tailcall(
          instantiatedFrom(function, depth, value)
        )
        argumentInstantiated <- tailcall(
          instantiatedFrom(argument, depth, value)
        )
      yield DeBruijnTerm.Apply(functionInstantiated, argumentInstantiated)
    case DeBruijnTerm.Lambda(body) =>
      tailcall(instantiatedFrom(body, depth + 1, value))
        .map(DeBruijnTerm.Lambda(_))
    case DeBruijnTerm.Choice(left, right) =>
      for
        leftInstantiated <- tailcall(instantiatedFrom(left, depth, value))
        rightInstantiated <- tailcall(instantiatedFrom(right, depth, value))
      yield DeBruijnTerm.Choice(leftInstantiated, rightInstantiated)
    case DeBruijnTerm.Parallel(left, right) =>
      for
        leftInstantiated <- tailcall(instantiatedFrom(left, depth, value))
        rightInstantiated <- tailcall(instantiatedFrom(right, depth, value))
      yield DeBruijnTerm.Parallel(leftInstantiated, rightInstantiated)
