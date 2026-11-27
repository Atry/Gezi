package com.yang_bo.gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts

/** Generated closed instructions of every construct, some holding a closed part
  * several times (towers of diamonds, whose tree is exponential in their
  * height), the bits of literals as arguments, the variable arguments partial
  * function of a literal and top beside it in one body, and some whose own text
  * begins with a binding of the printer's shape `(λt. t V) λm. BODY`:
  * instructions the printer binds parts of (`ReadableText.printedNameless`),
  * the inputs of the laws of the contraction of its bindings
  * (`ExchangeTextLawTest`, `LocatedBindingsContractionLawTest`).
  */
object SharingInstructions:

  /** A literal: an integer of any size or a text with characters the diagnostic
    * notation escapes.
    */
  private val literal: Gen[Literal] = Gen.choice1(
    Gen
      .long(Range.linearFrom(0L, Long.MinValue, Long.MaxValue))
      .map(value => Literal.of(Literal.integerElement(BigInt(value)))),
    Gen
      .string(Gen.element1('a', 'z', '"', '\n', '\t', 'λ'), Range.linear(0, 5))
      .map(Literal.text)
  )

  private val closedTerms: Gen[DeBruijnTerm] =
    HoasGenerators.closedTerm.map(_.deBruijnTerm(Map.empty))

  /** `λf. f t t`, `height` times around the closed term. */
  private def tower(term: DeBruijnTerm, height: Int): DeBruijnTerm =
    (1 to height).foldLeft(term)((below, _) =>
      DeBruijnTerm.Lambda(
        DeBruijnTerm.Apply(
          DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), below),
          below
        )
      )
    )

  /** `λx. x ARGUMENT top top t (λBINDER. x)`: the bits of a literal as
    * arguments, top twice outside a literal, so that the printer binds it, and
    * top again inside the partial function of a literal, in one body.
    */
  private def literalUse(
      term: DeBruijnTerm,
      argument: Literal,
      binder: Literal
  ): DeBruijnTerm =
    DeBruijnTerm.Lambda(
      (Literals.arguments(argument) ++ Vector(
        Literals.top,
        Literals.top,
        term,
        Literals.partialFunction(binder, DeBruijnTerm.Variable(0))
      ))
        .foldLeft(DeBruijnTerm.Variable(0))(DeBruijnTerm.Apply(_, _))
    )

  /** `(λt. t V) λm. m W m`: a program whose own text begins with a binding of
    * the printer's shape.
    */
  private def imported(value: DeBruijnTerm, body: DeBruijnTerm): DeBruijnTerm =
    DeBruijnTerm.Apply(
      DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), value)),
      DeBruijnTerm.Lambda(
        DeBruijnTerm.Apply(
          DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), body),
          DeBruijnTerm.Variable(0)
        )
      )
    )

  /** A shape a closed term is put in. */
  private enum Shape:
    case Plain, Tower, Literals, TowerWithLiterals

  private val shaped: Gen[DeBruijnTerm] =
    for
      base <- closedTerms
      shape <- Gen.elementUnsafe(Shape.values.toList)
      height <- Gen.int(Range.linear(1, 6))
      argument <- literal
      binder <- literal
    yield shape match
      case Shape.Plain             => base
      case Shape.Tower             => tower(base, height)
      case Shape.Literals          => literalUse(base, argument, binder)
      case Shape.TowerWithLiterals =>
        literalUse(tower(base, height), argument, binder)

  /** Instructions of the shapes, a third of them inside a program's own
    * binding.
    */
  val instructions: Gen[Configured[NoFacts.type]] =
    for
      value <- shaped
      body <- shaped
      inside <- Gen.frequency1(
        2 -> Gen.constant(false),
        1 -> Gen.constant(true)
      )
    yield Defunctionalization.thunkInstruction[NoFacts.type](if inside then
      imported(value, body)
    else value)(using NoFacts)
