package com.yang_bo.gezi.contest.corpora.reductions

import com.yang_bo.gezi.contest.corpora.common.ProblemData
import com.yang_bo.gezi.contest.corpora.common.ProblemField

import com.yang_bo.gezi.contest.corpora.reductions.Encodings.*
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.*

/** A natural expression of a proposition, the constructors of
  * problems/schema/natural_expression in order: self_number (the n the search
  * is at), a literal, `double(e)`, `plus(a, b)` and `successor(e)`. `written`
  * is the expression as Prolog's `~w` wrote the term it was ported from:
  * self_number as `n`, a literal as its digits; the data do not write it.
  */
enum NaturalExpression:
  case SelfNumber
  case Literal(value: Int)
  case Double(expression: NaturalExpression)
  case Plus(left: NaturalExpression, right: NaturalExpression)
  case Successor(expression: NaturalExpression)

  def written: String = this match
    case SelfNumber          => "n"
    case Literal(value)      => value.toString
    case Double(expression)  => s"double(${expression.written})"
    case Plus(left, right)   => s"plus(${left.written},${right.written})"
    case Successor(argument) => s"successor(${argument.written})"

/** A periodic slot of the counterexample search's mixin, the constructors of
  * problems/schema/periodic_slot in order. `written` is the slot's name in the
  * mixin library, which the host gives by the constructor's position; the data
  * do not write it.
  */
enum PeriodicSlot(val written: String):
  case ResidueZero extends PeriodicSlot("residue_zero")
  case ResidueOne extends PeriodicSlot("residue_one")
  case ResidueTwo extends PeriodicSlot("residue_two")
  case Even extends PeriodicSlot("even")

/** A residue modulo 3, the constructors of problems/schema/residue in order, so
  * that a residue's ordinal is its value. `slot` is the periodic slot that
  * holds at the numbers of the residue.
  */
enum Residue(val slot: PeriodicSlot):
  case ResidueZero extends Residue(PeriodicSlot.ResidueZero)
  case ResidueOne extends Residue(PeriodicSlot.ResidueOne)
  case ResidueTwo extends Residue(PeriodicSlot.ResidueTwo)

/** A parity, the constructors of problems/schema/parity in order. `written` is
  * the parity as the host prints it; the data do not write it.
  */
enum Parity(val written: String):
  case Even extends Parity("even")
  case Odd extends Parity("odd")

/** A proposition checked at self.n, the constructors of
  * problems/schema/proposition in order: `equal(a, b)`, `periodic(r, p)`,
  * `not_periodic(s)`, `both(p, q)`, or `stepped(Step, Check)`, whose search
  * steps n by Step. `written` is the proposition as Prolog's `~w` wrote the
  * term it was ported from; the data do not write it.
  */
enum Proposition:
  case Equal(left: NaturalExpression, right: NaturalExpression)
  case Periodic(residue: Residue, parity: Parity)
  case NotPeriodic(slot: PeriodicSlot)
  case Both(left: Proposition, right: Proposition)
  case Stepped(step: Int, check: Proposition)

  def written: String = this match
    case Equal(left, right)        => s"equal(${left.written},${right.written})"
    case Periodic(residue, parity) =>
      s"periodic(${residue.slot.written},${parity.written})"
    case NotPeriodic(slot)    => s"not_periodic(${slot.written})"
    case Both(left, right)    => s"both(${left.written},${right.written})"
    case Stepped(step, check) => s"stepped($step,${check.written})"

/** Theorems as counterexample searches in the mixin encoding, the port of
  * `problems/reduction_mixin_theorems`: `{counterexample_search, n : 0}.found`
  * read at church.
  */
object ReductionMixinTheorems:

  private val family = "reduction_mixin_theorems"

  /** The proposition a datum writes, a constructor of
    * problems/schema/proposition read by its position
    * (`ProblemData.alternative`), in the order of `Proposition`'s cases;
    * stepped's step is a Scott integer (`ProblemData.small`).
    */
  def propositionOf(term: ProblemField): Proposition =
    ProblemData.alternative(term, ProblemData.caseCount[Proposition]) match
      case (0, Vector(left, right)) =>
        Proposition.Equal(expressionOf(left), expressionOf(right))
      case (1, Vector(residue, parity)) =>
        Proposition.Periodic(residueOf(residue), parityOf(parity))
      case (2, Vector(slot)) => Proposition.NotPeriodic(periodicSlotOf(slot))
      case (3, Vector(left, right)) =>
        Proposition.Both(propositionOf(left), propositionOf(right))
      case (4, Vector(step, check)) =>
        Proposition.Stepped(ProblemData.small(step), propositionOf(check))
      case (position, fields) =>
        throw IllegalArgumentException(
          s"a proposition at position $position has ${fields.size} fields"
        )

  /** The natural expression a datum writes, a constructor of
    * problems/schema/natural_expression read by its position
    * (`ProblemData.alternative`), in the order of `NaturalExpression`'s cases;
    * a literal's value is a Scott integer (`ProblemData.small`).
    */
  private def expressionOf(term: ProblemField): NaturalExpression =
    ProblemData.alternative(
      term,
      ProblemData.caseCount[NaturalExpression]
    ) match
      case (0, Vector())      => NaturalExpression.SelfNumber
      case (1, Vector(value)) =>
        NaturalExpression.Literal(ProblemData.small(value))
      case (2, Vector(expression)) =>
        NaturalExpression.Double(expressionOf(expression))
      case (3, Vector(left, right)) =>
        NaturalExpression.Plus(expressionOf(left), expressionOf(right))
      case (4, Vector(expression)) =>
        NaturalExpression.Successor(expressionOf(expression))
      case (position, fields) =>
        throw IllegalArgumentException(
          s"a natural expression at position $position has ${fields.size} fields"
        )

  /** The residue a datum writes, a constructor of problems/schema/residue read
    * by its position, in the order of `Residue`'s cases.
    */
  private def residueOf(term: ProblemField): Residue =
    ProblemData.alternative(term, Residue.values.size) match
      case (position, Vector()) => Residue.fromOrdinal(position)
      case (_, fields)          =>
        throw IllegalArgumentException(s"a residue has ${fields.size} fields")

  /** The parity a datum writes, a constructor of problems/schema/parity read by
    * its position, in the order of `Parity`'s cases.
    */
  private def parityOf(term: ProblemField): Parity =
    ProblemData.alternative(term, Parity.values.size) match
      case (position, Vector()) => Parity.fromOrdinal(position)
      case (_, fields)          =>
        throw IllegalArgumentException(s"a parity has ${fields.size} fields")

  /** The periodic slot a datum writes, a constructor of
    * problems/schema/periodic_slot read by its position, in the order of
    * `PeriodicSlot`'s cases.
    */
  private def periodicSlotOf(term: ProblemField): PeriodicSlot =
    ProblemData.alternative(term, PeriodicSlot.values.size) match
      case (position, Vector()) => PeriodicSlot.fromOrdinal(position)
      case (_, fields)          =>
        throw IllegalArgumentException(
          s"a periodic slot has ${fields.size} fields"
        )

  /** The step budget of a search: the number of checks it may make after the
    * one at n = 0, so it checks n = 0, Step, ..., 101 Step. A problem's
    * counterexample is at most 100 at Step 1 (`counterexample`; a stepped
    * proposition has none and is posed only as a trap), so the search reaches
    * it.
    */
  val searchBudget: Int = 101

  /** `{counterexample_search, n : 0}.found budget` of the proposition, read at
    * church (`proposition_surface/2`), the budget `searchBudget` as a Scott
    * unary numeral.
    */
  def propositionSurface(
      mixins: MixinLibrary,
      proposition: Proposition
  ): ProblemTerm =
    val (step, check) = proposition match
      case Proposition.Stepped(stepBy, stepped) =>
        require(stepBy > 0, s"a search steps by a positive integer: $stepBy")
        (stepBy, stepped)
      case other => (1, other)
    mixins.withMixinLibrary(
      Vector("natural"),
      Vector("theorem_module", "counterexample_search", "periodic")
    )(names =>
      val module = theoremModule(mixins, names, step, check)
      val search =
        mixins.readSlot("theorem_module", "counterexample_search", module)
      mixins.readSlot(
        "boolean",
        "church",
        searchFound(mixins, search, mixins.naturalInstance(names, 0))(
          unary(searchBudget)
        )
      )
    )

  /** The module of the classes counterexample_search and periodic
    * (`theorem_module/4`).
    */
  private def theoremModule(
      mixins: MixinLibrary,
      names: MixinNames,
      step: Int,
      check: Proposition
  ): ProblemTerm =
    members(
      Vector(
        mixins.selfMixin("theorem_module", "counterexample_search")(
          searchModule =>
            members(
              Vector(searchMixin(mixins, names, step, check, searchModule))
            )
        ),
        mixins.selfMixin("theorem_module", "periodic")(periodicModule =>
          periodicMixins(mixins, names, periodicModule)
        )
      )
    )

  /** `{counterexample_search, n : N}.found` (`search_found/3`). */
  private def searchFound(
      mixins: MixinLibrary,
      search: ProblemTerm,
      number: ProblemTerm
  ): ProblemTerm =
    mixins.readSlot(
      "counterexample_search",
      "found",
      members(
        Vector(
          search,
          mixins.valueMixin("counterexample_search", "n" -> number)
        )
      )
    )

  /** found is `\budget. check.church true (budget top (\p.
    * {counterexample_search, n : self.n + Step}.found p))` (`search_mixin/5`):
    * a Scott unary budget that each further check takes the predecessor of, top
    * once it is spent. Without the budget the search of a true theorem runs
    * over every n and reads ⊥ in DdLP96's reading (a choice is a meet, the
    * recursion a least fixed point), so every closed βη normal form would be an
    * answer of the trap that says neither Boolean is one (FIXME: the claim
    * families' answers rest on this budget,
    * https://github.com/Atry/private-overlay/issues/1989). With it the
    * recursion terminates and the selection theorem applies: a false theorem's
    * search reaches its counterexample within the budget and reads true, a true
    * theorem's spends the budget and has no answer.
    */
  private def searchMixin(
      mixins: MixinLibrary,
      names: MixinNames,
      step: Int,
      proposition: Proposition,
      module: ProblemTerm
  ): ProblemTerm =
    mixins.selfMixin("counterexample_search", "found")(self =>
      val checked = check(mixins, names, module, self, proposition)
      val trueValue = mixins.libraryClass(names, "natural", "true")
      val search =
        mixins.readSlot("theorem_module", "counterexample_search", module)
      val stepped = (1 to step).foldLeft(
        mixins.readSlot("counterexample_search", "n", self)
      )((inner, _) => mixins.successorClass(names, inner))
      λ(budget =>
        mixins.slotApplied(
          "boolean",
          "church",
          checked,
          trueValue,
          budget(Term.top)(
            λ(predecessor => searchFound(mixins, search, stepped)(predecessor))
          )
        )
      )
    )

  /** The Boolean object of the proposition at self.n (`check/5`). */
  private def check(
      mixins: MixinLibrary,
      names: MixinNames,
      module: ProblemTerm,
      self: ProblemTerm,
      proposition: Proposition
  ): ProblemTerm =
    proposition match
      case Proposition.Both(left, right) =>
        mixins.slotApplied(
          "boolean",
          "conjunction",
          check(mixins, names, module, self, left),
          check(mixins, names, module, self, right)
        )
      case Proposition.NotPeriodic(slot) =>
        mixins.readSlot(
          "boolean",
          "not",
          periodicRead(mixins, module, self, slot)
        )
      case Proposition.Equal(left, right) =>
        mixins.slotApplied(
          "natural",
          "equality",
          naturalTerm(mixins, names, self, left),
          naturalTerm(mixins, names, self, right)
        )
      case Proposition.Periodic(residue, parity) =>
        val residueHolds = periodicRead(mixins, module, self, residue.slot)
        val even = periodicRead(mixins, module, self, PeriodicSlot.Even)
        val parityHolds = parity match
          case Parity.Even => even
          case Parity.Odd  => mixins.readSlot("boolean", "not", even)
        mixins.slotApplied("boolean", "conjunction", residueHolds, parityHolds)
      case Proposition.Stepped(_, _) =>
        throw IllegalArgumentException(
          s"a stepped proposition is checked only at the top: $proposition"
        )

  /** `{periodic, n : self.n}.Slot`, the class read from the module. */
  private def periodicRead(
      mixins: MixinLibrary,
      module: ProblemTerm,
      self: ProblemTerm,
      slot: PeriodicSlot
  ): ProblemTerm =
    val periodic = mixins.readSlot("theorem_module", "periodic", module)
    val number = mixins.readSlot("counterexample_search", "n", self)
    mixins.readSlot(
      "periodic",
      slot.written,
      members(Vector(periodic, mixins.valueMixin("periodic", "n" -> number)))
    )

  /** The object of the expression at self.n, each n read anew
    * (`natural_term/4`).
    */
  private def naturalTerm(
      mixins: MixinLibrary,
      names: MixinNames,
      self: ProblemTerm,
      expression: NaturalExpression
  ): ProblemTerm =
    expression match
      case NaturalExpression.SelfNumber =>
        mixins.readSlot("counterexample_search", "n", self)
      case NaturalExpression.Successor(inner) =>
        mixins.successorClass(names, naturalTerm(mixins, names, self, inner))
      case NaturalExpression.Literal(value) =>
        mixins.naturalInstance(names, value)
      case NaturalExpression.Double(inner) =>
        naturalTerm(mixins, names, self, NaturalExpression.Plus(inner, inner))
      case NaturalExpression.Plus(left, right) =>
        mixins.slotApplied(
          "natural",
          "plus",
          naturalTerm(mixins, names, self, left),
          naturalTerm(mixins, names, self, right)
        )

  /** even and the three residues by recursion on self.n's accept
    * (`periodic_mixins/3`).
    */
  private def periodicMixins(
      mixins: MixinLibrary,
      names: MixinNames,
      module: ProblemTerm
  ): ProblemTerm =
    members(
      Vector(
        (PeriodicSlot.Even, "true", PeriodicSlot.Even, true),
        (PeriodicSlot.ResidueZero, "true", PeriodicSlot.ResidueTwo, false),
        (PeriodicSlot.ResidueOne, "false", PeriodicSlot.ResidueZero, false),
        (PeriodicSlot.ResidueTwo, "false", PeriodicSlot.ResidueOne, false)
      ).map((slot, atZero, fromPredecessor, negated) =>
        mixins.selfMixin("periodic", slot.written)(self =>
          val number = mixins.readSlot("periodic", "n", self)
          val zeroValue = mixins.libraryClass(names, "natural", atZero)
          val periodic = mixins.readSlot("theorem_module", "periodic", module)
          mixins.slotApplied(
            "natural",
            "accept",
            number,
            zeroValue,
            λ(predecessor =>
              val objectTerm = members(
                Vector(
                  periodic,
                  mixins.valueMixin("periodic", "n" -> predecessor)
                )
              )
              val value =
                mixins.readSlot("periodic", fromPredecessor.written, objectTerm)
              if negated then mixins.readSlot("boolean", "not", value)
              else value
            )
          )
        )
      )
    )

  /** The least n at most 100 at which the check holds, by integer arithmetic
    * (`counterexample/2`).
    */
  def counterexample(proposition: Proposition): Option[Int] =
    (0 to 100).find(holds(proposition, _))

  private def holds(proposition: Proposition, number: Int): Boolean =
    proposition match
      case Proposition.Equal(left, right) =>
        value(left, number).zip(value(right, number)).exists(_ == _)
      case Proposition.Periodic(residue, parity) =>
        number % 3 == residue.ordinal && (parity match
          case Parity.Even => number % 2 == 0
          case Parity.Odd  => number % 2 == 1)
      case _ => false

  /** The expression's value at n; nothing for a successor, for which the
    * Prolog's `value/3` has no clause, so that the check does not hold.
    */
  private def value(expression: NaturalExpression, number: Int): Option[Int] =
    expression match
      case NaturalExpression.SelfNumber       => Some(number)
      case NaturalExpression.Literal(literal) => Some(literal)
      case NaturalExpression.Double(inner)    => value(inner, number).map(2 * _)
      case NaturalExpression.Plus(left, right) =>
        value(left, number).zip(value(right, number)).map(_ + _)
      case NaturalExpression.Successor(_) => None

  /** The problems (`theorem/2`), each with a counterexample, expecting true. */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("theorem").flatMap {
      case Vector(point, proposition) =>
        val parsed = propositionOf(proposition)
        counterexample(parsed).map(_ =>
          ReductionProblem(
            ProblemData.text(point),
            propositionSurface(group.mixins, parsed),
            "boolean",
            Expected.One(Scott.leaf("true")),
            Reduction.defaultLimits
          )
        )
      case other => throw IllegalArgumentException(s"not a theorem: $other")
    }
