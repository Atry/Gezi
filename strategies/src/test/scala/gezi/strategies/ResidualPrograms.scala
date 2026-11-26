package gezi.strategies

import hedgehog.Gen
import hedgehog.Range
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.generatedinputs.HoasGenerators
import gezi.ir.BindingNormalForm
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.rewritetrace.Statements

/** Programs whose β residuals are not their own spelling, shared by the
  * replay spelling and trace laws (`ReplaySpellingLawTest`, `RewriteTraceLawTest`).
  */
object ResidualPrograms:

  private given NoFacts.type = NoFacts

  private given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()


  /** A lambda of two or three binders whose body is the choice of `z (x C)`
    * (x the first binder, z the last, C a generated closed term) and a
    * generated term under the binders: filling the first hole of its thunk
    * leaves `x C` inline though it reads no binder once x is filled, which
    * the front end makes one filling.
    */
  val lambdas: Gen[Term] =
    for
      count <- Gen.int(Range.linear(2, 3))
      body <- Gen.sized(size => HoasGenerators.openTerm(count, size.value / 2))
      constant <- HoasGenerators.closedTerm
    yield
      def under(outer: Vector[Term]): Term =
        if outer.size == count then Term.choice(outer.last(outer.head(constant)), body(outer))
        else Term.λ(bound => under(outer :+ bound))
      under(Vector.empty)

  /** The lambdas of `lambdas` whose generated term does not read the first
    * binder x: applied to an argument A, the β rule gives
    * `λ… z. z (A C) + body`, smaller than the application by the
    * application's node, x's binder and its one occurrence.
    */
  val lambdasIgnoringTheFirstBinder: Gen[Term] =
    for
      count <- Gen.int(Range.linear(2, 3))
      body <- Gen.sized(size => HoasGenerators.openTerm(count - 1, size.value / 2))
      constant <- HoasGenerators.closedTerm
    yield
      def under(outer: Vector[Term]): Term =
        if outer.size == count then Term.choice(outer.last(outer.head(constant)), body(outer.tail))
        else Term.λ(bound => under(outer :+ bound))
      under(Vector.empty)

  /** The front end's thunks of `lambdas`. */
  val thunks: Gen[Configured[NoFacts.type]] =
    lambdas.map(lambda => Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](lambda.deBruijnTerm(Map.empty))(using gezi.ir.NoFacts))

  /** The thunk the defunctionalized β rule leaves when the argument fills
    * the thunk's first hole (`Statements.fill`), as the rule states it, not
    * respelled.
    */
  def residual(thunk: Configured[NoFacts.type], argument: Configured[NoFacts.type]): Configured[NoFacts.type] = thunk.layer match
    case gezi.ir.Thunk(code, holes, _) =>
      val equation = Statements.fill(code, holes)
      Statements.instance(equation.right, Statements.bindings(equation.left, NoFacts.application(thunk, argument)))
    case other => throw IllegalArgumentException(s"no thunk: $other")

  /** The thunks with holes of the term that are not their own respelling
    * (`gezi.ir.BindingNormalForm.respelled`), each distinct subterm
    * once.
    */
  def respellable(term: Configured[NoFacts.type]): Set[Configured[NoFacts.type]] =
    @scala.annotation.tailrec
    def found(pending: List[Configured[NoFacts.type]], seen: Set[Configured[NoFacts.type]], gathered: Set[Configured[NoFacts.type]]): Set[Configured[NoFacts.type]] =
      pending match
        case Nil                                              => gathered
        case next :: rest if seen(next) || next.opaque        => found(rest, seen, gathered)
        case next :: rest =>
          val here = next.layer match
            case gezi.ir.Thunk(code, holes, fillings) =>
              holes.nonEmpty && BindingNormalForm.respelled(code, holes, fillings.size).isDefined
            case _ => false
          found(next.layer.children.toList ::: rest, seen + next, if here then gathered + next else gathered)
    found(List(term), Set.empty, Set.empty)
