package gezi.narrowblocks

import hedgehog.Gen
import hedgehog.Range
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.SeededSnapshots
import gezi.ir.Configured
import gezi.ir.NoFacts
import snapshot4s.generated.snapshotConfig

private given boundFunctionUnitSnapshotTestNoFacts: NoFacts.type = NoFacts

/** The cut of `BoundFunctionUnit.of` on generated programs: a let `(λf. B) F`,
  * B a site or an opaque leaf applied to several sites, each site f applied to
  * some arguments, f passed bare as an argument, or a site under an inner
  * lambda that captures f; or a program that is no let, F applied to the same
  * body with f's place taken by a leaf. The snapshot records each program's
  * description with the unit's arity, or none. A body that is one site under a
  * lambda makes the let `λf. λx. …`, which the front end writes as one thunk of
  * two holes, a chain and no let, so it has no unit, as the rule says. Its
  * purpose is to catch a cut that misses a site under an inner lambda, counts a
  * bare occurrence as an application, or cuts a program that is no let.
  */
class BoundFunctionUnitSnapshotTest
    extends GeneratedProperties
    with SeededSnapshots:

  /** A site of a body, as its description is drawn: drawn before any term is
    * built, so that no draw happens inside a lambda of the term.
    */
  private enum Site:
    case Applied(arguments: Int)
    case Bare
    case UnderLambda(inner: Site)

  /** A generated program: whether it is a let, and the sites of its body. */
  private final case class Program(let: Boolean, sites: Vector[Site])

  private val leaf: Term =
    Term.closed(NoFacts.opaque("bound-function-unit-leaf"))

  private val function: Term =
    Term.closed(NoFacts.opaque("bound-function-unit-function"))

  private val site: Gen[Site] = Gen.sized(size =>
    def drawn(depth: Int): Gen[Site] =
      if depth == 0 then Gen.int(Range.constant(0, 4)).map(Site.Applied(_))
      else
        Gen.frequency1(
          4 -> Gen.int(Range.constant(0, 4)).map(Site.Applied(_)),
          1 -> Gen.constant(Site.Bare),
          2 -> drawn(depth - 1).map(Site.UnderLambda(_))
        )
    drawn(math.min(3, size.value / 20))
  )

  private val program: Gen[Program] =
    for
      let <- Gen.frequency1(5 -> Gen.constant(true), 1 -> Gen.constant(false))
      sites <- site.list(Range.linear(1, 4))
    yield Program(let, sites.toVector)

  private def described(site: Site): String = site match
    case Site.Applied(arguments) => s"f/$arguments"
    case Site.Bare               => "g f"
    case Site.UnderLambda(inner) => s"λ(${described(inner)})"

  /** The site's term, `bound` standing for f. */
  private def term(site: Site, bound: Term): Term = site match
    case Site.Applied(arguments) =>
      (1 to arguments).foldLeft(bound)((applied, _) => applied(leaf))
    case Site.Bare               => leaf(bound)
    case Site.UnderLambda(inner) => λ(_ => term(inner, bound))

  /** The body, the leaf applied to the sites, or the one site alone. */
  private def body(sites: Vector[Site], bound: Term): Term = sites match
    case Vector(only) => term(only, bound)
    case _            =>
      sites.foldLeft(leaf)((applied, site) => applied(term(site, bound)))

  private def instruction(drawn: Program): Configured[NoFacts.type] =
    val whole =
      if drawn.let then λ(bound => body(drawn.sites, bound))(function)
      else function(body(drawn.sites, leaf))
    Defunctionalization.thunkInstruction(whole.deBruijnTerm(Map.empty))(using
      gezi.ir.NoFacts
    )

  test(
    "the unit of a let is its function at the most arguments a site applies it to"
  ) {
    assertSeededSnapshot(
      program,
      20261122L,
      40,
      "bound_function_unit/cuts.txt"
    )(
      drawn =>
        s"${if drawn.let then "let" else "no let"}: ${drawn.sites.map(described).mkString(", ")}",
      (unit: Option[Int]) => unit.fold("no unit")(arity => s"arity $arity")
    )(drawn => BoundFunctionUnit.of(instruction(drawn)).map(_.arity))
  }
