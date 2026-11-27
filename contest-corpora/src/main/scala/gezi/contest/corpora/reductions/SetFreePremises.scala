package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemField

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** Repeated functions on a binary numeral whose premises make them the
  * identity, the port of `problems/set_free_premises`: the rebuild, the
  * complement's involution and plus's unit law, with near misses.
  */
object SetFreePremises:

  private val family = "set_free_premises"

  /** The law of a twin of law_twin, the constructors of
    * problems/set_free_premises/law in order: the complement's involution and
    * plus's unit law. `written` is the law's name as the twin's point name
    * splices it, `set_free_involution_medium_direct` for instance; it is not a
    * key of the data.
    */
  enum Law(val written: String):
    case Involution extends Law("involution")
    case Unit extends Law("unit")

  /** The law a field writes, a constructor of problems/set_free_premises/law
    * read by its position (`ProblemData.alternative`).
    */
  def law(field: ProblemField): Law =
    ProblemData.alternative(field, Law.values.size) match
      case (position, Vector()) => Law.fromOrdinal(position)
      case (_, fields)          =>
        throw IllegalArgumentException(
          s"the law of $family has ${fields.size} fields"
        )

  /** A point: its function, spelling, repetitions and number
    * (`rebuild_point/5`).
    */
  final case class RebuildPoint(
      point: String,
      function: String,
      spelling: Spelling,
      times: Int,
      number: BigInt
  )

  /** The points: the facts read; each rebuild size with each rebuild twin; each
    * size with each law twin, the involution applied once more, the number
    * `10^Digits // 7`.
    */
  def points(group: ReductionGroup): Vector[RebuildPoint] =
    val stated = group.problems(family).rows("rebuild_point").map {
      case Vector(point, function, spelling, times, number) =>
        RebuildPoint(
          ProblemData.text(point),
          ProblemData.text(function),
          SetFree.spelling(spelling),
          ProblemData.small(times),
          ProblemData.integer(number)
        )
      case other =>
        throw IllegalArgumentException(s"not a rebuild point: $other")
    }
    val sizes = group.problems(family).rows("rebuild_size")
    val rebuilds = for
      size <- sizes
      twin <- group.problems(family).rows("rebuild_twin")
    yield RebuildPoint(
      s"set_free_rebuild_${ProblemData.text(size(0))}_${ProblemData.text(twin(0))}",
      ProblemData.text(twin(1)),
      SetFree.spelling(twin(2)),
      ProblemData.small(size(1)),
      BigInt(10).pow(ProblemData.small(size(2))) / 7
    )
    val laws = for
      size <- sizes
      twin <- group.problems(family).rows("law_twin")
    yield
      val law = this.law(twin(0))
      val oddTimes = ProblemData.small(size(1))
      val times = law match
        case Law.Involution => oddTimes + 1
        case Law.Unit       => oddTimes
      RebuildPoint(
        s"set_free_${law.written}_${ProblemData.text(size(0))}_${ProblemData.text(twin(1))}",
        ProblemData.text(twin(2)),
        SetFree.spelling(twin(3)),
        times,
        BigInt(10).pow(ProblemData.small(size(2))) / 7
      )
    stated ++ rebuilds ++ laws

  /** `Repeat Times Function Numeral` (`rebuild_point_surface/2`). */
  def pointSurface(group: ReductionGroup, point: RebuildPoint): ProblemTerm =
    repeatedFunction(group, point.function, point.spelling, point.times)(
      binary(point.number)
    )

  /** `Repeat Times Function`, the function a point applies to its numeral. */
  private[reductions] def repeatedFunction(
      group: ReductionGroup,
      function: String,
      spelling: Spelling,
      times: Int
  ): ProblemTerm =
    repeatFunction(group.attractors, spelling)(unary(times))(
      appliedFunction(group, function, spelling)
    )

  /** `Y (\self. \n. \f. \x. n x (\p. f (self p f x)))` (`repeat_function/2`).
    */
  private def repeatFunction(
      attractors: Attractors,
      spelling: Spelling
  ): ProblemTerm =
    attractors.fixpoint(
      Attractors.spelledSurface(
        spelling,
        λ(self =>
          λ(count =>
            λ(function =>
              λ(start =>
                count(start)(
                  λ(predecessor => function(self(predecessor)(function)(start)))
                )
              )
            )
          )
        )
      )
    )

  /** The function: for the unit law `\acc. plus acc zero`, for its near miss
    * `\acc. plus acc one`, otherwise the rebuild or complement tied by self
    * application (`applied_function/3`).
    */
  private def appliedFunction(
      group: ReductionGroup,
      name: String,
      spelling: Spelling
  ): ProblemTerm =
    val attractors = group.attractors
    name match
      case "unit" =>
        val plus = SetFree.libraryFunction(group, "merge_binary_plus", spelling)
        val zero = attractors.attractorSurface("binary_zero", Spelling.Direct)
        λ(accumulated => plus(accumulated)(zero))
      case "unit_near" =>
        val plus = SetFree.libraryFunction(group, "merge_binary_plus", spelling)
        val odd = attractors.attractorSurface("binary_odd", Spelling.Direct)
        val zero = attractors.attractorSurface("binary_zero", Spelling.Direct)
        λ(accumulated => plus(accumulated)(odd(zero)))
      case _ =>
        functionBody(group, name, spelling)(functionBody(group, name, spelling))

  /** `\self. \n. n zero (\h. C1 (self self h)) (\h. C2 (self self h))`, the
    * constructors the facts `function_constructors/3` name (`function_body/3`).
    */
  private def functionBody(
      group: ReductionGroup,
      name: String,
      spelling: Spelling
  ): ProblemTerm =
    val attractors = group.attractors
    val (evenCase, oddCase) =
      group.problems(family).keyed("function_constructors").get(name) match
        case Some(Vector(even, odd)) =>
          (ProblemData.text(even), ProblemData.text(odd))
        case other =>
          throw IllegalArgumentException(s"no constructors of $name: $other")
    val zero = attractors.attractorSurface("binary_zero", Spelling.Direct)
    val evenConstructor = attractors.attractorSurface(evenCase, Spelling.Direct)
    val oddConstructor = attractors.attractorSurface(oddCase, Spelling.Direct)
    Attractors.spelledSurface(
      spelling,
      λ(self =>
        λ(number =>
          number(zero)(λ(half => evenConstructor(self(self)(half))))(
            λ(half => oddConstructor(self(self)(half)))
          )
        )
      )
    )

  /** Every even and odd exchanged (`complemented/2`). */
  def complemented(tree: ScottTree): ScottTree = tree match
    case ScottTree("zero", _)            => tree
    case ScottTree("even", Vector(half)) =>
      ScottTree("odd", Vector(complemented(half)))
    case ScottTree("odd", Vector(half)) =>
      ScottTree("even", Vector(complemented(half)))
    case _ => throw IllegalArgumentException(s"not a binary tree: $tree")

  /** The tree the point expects (`reference/5`). */
  def reference(point: RebuildPoint): ScottTree =
    val tree = Scott.binaryTree(point.number)
    point.function match
      case "unit"       => tree
      case "unit_near"  => Scott.binaryTree(point.number + point.times)
      case "rebuild"    => tree
      case "complement" =>
        if point.times % 2 == 1 then complemented(tree) else tree
      case other => throw IllegalArgumentException(s"no function $other")

  /** The problems. */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    points(group).map(point =>
      ReductionProblem(
        point.point,
        pointSurface(group, point),
        "binary",
        Expected.One(reference(point)),
        Reduction.defaultLimits
      )
    )
