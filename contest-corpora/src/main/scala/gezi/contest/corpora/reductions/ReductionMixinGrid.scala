package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The lattice paths in the mixin encoding, the port of
  * `problems/reduction_mixin_grid`:
  * `Claimed.equality({grid, i : Rows, j : Columns}.count)` read at church.
  */
object ReductionMixinGrid:

  private val family = "reduction_mixin_grid"

  /** The program (`grid_surface/4`). */
  def gridSurface(mixins: MixinLibrary, rows: Int, columns: Int, claimed: BigInt): Term =
    mixins.withMixinLibrary(Vector("natural", "binary"), Vector("grid_module", "grid"))(names =>
      val module = gridModule(mixins, names)
      val count =
        gridCall(mixins, module, mixins.naturalInstance(names, rows), mixins.naturalInstance(names, columns))
      val compared = mixins.slotApplied("binary", "equality", mixins.binaryInstance(names, claimed), count)
      mixins.readSlot("boolean", "church", compared)
    )

  /** The module whose one slot is the class grid (`grid_module/2`). */
  private def gridModule(mixins: MixinLibrary, names: MixinNames): Term =
    members(Vector(mixins.selfMixin("grid_module", "grid")(module => members(Vector(gridMixin(mixins, names, module))))))

  /** count over self's i and j (`grid_mixin/3`). */
  private def gridMixin(mixins: MixinLibrary, names: MixinNames, module: Term): Term =
    mixins.selfMixin("grid", "count")(self =>
      val upCount = gridCall(
        mixins,
        module,
        mixins.readSlot("natural", "predecessor", mixins.readSlot("grid", "i", self)),
        mixins.readSlot("grid", "j", self)
      )
      val leftCount = gridCall(
        mixins,
        module,
        mixins.readSlot("grid", "i", self),
        mixins.readSlot("natural", "predecessor", mixins.readSlot("grid", "j", self))
      )
      val sum = mixins.slotApplied("binary", "plus", upCount, leftCount)
      val onColumn = mixins.slotApplied(
        "natural",
        "accept",
        mixins.readSlot("grid", "j", self),
        mixins.binaryInstance(names, 1),
        λ(_ => sum)
      )
      mixins.slotApplied(
        "natural",
        "accept",
        mixins.readSlot("grid", "i", self),
        mixins.binaryInstance(names, 1),
        λ(_ => onColumn)
      )
    )

  /** `{grid, i : I, j : J}.count`, the class read from the module
    * (`grid_call/4`).
    */
  private def gridCall(mixins: MixinLibrary, module: Term, row: Term, column: Term): Term =
    val grid = mixins.readSlot("grid_module", "grid", module)
    mixins.readSlot("grid", "count", members(Vector(grid, mixins.valueMixin("grid", "i" -> row, "j" -> column))))

  /** The problems (`grid_point/3`), each expecting whether its claim is the
    * number of paths.
    */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("grid_point").map {
      case Vector(point, size, claimed) =>
        val (sizeValue, claimedValue) = (ProblemData.small(size), ProblemData.integer(claimed))
        ReductionProblem(
          ProblemData.text(point),
          gridSurface(group.mixins, sizeValue, sizeValue, claimedValue),
          "boolean",
          Expected.One(Scott.booleanTree(DynamicReferences.referenceGridPaths(sizeValue, sizeValue) == claimedValue)),
          Reduction.defaultLimits
        )
      case other => throw IllegalArgumentException(s"not a grid point: $other")
    }
