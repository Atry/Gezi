object Planted:
  val applied = Array(1, 2)
  val constructed = new Array[Int](2)
  val allocated = Array.ofDim[Int](2)
  val filled = Array.fill(2)(0)
  val tabulated = Array.tabulate(2)(index => index)
  val emptied = Array.empty[Int]
  val ranged = Array.range(0, 2)
  val iterated = Array.iterate(0, 2)(_ + 1)
  val concatenated = Array.concat(applied, applied)
  val copiedOf = Array.copyOf(applied, 3)
  val copiedAs = Array.copyAs[Long](applied, 2)
  val written = applied.update(0, 1)
  val assigned = applied(0) = 1
  val copied = System.arraycopy(applied, 0, constructed, 0, 2)
  val arraysFilled = java.util.Arrays.fill(applied, 0)
  val arraysSet = java.util.Arrays.setAll(applied, index => index)
  val arraysSorted = java.util.Arrays.sort(applied)
  val arraysParallelSorted = java.util.Arrays.parallelSort(applied)
  val converted = Vector(1, 2).toArray
