package gezi.contest.corpora.reductions

/** The native reference solutions of the CSES families (`CsesFamily.solved`): the best known algorithm of each problem,
  * on fixed-width integers, from a site's data to its answer, written with the problems they solve.
  * Their JMH readings are the families' reference times (`NativeSolverBenchmark`), meant to be an expert's typed native
  * code. They are written immutably, as all of Gezi's Scala is, on unboxed tables: an immutable array (`IArray[Int]`,
  * `IArray[Long]`, `IArray[Boolean]`) for each pass of a dynamic program or each row of a matrix; a `BlockedInts` or a
  * `BlockedLongs` where a loop updates or appends one entry at a time (a union-find, a visited set, a queue, settled
  * distances, the table of a patience sort, the counts of a topological sort) or where an entry reads the entries before
  * it (`BlockedInts.recurrence`); and loops that are tail recursions over Int indices. A solution converts the `Vector`s
  * of its site once, at its entry.
  */
object CsesSolutions:

  private val modulus: Long = CsesFamily.modulus.toLong

  /** The modulus as an Int: a residue fits one, and so does the sum of two residues, below 2 (10^9 + 7) < 2^31. */
  private val intModulus: Int = CsesFamily.modulus

  /** The sum of two residues modulo 10^9 + 7. */
  private def addedModulo(first: Int, second: Int): Int =
    val sum = first + second
    if sum >= intModulus then sum - intModulus else sum

  /** a^b modulo 10^9 + 7, 0^0 being 1, by exponentiation by squaring on Longs reduced at each step, in O(log b) time. */
  private def power(base: Long, exponent: Long): Long =
    @scala.annotation.tailrec
    def powered(square: Long, remaining: Long, product: Long): Long =
      if remaining == 0 then product
      else powered(square * square % modulus, remaining >> 1, if (remaining & 1) == 1 then product * square % modulus else product)
    powered(base % modulus, exponent, 1L)

  /** The first index of the sorted keys whose key is at least the given one, by binary search. */
  @scala.annotation.tailrec
  private def lowerBound(keys: IArray[Long], key: Long, low: Int, high: Int): Int =
    if low >= high then low
    else
      val middle = (low + high) >>> 1
      if keys(middle) < key then lowerBound(keys, key, middle + 1, high) else lowerBound(keys, key, low, middle)

  /** The input a top rung computes from its seed, `seeded_numbers seed count low high` of
    * `problems/cses/common/seeded_input`: count numbers, the k-th (k from 1) low + s_k mod (high - low + 1), where
    * s_0 = seed and s_k = 48271 s_(k-1) mod (2^31 - 1), the Lehmer generator of Park and Miller's minimal standard. A
    * seed below 2^31 - 1 keeps every product within a Long.
    */
  def seededNumbers(seed: Long, count: Int, low: Long, high: Long): IArray[Long] =
    require(seed >= 0 && seed < seededModulus, s"no seed $seed below 2^31 - 1")
    require(count >= 0 && low >= 0 && low <= high, s"no $count numbers from $low to $high")
    val range = high - low + 1
    IArray.iterate(seed * seededMultiplier % seededModulus, count)(state => state * seededMultiplier % seededModulus).map(state => low + state % range)

  /** The state after the seeded generators' state, `next_state` of
    * `problems/cses/common/seeded_input`: 48271 state mod (2^31 - 1).
    */
  def nextSeededState(state: Long): Long =
    require(state >= 0 && state < seededModulus, s"no state $state below 2^31 - 1")
    state * seededMultiplier % seededModulus

  /** The multiplier of `seededNumbers`' generator. */
  private val seededMultiplier: Long = 48271L

  /** The modulus of `seededNumbers`' generator, 2^31 - 1. */
  private val seededModulus: Long = 2147483647L

  /** CSES 1633: the sequences of faces 1 to 6 that sum to n, modulo 10^9 + 7, by the recurrence ways(s) = ways(s - 1) +
    * … + ways(s - 6), ways(0) = 1 and ways of a negative sum 0, in O(n) time on a window of the last six values.
    */
  def diceCombinations(sum: Int): BigInt =
    require(sum >= 0, s"no sum $sum")
    @scala.annotation.tailrec
    def ways(remaining: Int, last: Long, second: Long, third: Long, fourth: Long, fifth: Long, sixth: Long): Long =
      if remaining == 0 then last
      else ways(remaining - 1, (last + second + third + fourth + fifth + sixth) % modulus, last, second, third, fourth, fifth)
    BigInt(ways(sum, 1L, 0L, 0L, 0L, 0L, 0L))

  /** CSES 1634: the fewest coins of the values, each usable any number of times, that sum to x, or none, by the unbounded
    * knapsack recurrence fewest(s) = 1 + the least fewest(s - c) over the coins c ≤ s, fewest(0) = 0, in O(n x) time.
    * The table is a `BlockedInts.recurrence` whose blocks are no longer than the least coin, and the coins an `IArray[Int]`
    * read in increasing order up to the first above s.
    */
  def minimizingCoins(coins: Vector[Int], target: Int): Option[BigInt] =
    require(target >= 0 && coins.forall(_ > 0), s"no coins $coins for $target")
    val values = IArray.from(coins).sorted
    val unreachable = Int.MaxValue
    @scala.annotation.tailrec
    def least(table: BlockedInts, sum: Int, index: Int, found: Int): Int =
      if index == values.length || values(index) > sum then found
      else
        val before = table(sum - values(index))
        least(table, sum, index + 1, if before != unreachable && before + 1 < found then before + 1 else found)
    val fewest = BlockedInts.recurrence(target + 1, values.headOption.getOrElse(Int.MaxValue))((table, sum) =>
      if sum == 0 then 0 else least(table, sum, 0, unreachable)
    )
    val answer = fewest(target)
    Option.when(answer != unreachable)(BigInt(answer))

  /** CSES 1667: the fewest computers on a route from computer 1 to computer n over the undirected connections, or none,
    * by a breadth-first search from computer 1, in O(n + m) time: the connections are an `Adjacency`, the queue of the
    * computers reached a `BlockedInts` appended to, and the computers on the route to each computer reached a `BlockedInts`
    * (0 for a computer not reached yet).
    */
  def messageRoute(computers: Int, connections: Vector[(Int, Int)]): Option[BigInt] =
    require(
      computers >= 1 && connections.forall((from, to) => from >= 1 && from <= computers && to >= 1 && to <= computers),
      s"no connections $connections over $computers computers"
    )
    val neighbours = Adjacency.of(
      computers,
      IArray.from(connections.map(_._1) ++ connections.map(_._2)),
      IArray.from(connections.map(_._2) ++ connections.map(_._1))
    )
    @scala.annotation.tailrec
    def reached(index: Int, last: Int, onRoute: Int, queue: BlockedInts, route: BlockedInts): Search =
      if index == last then Search(queue, route)
      else
        val neighbour = neighbours.payload(index)
        if route(neighbour) != 0 then reached(index + 1, last, onRoute, queue, route)
        else reached(index + 1, last, onRoute, queue.appended(neighbour), route.updated(neighbour, onRoute))
    @scala.annotation.tailrec
    def search(head: Int, found: Search): BlockedInts =
      if head == found.queue.length then found.marks
      else
        val computer = found.queue(head)
        search(head + 1, reached(neighbours.first(computer), neighbours.first(computer + 1), found.marks(computer) + 1, found.queue, found.marks))
    val start = Search(BlockedInts.emptyInBlocks(BlockedInts.updateShift).appended(1), BlockedInts.fill(computers + 1, BlockedInts.updateShift)(0).updated(1, 1))
    val onRoute = search(0, start)(computers)
    Option.when(onRoute != 0)(BigInt(onRoute))

  /** CSES 1192: the rooms of a map, floor true, by a flood fill (breadth first) from each floor square not yet reached,
    * in O(n m) time: the map is an `IArray[Boolean]` of its squares row by row, and the queue of the squares reached and
    * the marks of the squares reached (1, else 0) are `BlockedInts`, one queue for every room in turn.
    */
  def countingRooms(rows: Vector[Vector[Boolean]]): BigInt =
    val width = rows.headOption.fold(0)(_.size)
    require(rows.forall(_.size == width), s"the rows of the map are not of one width: ${rows.map(_.size)}")
    val height = rows.size
    val floors = IArray.from(rows.flatten)
    def reached(found: Search, square: Int): Search =
      if !floors(square) || found.marks(square) != 0 then found
      else Search(found.queue.appended(square), found.marks.updated(square, 1))
    @scala.annotation.tailrec
    def filled(head: Int, found: Search): Search =
      if head == found.queue.length then found
      else
        val square = found.queue(head)
        val row = square / width
        val column = square - row * width
        val above = if row > 0 then reached(found, square - width) else found
        val below = if row < height - 1 then reached(above, square + width) else above
        val left = if column > 0 then reached(below, square - 1) else below
        filled(head + 1, if column < width - 1 then reached(left, square + 1) else left)
    @scala.annotation.tailrec
    def counted(square: Int, rooms: Int, found: Search): Int =
      if square == floors.length then rooms
      else if !floors(square) || found.marks(square) != 0 then counted(square + 1, rooms, found)
      else counted(square + 1, rooms + 1, filled(found.queue.length, reached(found, square)))
    BigInt(counted(0, 0, Search(BlockedInts.emptyInBlocks(BlockedInts.updateShift), BlockedInts.fill(floors.length, BlockedInts.updateShift)(0))))

  /** CSES 1095: a^b modulo 10^9 + 7, 0^0 being 1, by exponentiation by squaring on fixed-width integers reduced at each
    * step, in O(log b) time.
    */
  def exponentiation(base: Int, exponent: Int): BigInt =
    require(base >= 0 && exponent >= 0, s"no power $base^$exponent")
    BigInt(power(base.toLong, exponent.toLong))

  // The second batch.

  /** CSES 1635: the ordered sequences of coins, each value usable any number of times, that sum to x, modulo 10^9 + 7,
    * by the recurrence ways(s) = the sum of ways(s - c) over the coins c ≤ s, ways(0) = 1, in O(n x) time. The table is a
    * `BlockedInts.recurrence` whose blocks are no longer than the least coin, and the coins an `IArray[Int]` read in
    * increasing order up to the first above s, the sum of an entry's residues taken on a Long and reduced once.
    */
  def coinCombinationsOrdered(coins: Vector[Int], target: Int): BigInt =
    require(target >= 0 && coins.forall(_ > 0), s"no coins $coins for $target")
    val values = IArray.from(coins).sorted
    @scala.annotation.tailrec
    def total(table: BlockedInts, sum: Int, index: Int, found: Long): Long =
      if index == values.length || values(index) > sum then found
      else total(table, sum, index + 1, found + table(sum - values(index)))
    val ways = BlockedInts.recurrence(target + 1, values.headOption.getOrElse(Int.MaxValue))((table, sum) =>
      if sum == 0 then 1 else (total(table, sum, 0, 0L) % modulus).toInt
    )
    BigInt(ways(target))

  /** CSES 1636: the multisets of coins, each value usable any number of times, that sum to x, modulo 10^9 + 7, by the
    * unbounded knapsack count taking the coins one at a time, so that each multiset is counted once, in O(n x) time:
    * after a coin c, ways(s) = the ways before it + ways(s - c) after it. Each coin's table is a new
    * `BlockedInts.recurrence` whose blocks are no longer than c, reading the table before the coin.
    */
  def coinCombinationsUnordered(coins: Vector[Int], target: Int): BigInt =
    require(target >= 0 && coins.forall(_ > 0), s"no coins $coins for $target")
    val start = BlockedInts.tabulate(target + 1)(sum => if sum == 0 then 1 else 0)
    val ways = coins.foldLeft(start) { (before, coin) =>
      if coin > target then before
      else
        BlockedInts.recurrence(target + 1, coin)((after, sum) =>
          if coin > sum then before(sum) else addedModulo(before(sum), after(sum - coin))
        )
    }
    BigInt(ways(target))

  /** The fewest steps of each of the nine numbers below a number v, `first` that of v - 1: the window of
    * `removingDigits`.
    */
  private final case class NineBefore(
      first: Int,
      second: Int,
      third: Int,
      fourth: Int,
      fifth: Int,
      sixth: Int,
      seventh: Int,
      eighth: Int,
      ninth: Int
  ):

    /** The fewest steps of v - distance, for a distance from 1 to 9. */
    def at(distance: Int): Int = distance match
      case 1     => first
      case 2     => second
      case 3     => third
      case 4     => fourth
      case 5     => fifth
      case 6     => sixth
      case 7     => seventh
      case 8     => eighth
      case 9     => ninth
      case other => throw IllegalArgumentException(s"the window holds the nine numbers below, not the one $other below")

    /** The window of v + 1, the fewest steps of v being the given ones. */
    def shifted(latest: Int): NineBefore = NineBefore(latest, first, second, third, fourth, fifth, sixth, seventh, eighth)

  /** CSES 1637: the fewest steps that take n to 0, a step subtracting one of the number's nonzero decimal digits, by the
    * recurrence steps(s) = 1 + the least steps(s - d) over the nonzero digits d of s, steps(0) = 0, in O(n log n) time,
    * on a window of the last nine values (a digit is at most 9).
    */
  def removingDigits(number: Int): BigInt =
    require(number >= 0, s"no number $number")
    @scala.annotation.tailrec
    def least(window: NineBefore, rest: Int, found: Int): Int =
      if rest == 0 then found
      else
        val digit = rest % 10
        least(window, rest / 10, if digit == 0 then found else math.min(found, window.at(digit)))
    @scala.annotation.tailrec
    def steps(value: Int, window: NineBefore): Int =
      if value > number then window.first
      else steps(value + 1, window.shifted(1 + least(window, value, Int.MaxValue)))
    BigInt(steps(1, NineBefore(0, 0, 0, 0, 0, 0, 0, 0, 0)))

  /** CSES 1638: the paths from the top left square to the bottom right one by steps right and down over free squares
    * (true), modulo 10^9 + 7, by the recurrence ways(r, c) = ways(r - 1, c) + ways(r, c - 1) on free squares, one row at
    * a time, in O(n²) time: each row an `IArray[Int]`, the scan of its columns from the left.
    */
  def gridPaths(rows: Vector[Vector[Boolean]]): BigInt =
    val width = rows.headOption.fold(0)(_.size)
    require(rows.nonEmpty && rows.forall(_.size == width), s"the rows of the grid are not of one width: ${rows.map(_.size)}")
    val columns = IArray.range(0, width)
    val above = IArray.tabulate(width)(column => if column == 0 then 1 else 0)
    val last = rows.foldLeft(above) { (previous, row) =>
      val free = IArray.from(row)
      columns.scanLeft(0)((left, column) => if !free(column) then 0 else addedModulo(previous(column), left)).drop(1)
    }
    BigInt(last(width - 1))

  /** CSES 1158: the most pages of books, each bought at most once, whose prices sum to at most x, by the 0/1 knapsack
    * table best(b) = the most pages within budget b, the books taken one at a time, in O(n x) time: one `IArray[Int]`
    * for each book.
    */
  def bookShop(books: Vector[(Int, Int)], budget: Int): BigInt =
    require(budget >= 0 && books.forall((price, pages) => price > 0 && pages >= 0), s"no books $books for $budget")
    val best = books.foldLeft(IArray.fill(budget + 1)(0)) { case (before, (price, pages)) =>
      IArray.tabulate(budget + 1)(spent => if price > spent then before(spent) else math.max(before(spent), before(spent - price) + pages))
    }
    BigInt(best(budget))

  /** CSES 1671: the sum over the cities of the least cost of a trip from city 1 to the city over one-way flights of positive cost, by Dijkstra's
    * algorithm with a priority queue, in O((n + m) log n) time: the flights are an `Adjacency` to their places in
    * `IArray`s of their ends and costs, the queue a `DistanceHeap`, and the settled costs a `BlockedLongs` (-1 for a city
    * not settled yet). A city no trip reaches counts the total cost of all flights plus one, as the problem's program
    * does (CSES promises every city is reached, and the generator draws so).
    */
  def shortestRoutesSingleSource(cities: Int, flights: Vector[(Int, Int, Long)]): BigInt =
    require(
      cities >= 1 && flights.forall((from, to, cost) => from >= 1 && from <= cities && to >= 1 && to <= cities && cost > 0),
      s"no flights $flights over $cities cities"
    )
    val ends = IArray.from(flights.map(_._2))
    val costs = IArray.from(flights.map(_._3))
    val departures = Adjacency.of(cities, IArray.from(flights.map(_._1)), IArray.range(0, flights.length))
    @scala.annotation.tailrec
    def relaxed(index: Int, last: Int, distance: Long, pending: DistanceHeap, settled: BlockedLongs): DistanceHeap =
      if index == last then pending
      else
        val flight = departures.payload(index)
        val to = ends(flight)
        relaxed(index + 1, last, distance, if settled(to) >= 0 then pending else pending.inserted(distance + costs(flight), to), settled)
    @scala.annotation.tailrec
    def search(queue: DistanceHeap, settled: BlockedLongs): BlockedLongs = queue match
      case DistanceHeap.Empty => settled
      case nearest @ DistanceHeap.Node(distance, city, _) =>
        val rest = nearest.withoutLeast
        if settled(city) >= 0 then search(rest, settled)
        else search(relaxed(departures.first(city), departures.first(city + 1), distance, rest, settled), settled.updated(city, distance))
    val distances = search(DistanceHeap.Empty.inserted(0L, 1), BlockedLongs.fill(cities + 1)(-1L))
    val unreachable = BigInt(flights.map(_._3).sum) + 1
    (1 to cities).foldLeft(BigInt(0))((sum, city) => sum + (if distances(city) < 0 then unreachable else BigInt(distances(city))))

  /** CSES 1672: for each query, the least cost of a route between two cities over two-way roads of positive cost, or
    * none, by the Floyd–Warshall algorithm on the matrix of least costs, in O(n³ + q) time: the matrix is an `IArray` of
    * rows of `IArray[Long]`, a new one for each intermediate city, whose row from a city that does not reach the
    * intermediate one is the row before, shared. The direct costs are read from the roads sorted as packed Longs, the
    * cell of the matrix above the cost, each cost below 2^(63 - b) for n² cells numbered by b bits.
    */
  def shortestRoutesQueries(cities: Int, roads: Vector[(Int, Int, Long)], queries: Vector[(Int, Int)]): Vector[Option[BigInt]] =
    require(
      cities >= 1 && cities <= 46340 && roads.forall((from, to, cost) => from >= 1 && from <= cities && to >= 1 && to <= cities && cost > 0),
      s"no roads $roads over $cities cities"
    )
    val none = Long.MaxValue
    val costBits = 63 - (32 - Integer.numberOfLeadingZeros(cities * cities))
    require(roads.forall(_._3 < (1L << costBits)), "a cost is too large to be packed with its cell")
    val costMask = (1L << costBits) - 1
    def packed(from: Int, to: Int, cost: Long): Long = (((from - 1) * cities + to - 1).toLong << costBits) | cost
    val byCell = IArray.from(roads.flatMap((from, to, cost) => Vector(packed(from, to, cost), packed(to, from, cost)))).sorted
    def directCost(from: Int, to: Int): Long =
      if from == to then 0L
      else
        val cell = (from * cities + to).toLong
        val first = lowerBound(byCell, cell << costBits, 0, byCell.length)
        if first < byCell.length && (byCell(first) >>> costBits) == cell then byCell(first) & costMask else none
    val direct = IArray.tabulate(cities)(from => IArray.tabulate(cities)(to => directCost(from, to)))
    val least = (0 until cities).foldLeft(direct) { (matrix, through) =>
      val viaRow = matrix(through)
      IArray.tabulate(cities) { from =>
        val row = matrix(from)
        val viaFrom = row(through)
        if viaFrom == none then row
        else
          IArray.tabulate(cities) { to =>
            val viaTo = viaRow(to)
            if viaTo == none then row(to) else math.min(row(to), viaFrom + viaTo)
          }
      }
    }
    queries.map((from, to) => Option(least(from - 1)(to - 1)).filter(_ != none).map(BigInt(_)))

  /** CSES 1713: the sum over the numbers of the number of divisors of each, by trial division up to its square root, counting each divisor
    * pair once, in O(q √x) time.
    */
  def countingDivisors(numbers: Vector[Int]): BigInt =
    require(numbers.forall(_ >= 1), s"no divisors of $numbers")
    numbers.foldLeft(BigInt(0))((sum, number) =>
      @scala.annotation.tailrec
      def count(divisor: Long, found: Int): Int =
        if divisor * divisor > number then found
        else if number % divisor != 0 then count(divisor + 1, found)
        else count(divisor + 1, found + (if divisor * divisor == number then 1 else 2))
      sum + count(1L, 0)
    )

  /** CSES 1079: a choose b modulo 10^9 + 7 for each query, by the factorials up to the largest a, an `IArray[Long]`, and
    * their inverses by Fermat's little theorem (exponentiation by squaring on Longs), then three multiplications a query,
    * in O(A + q log p) time.
    */
  def binomialCoefficients(queries: Vector[(Int, Int)]): Vector[BigInt] =
    require(queries.forall((whole, chosen) => 0 <= chosen && chosen <= whole), s"no binomials $queries")
    val largest = queries.map(_._1).maxOption.getOrElse(0)
    val factorials = IArray.range(1, largest + 1).scanLeft(1L)((product, factor) => product * factor % modulus)
    def inverse(value: Long): Long = power(value, modulus - 2)
    queries.map((whole, chosen) =>
      BigInt(factorials(whole) * inverse(factorials(chosen)) % modulus * inverse(factorials(whole - chosen)) % modulus)
    )

  /** CSES 1621: the number of distinct values in a list, by sorting them as an `IArray[Int]` and counting the places
    * whose value differs from the one before, in O(n log n) time.
    */
  def distinctNumbers(numbers: Vector[Int]): BigInt =
    val sorted = IArray.from(numbers).sorted
    @scala.annotation.tailrec
    def counted(index: Int, found: Int): Int =
      if index >= sorted.length then found else counted(index + 1, if sorted(index) != sorted(index - 1) then found + 1 else found)
    BigInt(if sorted.isEmpty then 0 else counted(1, 1))

  /** The queue of a breadth-first search, the places reached in the order reached, and its marks, an entry of each place
    * (0 for a place not reached).
    */
  private final case class Search(queue: BlockedInts, marks: BlockedInts)

  /** The edges of a graph on the vertices 0 to n out of each vertex: packed Longs, the start above a payload of 32 bits
    * (the end, or the edge's place), sorted, so that the edges out of a vertex are the places `first(vertex)` to
    * `first(vertex + 1)`, found by binary search.
    */
  private final class Adjacency private (edges: IArray[Long], firsts: IArray[Int]):

    /** The place of the first edge out of the vertex, for a vertex from 0 to n + 1. */
    def first(vertex: Int): Int = firsts(vertex)

    /** The payload of the edge at the place. */
    def payload(place: Int): Int = (edges(place) & 0xffffffffL).toInt

  private object Adjacency:

    /** The edges from the starts to the payloads, of equal length, over the vertices 0 to `vertices`, every payload
      * nonnegative.
      */
    def of(vertices: Int, starts: IArray[Int], payloads: IArray[Int]): Adjacency =
      require(starts.length == payloads.length && payloads.forall(_ >= 0), "the starts and the payloads of the edges do not pair")
      val edges = IArray.tabulate(starts.length)(place => (starts(place).toLong << 32) | payloads(place).toLong).sorted
      Adjacency(edges, IArray.tabulate(vertices + 2)(vertex => lowerBound(edges, vertex.toLong << 32, 0, edges.length)))

  /** An immutable pairing heap of the cities a Dijkstra search has reached, by their tentative costs, the least first. */
  private enum DistanceHeap:
    case Empty
    case Node(distance: Long, city: Int, subheaps: List[DistanceHeap.Node])

    /** The heap with one more city. */
    def inserted(distance: Long, city: Int): DistanceHeap = DistanceHeap.merged(this, new DistanceHeap.Node(distance, city, Nil))

    /** The heap without its least city, its subheaps merged in pairs from the left, then the pairs from the right. */
    def withoutLeast: DistanceHeap = this match
      case DistanceHeap.Empty                => throw IllegalStateException("an empty heap has no least city")
      case DistanceHeap.Node(_, _, subheaps) =>
        @scala.annotation.tailrec
        def paired(rest: List[DistanceHeap.Node], found: List[DistanceHeap.Node]): List[DistanceHeap.Node] = rest match
          case first :: second :: more => paired(more, DistanceHeap.joined(first, second) :: found)
          case last                    => last ::: found
        paired(subheaps, Nil).reduceLeftOption(DistanceHeap.joined).getOrElse(DistanceHeap.Empty)

  private object DistanceHeap:

    /** The two heaps' cities in one heap. */
    def merged(first: DistanceHeap, second: DistanceHeap.Node): DistanceHeap = first match
      case DistanceHeap.Empty     => second
      case node: DistanceHeap.Node => joined(node, second)

    /** The two nonempty heaps' cities in one heap, the one with the lesser least city on top. */
    def joined(first: DistanceHeap.Node, second: DistanceHeap.Node): DistanceHeap.Node =
      if first.distance <= second.distance then new DistanceHeap.Node(first.distance, first.city, second :: first.subheaps)
      else new DistanceHeap.Node(second.distance, second.city, first :: second.subheaps)

  /** An immutable array of Longs kept in blocks of 32, so that a read is two index operations and an update copies one
    * block of 32 Longs and the path to it in the vector of blocks, instead of copying the whole array as `IArray.updated`
    * does.
    */
  private final class BlockedLongs private (blocks: Vector[IArray[Long]]):

    /** The entry at the index. */
    def apply(index: Int): Long = blocks(index >> BlockedLongs.shift)(index & BlockedLongs.mask)

    /** The array with the entry at the index replaced. */
    def updated(index: Int, value: Long): BlockedLongs =
      val block = index >> BlockedLongs.shift
      BlockedLongs(blocks.updated(block, blocks(block).updated(index & BlockedLongs.mask, value)))

  private object BlockedLongs:
    val shift: Int = 5
    val mask: Int = (1 << shift) - 1

    /** The array of the given length whose every entry is the value. */
    def fill(length: Int)(value: Long): BlockedLongs =
      BlockedLongs(Vector.tabulate((length + mask) >> shift)(block => IArray.fill(math.min(1 << shift, length - (block << shift)))(value)))

  // The third batch.

  /** An immutable array of Ints kept in blocks of 2^k Ints (k = `shift`), so that a read is two index operations and an
    * update copies one block and the path to it in the vector of blocks, instead of copying the whole array as
    * `IArray.updated` does: blocks of 512 (`BlockedInts.shift`) for a table updated now and then, of 32
    * (`BlockedInts.updateShift`) for a table that a loop updates or appends to once for each of its entries, and of the
    * size a `BlockedInts.recurrence` chooses for its table.
    */
  private final class BlockedInts private (blocks: Vector[IArray[Int]], val length: Int, shift: Int):

    private val mask: Int = (1 << shift) - 1

    /** The entry at the index. */
    def apply(index: Int): Int = blocks(index >> shift)(index & mask)

    /** The array with the entry at the index replaced. */
    def updated(index: Int, value: Int): BlockedInts =
      val block = index >> shift
      BlockedInts(blocks.updated(block, blocks(block).updated(index & mask, value)), length, shift)

    /** The array with one more entry at its end. */
    def appended(value: Int): BlockedInts =
      if (length & mask) == 0 then BlockedInts(blocks :+ IArray(value), length + 1, shift)
      else BlockedInts(blocks.updated(blocks.length - 1, blocks.last :+ value), length + 1, shift)

    /** The array with one more block at its end, of at most 2^k entries, its length a multiple of 2^k. */
    def withBlock(block: IArray[Int]): BlockedInts =
      require((length & mask) == 0 && block.length <= mask + 1, s"a block of ${block.length} after $length entries in blocks of ${mask + 1}")
      BlockedInts(blocks :+ block, length + block.length, shift)

  private object BlockedInts:
    val shift: Int = 9

    /** The shift of a table that a loop updates or appends to once for each entry. */
    val updateShift: Int = 5

    val empty: BlockedInts = BlockedInts(Vector.empty, 0, shift)

    /** The empty array in blocks of 2^shift. */
    def emptyInBlocks(blockShift: Int): BlockedInts = BlockedInts(Vector.empty, 0, blockShift)

    /** The array of the given length whose entry at an index is the function of it. */
    def tabulate(length: Int)(function: Int => Int): BlockedInts =
      BlockedInts(
        Vector.tabulate((length + mask(shift)) >> shift)(block =>
          IArray.tabulate(math.min(1 << shift, length - (block << shift)))(offset => function((block << shift) + offset))
        ),
        length,
        shift
      )

    /** The array of the given length in blocks of 2^shift whose every entry is the value. */
    def fill(length: Int, blockShift: Int)(value: Int): BlockedInts =
      BlockedInts(
        Vector.tabulate((length + mask(blockShift)) >> blockShift)(block =>
          IArray.fill(math.min(1 << blockShift, length - (block << blockShift)))(value)
        ),
        length,
        blockShift
      )

    private def mask(blockShift: Int): Int = (1 << blockShift) - 1

    /** The table of the given length whose entry at an index is `entry` of the table so far and the index, for an entry
      * that reads only entries at least `independence` below its index: built one block at a time by `IArray.tabulate`,
      * in blocks of the largest power of two not above `independence` and not above 512, so that every entry it reads
      * is in a block built before its own. Inline, so that the entry is called with no boxing of its index and value.
      */
    inline def recurrence(length: Int, independence: Int)(inline entry: (BlockedInts, Int) => Int): BlockedInts =
      require(length >= 0 && independence >= 1, s"no recurrence of $length entries, each reading $independence below")
      val blockShift = math.min(shift, 31 - Integer.numberOfLeadingZeros(independence))
      @scala.annotation.tailrec
      def built(table: BlockedInts): BlockedInts =
        val start = table.length
        if start == length then table
        else built(table.withBlock(IArray.tabulate(math.min(1 << blockShift, length - start))(offset => entry(table, start + offset))))
      built(emptyInBlocks(blockShift))

  /** The disjoint sets of the cities 1 to n of a graph, as a forest of parent links with union by size and no path
    * compression (a find is O(log n) reads, a union two block updates).
    */
  private final case class UnionFind(parent: BlockedInts, size: BlockedInts):

    /** The set's representative of a city. */
    @scala.annotation.tailrec
    def find(city: Int): Int = if parent(city) == city then city else find(parent(city))

    /** The sets joined, or none when the two cities are in one set already. */
    def union(first: Int, second: Int): Option[UnionFind] =
      val firstRoot = find(first)
      val secondRoot = find(second)
      if firstRoot == secondRoot then None
      else
        val (smaller, larger) = if size(firstRoot) < size(secondRoot) then (firstRoot, secondRoot) else (secondRoot, firstRoot)
        Some(UnionFind(parent.updated(smaller, larger), size.updated(larger, size(larger) + size(smaller))))

  private object UnionFind:
    /** Each of the cities 1 to cities alone. */
    def separate(cities: Int): UnionFind = UnionFind(BlockedInts.tabulate(cities + 1)(identity), BlockedInts.tabulate(cities + 1)(_ => 1))

  /** CSES 1745: the sum of the sums that a nonempty set of the coins makes, each counted once, by the reachability table
    * of subset sums, reachable(s) = reachable(s) or reachable(s - c) for each coin c, one table of Booleans for each
    * coin, in O(n S) time for n coins that sum to S.
    */
  def moneySums(coins: IArray[Int]): BigInt =
    require(coins.forall(_ > 0), s"no coins ${coins.mkString(",")}")
    val total = coins.foldLeft(0)(_ + _)
    val reachable = coins.foldLeft(IArray.tabulate(total + 1)(_ == 0)) { (before, coin) =>
      IArray.tabulate(total + 1)(sum => before(sum) || (sum >= coin && before(sum - coin)))
    }
    (1 to total).filter(reachable(_)).foldLeft(BigInt(0))(_ + _)

  /** CSES 1744: the fewest cuts that make a rectangle of whole units into squares, by the table cuts(a, b) = 0 for a = b and
    * 1 + the least over the first cuts of cuts(c, b) + cuts(a - c, b) and cuts(a, c) + cuts(a, b - c), one row of
    * unboxed Ints at a time (a row grows by one entry at a time, an O(b) copy that costs no more than the entry's own
    * O(a + b) cuts), in O(a b (a + b)) time.
    */
  def rectangleCutting(first: Int, second: Int): BigInt =
    require(first >= 1 && second >= 1, s"no rectangle $first by $second")
    @scala.annotation.tailrec
    def heightCuts(rows: Vector[IArray[Int]], height: Int, width: Int, cut: Int, least: Int): Int =
      if cut >= height then least
      else heightCuts(rows, height, width, cut + 1, math.min(least, rows(cut - 1)(width - 1) + rows(height - cut - 1)(width - 1)))
    @scala.annotation.tailrec
    def widthCuts(current: IArray[Int], width: Int, cut: Int, least: Int): Int =
      if cut >= width then least
      else widthCuts(current, width, cut + 1, math.min(least, current(cut - 1) + current(width - cut - 1)))
    @scala.annotation.tailrec
    def row(rows: Vector[IArray[Int]], height: Int, current: IArray[Int]): IArray[Int] =
      val width = current.length + 1
      if width > second then current
      else
        val cuts =
          if height == width then 0
          else 1 + widthCuts(current, width, 1, heightCuts(rows, height, width, 1, Int.MaxValue))
        row(rows, height, current :+ cuts)
    @scala.annotation.tailrec
    def table(rows: Vector[IArray[Int]]): Vector[IArray[Int]] =
      if rows.length == first then rows else table(rows :+ row(rows, rows.length + 1, IArray.empty[Int]))
    BigInt(table(Vector.empty).last(second - 1))

  /** CSES 1145: the length of the longest strictly increasing subsequence, by patience sorting: for each length, the least
    * number that ends an increasing subsequence of that length, found by binary search, in O(n log n) comparisons (the
    * table of ends is a `BlockedInts`, an update copying one block of 512).
    */
  def increasingSubsequence(numbers: IArray[Int]): BigInt =
    @scala.annotation.tailrec
    def place(ends: BlockedInts, value: Int, low: Int, high: Int): Int =
      if low >= high then low
      else
        val middle = (low + high) >>> 1
        if ends(middle) < value then place(ends, value, middle + 1, high) else place(ends, value, low, middle)
    @scala.annotation.tailrec
    def sorted(index: Int, ends: BlockedInts): Int =
      if index == numbers.length then ends.length
      else
        val found = place(ends, numbers(index), 0, ends.length)
        sorted(index + 1, if found == ends.length then ends.appended(numbers(index)) else ends.updated(found, numbers(index)))
    BigInt(sorted(0, BlockedInts.empty))

  /** CSES 1746: the fillings of the unknown entries (0) of an array with values 1 to m, neighbours differing by at most 1,
    * modulo 10^9 + 7, by the table ways(position, value) = ways(position - 1, value - 1) + ways(position - 1, value) +
    * ways(position - 1, value + 1) on the values the entry may take, one array of Longs for each entry, in O(n m) time.
    */
  def arrayDescription(upper: Int, entries: IArray[Int]): BigInt =
    require(upper >= 1 && entries.nonEmpty && entries.forall(entry => entry >= 0 && entry <= upper), s"no array ${entries.mkString(",")} with values up to $upper")
    def allowed(entry: Int, value: Int): Boolean = value >= 1 && value <= upper && (entry == 0 || entry == value)
    val first = IArray.tabulate(upper + 2)(value => if allowed(entries(0), value) then 1L else 0L)
    val last = entries.drop(1).foldLeft(first) { (before, entry) =>
      IArray.tabulate(upper + 2)(value =>
        if !allowed(entry, value) then 0L else (before(value - 1) + before(value) + before(value + 1)) % modulus
      )
    }
    BigInt(last.foldLeft(0L)(_ + _) % modulus)

  /** CSES 1666: the fewest new roads that connect every city, the number of components minus one, found by a union-find
    * over the roads, in O((n + m) log n) time.
    */
  def buildingRoads(cities: Int, roads: Vector[(Int, Int)]): BigInt =
    require(cities >= 1 && roads.forall((from, to) => from >= 1 && from <= cities && to >= 1 && to <= cities), s"no roads $roads over $cities cities")
    val froms = IArray.from(roads.map(_._1))
    val tos = IArray.from(roads.map(_._2))
    @scala.annotation.tailrec
    def joined(index: Int, sets: UnionFind, components: Int): Int =
      if index == froms.length then components
      else
        sets.union(froms(index), tos(index)) match
          case Some(more) => joined(index + 1, more, components - 1)
          case None       => joined(index + 1, sets, components)
    BigInt(joined(0, UnionFind.separate(cities), cities) - 1)

  /** CSES 1675: the least total cost of roads that connect every city, by Kruskal's algorithm: the roads in order of cost
    * (the costs packed with the roads' places into Longs and sorted as unboxed Longs), each taken when it joins two sets
    * of a union-find, in O(m log m) time. The roads must connect the cities, and each cost is below 2^(62 - b) for roads
    * numbered by b bits.
    */
  def roadReparation(cities: Int, roads: Vector[(Int, Int, Long)]): BigInt =
    require(cities >= 1 && roads.forall((from, to, cost) => from >= 1 && from <= cities && to >= 1 && to <= cities && cost >= 0), s"no roads $roads over $cities cities")
    val placeBits = 32 - Integer.numberOfLeadingZeros(roads.length)
    require(roads.forall(_._3 < (1L << (62 - placeBits))), "a cost is too large to be packed with the road's place")
    val froms = IArray.from(roads.map(_._1))
    val tos = IArray.from(roads.map(_._2))
    val costs = IArray.from(roads.map(_._3))
    val byCost = IArray.tabulate(roads.length)(place => (costs(place) << placeBits) | place.toLong).sorted
    val placeMask = (1L << placeBits) - 1
    @scala.annotation.tailrec
    def taken(index: Int, sets: UnionFind, count: Int, total: Long): (Int, Long) =
      if index == byCost.length then (count, total)
      else
        val place = (byCost(index) & placeMask).toInt
        sets.union(froms(place), tos(place)) match
          case Some(more) => taken(index + 1, more, count + 1, total + costs(place))
          case None       => taken(index + 1, sets, count, total)
    val (count, total) = taken(0, UnionFind.separate(cities), 0, 0L)
    require(count == cities - 1, s"the roads $roads do not connect $cities cities")
    BigInt(total)

  /** CSES 1681: the routes from level 1 to level n over flights without a cycle, modulo 10^9 + 7, by the table
    * routes(level) = the sum of routes(end) over the flights of the level, routes(n) = 1, filled from the last level of a
    * topological order (Kahn's algorithm) to the first, the flights read from sorted packed Longs, in O((n + m) log m)
    * time.
    */
  def gameRoutes(levels: Int, flights: Vector[(Int, Int)]): BigInt =
    require(levels >= 1 && flights.forall((from, to) => from >= 1 && from <= levels && to >= 1 && to <= levels), s"no flights $flights over $levels levels")
    val lowMask = 0xffffffffL
    val byFrom = IArray.from(flights.map((from, to) => (from.toLong << 32) | to.toLong)).sorted
    val byTo = IArray.from(flights.map((from, to) => (to.toLong << 32) | from.toLong)).sorted
    val firstDeparture = IArray.tabulate(levels + 2)(level => lowerBound(byFrom, level.toLong << 32, 0, byFrom.length))
    val firstArrival = IArray.tabulate(levels + 2)(level => lowerBound(byTo, level.toLong << 32, 0, byTo.length))
    def end(index: Int): Int = (byFrom(index) & lowMask).toInt
    @scala.annotation.tailrec
    def release(index: Int, last: Int, ready: List[Int], missing: BlockedInts): (List[Int], BlockedInts) =
      if index == last then (ready, missing)
      else
        val to = end(index)
        val left = missing(to) - 1
        release(index + 1, last, if left == 0 then to :: ready else ready, missing.updated(to, left))
    @scala.annotation.tailrec
    def order(ready: List[Int], missing: BlockedInts, found: List[Int]): List[Int] = ready match
      case Nil => found
      case level :: rest =>
        val (nextReady, nextMissing) = release(firstDeparture(level), firstDeparture(level + 1), rest, missing)
        order(nextReady, nextMissing, level :: found)
    val arrivals = BlockedInts.tabulate(levels + 1)(level => if level == 0 then 0 else firstArrival(level + 1) - firstArrival(level))
    val lastFirst = order((1 to levels).filter(arrivals(_) == 0).toList, arrivals, Nil)
    require(lastFirst.length == levels, s"the flights $flights have a cycle")
    @scala.annotation.tailrec
    def summed(index: Int, last: Int, known: BlockedInts, total: Long): Int =
      if index == last then (total % modulus).toInt else summed(index + 1, last, known, total + known(end(index)))
    val routes = lastFirst.foldLeft(BlockedInts.tabulate(levels + 1)(_ => 0)) { (known, level) =>
      known.updated(level, if level == levels then 1 else summed(firstDeparture(level), firstDeparture(level + 1), known, 0L))
    }
    BigInt(routes(1))

  /** CSES 1646: the sum over the queries of the sum of the values from place a to place b (counted from 1, both included), by prefix
    * sums in an unboxed array of Longs, in O(n + q) time.
    */
  def staticRangeSums(values: IArray[Long], queries: Vector[(Int, Int)]): BigInt =
    require(queries.forall((first, last) => first >= 1 && first <= last && last <= values.length), s"no queries $queries over ${values.length} values")
    val prefixes = values.scanLeft(0L)(_ + _)
    queries.foldLeft(BigInt(0))((sum, query) =>
      val (first, last) = query
      sum + BigInt(prefixes(last) - prefixes(first - 1))
    )

  /** CSES 1618: the zeros that end n!, by Legendre's formula, the sum of floor(n / 5^k) over k ≥ 1, in O(log n) time. */
  def trailingZeros(number: Long): BigInt =
    require(number >= 1, s"no factorial of $number")
    @scala.annotation.tailrec
    def zeros(rest: Long, found: Long): Long = if rest == 0 then found else zeros(rest / 5, found + rest / 5)
    BigInt(zeros(number, 0L))

  /** CSES 1082: the sum over i from 1 to n of the sum of the divisors of i, modulo 10^9 + 7, as the sum over d of d times
    * floor(n / d), summed over the runs of d on which floor(n / d) is constant (the sum of d over a run in closed form, its
    * even factor halved, both factors and the quotient reduced modulo 10^9 + 7 before they are multiplied, so that each
    * product fits a Long), in O(√n) time on Longs.
    */
  def sumOfDivisors(limit: Long): BigInt =
    require(limit >= 1, s"no divisors up to $limit")
    @scala.annotation.tailrec
    def runs(first: Long, total: Long): Long =
      if first > limit then total
      else
        val quotient = limit / first
        val last = limit / quotient
        val sum = first + last
        val count = last - first + 1
        val (half, other) = if sum % 2 == 0 then (sum / 2, count) else (sum, count / 2)
        val runSum = (half % modulus) * (other % modulus) % modulus
        runs(last + 1, (total + runSum * (quotient % modulus)) % modulus)
    BigInt(runs(1L, 0L))

  // The fourth batch.

  /** CSES 1083: the number from 1 to n that a list of the other n - 1 distinct numbers leaves out, as n (n + 1) / 2
    * less their sum, in O(n) time.
    */
  def missingNumber(upper: Int, numbers: IArray[Int]): BigInt =
    require(
      upper >= 1 && numbers.length == upper - 1 && numbers.forall(number => number >= 1 && number <= upper) && numbers.distinct.length == numbers.length,
      s"no list ${numbers.mkString(",")} of the numbers of 1 to $upper but one"
    )
    BigInt(upper.toLong * (upper + 1) / 2 - numbers.foldLeft(0L)(_ + _))

  /** CSES 1069: the length of the longest run of one letter, by one linear scan that counts the run that ends at each
    * letter, in O(n) time.
    */
  def repetitions(letters: IArray[Int]): BigInt =
    @scala.annotation.tailrec
    def scanned(index: Int, run: Int, longest: Int): Int =
      if index == letters.length then longest
      else
        val next = if letters(index) == letters(index - 1) then run + 1 else 1
        scanned(index + 1, next, math.max(longest, next))
    BigInt(if letters.isEmpty then 0 else scanned(1, 1, 1))

  /** CSES 1090: the fewest gondolas that carry the children, each gondola one child or two whose weights sum to at most
    * x, by sorting the weights and, from the lightest and the heaviest, pairing them when they fit and sending the
    * heaviest alone when they do not, with two pointers, in O(n log n) time. Each weight must be at most x.
    */
  def ferrisWheel(capacity: Int, weights: IArray[Int]): BigInt =
    require(weights.forall(weight => weight >= 1 && weight <= capacity), s"a weight of ${weights.mkString(",")} is above $capacity")
    val sorted = weights.sorted
    @scala.annotation.tailrec
    def carried(light: Int, heavy: Int, gondolas: Int): Int =
      if light > heavy then gondolas
      else if light == heavy then gondolas + 1
      else if sorted(light).toLong + sorted(heavy) <= capacity then carried(light + 1, heavy - 1, gondolas + 1)
      else carried(light, heavy - 1, gondolas + 1)
    BigInt(carried(0, sorted.length - 1, 0))

  /** CSES 1640, narrowed to the count: the pairs of places i < j whose values sum to x, by sorting and moving two
    * pointers in from both ends; where the two ends are equal, every pair of the run counts, and where they are not, the
    * two runs of equal values at the ends count the product of their lengths, in O(n log n) time.
    */
  def sumOfTwoValues(target: Long, values: IArray[Long]): BigInt =
    val sorted = values.sorted
    @scala.annotation.tailrec
    def runEnd(index: Int, step: Int): Int =
      if index + step >= 0 && index + step < sorted.length && sorted(index + step) == sorted(index) then runEnd(index + step, step) else index
    @scala.annotation.tailrec
    def paired(low: Int, high: Int, found: Long): Long =
      if low >= high then found
      else
        val sum = sorted(low) + sorted(high)
        if sum < target then paired(low + 1, high, found)
        else if sum > target then paired(low, high - 1, found)
        else if sorted(low) == sorted(high) then found + (high - low + 1).toLong * (high - low) / 2
        else
          val lowEnd = runEnd(low, 1)
          val highEnd = runEnd(high, -1)
          paired(lowEnd + 1, highEnd - 1, found + (lowEnd - low + 1).toLong * (high - highEnd + 1))
    BigInt(paired(0, sorted.length - 1, 0L))

  /** CSES 1660: the contiguous subarrays of positive values that sum to x, by two pointers: the right end moves over each
    * place, and the left end moves right while the window's sum is above x, in O(n) time.
    */
  def subarraySums(target: Long, values: IArray[Long]): BigInt =
    require(values.forall(_ >= 1), s"a value of ${values.mkString(",")} is not positive")
    @scala.annotation.tailrec
    def shrunk(left: Int, right: Int, sum: Long): (Int, Long) =
      if sum > target then shrunk(left + 1, right, sum - values(left)) else (left, sum)
    @scala.annotation.tailrec
    def windows(right: Int, left: Int, sum: Long, found: Long): Long =
      if right == values.length then found
      else
        val (nextLeft, nextSum) = shrunk(left, right, sum + values(right))
        windows(right + 1, nextLeft, nextSum, if nextSum == target then found + 1 else found)
    BigInt(windows(0, 0, 0L, 0L))

  /** CSES 1647: the sum over the queries of the least value from place a to place b (counted from 1, both included), by a sparse
    * table, level k holding the least of each window of 2^k values, so that a query is the least of two overlapping
    * windows, built in O(n log n) time and answered in O(1) each.
    */
  def staticRangeMinimums(values: IArray[Int], queries: Vector[(Int, Int)]): BigInt =
    require(queries.forall((first, last) => first >= 1 && first <= last && last <= values.length), s"no queries $queries over ${values.length} values")
    @scala.annotation.tailrec
    def levels(table: Vector[IArray[Int]]): Vector[IArray[Int]] =
      val width = 1 << table.length
      if width > values.length then table
      else
        val below = table.last
        levels(table :+ IArray.tabulate(values.length - width + 1)(place => math.min(below(place), below(place + (width >> 1)))))
    val table = levels(Vector(values))
    queries.foldLeft(BigInt(0))((sum, query) =>
      val (first, last) = query
      val level = 31 - Integer.numberOfLeadingZeros(last - first + 1)
      sum + BigInt(math.min(table(level)(first - 1), table(level)(last - (1 << level))))
    )

  /** CSES 1131: the longest distance between two nodes of a tree, by two breadth-first searches: from any node to its
    * farthest node, then from that node to its farthest, in O(n) time.
    */
  def treeDiameter(nodes: Int, edges: Vector[(Int, Int)]): BigInt =
    val neighbours = treeNeighbours(nodes, edges)
    val first = treeSearch(neighbours, nodes, 1)
    val second = treeSearch(neighbours, nodes, first.order(nodes - 1))
    BigInt(second.distance(second.order(nodes - 1)))

  /** CSES 1130: the most edges of a tree that share no node, by the greedy that goes from the leaves up: in the reverse of
    * a breadth-first order from the root, a node joins the edge to its parent when neither is matched, in O(n) time.
    */
  def treeMatching(nodes: Int, edges: Vector[(Int, Int)]): BigInt =
    val search = treeSearch(treeNeighbours(nodes, edges), nodes, 1)
    @scala.annotation.tailrec
    def matched(index: Int, taken: BlockedInts, count: Int): Int =
      if index == 0 then count
      else
        val node = search.order(index)
        val parent = search.parent(node)
        if taken(node) == 0 && taken(parent) == 0 then matched(index - 1, taken.updated(node, 1).updated(parent, 1), count + 1)
        else matched(index - 1, taken, count)
    BigInt(matched(nodes - 1, BlockedInts.fill(nodes + 1, BlockedInts.updateShift)(0), 0))

  /** The tree's nodes 1 to n and its n - 1 edges, as an undirected `Adjacency`. */
  private def treeNeighbours(nodes: Int, edges: Vector[(Int, Int)]): Adjacency =
    require(
      nodes >= 1 && edges.length == nodes - 1 && edges.forall((from, to) => from >= 1 && from <= nodes && to >= 1 && to <= nodes),
      s"no tree of $nodes nodes with the edges $edges"
    )
    Adjacency.of(nodes, IArray.from(edges.map(_._1) ++ edges.map(_._2)), IArray.from(edges.map(_._2) ++ edges.map(_._1)))

  /** The nodes of a tree in the order a breadth-first search from the start reaches them, the parent of each (0 for the
    * start) and its distance from the start (-1 for a node not reached).
    */
  private final case class TreeSearch(order: BlockedInts, parent: BlockedInts, distance: BlockedInts)

  /** The breadth-first search of the tree from the start, which reaches every node, in O(n) time. */
  private def treeSearch(neighbours: Adjacency, nodes: Int, start: Int): TreeSearch =
    @scala.annotation.tailrec
    def reached(index: Int, last: Int, from: Int, found: TreeSearch): TreeSearch =
      if index == last then found
      else
        val neighbour = neighbours.payload(index)
        if found.distance(neighbour) >= 0 then reached(index + 1, last, from, found)
        else
          reached(
            index + 1,
            last,
            from,
            TreeSearch(found.order.appended(neighbour), found.parent.updated(neighbour, from), found.distance.updated(neighbour, found.distance(from) + 1))
          )
    @scala.annotation.tailrec
    def search(head: Int, found: TreeSearch): TreeSearch =
      if head == found.order.length then found
      else
        val node = found.order(head)
        search(head + 1, reached(neighbours.first(node), neighbours.first(node + 1), node, found))
    val found = search(
      0,
      TreeSearch(
        BlockedInts.emptyInBlocks(BlockedInts.updateShift).appended(start),
        BlockedInts.fill(nodes + 1, BlockedInts.updateShift)(0),
        BlockedInts.fill(nodes + 1, BlockedInts.updateShift)(-1).updated(start, 0)
      )
    )
    require(found.order.length == nodes, s"the edges do not make a tree of $nodes nodes")
    found

  /** CSES 1753: the places of the text where the pattern occurs, by the Knuth-Morris-Pratt prefix function of the
    * pattern, a separator that no letter equals, and the text: a place counts where the longest prefix of the pattern that
    * ends there is the whole pattern, in O(n + m) time.
    */
  def stringMatching(text: IArray[Int], pattern: IArray[Int]): BigInt =
    require(pattern.nonEmpty && (text ++ pattern).forall(_ >= 0), "no pattern, or a letter below 0")
    val combined = (pattern :+ -1) ++ text
    @scala.annotation.tailrec
    def fallback(table: BlockedInts, length: Int, letter: Int): Int =
      if length > 0 && combined(length) != letter then fallback(table, table(length - 1), letter)
      else if combined(length) == letter then length + 1
      else length
    @scala.annotation.tailrec
    def prefixes(index: Int, table: BlockedInts, found: Int): Int =
      if index == combined.length then found
      else
        val length = fallback(table, table(index - 1), combined(index))
        prefixes(index + 1, table.appended(length), if length == pattern.length then found + 1 else found)
    BigInt(prefixes(1, BlockedInts.emptyInBlocks(BlockedInts.updateShift).appended(0), 0))

  /** CSES 1712: a^(b^c) modulo 10^9 + 7, 0^0 being 1: where b^c is 0 (b = 0, c > 0) the power is a^0 = 1; where 10^9 + 7
    * divides a the answer is 0; otherwise Fermat's little theorem lets b^c be reduced modulo 10^9 + 6, which is found by
    * exponentiation by squaring, and then a is raised to it by the same, in O(log b c) time on Longs.
    */
  def exponentiationTwo(base: Long, exponentBase: Long, exponentPower: Long): BigInt =
    require(base >= 0 && exponentBase >= 0 && exponentPower >= 0, s"no powers of $base, $exponentBase, $exponentPower")
    @scala.annotation.tailrec
    def powered(square: Long, remaining: Long, product: Long, residue: Long): Long =
      if remaining == 0 then product
      else powered(square * square % residue, remaining >> 1, if (remaining & 1) == 1 then product * square % residue else product, residue)
    if exponentBase == 0 && exponentPower > 0 then BigInt(1)
    else if base % modulus == 0 then BigInt(0)
    else
      val exponent = powered(exponentBase % (modulus - 1), exponentPower, 1L, modulus - 1)
      BigInt(power(base, exponent))

  /** The weighted paths of `problems/speculative_untabling`: the value of node 0 of a directed acyclic graph whose
    * every edge goes from a node to a later one, a node's value being its weight plus its successors' values modulo
    * 10^9 + 7, and its weight its seed after K steps of x ↦ x² + 1 modulo 10^9 + 7. Each distinct seed's weight is
    * iterated once, and each node's value is summed once, from the last node to the first, in O(d K + n + m) time for d
    * distinct seeds, n nodes and m edges. The iteration has no closed form, and K is far below the length of its cycle
    * modulo the prime (about √p), so nothing shorter than K steps per seed is known.
    */
  def weightedPaths(steps: Int, seeds: Vector[Int], successors: Vector[Vector[Int]]): BigInt =
    require(steps >= 0 && seeds.nonEmpty && seeds.size == successors.size, s"no weighted paths of $steps steps, ${seeds.size} seeds, ${successors.size} nodes")
    require(successors.zipWithIndex.forall((after, node) => after.forall(successor => successor > node && successor < seeds.size)), "an edge that is not to a later node")
    @scala.annotation.tailrec
    def iterated(value: Long, remaining: Int): Long =
      if remaining == 0 then value else iterated((value * value + 1) % modulus, remaining - 1)
    val weights: Map[Int, Long] = seeds.distinct.map(seed => seed -> iterated(seed.toLong, steps)).toMap
    // The values of the nodes after the current one, node n - 1 first: the value of node j is at index j - (node + 1).
    val values = (seeds.size - 1 to 0 by -1).foldLeft(Vector.empty[Long]) { (later, node) =>
      successors(node).foldLeft(weights(seeds(node)))((total, successor) => (total + later(successor - node - 1)) % modulus) +: later
    }
    BigInt(values.head)
