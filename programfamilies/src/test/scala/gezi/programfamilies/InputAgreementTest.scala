package gezi.programfamilies

import snapshot4s.generated.snapshotConfig

/** The inputs Scala builds agree with those the Prolog exporter wrote into
  * the 125 fixtures. Its purpose: a change to the front end, the library's
  * compilation, the orientations' compilation or the initial graph that
  * alters any item's input is caught.
  *
  * Each item is a test of its own, named `configuration/item`. Its run's
  * whole input in the exporter's numbering (`ExportedNumbering`: the store,
  * the orientations, the pattern instructions, the input and the budget) and the
  * graph built from that input before the saturation (every node's layer in
  * node order, every filing in filing order, the input's node and the number
  * of nodes the input made) are written as one text (`InputText`), whose
  * digest is the item's snapshot. The snapshots were recorded from the
  * fixtures themselves, the same text written from a fixture's input and its
  * `reference initial_node`, `initial_handle`, `input_node` and
  * `input_nodes_made` records, on 2026-10-31, when Scala's inputs agreed with
  * every fixture; so an item passes exactly when Scala's text is the
  * fixture's. The fixtures are not in the repository, and the test does not
  * read them.
  */
class InputAgreementTest extends gezi.generatedinputs.FailFastSuite with snapshot4s.munit.SnapshotAssertions:

  /** The configurations compiled, forced before the first test and not
    * charged to it (FailFastSuite): charged, they put the suite's first
    * item, `cost_comparison/coverage-applied_booleans`, past its deadline
    * on every run (measured 2026-11-21, at load 7 as well).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => CompiledConfigurations.byName)


  private def digest(configuration: Configuration, item: Item): String =
    val compiled = CompiledConfigurations.byName(configuration.name)
    InputText.digest(InputText.ofRun(FixedPointRuns.input(compiled, item).exported))

  FixedPointLines.itemsInFileOrder.foreach { (configuration, item) =>
    test(s"${configuration.name}/${item.name}") {
      assertFileSnapshot(
        digest(configuration, item) + "\n",
        s"input_digests/${configuration.name}/${item.name}.txt"
      )
    }
  }

  /** Its purpose: the digest tells an input from its neighbour's, so that the
    * snapshots above are not passed by a text that leaves the input out.
    */
  test("theDigestTellsAProgramFromItsNeighbour") {
    val configuration = Configurations.hindleyMilnerBaseline
    val Vector(one, two) =
      configuration.items.filter(item => item.family == "numeral" && Set("1", "2").contains(item.size)): @unchecked
    assertNotEquals(digest(configuration, one), digest(configuration, two))
  }
