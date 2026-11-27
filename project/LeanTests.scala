import sbt.*

/** The tag of the test tasks of the projects whose tests run `lake` in the
  * build's one Lean package, `lean` (`LeanFiniteTerms.lakeOutput`: `lake build`
  * from proofs' `ProofTestFiles`, `lake env lean` from standardlibrary's
  * tests). build.sbt limits it to one task at a time, so that two test JVMs
  * never run `lake` over one `.lake` at once: with sbt 2's two test workers (or
  * more, under `-Dsbt.worker_max_instances`), a proofs suite and a
  * standardlibrary suite could otherwise run lake side by side over the same
  * build outputs, each with a Lean build's memory.
  */
object LeanTests {

  val lean: Tags.Tag = Tags.Tag("lean")

  /** The test groups, each tagged `lean`. The tag goes on the groups and not on
    * the `test` task: sbt tags a forked group's task with
    * `Tags.ForkedTestGroup` and the group's own tags only, not with the tags of
    * the task that runs it (sbt 2.0.12, Defaults.allTestGroupsTask).
    */
  def tagged(groups: Seq[Tests.Group]): Seq[Tests.Group] =
    groups.map(group => group.withTags(group.tags :+ (lean -> 1)))
}
