import sbt.*
import sbt.Keys.*
import snapshot4s.Snapshot4sPlugin
import snapshot4s.Snapshot4sPlugin.autoImport.snapshot4sDirectory

/** Every test run of a project starts with no snapshot patch, so that
  * `snapshot4sPromote` applies only the patches of the last run.
  *
  * snapshot4s 0.2.11 writes a patch (`resource-patch`, `inline-patch` under
  * `snapshot4sDirectory`) when a snapshot assertion fails and never deletes it
  * when the assertion passes later (`snapshot4s.FileSnapshot`, which returns
  * `Success` and leaves the patch file), and `snapshot4sPromote` applies every
  * patch it finds: twice it wrote back a snapshot of a test that had since
  * passed (2026-11-19: membership_steps, rewrite-trace/text-sizes). The patches
  * are deleted when the run starts (`Tests.Setup`), whatever suites it selects:
  * a suite not run again has no patch to promote until it is run.
  */
object SnapshotPatchesOfTheLastRun extends AutoPlugin {

  override def trigger = allRequirements

  override def requires = Snapshot4sPlugin

  override def projectSettings: Seq[Setting[?]] = Seq(
    Test / testOptions += {
      val directory = snapshot4sDirectory.value
      Tests.Setup(() =>
        IO.delete(Seq(directory / "resource-patch", directory / "inline-patch"))
      )
    }
  )
}
