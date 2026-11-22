import sbt.*
import sbt.Keys.*

/** Where a project's outputs go under the server's one root output
  * directory (build.sbt, `Global / rootOutputDirectory`).
  *
  * sbt 2 names a project's output directory by its platform, Scala version
  * and module name only (`outputPath`, sbt 2.1.0-RC3 Defaults), so the
  * projects of two worktrees loaded by one server as RootProjects of a
  * meta-build, so that one sbt server manages several worktrees, would share one target, which sbt refuses to load ("Overlapping output
  * directories"). A build other than the server's own puts its projects
  * under `builds/<its base directory's path, URL-encoded>` of the root; the server's own
  * build keeps sbt's default path, so a build loaded on its own is unchanged.
  */
object BuildOutputs extends AutoPlugin {

  override def trigger = allRequirements

  override def requires = plugins.JvmPlugin

  override def projectSettings: Seq[Setting[?]] = Seq(
    outputPath := {
      val default = outputPath.value
      val build = (ThisBuild / baseDirectory).value.getCanonicalFile
      val server = appConfiguration.value.baseDirectory.getCanonicalFile
      if (build == server) default
      // One path segment per base directory, injective (URL encoding escapes
      // every '/' and '%'), so that two builds never share a directory and the
      // segment never leaves the root.
      else s"builds/${java.net.URLEncoder.encode(build.getPath, java.nio.charset.StandardCharsets.UTF_8)}/$default"
    }
  )
}
