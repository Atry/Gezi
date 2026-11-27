// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

publish / skip := true

// The generator runs forked, with the build's root, from which the library,
// the fixtures and wren's entry are read (`LibraryFiles.buildRoot`).
Test / fork := true

Test / javaOptions += s"-Dgezi.buildRoot=${baseDirectory.value.getParentFile}"

// Writes the trace player's end-to-end showcase, Gezi's directory
// trace-showcase (https://github.com/Atry/private-overlay/issues/1807): the
// player's script linked by fullLinkJS and its style sheets, given with the
// directory to the generator gezi.traceshowcase.ShowcasePages, which deletes
// the directory and writes it again whole. gezi/.gitattributes marks the
// directory generated and names this task.
lazy val regenerate = taskKey[Unit](
  "writes the trace player's end-to-end showcase into gezi's directory trace-showcase"
)

lazy val tracePlayer = LocalProject("trace-player")

// Uncached: the task writes files outside sbt's view.
regenerate := Def.uncached(Def.taskDyn {
  val _ = (tracePlayer / Compile / fullLinkJS).value
  val script =
    (tracePlayer / Compile / fullLinkJS / scalaJSLinkerOutputDirectory).value / "main.js"
  val assets =
    (tracePlayer / Assets / com.typesafe.sbt.web.Import.WebKeys.assets).value
  val destination = baseDirectory.value.getParentFile / "trace-showcase"
  (Test / runMain).toTask(
    s" gezi.traceshowcase.ShowcasePages $destination $script $assets"
  )
}.value)
