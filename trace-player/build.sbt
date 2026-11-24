// The trace player (https://github.com/Atry/private-overlay/issues/1497,
// section 6.5), compiled by Scala.js to a classic script: no module
// system (ModuleKind.NoModule), no npm and no bundler, so that a page opened
// from file:// loads it with a relative <script src>. Its main method runs
// when the script loads.
enablePlugins(ScalaJSPlugin)

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

scalaJSLinkerConfig ~= (_.withModuleKind(ModuleKind.NoModule))

scalaJSUseMainModuleInitializer := true

// The tests do not run the main method, which reads the page's DOM, absent
// on Node.js.
Test / scalaJSUseMainModuleInitializer := false

// The tests link as CommonJS modules, which Node.js runs: snapshot4s reads and
// writes its snapshot files through Node.js's module `fs`, which a script with
// no module system cannot import (the linker's error: "needs to be imported
// from module 'fs' but module support is disabled").
Test / scalaJSLinkerConfig ~= (_.withModuleKind(ModuleKind.CommonJSModule))

// The DOM facades of Scala.js. 2.8.1, released 2025-07, the latest release.
// `%%` names the artifact of the platform (generatedinputs-js/build.sbt).
libraryDependencies += "org.scala-js" %% "scalajs-dom" % "2.8.1"

// Binding.scala, html.scala and LatestEvent.scala, the player's interface
// (https://github.com/Atry/private-overlay/issues/1497, section 6.5, "界面"; the
// user, 2026-11-09: "我觉得应该用Binding.scala做控制UI"; "https://github.com/ThoughtWorksInc/LatestEvent.scala
// 可以避免很多Var的使用"). html 3.0.3+61-a38243c3 and latestevent
// 2.0.0+13-cd63a4e2, the latest builds for Scala 3 and Scala.js on Maven
// Central (2026-11-09), are both built against Binding.scala 12.2.0, whose
// `ChangedListener` LatestEvent implements; Binding.scala 13.0.0-M0 replaces
// that API by streams, so binding stays at 12.2.0, named here because the
// player's own code uses it.
libraryDependencies ++= Seq(
  "com.thoughtworks.binding" %% "binding" % "12.2.0",
  "com.thoughtworks.binding" %% "latestevent" % "2.0.0+13-cd63a4e2",
  "com.yang-bo" %% "html" % "3.0.3+61-a38243c3"
)

libraryDependencies += "com.siriusxm" %% "snapshot4s-munit" % "0.2.11" % Test

enablePlugins(Snapshot4sPlugin)

// The styles of the player's controls, Bootstrap 5 and Bootstrap Icons, as
// webjars through sbt-web (the plan's section 6.5, "依赖与打包"; the user,
// 2026-11-09: "同意" to the pure-CSS Bootstrap through sbt-web, with no npm).
// sbt-web copies the player's own style sheet (src/main/assets) and the
// webjars' files (under lib/) into `Assets / WebKeys.assets`. 5.3.8 and
// 1.13.2 are the latest releases of the two npm webjars on Maven Central
// (2026-11-09; bootstrap's 6.0.0-alpha.1 is a prerelease).
enablePlugins(com.typesafe.sbt.web.SbtWeb)

libraryDependencies ++= Seq(
  "org.webjars.npm" % "bootstrap" % "5.3.9",
  "org.webjars.npm" % "bootstrap-icons" % "1.13.2"
)

// The page the player is looked at with: the page that
// TracePageTextSnapshotTest records for a generated trace, in
// target/demonstration, with the linked script and the style sheets in its
// directory trace-player/ (TracePageText.playerDirectory, where every page
// TracePageText.playerPage writes looks for them); open its index.html from
// file://. To play the pages a schedule writes, copy that trace-player/
// directory beside them.
lazy val demonstrationPage = taskKey[File](
  "the trace player's page of a generated trace, with its script and style sheets"
)

// Uncached: the task copies files, and sbt 2 caches no task whose result is
// a File.
demonstrationPage := Def.uncached {
  val report = (Compile / fastLinkJS).value.data
  val linked = (Compile / fastLinkJS / scalaJSLinkerOutputDirectory).value
  val styles = (Assets / com.typesafe.sbt.web.Import.WebKeys.assets).value
  val page =
    baseDirectory.value / "src" / "test" / "resources" / "snapshot" / "trace_page" / "generated_trace.html"
  val destination = target.value / "demonstration"
  val scripts = report.publicModules.map(_.jsFileName).toVector
  assert(
    scripts == Vector("main.js"),
    s"the player links to one script, main.js: $scripts"
  )
  assert(
    page.exists,
    s"the page $page is recorded by TracePageTextSnapshotTest"
  )
  IO.delete(destination)
  IO.copyDirectory(styles, destination / "trace-player")
  IO.copyFile(linked / "main.js", destination / "trace-player" / "main.js")
  IO.copyFile(page, destination / "index.html")
  destination
}
