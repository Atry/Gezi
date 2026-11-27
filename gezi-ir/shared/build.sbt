moduleName := "gezi-ir"
publish / skip := false

scalacOptions -= "-Xcheckinit"
Test / scalacOptions -= "-Xcheckinit"

libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test
libraryDependencies ++= Seq(
  "qa.hedgehog" %% "hedgehog-core" % "0.15.1" % Test,
  "qa.hedgehog" %% "hedgehog-runner" % "0.15.1" % Test
)
