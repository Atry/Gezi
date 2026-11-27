libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test
libraryDependencies ++= Seq(
  "qa.hedgehog" %% "hedgehog-core" % "0.15.1" % Test,
  "qa.hedgehog" %% "hedgehog-runner" % "0.15.1" % Test
)

Test / fork := true
