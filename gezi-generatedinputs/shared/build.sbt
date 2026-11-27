// Test infrastructure is also a main dependency of other projects' tests.
libraryDependencies += "org.scalameta" %% "munit" % "1.3.6"

libraryDependencies ++= Seq(
  "qa.hedgehog" %% "hedgehog-core" % "0.15.1",
  "qa.hedgehog" %% "hedgehog-runner" % "0.15.1"
)

libraryDependencies += "com.siriusxm" %% "snapshot4s-munit" % "0.2.11"

scalacOptions -= "-Xcheckinit"
Test / scalacOptions -= "-Xcheckinit"
