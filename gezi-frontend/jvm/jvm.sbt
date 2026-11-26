enablePlugins(Snapshot4sPlugin)

libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test
libraryDependencies += "com.siriusxm" %% "snapshot4s-munit" % "0.2.11" % Test

Test / fork := true

Test / javaOptions += s"-Dgezi.buildRoot=${baseDirectory.value.getParentFile.getParentFile}"
