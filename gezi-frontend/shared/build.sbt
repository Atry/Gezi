moduleName := "gezi-frontend"
publish / skip := false

scalacOptions -= "-Xcheckinit"
Test / scalacOptions -= "-Xcheckinit"

libraryDependencies += "com.github.j-mie6" %% "parsley" % "4.6.2"
libraryDependencies += "io.bullet" %% "borer-core" % "1.19.0"
