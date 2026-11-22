// The generator of coursier's bootstrap launchers, the library behind
// `cs bootstrap`: jupyter-kernel/jupyterKernelInstall calls it to put the
// kernel's class path into one launcher, which almond's `--install` needs.
// A Scala 2.13 artifact,
// which sbt 2's Scala 3 build definition reads; 2.1.24 is the version whose
// sources were read (2026-11-10).
libraryDependencies += ("io.get-coursier" %% "coursier-launcher" % "2.1.24").cross(CrossVersion.for3Use2_13)
