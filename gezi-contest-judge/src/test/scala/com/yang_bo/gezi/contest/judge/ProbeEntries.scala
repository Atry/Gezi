package com.yang_bo.gezi.contest.judge

import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.nio.file.StandardCopyOption
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** The probe entries of the judge's tests: a class of this test project that is
  * its own `EntryProvider` and `Entry`, copied with its services file into a
  * directory of its own, so that the directory is the probe entry's whole
  * classpath, as an entry project's is beside the runner's.
  */
object ProbeEntries:

  /** A new directory holding the class files of the probe class (the class and
    * its companions, `<Name>.class` and `<Name>$...`) and a services file
    * registering it as the one `EntryProvider`.
    */
  def classes(probeClass: Class[?]): Path =
    val classes = Files.createTempDirectory("judge-probe")
    val packagePath = Paths.get(probeClass.getPackageName.replace('.', '/'))
    val compiled = Paths
      .get(probeClass.getProtectionDomain.getCodeSource.getLocation.toURI)
      .resolve(packagePath)
    val simpleName = probeClass.getSimpleName
    Files.createDirectories(classes.resolve(packagePath))
    Using
      .resource(Files.list(compiled))(_.toList.asScala.toVector)
      .filter(file =>
        file.getFileName.toString == s"$simpleName.class" || file.getFileName.toString
          .startsWith(s"$simpleName$$")
      )
      .foreach(file =>
        Files.copy(
          file,
          classes.resolve(packagePath).resolve(file.getFileName),
          StandardCopyOption.REPLACE_EXISTING
        )
      )
    Files.createDirectories(classes.resolve("META-INF/services"))
    Files.writeString(
      classes.resolve("META-INF/services/com.yang_bo.gezi.contest.entry.EntryProvider"),
      s"${probeClass.getName}\n"
    )
    classes
