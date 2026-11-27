package com.yang_bo.gezi.narrowblocks.groups

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import scala.jdk.CollectionConverters.*
import com.yang_bo.gezi.generatedinputs.FailFastSuite
import snapshot4s.generated.snapshotConfig

/** Which kernels of the JVM array group backend (`JvmArrayKernels`) HotSpot's
  * C2 compiles to vector instructions. A fresh JVM, the one this test runs on,
  * loads the kernels' class file under its fixed name and runs each kernel
  * 20000 times on arrays of 4096 cells (the outer product's left factor at 64 ×
  * 64), compiled at once by C2 alone (`-Xbatch`, no on-stack replacement), with
  * AVX2 (`-XX:UseAVX=2`), printing each kernel's one C2 compilation; the test
  * disassembles the printed machine code with the `objdump` the dev shell names
  * (`GEZI_OBJDUMP`). A second JVM runs the same with C2's vectorization turned
  * off (`-XX:-UseSuperWord`), the control: an expected instruction absent there
  * comes from the vectorized loop, not from elsewhere in the compiled method.
  *
  * The expectation, derived before the run from the kernels' shapes and a first
  * reading of each kernel's C2 compilation on this machine: each kernel of
  * `expectedVectorInstructions` holds its instruction; the vector instructions
  * of every kernel are recorded as a snapshot, so that a JVM or a machine that
  * vectorizes otherwise shows as a diff to read, not as a failure of the
  * expectation alone.
  *
  * Its purpose is to catch a kernel whose loop no longer vectorizes after a
  * change of the generator, which no law of the values would show.
  */
class JvmArrayKernelsSimdTest
    extends FailFastSuite
    with snapshot4s.munit.SnapshotAssertions:

  /** The two child JVMs' runs with the printing of their compilations and the
    * disassembly, measured at 5.5 s and 5.8 s together on 6 cores at nice 10
    * (2026-11-24); a minute bounds them with room.
    */
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(60, "s")

  private val kernels: Vector[String] =
    JvmArrayKernels.elementwiseNames ++ Vector(
      "negated",
      "gathered",
      "repeated",
      "tiled",
      "compressed",
      "compressedZeros",
      "concatenated",
      "iota"
    )
      ++ Vector(
        "packed",
        "high",
        "low",
        "sortedUnique",
        "mergeJoined",
        "histogram",
        "filled",
        "ranked",
        "firstRows"
      )

  /** The driver the child JVM runs, a Java source file launched by its source:
    * each kernel called 20000 times on its arrays, every result read so that no
    * call is dead.
    */
  private def driver(simpleName: String): String =
    val binary = Vector(
      "added",
      "subtracted",
      "multiplied",
      "equal",
      "lessThan",
      "gathered",
      "concatenated"
    )
    val calls = binary.map(name =>
      s"sum += $simpleName.$name(left, right)[k & 4095];"
    ) ++ Vector(
      s"sum += $simpleName.negated(left)[k & 4095];",
      s"sum += $simpleName.compressed(left).length;",
      s"sum += $simpleName.compressedZeros(mask).length;",
      s"sum += $simpleName.repeated(64, 64)[k & 4095];",
      s"sum += $simpleName.tiled(64, 64)[k & 4095];",
      s"sum += $simpleName.iota(4096)[k & 4095];",
      s"sum += $simpleName.packed(left, Integer.MIN_VALUE, right, 0)[k & 4095];",
      s"sum += $simpleName.high(keys, Integer.MIN_VALUE)[k & 4095];",
      s"sum += $simpleName.low(keys, 0)[k & 4095];",
      s"sum += $simpleName.sortedUnique(keys).length;",
      s"sum += $simpleName.mergeJoined(keys, keys).length;",
      s"sum += $simpleName.histogram(right, 4096)[k & 4095];",
      s"sum += $simpleName.filled(4096, k)[k & 4095];",
      s"sum += $simpleName.ranked(keys, keys)[k & 4095];",
      s"sum += $simpleName.firstRows(right, 4096)[k & 4095];"
    )
    s"""import com.yang_bo.gezi.narrowblocks.groups.$simpleName;
       |public final class KernelDriver {
       |  public static void main(String[] arguments) {
       |    int[] left = new int[4096], right = new int[4096];
       |    int[] mask = new int[4096];
       |    for (int i = 0; i < 4096; i++) { left[i] = i * 7 - 9000; right[i] = (i * 13) & 4095; mask[i] = i & 1; }
       |    long[] keys = $simpleName.sortedUnique($simpleName.packed(right, 0, $simpleName.iota(4096), 0));
       |    long sum = 0;
       |    for (int k = 0; k < 20000; k++) {
       |      ${calls.mkString("\n      ")}
       |    }
       |    System.out.println(sum);
       |  }
       |}
       |""".stripMargin

  /** Each kernel's machine code from its one C2 compilation, by name. */
  private def compiledCode(printed: Vector[String]): Map[String, Vector[Byte]] =
    val header = """Compiled method \(c2\).*JvmArrayKernelClass::(\w+).*""".r
    val code = """\s+0x[0-9a-f]+: ([0-9a-f |]+)$""".r
    printed
      .foldLeft(
        (Map.empty[String, Vector[Byte]], Option.empty[String], false)
      ) {
        case ((found, _, _), header(name)) => (found, Some(name), false)
        case ((found, Some(name), _), line) if line.startsWith("[MachCode]") =>
          (found.updated(name, Vector.empty), Some(name), true)
        case ((found, Some(_), true), line) if line.startsWith("[/MachCode]") =>
          (found, None, false)
        case ((found, Some(name), true), code(hex)) =>
          val bytes = hex
            .split('|')
            .toVector
            .map(_.replace(" ", ""))
            .flatMap(group =>
              group.grouped(2).map(Integer.parseInt(_, 16).toByte)
            )
          (
            found.updated(name, found.getOrElse(name, Vector.empty) ++ bytes),
            Some(name),
            true
          )
        case ((found, current, inside), _) => (found, current, inside)
      }
      ._1

  /** The vector instructions of the machine code other than moves, each with
    * the widest register it names, distinct and sorted.
    */
  private def vectorInstructions(
      objdump: String,
      directory: Path,
      name: String,
      bytes: Vector[Byte]
  ): Vector[String] =
    val binary = directory.resolve(s"$name.bin")
    scala.util.Using.resource(Files.newOutputStream(binary))(stream =>
      bytes.foreach(byte => stream.write(byte.toInt))
    )
    val listing = run(
      Vector(
        objdump,
        "-D",
        "-b",
        "binary",
        "-m",
        "i386:x86-64",
        binary.toString
      ),
      directory
    )
    val instruction = """\s*[0-9a-f]+:\t[0-9a-f ]+\t(v[a-z0-9]+)\s+(.*)""".r
    listing
      .collect {
        case instruction(mnemonic, operands)
            if !mnemonic.startsWith("vmov") && mnemonic != "vzeroupper" =>
          s"$mnemonic ${if operands.contains("%ymm") then "ymm" else "xmm"}"
      }
      .distinct
      .sorted

  private def run(command: Vector[String], directory: Path): Vector[String] =
    val process = ProcessBuilder(command.asJava)
      .directory(directory.toFile)
      .redirectErrorStream(false)
      .start()
    val output =
      String(process.getInputStream.readAllBytes(), StandardCharsets.UTF_8)
    val status = process.waitFor()
    assert(status == 0, s"${command.mkString(" ")} exited with $status")
    output.linesIterator.toVector

  test(
    "the kernels C2 is expected to vectorize hold their vector instructions"
  ) {
    val objdump = sys.env.getOrElse(
      "GEZI_OBJDUMP",
      throw IllegalStateException(
        "the dev shell names no objdump (GEZI_OBJDUMP); start sbt under it"
      )
    )
    val directory = Files.createTempDirectory("jvm-array-kernels")
    val simpleName = JvmArrayKernels.className.split('.').last
    val classFile =
      directory.resolve(JvmArrayKernels.className.replace('.', '/') + ".class")
    Files.createDirectories(classFile.getParent)
    Files.write(classFile, JvmArrayKernels.classBytes)
    Files.writeString(
      directory.resolve("KernelDriver.java"),
      driver(simpleName)
    )
    val java = ProcessHandle.current().info().command().orElseThrow()
    def vectorized(
        superWord: String,
        label: String
    ): Map[String, Vector[String]] =
      val printed = run(
        Vector(
          java,
          "-Xbatch",
          "-XX:-UseOnStackReplacement",
          "-XX:+UnlockDiagnosticVMOptions",
          "-XX:UseAVX=2",
          superWord,
          "-XX:CompileCommand=quiet",
          s"-XX:CompileCommand=print,${JvmArrayKernels.className}::*",
          "-cp",
          directory.toString,
          directory.resolve("KernelDriver.java").toString
        ),
        directory
      )
      val code = compiledCode(printed)
      kernels
        .map(name =>
          name -> vectorInstructions(
            objdump,
            directory,
            s"$label-$name",
            code.getOrElse(name, Vector.empty)
          )
        )
        .toMap
    val found = vectorized("-XX:+UseSuperWord", "vectorized")
    val control = vectorized("-XX:-UseSuperWord", "control")
    def holds(
        instructions: Map[String, Vector[String]],
        name: String,
        mnemonic: String
    ) = instructions(name).exists(_.startsWith(s"$mnemonic "))
    assertFileSnapshot(
      kernels
        .map(name => s"$name: ${found(name).mkString(", ")}")
        .mkString("", "\n", "\n"),
      "jvm_array_kernels/simd.txt"
    )
    assertEquals(
      (
        JvmArrayKernels.expectedVectorInstructions.filterNot((name, mnemonic) =>
          holds(found, name, mnemonic)
        ),
        JvmArrayKernels.expectedVectorInstructions.filter((name, mnemonic) =>
          holds(control, name, mnemonic)
        )
      ),
      (Vector.empty, Vector.empty)
    )
  }
