package gezi.contest.runner

import java.lang.foreign.Arena
import java.lang.foreign.FunctionDescriptor
import java.lang.foreign.Linker
import java.lang.foreign.ValueLayout
import scala.util.Using

/** One instruction of a classic BPF program (`struct sock_filter`,
  * linux/filter.h): the operation code, the two jump offsets and the operand,
  * in the 8 bytes the kernel reads, as one little-endian long.
  */
final case class FilterInstruction(
    code: Int,
    jumpIfTrue: Int,
    jumpIfFalse: Int,
    operand: Long
):
  def encoded: Long =
    (code & 0xffff).toLong | ((jumpIfTrue & 0xff).toLong << 16) | ((jumpIfFalse & 0xff).toLong << 24) | ((operand & 0xffffffffL) << 32)

/** The seccomp filter that denies an entry's JVM the execution of any program:
  * the system calls `execve` and `execveat` fail with EPERM, on every thread of
  * the JVM, for the rest of its life. Threads stay allowed (`clone` is not
  * filtered), so the JVM's own threads run as before; what is denied is
  * starting a program, which is how Java starts a process (`ProcessBuilder`
  * executes the JDK's `jspawnhelper`, then the program).
  *
  * The runner installs it, when the supervisor asks, before it loads the entry,
  * so no code of the entry runs without it. A seccomp filter cannot be removed
  * once installed, by the thread that installed it or by any other. The
  * sandbox's other walls (the file system, the network, other processes) are
  * bubblewrap's, outside the JVM; this one cannot be: bubblewrap and systemd
  * load a seccomp filter before they execute the program they start, so a
  * filter that denies `execve` denies them the JVM itself (measured 2026-10-31
  * with `systemd-run --user -p 'SystemCallFilter=~execve execveat'`: the
  * service was killed by SIGSYS before it ran).
  *
  * The program, on the `struct seccomp_data` of each system call: a call of
  * another architecture than x86_64 (the 32-bit `int 0x80` entry included) is
  * denied; a call of the x32 ABI (its number has bit 30 set) is denied;
  * `execve` (59) and `execveat` (322) are denied; any other call is allowed.
  * Denied means the call returns EPERM.
  */
object ExecutionFilter:

  private val loadWordAbsolute = 0x20
  private val jumpIfEqual = 0x15
  private val jumpIfGreaterOrEqual = 0x35
  private val returnOperand = 0x06

  private val architectureOffset = 4L
  private val numberOffset = 0L

  /** AUDIT_ARCH_X86_64, linux/audit.h. */
  private val x86Architecture = 0xc000003eL

  /** __X32_SYSCALL_BIT, asm/unistd.h. */
  private val x32Bit = 0x40000000L

  private val executeNumber = 59L
  private val executeAtNumber = 322L

  /** SECCOMP_RET_ALLOW. */
  private val allowed = 0x7fff0000L

  /** SECCOMP_RET_ERRNO with EPERM (1). */
  private val deniedWithPermission = 0x00050001L

  val program: Vector[FilterInstruction] = Vector(
    FilterInstruction(loadWordAbsolute, 0, 0, architectureOffset),
    FilterInstruction(jumpIfEqual, 1, 0, x86Architecture),
    FilterInstruction(returnOperand, 0, 0, deniedWithPermission),
    FilterInstruction(loadWordAbsolute, 0, 0, numberOffset),
    FilterInstruction(jumpIfGreaterOrEqual, 3, 0, x32Bit),
    FilterInstruction(jumpIfEqual, 2, 0, executeNumber),
    FilterInstruction(jumpIfEqual, 1, 0, executeAtNumber),
    FilterInstruction(returnOperand, 0, 0, allowed),
    FilterInstruction(returnOperand, 0, 0, deniedWithPermission)
  )

  /** PR_SET_NO_NEW_PRIVS, linux/prctl.h. */
  private val setNoNewPrivileges = 38

  /** The number of the system call `seccomp` on x86_64. */
  private val seccompNumber = 317L

  /** SECCOMP_SET_MODE_FILTER. */
  private val setModeFilter = 1L

  /** SECCOMP_FILTER_FLAG_TSYNC: the filter is installed on every thread of the
    * process at once, the JVM's threads started before it (the collector's, the
    * compilers', the cleaner's) included; the call fails instead if it cannot.
    */
  private val synchronizeThreads = 1L

  /** The filter installed on every thread of this JVM, after `no_new_privs`,
    * which an unprivileged process needs for a filter. Throws
    * `IllegalStateException` on another architecture than x86_64, or when
    * `prctl` or `seccomp` does not return 0.
    */
  def installed(): Unit =
    val architecture = System.getProperty("os.arch")
    if architecture != "amd64" then
      throw IllegalStateException(
        s"the execution filter is written for x86_64, not $architecture; the judge's --sandbox none runs without it"
      )
    val linker = Linker.nativeLinker()
    val library = linker.defaultLookup()
    val processControl = linker.downcallHandle(
      library.find("prctl").orElseThrow(),
      FunctionDescriptor.of(
        ValueLayout.JAVA_INT,
        ValueLayout.JAVA_INT,
        ValueLayout.JAVA_LONG,
        ValueLayout.JAVA_LONG,
        ValueLayout.JAVA_LONG,
        ValueLayout.JAVA_LONG
      ),
      Linker.Option.firstVariadicArg(1)
    )
    val systemCall = linker.downcallHandle(
      library.find("syscall").orElseThrow(),
      FunctionDescriptor.of(
        ValueLayout.JAVA_LONG,
        ValueLayout.JAVA_LONG,
        ValueLayout.JAVA_LONG,
        ValueLayout.JAVA_LONG,
        ValueLayout.ADDRESS
      ),
      Linker.Option.firstVariadicArg(1)
    )
    val noNewPrivileges = processControl
      .invokeWithArguments(setNoNewPrivileges, 1L, 0L, 0L, 0L)
      .asInstanceOf[Int]
    if noNewPrivileges != 0 then
      throw IllegalStateException(
        s"prctl(PR_SET_NO_NEW_PRIVS) returned $noNewPrivileges"
      )
    Using.resource(Arena.ofConfined()) { arena =>
      val filter =
        arena.allocateFrom(ValueLayout.JAVA_LONG, program.map(_.encoded)*)
      // struct sock_fprog: the instructions' count (an unsigned short, padded
      // to 8 bytes) and the address of the first.
      val programHeader = arena.allocateFrom(
        ValueLayout.JAVA_LONG,
        program.size.toLong,
        filter.address()
      )
      val installation = systemCall
        .invokeWithArguments(
          seccompNumber,
          setModeFilter,
          synchronizeThreads,
          programHeader
        )
        .asInstanceOf[Long]
      if installation != 0 then
        throw IllegalStateException(
          s"seccomp(SECCOMP_SET_MODE_FILTER, SECCOMP_FILTER_FLAG_TSYNC) returned $installation"
        )
    }
