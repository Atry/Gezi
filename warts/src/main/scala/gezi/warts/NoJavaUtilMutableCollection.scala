package gezi.warts

/** Forbids the mutable collections of `java.util` that the rule names. */
object NoJavaUtilMutableCollection extends ForbiddenSymbols:

  private val mutableCollections: Set[String] = Set(
    "java.util.ArrayList",
    "java.util.LinkedList",
    "java.util.HashMap",
    "java.util.HashSet",
    "java.util.TreeMap",
    "java.util.TreeSet",
    "java.util.ArrayDeque",
    "java.util.PriorityQueue",
    "java.util.Vector",
    "java.util.Stack",
    "java.util.Hashtable",
    "java.util.IdentityHashMap",
    "java.util.WeakHashMap",
    "java.util.LinkedHashMap",
    "java.util.LinkedHashSet",
    "java.util.BitSet",
    "java.util.EnumMap"
  )

  override protected val message: String =
    "mutable java.util collection is disabled"

  override protected def isForbidden(
      fullName: String,
      simpleName: String
  ): Boolean =
    mutableCollections(fullName)
