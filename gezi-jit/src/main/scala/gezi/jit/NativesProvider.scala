package gezi.jit

import scala.jdk.CollectionConverters.*

/** What a natives project registers with `java.util.ServiceLoader`,
  * in `META-INF/services/gezi.jit.NativesProvider` of its project
  * `contest-natives-<name>/`: the native implementations its `native` declarations bind,
  * beside the framework's own (the base knowledge's natives among them,
  * `BinaryNaturalNatives`). The framework finds them by the service, so no
  * entry's data and no framework code names a natives project's class. An
  * implementation has a public constructor of no parameter.
  *
  * A native takes and gives backend values; it reads no term and no
  * e-graph, chooses no round or cost, and does not check its own operands
  * (`CONTRIBUTING.md`, "Types live only in the term").
  */
trait NativesProvider:

  /** The provider's natives and data families, which the framework adds to
    * its own (`NativesProvider.combined`).
    */
  def natives: NativeBackend

object NativesProvider:

  /** The framework's natives with those of every provider on the
    * classpath: on a data entry's, the base natives' provider and its own
    * natives project's, if it has one (`combined`).
    */
  def loaded: NativeBackend =
    combined(
      java.util.ServiceLoader
        .load(classOf[NativesProvider])
        .stream()
        .toList
        .asScala
        .toVector
        .map(_.get.natives)
    )

  /** The standard set with the providers' natives and families added.
    * Throws `IllegalStateException` when a native or a family is named twice,
    * in the standard set and a provider or in two providers: with more than
    * one provider on a classpath, `NativeBackend.extended` would let one
    * replace another's silently, in the order the service loader found them
    * (found in review, 2026-11-07).
    */
  def combined(providers: Vector[NativeBackend]): NativeBackend =
    providers.foldLeft(NativeBackend.standard)((sofar, more) =>
      val natives = more.natives.keySet.intersect(sofar.natives.keySet)
      val families = more.families.map(_.identity).toSet.intersect(sofar.families.map(_.identity).toSet)
      if natives.nonEmpty || families.nonEmpty then
        throw IllegalStateException(
          s"natives or families given twice by the natives providers: ${(natives.map(_.toString) ++ families.map(_.shown)).toVector.sorted.mkString(", ")}"
        )
      sofar.extended(more)
    )
