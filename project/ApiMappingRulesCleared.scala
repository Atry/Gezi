import com.thoughtworks.sbtApiMappings.ApiMappings.autoImport.apiMappingRules
import com.thoughtworks.sbtApiMappings.JavadocIoApiMappingRule
import com.thoughtworks.sbtApiMappings.PlayApiMappingRule
import com.thoughtworks.sbtApiMappings.ScalaApiMappingRule
import com.thoughtworks.sbtApiMappings.SonatypeApiMappingRuleForSbtPlugins
import com.thoughtworks.sbtApiMappings.SparkApiMappingRule
import sbt.*

/** No api mapping rule in any project, so that `doc` runs.
  *
  * FIXME: a workaround (https://github.com/Atry/private-overlay/issues/2055).
  * sbt-best-practice 11.0.0 brings sbt-api-mappings, whose rules
  * (`JavadocIoApiMappingRule`, `SonatypeApiMappingRuleForSbtPlugins`) read
  * `sbt.internal.librarymanagement.mavenint.PomExtraDependencyAttributes`, a
  * class sbt 2.1.0-RC3 lacks: every project's `Compile / doc / apiMappings`
  * failed with `NoClassDefFoundError` (measured 2026-11-21 on `ir/doc`). With
  * the rules empty, scaladoc links no dependency's documentation by URL; a link
  * to a member of a dependency is still resolved, by its TASTy. Remove this
  * plugin when sbt-best-practice is upgraded to a release whose rules run on
  * the build's sbt.
  *
  * It requires every rule plugin that triggers on its own, so that its setting
  * is applied after theirs.
  */
object ApiMappingRulesCleared extends AutoPlugin {

  override def trigger = allRequirements

  override def requires =
    JavadocIoApiMappingRule && SonatypeApiMappingRuleForSbtPlugins && ScalaApiMappingRule && PlayApiMappingRule &&
      SparkApiMappingRule

  override def projectSettings: Seq[Setting[?]] = Seq(
    apiMappingRules := PartialFunction.empty
  )
}
