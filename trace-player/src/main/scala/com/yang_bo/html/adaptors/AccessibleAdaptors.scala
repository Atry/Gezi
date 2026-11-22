package com.yang_bo.html.adaptors

import com.yang_bo.html.AttributeAdaptor
import com.yang_bo.html.BindingSeqNodeAdaptor

/** html.scala's adaptor givens, made reachable from the trace player's code.
  *
  * FIXME (a defect of html.scala 3.0.3+61-a38243c3 under this build's Scala https://github.com/Atry/private-overlay/issues/2031
  * 3.10, measured on 2026-11-09): the `html"..."` macro looks up, at the call
  * site, an `AttributeAdaptor` for every interpolated attribute and a
  * `BindingSeqNodeAdaptor` for an interpolated `Binding` of a node, givens of
  * companions that the library declares `private[html]`. From a call site
  * outside the package `com.yang_bo.html` the search finds none ("no implicit
  * values were found that match type com.yang_bo.html.AttributeAdaptor[...]"),
  * while the same `html"<span id=$key></span>"` compiles in that package, and
  * the same givens re-declared publicly elsewhere are found: the givens are
  * not accessible from the call site. This object, in a subpackage of
  * `com.yang_bo.html` (which `private[html]` admits; the package itself
  * already has html.scala's package object, and a second would clash),
  * exports them, and the player's views import `AccessibleAdaptors.given`,
  * so that the search finds them in lexical scope. The fix is upstream: an
  * html.scala whose adaptors are not `private[html]`, or that searches them
  * from its own package; this package goes when the player depends on such a
  * release.
  */
object AccessibleAdaptors:
  export AttributeAdaptor.given
  export BindingSeqNodeAdaptor.given
