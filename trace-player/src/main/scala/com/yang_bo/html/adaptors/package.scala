package com.yang_bo.html

/** The trace player's bridge to html.scala's `private[html]` adaptor givens,
  * which html.scala's macro does not find from a call site outside its
  * package under Scala 3.10 (FIXME in `AccessibleAdaptors`). Not part of
  * html.scala: it lives in a subpackage of html.scala's package only because
  * `private[html]` admits nothing else.
  */
package object adaptors
