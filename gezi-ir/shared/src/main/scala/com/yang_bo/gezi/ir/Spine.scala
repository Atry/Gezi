package com.yang_bo.gezi.ir

import com.yang_bo.gezi.ir.Interned.Interned

/** The spine of an interned term of any union of layers that admits [[Apply]]:
  * its head and its arguments, the first applied first, read from the flat copy
  * an application stores (`Apply.spineHead`, `Apply.spineArguments`), so that
  * reading a spine costs no walk along its prefixes. A term that is no
  * application is its own head, with no argument.
  *
  * `case Spine(head, first, second) =>` matches an application of exactly two
  * arguments; `case Spine(head, arguments*) =>` any application.
  */
object Spine:

  /** The head and the arguments of the term; the term and no argument when it
    * is no application.
    */
  def of[Layer[_]](
      term: Interned[Layer]
  ): (Interned[Layer], Vector[Interned[Layer]]) = term.layer match
    case application: Apply[Interned[Layer] @unchecked] =>
      (application.spineHead, application.spineArguments)
    case _ => (term, Vector.empty)

  /** The head and the arguments of an application; none for a term that is no
    * application.
    */
  def unapplySeq[Layer[_]](
      term: Interned[Layer]
  ): Option[(Interned[Layer], Seq[Interned[Layer]])] = term.layer match
    case application: Apply[Interned[Layer] @unchecked] =>
      Some((application.spineHead, application.spineArguments))
    case _ => None
