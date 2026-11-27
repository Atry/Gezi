package com.yang_bo.gezi.ffi

import com.yang_bo.gezi.hotspot.ForeignValue

/** Where a continuation-aware method gives the replies of one call, as its last
  * parameter: `resumed` once for each reply, an input symbol of the program's
  * Moore machine, a JVM value or a closed term, from any thread, before or
  * after the method returns; then `completed` once, after which the call has no
  * more replies. Each reply is one branch of the state's transition.
  */
trait ReplyHandler:
  def resumed(reply: ForeignValue): Unit
  def completed(): Unit
