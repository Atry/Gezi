package com.yang_bo.gezi.hotspot:
  trait ThreadConfined
  final class Guard extends ThreadConfined:
    def get(key: Int): Int = key
    def getOrElseUpdate(key: Int, value: => Int): Int = value

object Planted:
  import com.yang_bo.gezi.hotspot.Guard
  def locked[Result](body: Guard => Result): Result = body(Guard())
  def later(run: => Int): Int = run
  val inLambda = locked(guard => List(1, 2).map(key => guard.get(key)))
  val inEta = locked(guard => List(1, 2).map(guard.get))
  val byName = locked(guard => later(guard.get(1)))
  val inComputation = locked(guard => guard.getOrElseUpdate(1, guard.get(2)))
  val inAnonymousClass =
    locked(guard => new Runnable { def run(): Unit = { val _ = guard.get(1) } })
