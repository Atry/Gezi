object Clean:
  import com.yang_bo.gezi.hotspot.Guard
  def locked[Result](body: Guard => Result): Result = body(Guard())
  val asParameter = locked(guard => guard.get(1) + guard.get(2))
  val computedOutside = locked(guard =>
    val computed = 3
    guard.getOrElseUpdate(1, computed)
  )
  val ownGuard = List(1, 2).map(key => Guard().get(key))
  inline def twice(inline step: Int => Int, inline start: => Int): Int = step(
    step(start)
  )
  val throughInline =
    locked(guard => twice(key => guard.get(key), guard.get(0)))
