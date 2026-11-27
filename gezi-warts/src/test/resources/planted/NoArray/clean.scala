object Clean:
  val immutable = IArray(1, 2)
  val first = immutable(0)
  val parts = "a b".split(" ")
  val read = parts(0) + parts.length + parts.toVector
  val wrapped = IArray.unsafeFromArray(parts)

enum Fixity:
  case Prefix, Infix

@main def entry(argument: String): Unit = ()
