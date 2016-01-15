package at.logic.gapt.utils

object time {
  val nLine = "\n"

  def apply[T]( f: => T ): T = {
    val start = java.lang.System.currentTimeMillis()
    val r = f
    println( nLine + "time: " + ( java.lang.System.currentTimeMillis() - start ) + " ms" + nLine )
    r
  }
}
