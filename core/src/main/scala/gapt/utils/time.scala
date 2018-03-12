package gapt.utils

object time {
  private val nLine = sys.props( "line.separator" )

  def apply[T]( f: => T ): T = {
    val start = java.lang.System.currentTimeMillis()
    val r = f
    println( nLine + "time: " + ( java.lang.System.currentTimeMillis() - start ) + " ms" + nLine )
    r
  }
}
