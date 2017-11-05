package at.logic.gapt.utils

@deprecated( "Use logger instead", "2.9" )
object metrics {
  def time[T]( key: String )( toTime: => T ): T =
    logger.time( key, key )( toTime )
  def value( key: String, value: => Any ): Unit =
    logger.metric( key, key, value )
}