package at.logic.gapt.utils.logging

import scala.util.DynamicVariable

trait MetricsCollector {
  def time[T]( key: String )( f: => T ): T
  def value( key: String, value: => Any )
}

object IgnoreMetrics extends MetricsCollector {
  override def time[T]( key: String )( f: => T ): T = f
  override def value( key: String, value: => Any ) = ()
}

object PrintMetrics extends MetricsCollector {
  override def time[T]( key: String )( f: => T ): T = f
  override def value( key: String, value: => Any ) = println( s"$key = $value" )
}

object metrics extends MetricsCollector {
  val current = new DynamicVariable[MetricsCollector]( IgnoreMetrics )

  override def time[T]( key: String )( toTime: => T ): T = current.value.time( key )( toTime )
  override def value( key: String, value: => Any ) = current.value.value( key, value )
}