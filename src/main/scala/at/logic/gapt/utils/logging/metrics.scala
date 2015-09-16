package at.logic.gapt.utils.logging

import scala.collection.mutable
import scala.util.DynamicVariable

trait MetricsCollector {
  def time[T]( key: String )( f: => T ): T
  def value( key: String, value: => Any )
}

class CollectMetrics extends MetricsCollector {
  var currentPhase: String = ""
  val data = mutable.Map[String, Any]()

  private def add( key: String, value: Long ) =
    data( key ) = data.getOrElse( key, 0 ).toString.toLong + value

  override def time[T]( phase: String )( f: => T ): T = {
    currentPhase = phase

    val beginTime = System.currentTimeMillis()
    val result = f
    val endTime = System.currentTimeMillis()

    add( s"time_$phase", endTime - beginTime )

    result
  }

  override def value( key: String, value: => Any ) = data( key ) = value

  def copy: CollectMetrics = {
    val clone = new CollectMetrics
    clone.currentPhase = currentPhase
    clone.data ++= data
    clone
  }
}

class IgnoreMetrics extends MetricsCollector {
  override def time[T]( key: String )( f: => T ): T = f
  override def value( key: String, value: => Any ) = ()
}

object metrics extends MetricsCollector {
  val current = new DynamicVariable[MetricsCollector]( new IgnoreMetrics )

  override def time[T]( key: String )( toTime: => T ): T = current.value.time( key )( toTime )
  override def value( key: String, value: => Any ) = current.value.value( key, value )
}