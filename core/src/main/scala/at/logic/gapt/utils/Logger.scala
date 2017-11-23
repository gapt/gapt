package at.logic.gapt.utils

import scala.concurrent.duration._
import scala.util.DynamicVariable

sealed trait LogSeverity
object LogSeverity {
  case object Warn extends LogSeverity
  case object Info extends LogSeverity
  case object Debug extends LogSeverity
}
import LogSeverity._

trait LogHandler {
  def message( severity: LogSeverity, msg: => Any ): Unit

  def metric( key: String, desc: String, value: => Any ): Unit =
    message( Info, s"$desc: $value" )

  def time( key: String, desc: String, duration: Duration ): Unit =
    message( Info, s"$desc took ${LogHandler.formatTime( duration )}" )
}
object LogHandler {
  val current = new DynamicVariable[LogHandler]( default )

  def use[T]( handler: LogHandler )( f: => T ): T =
    current.withValue( handler )( f )

  def scope[T]( f: => T ): T =
    use( current.value )( f )

  def formatTime( duration: Duration ): String =
    if ( duration < 1.second ) {
      s"${duration.toMillis}ms"
    } else if ( duration < 10.second ) {
      s"${duration.toMillis / 1000f}s"
    } else {
      s"${duration.toSeconds}s"
    }

  object silent extends LogHandler {
    def message( severity: LogSeverity, msg: => Any ): Unit = ()
  }

  object default extends LogHandler {
    def message( severity: LogSeverity, msg: => Any ): Unit =
      if ( severity == Warn ) Console.err.println( msg )
  }

  object verbose extends LogHandler {
    def message( severity: LogSeverity, msg: => Any ): Unit =
      if ( severity == Warn ) Console.err.println( msg )
      else Console.out.println( msg )
  }

  object tstpVerbose extends LogHandler {
    def message( severity: LogSeverity, msg: => Any ): Unit =
      Console.out.println( s"% ${msg.toString.replace( '\n', ' ' ).replace( '\r', ' ' )}" )
  }
}

object logger {
  def handler = LogHandler.current.value

  def warn( msg: => Any ) = handler.message( Warn, msg )
  def info( msg: => Any ) = handler.message( Info, msg )
  def debug( msg: => Any ) = handler.message( Debug, msg )
  def time[T]( key: String, desc: String )( f: => T ): T = {
    val a = System.nanoTime
    try f finally {
      val b = System.nanoTime
      handler.time( key, desc, ( b - a ).nanos )
    }
  }
  def metric( key: String, desc: String, value: => Any ) =
    handler.metric( key, desc, value )
}

object verbose {
  def apply[T]( f: => T ): T =
    LogHandler.use( LogHandler.verbose )( f )
}

