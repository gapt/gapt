package gapt.utils

import gapt.utils.LogHandler.VerbosityLevel

import scala.concurrent.duration._
import scala.util.DynamicVariable

trait LogHandler {
  import LogHandler._

  def message( domain: String, verbosity: VerbosityLevel, msg: => Any ): Unit

  def metric( domain: String, verbosity: VerbosityLevel, key: String, desc: String, value: => Any ): Unit =
    message( domain, verbosity, s"$desc: $value" )

  def timeBegin( domain: String, verbosity: VerbosityLevel, key: String, desc: String ): Unit = ()

  def time( domain: String, verbosity: VerbosityLevel, key: String, desc: String, duration: Duration ): Unit =
    message( domain, verbosity, s"$desc took ${LogHandler.formatTime( duration )}" )
}
object LogHandler {
  val current = new DynamicVariable[LogHandler]( default )

  type VerbosityLevel = Int
  val Warn = 0
  val Info = 1
  val Debug = 2
  case class Verbosity( general: VerbosityLevel, specialCases: Map[String, VerbosityLevel] ) {
    def get( domain: String ): VerbosityLevel = general + specialCases.getOrElse( domain, 0 )
    def get( domain: String, verbosityLevel: VerbosityLevel ): VerbosityLevel = verbosityLevel - get( domain )
    def increase( level: VerbosityLevel ): Verbosity = copy( general = general + level )
    def increase( domains: Iterable[String], level: VerbosityLevel ): Verbosity =
      copy( specialCases = specialCases ++ domains.map( d => ( d, specialCases.getOrElse( d, 0 ) + level ) ) )
    def increase( domains: Iterable[Logger], level: VerbosityLevel )( implicit dummy: DummyImplicit ): Verbosity =
      increase( domains.map( _.domain ), level )
  }
  val verbosity = new DynamicVariable[Verbosity]( Verbosity( 0, Map() ) )

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
    def message( domain: String, level: VerbosityLevel, msg: => Any ): Unit = ()
  }

  object default extends LogHandler {
    def message( domain: String, level: VerbosityLevel, msg: => Any ): Unit =
      if ( level <= Warn ) Console.err.println( s"[$domain] $msg" )
  }

  object tstp extends LogHandler {
    def message( domain: String, level: VerbosityLevel, msg: => Any ): Unit =
      if ( level <= Warn ) Console.out.println( s"% ${msg.toString.replace( "\n", "\n% " )}" )
  }
}

case class Logger( domain: String ) {
  import Logger._
  import LogHandler._
  def warn( msg: => Any ): Unit = message( domain, Warn, msg )
  def info( msg: => Any ): Unit = message( domain, Info, msg )
  def debug( msg: => Any ): Unit = message( domain, Debug, msg )
  def time[T]( key: String )( f: => T ): T = time( key, key )( f )
  def time[T]( key: String, desc: String )( f: => T ): T = {
    handler.timeBegin( domain, Info, key, desc )
    val a = System.nanoTime
    try f finally {
      val b = System.nanoTime
      handler.time( domain, Info, key, desc, ( b - a ).nanos )
    }
  }
  def metric( key: String, value: => Any ): Unit = metric( key, key, value )
  def metric( key: String, desc: String, value: => Any ): Unit =
    handler.metric( domain, Debug, key, desc, value )
}
object Logger extends LogHandler {
  def handler: LogHandler = LogHandler.current.value
  def verbositySetting: LogHandler.Verbosity = LogHandler.verbosity.value

  override def message( domain: String, verbosity: VerbosityLevel, msg: => Any ): Unit =
    handler.message( domain, verbositySetting.get( domain, verbosity ), msg )
  override def metric( domain: String, verbosity: VerbosityLevel, key: String, desc: String, value: => Any ): Unit =
    handler.metric( domain, verbositySetting.get( domain, verbosity ), key, desc, value )
  override def timeBegin( domain: String, verbosity: VerbosityLevel, key: String, desc: String ): Unit =
    handler.timeBegin( domain, verbositySetting.get( domain, verbosity ), key, desc )
  override def time( domain: String, verbosity: VerbosityLevel, key: String, desc: String, duration: Duration ): Unit =
    handler.time( domain, verbositySetting.get( domain, verbosity ), key, desc, duration )
}

private[utils] abstract class VerbosityChanger( by: Int ) {
  def apply[T]( f: => T ): T =
    LogHandler.verbosity.withValue( LogHandler.verbosity.value.increase( by ) )( f )
  def only[T]( loggers: Logger* )( f: => T ): T =
    LogHandler.verbosity.withValue( LogHandler.verbosity.value.increase( loggers.map( _.domain ), by ) )( f )
}
object verbose extends VerbosityChanger( 1 )
object quiet extends VerbosityChanger( -1 )

