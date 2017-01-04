package at.logic.gapt.utils

import ch.qos.logback.classic.encoder.PatternLayoutEncoder
import ch.qos.logback.classic.{ Level, LoggerContext, Logger => LogbackLogger }
import ch.qos.logback.core.ConsoleAppender
import org.slf4j
import org.slf4j.LoggerFactory

trait Logger {
  private val log = Logger.loggerForClass( getClass )

  // Ordered by level of importance.
  // E.g. if the logging level is chosen to be info, info, warn and error
  // messages will be logged as well, but not debug and trace.
  protected def error( msg: => Any ) = if ( log.isErrorEnabled ) log.error( msg.toString )
  protected def error( msg: => Any, e: Throwable ) = { if ( log.isErrorEnabled ) log.error( msg.toString, e ); throw e }
  protected def warn( msg: => Any ) = if ( log.isWarnEnabled ) log.warn( msg.toString )
  protected def warn( msg: => Any, e: Throwable ) = if ( log.isWarnEnabled ) log.warn( msg.toString, e )
  protected def info( msg: => Any ) = if ( log.isInfoEnabled ) log.info( msg.toString )
  protected def debug( msg: => Any ) = if ( log.isDebugEnabled ) log.debug( msg.toString )
  protected def trace( msg: => Any ) = if ( log.isTraceEnabled ) log.trace( msg.toString )

  def makeVerbose() = Logger.makeVerbose( getClass )
}

object Logger {
  def loggerForClass( clazz: Class[_] ) =
    LoggerFactory.getLogger( clazz.getName.replace( "$", "" ) )

  def setConsolePattern( pattern: String ) = {
    val loggerContext = LoggerFactory.getILoggerFactory.asInstanceOf[LoggerContext]
    val rootLogger = loggerContext.getLogger( slf4j.Logger.ROOT_LOGGER_NAME )
    val appender = rootLogger.getAppender( "STDOUT" ).asInstanceOf[ConsoleAppender[_]]
    val encoder = appender.getEncoder.asInstanceOf[PatternLayoutEncoder]
    encoder.setPattern( pattern )
    encoder.start()
  }

  def useTptpComments() = setConsolePattern( "\\% %message%n" )

  def makeVerbose( clazz: Class[_] ) =
    loggerForClass( clazz ).asInstanceOf[LogbackLogger].
      setLevel( Level.DEBUG )
}

