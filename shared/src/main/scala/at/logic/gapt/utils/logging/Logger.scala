package at.logic.gapt.utils.logging

import at.logic.gapt.utils.logging.Logger.Interface

trait Logger {
  protected def loggerName = getClass.getName
  protected val log: Interface = LoggerFactory.getLogger( loggerName )

  protected def error( msg: => String ) = log.error( msg )
  protected def warn( msg: => String ) = log.warn( msg )
  protected def info( msg: => String ) = log.info( msg )
  protected def debug( msg: => String ) = log.debug( msg )
  protected def trace( msg: => String ) = log.trace( msg )
}

private[logging] object Logger {
  trait Interface {
    def error(msg: => String): Unit
    def warn(msg: => String): Unit
    def info(msg: => String): Unit
    def debug(msg: => String): Unit
    def trace(msg: => String): Unit
  }
}

