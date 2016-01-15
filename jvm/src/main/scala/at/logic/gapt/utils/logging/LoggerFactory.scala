package at.logic.gapt.utils.logging

import at.logic.gapt.utils.logging.Logger.Interface

object LoggerFactory {
  def getLogger( name: String ): Interface = {
    val log = org.slf4j.LoggerFactory.getLogger( name )
    new Interface {
      def error( msg: => String ) = if ( log.isErrorEnabled ) log.error( msg )
      def warn( msg: => String ) = if ( log.isWarnEnabled ) log.warn( msg )
      def info( msg: => String ) = if ( log.isInfoEnabled ) log.info( msg )
      def debug( msg: => String ) = if ( log.isDebugEnabled ) log.debug( msg )
      def trace( msg: => String ) = if ( log.isTraceEnabled ) log.trace( msg )
    }
  }
}
