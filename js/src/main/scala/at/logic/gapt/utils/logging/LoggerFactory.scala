package at.logic.gapt.utils.logging

import at.logic.gapt.utils.logging.Logger.Interface

object LoggerFactory {
  var level = 5

  def getLogger( name: String ): Interface =
    new Interface {
      def error( msg: => String ) = if ( level > 0 ) println( s"ERROR $name $msg" )
      def warn( msg: => String ) = if ( level > 1 ) println( s"WARN $name $msg" )
      def info( msg: => String ) = if ( level > 2 ) println( s"INFO $name $msg" )
      def debug( msg: => String ) = if ( level > 3 ) println( s"DEBUG $name $msg" )
      def trace( msg: => String ) = if ( level > 4 ) println( s"TRACE $name $msg" )
    }
}

