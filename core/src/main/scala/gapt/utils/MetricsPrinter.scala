package gapt.utils

import gapt.utils.LogHandler.VerbosityLevel
import org.json4s.native.JsonMethods.{ compact, render }
import org.json4s.{ JArray, JBool, JDouble, JInt, JObject, JString, JValue }

import scala.collection.mutable
import scala.concurrent.duration.Duration

class MetricsPrinter extends LogHandler {
  val data: mutable.Map[String, Any] = mutable.Map[String, Any]()

  def jsonify( v: Any ): JValue = v match {
    case l: Long    => JInt( l )
    case l: Int     => JInt( l )
    case l: BigInt  => JInt( l )
    case l: Double  => JDouble( l )
    case l: Float   => JDouble( l )
    case b: Boolean => JBool( b )
    case l: Seq[_]  => JArray( l map jsonify toList )
    case s          => JString( s toString )
  }

  val phaseStack: mutable.Buffer[String] = mutable.Buffer()
  override def timeBegin( domain: String, level: VerbosityLevel, key: String, desc: String ): Unit =
    if ( key != "total" ) {
      phaseStack += key
      value( "phase", phase )
    }
  override def time( domain: String, level: VerbosityLevel, key: String, desc: String, duration: Duration ): Unit =
    if ( key == "total" ) {
      value( "time_total", duration.toMillis )
    } else {
      value( s"time_$phase", duration.toMillis )
      phaseStack.trimEnd( 1 )
    }
  def phase: String = phaseStack.mkString( "_" )

  override def metric( domain: String, level: VerbosityLevel, key: String, desc: String, v: => Any ): Unit =
    value( key, v )

  def println( string: String ): Unit = Console.println( string )

  def value( key: String, value: => Any ): Unit = {
    data( key ) = value
    println( s"METRICS ${compact( render( JObject( key -> jsonify( data( key ) ) ) ) )}" )
  }

  override def message( domain: String, level: VerbosityLevel, msg: => Any ): Unit = ()
}
