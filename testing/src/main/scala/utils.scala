package at.logic.gapt.testing

import java.io._

import at.logic.gapt.utils.executionModels.timeout.{ TimeOutException, withTimeout }
import org.apache.commons.lang3.exception.ExceptionUtils

import scala.collection.mutable
import scala.concurrent.duration._
import scala.sys.process._
import scala.xml.Elem

abstract class RegressionTestCase( val name: String ) extends Serializable {
  protected def test( implicit testRun: TestRun ): Unit

  def timeout: Option[Duration] = None

  def run(): TestRun = {
    val testRun = new TestRun()
    testRun.runStep( None, timeout )( test( testRun ) )
    testRun
  }

  class TestRun {
    case class Step( name: Option[String], exception: Option[Throwable], runtime: Duration, isTimeout: Boolean )

    var steps = mutable.MutableList[Step]()

    private[RegressionTestCase] def runStep[T]( name: Option[String], timeout: Option[Duration] = None )( block: => T ) = {
      val beginTime = System.nanoTime()
      val result = try {
        Right( timeout match {
          case None             => block
          case Some( duration ) => withTimeout( duration )( block )
        } )
      } catch {
        case t: Throwable => Left( t )
      }
      val endTime = System.nanoTime()
      val runtime = ( endTime - beginTime ) nanos

      val ( exception, isTimeout ) = result match {
        case Left( t @ ( _: TimeOutException | _: ThreadDeath ) ) => ( Some( t ), true )
        case Left( t ) => ( Some( t ), false )
        case Right( _ ) => ( None, false )
      }
      steps += Step( name, exception, runtime, isTimeout )

      result
    }

    def toJUnitXml: Elem =
      <testsuite>
        {
          steps map { step =>
            val testCaseName = RegressionTestCase.this.getClass.getSimpleName
            val className = s"$testCaseName.${step.name.getOrElse( "<all>" )}"
            <testcase classname={ className } name={ name } time={ ( step.runtime / 1.second ).toString }>
              {
                for ( t <- step.exception.toSeq )
                  yield <error message={ t.getMessage } type={ t.getClass.getName }>{
                  ExceptionUtils.getStackTrace( t )
                }</error>
              }
              { if ( step.isTimeout ) <skipped/> }
            </testcase>
          }
        }
      </testsuite>
  }

  protected implicit class StepBlock[T]( block: => T ) {
    def ---( name: String )( implicit testRun: TestRun ) =
      testRun.runStep( Some( name ) )( block ) match {
        case Left( t )    => throw t
        case Right( res ) => res
      }
    def --?( name: String )( implicit testRun: TestRun ) =
      testRun.runStep( Some( name ) )( block ) match {
        case Left( t )    => None
        case Right( res ) => Some( res )
      }
  }

  protected implicit class StepCondition( block: => Boolean ) {
    def !--( name: String )( implicit testRun: TestRun ) =
      testRun.runStep( Some( name ) ) { require( block, name ) }
  }

  override def toString = s"${getClass.getSimpleName}.$name"
}

object runOutOfProcess {
  def main( args: Array[String] ): Unit = {
    val f: () => Serializable = deserialize( System.in )
    serialize( System.out, f() )
  }

  private def serialize( out: OutputStream, obj: Any ) = {
    val oos = new ObjectOutputStream( out )
    try oos.writeObject( obj ) finally oos.close()
  }

  private def deserialize[T]( in: InputStream ): T = {
    val ois = new ObjectInputStream( in )
    try ois.readObject().asInstanceOf[T] finally ois.close()
  }

  def apply[T <: Serializable]( extraJvmArgs: Seq[String] )( f: => T ): T = {
    var result: Option[T] = None
    val processIO = new ProcessIO(
      in => serialize( in, () => f ),
      out => result = Some( deserialize( out ) ),
      err = BasicIO.toStdErr )

    val javaBinary = new File( new File( System.getProperty( "java.home" ), "bin" ), "java" ).getAbsolutePath
    val process = ( Seq( javaBinary ) ++ extraJvmArgs ++
      Seq( "-cp", System.getProperty( "java.class.path" ),
        getClass.getCanonicalName.dropRight( 1 ) ) ) run processIO
    process.exitValue()

    result.get
  }
}

object recursiveListFiles {
  def apply( fn: String ): List[File] = apply( new File( fn ) )

  def apply( f: File ): List[File] =
    if ( f.isDirectory )
      f.listFiles.toList.flatMap( apply )
    else
      List( f )
}
