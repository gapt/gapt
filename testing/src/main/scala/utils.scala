package at.logic.gapt.testing

import java.io._

import at.logic.gapt.utils.executionModels.timeout.{ TimeOutException, withTimeout }
import org.apache.commons.lang3.exception.ExceptionUtils

import scala.collection.mutable
import scala.concurrent.duration._
import scala.sys.process._
import scala.xml.{ XML, Node }

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

    def toJUnitXml: Node =
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

  def runOutOfProcessToJUnitXML(): Node = {
    val baos = new ByteArrayOutputStream()
    val oos = new ObjectOutputStream( baos )
    oos.writeObject( this )
    oos.close()

    val javaBinary = new File( new File( System.getProperty( "java.home" ), "bin" ), "java" ).getAbsolutePath
    val stdout = Seq( javaBinary, "-Xmx1G", "-Xss30m",
      "-cp", System.getProperty( "java.class.path" ),
      OutOfProcessRunner.getClass.getCanonicalName.replace( "$", "" ),
      toString ) #< new ByteArrayInputStream( baos.toByteArray ) !!

    XML.loadString( stdout )
  }

  override def toString = s"${getClass.getSimpleName}.$name"
}

private object OutOfProcessRunner extends App {
  val testCase = new ObjectInputStream( System.in ).readObject().asInstanceOf[RegressionTestCase]
  print( testCase.run().toJUnitXml )
}

object recursiveListFiles {
  def apply( fn: String ): List[File] = apply( new File( fn ) )

  def apply( f: File ): List[File] =
    if ( f.isDirectory )
      f.listFiles.toList.flatMap( apply )
    else
      List( f )
}
