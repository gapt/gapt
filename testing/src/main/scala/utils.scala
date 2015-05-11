package at.logic.gapt.testing

import java.io.File

import at.logic.gapt.utils.executionModels.timeout.{ TimeOutException, withTimeout }
import org.apache.commons.lang3.exception.ExceptionUtils

import scala.collection.mutable
import scala.concurrent.duration._
import scala.xml.Node

case class Step( name: Option[String], exception: Option[Throwable], runtime: Duration, isTimeout: Boolean )

abstract class RegressionTestCase( val name: String ) {
  protected def test(): Unit

  def timeout: Option[Duration] = None

  private var steps = mutable.MutableList[Step]()
  def run(): Unit = runStep( None, timeout )( test() )

  def result: Seq[Step] = steps toList

  private def runStep[T]( name: Option[String], timeout: Option[Duration] = None )( block: => T ) = {
    val beginTime = System.nanoTime()
    val result = try {
      Right( timeout match {
        case None             => block
        case Some( duration ) => withTimeout( duration toMillis )( block )
      } )
    } catch {
      case t: Throwable => Left( t )
    }
    val endTime = System.nanoTime()
    val runtime = ( endTime - beginTime ) nanos

    val ( exception, isTimeout ) = result match {
      case Left( _: TimeOutException ) => ( None, true )
      case Left( _: ThreadDeath )      => ( None, true )
      case Left( t )                   => ( Some( t ), false )
      case Right( _ )                  => ( None, false )
    }
    steps += Step( name, exception, runtime, isTimeout )

    result
  }

  protected implicit class StepBlock[T]( block: => T ) {
    def ---( name: String ) = runStep( Some( name ) )( block ) match {
      case Left( t )    => throw t
      case Right( res ) => res
    }
    def --?( name: String ) = runStep( Some( name ) )( block ) match {
      case Left( t )    => None
      case Right( res ) => Some( res )
    }
  }

  protected implicit class StepCondition( block: => Boolean ) {
    def !--( name: String ) = runStep( Some( name ) ) { require( block, name ) }
  }
}

object toJUnitXml {
  private def apply( testCase: RegressionTestCase ): Seq[Node] =
    testCase.result.map { step =>
      val className = s"${testCase.getClass.getSimpleName}.${step.name.getOrElse( "<all>" )}"
      <testcase classname={ className } name={ testCase.name } time={ ( step.runtime / 1.second ).toString }>
        {
          for ( t <- step.exception.toSeq )
            yield <error message={ t.getMessage } type={ t.getClass.getName }>{
            ExceptionUtils.getStackTrace( t )
          }</error>
        }
        { if ( step.isTimeout ) <skipped/> }
      </testcase>
    }

  def apply( testCases: Seq[RegressionTestCase] ): Node =
    <testsuite>
      { for ( tc <- testCases ) yield toJUnitXml( tc ) }
    </testsuite>
}

object recursiveListFiles {
  def apply( fn: String ): List[File] = apply( new File( fn ) )

  def apply( f: File ): List[File] =
    if ( f.isDirectory )
      f.listFiles.toList.flatMap( apply )
    else
      List( f )
}
