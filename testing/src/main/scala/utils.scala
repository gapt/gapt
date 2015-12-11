package at.logic.gapt.testing

import java.io._

import at.logic.gapt.utils.executionModels.timeout.{ TimeOutException, withTimeout }
import at.logic.gapt.utils.withTempFile
import org.apache.commons.lang3.exception.ExceptionUtils

import scala.collection.mutable
import scala.concurrent.duration._
import scala.sys.process._
import scala.xml.Elem

/**
 * Single regression test case, e.g. Prover9TestCase.ALG-123.
 *
 * Subclasses only need to implement [[test()]].
 *
 * @param name  Name of this test case, e.g. "ALG-123".
 */
abstract class RegressionTestCase( val name: String ) extends Serializable {
  /**
   * Perform the actual testing; to be implemented by subclasses.
   *
   * The results of this test run--how long it took, what steps have succeeded, whether an exception has been
   * thrown--is saved in testRun.  More fine-grained reporting can be enabled by using the operators [[StepBlock.---]],
   * [[StepBlock.--?]], and [[StepCondition.!--]].
   *
   * The parameter testRun is implicit so that these operators can be used as binary operators without explicitly
   * specifying the testRun.
   *
   * @param testRun  Saves the results of this test run.
   */
  protected def test( implicit testRun: TestRun ): Unit

  def timeout: Option[Duration] = None

  /**
   * Run this test case (in the same process).
   *
   * @return Results of the test run.
   */
  def run(): TestRun = {
    val testRun = new TestRun()
    try testRun.runStep( None, timeout )( test( testRun ) )
    catch { case _: Throwable => () }
    testRun
  }

  /**
   * Results of running a single regression test case.
   */
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
        case Left( t @ ( _: TimeOutException | _: ThreadDeath | _: OutOfMemoryError | _: InterruptedException | _: StackOverflowError ) ) => ( Some( t ), true )
        case Left( t ) => ( Some( t ), false )
        case Right( _ ) => ( None, false )
      }
      steps += Step( name, exception, runtime, isTimeout )

      if ( isTimeout )
        throw exception.get
      else
        result
    }

    /**
     * JUnit XML result file describing this test run.  The format is compatible with Jenkins.
     */
    def toJUnitXml: Elem =
      <testsuite>
        {
          steps map { step =>
            val testCaseName = RegressionTestCase.this.getClass.getSimpleName
            val className = s"$testCaseName.${step.name.getOrElse( "<all>" )}"
            // This prevents name clashes in jenkins as both + and - are replaced by _
            val escapedName = name.replace( "+", "<p>" ).replace( "-", "<m>" )
            <testcase classname={ className } name={ escapedName } time={ ( step.runtime / 1.second ).toString }>
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
    /**
     * Runs the passed [[block]] as a step in a regression test case.
     *
     * @param name Name of the step.
     * @return The return value of [[block]].
     * @throws Throwable If [[block]] raises an exception, it is rethrown.
     */
    def ---( name: String )( implicit testRun: TestRun ) =
      testRun.runStep( Some( name ) )( block ) match {
        case Left( t )    => throw t
        case Right( res ) => res
      }

    /**
     * Runs the passed [[block]] as a step in a regression test case, ignoring thrown exceptions (but still recording
     * them in the test run).
     *
     * @param name Name of the step
     * @return Some(returnValue), if [[block]] returns returnValue.  None, if [[block]] throws an exception.
     */
    def --?( name: String )( implicit testRun: TestRun ) =
      testRun.runStep( Some( name ) )( block ) match {
        case Left( t )    => None
        case Right( res ) => Some( res )
      }
  }

  protected implicit class StepCondition( block: => Boolean ) {
    /**
     * Verify that [[block]] returns true.  Exceptions thrown in [[block]] are ignored (but still recorded in the test
     * run).
     *
     * @param name Name of the step
     */
    def !--( name: String )( implicit testRun: TestRun ) =
      testRun.runStep( Some( name ) ) { require( block, name ) }
  }

  override def toString = s"${getClass.getSimpleName}.$name"
}

/**
 * Runs a Scala closure in an external JVM, and returns the result (or exception, if thrown).
 */
object runOutOfProcess {
  private type InputType = () => Serializable
  private type OutputType = Either[Throwable, Serializable]

  def main( args: Array[String] ): Unit = try args match {
    case Array( inFile, outFile ) =>
      val f: InputType = deserialize( inFile )
      serialize[OutputType]( outFile, try Right( f() ) catch { case t: Throwable => Left( t ) } )
  } finally System.exit( 0 )

  private def serialize[T]( fileName: String, obj: T ) = {
    val oos = new ObjectOutputStream( new FileOutputStream( fileName ) )
    try oos.writeObject( obj ) finally oos.close()
  }

  private def deserialize[T]( fileName: String ): T = {
    val ois = new ObjectInputStream( new FileInputStream( fileName ) )
    try ois.readObject().asInstanceOf[T] finally ois.close()
  }

  def apply[T <: Serializable]( extraJvmArgs: Seq[String] )( f: => T ): T = {
    val output = withTempFile { inputFile =>
      withTempFile { outputFile =>
        serialize[InputType]( inputFile, () => f )

        val javaBinary = new File( new File( System.getProperty( "java.home" ), "bin" ), "java" ).getAbsolutePath
        ( Seq( javaBinary ) ++ extraJvmArgs ++
          Seq( "-cp", System.getProperty( "java.class.path" ),
            getClass.getCanonicalName.dropRight( 1 ),
            inputFile, outputFile ) ) !

        deserialize[OutputType]( outputFile )
      }
    }

    output match {
      case Left( t )       => throw t
      case Right( result ) => result.asInstanceOf[T]
    }
  }
}
