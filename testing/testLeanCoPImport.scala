import java.io.{ File, FileReader }
import org.slf4j.LoggerFactory

import at.logic.gapt.utils.executionModels.timeout._
import at.logic.gapt.formats.leanCoP._

/**
 * Usage: 
 *
 * gapt> :load testing/testLeanCoPImport.scala
 * gapt> testLeanCoPImport("testing/TSTP/leanCoP", 60)
 */

val LeanCoPImportLogger = LoggerFactory.getLogger("LeanCoPImportLogger")

object testLeanCoPImport {

  var fail = 0
  var timeout_error = 0
  var syntax_error = 0
  var no_match = 0
  var sk_fun_error = 0
  var lean_pred_error = 0
  var no_lean_pred = 0
  var success = 0
  var no_proof = 0

  def apply( str: String, timeout: Int ) = {
    
    private val nLine = sys.props("line.separator")
    val top_dir = new File( str )
    val proof_files = getAllProofFiles( top_dir )

    proof_files.foreach { case f =>
      try { withTimeout( timeout * 1000 ) { 
	LeanCoPParser.getExpansionProof( new FileReader( f ) ) match {
	  case Some(_) => success += 1
	  case None => success += 1; no_proof += 1
	}
      } } catch {
	case e: LeanCoPParserException =>
	  syntax_error += 1;
	  LeanCoPImportLogger.warn( "File: " + f.getPath + nLine + e )
	case e: LeanCoPNoMatchException =>
	  no_match += 1;
	  LeanCoPImportLogger.warn( "File: " + f.getPath + nLine + e )
	case e: LeanCoPNoLeanPredException =>
	  no_lean_pred += 1
	  LeanCoPImportLogger.warn( "File: " + f.getPath + nLine + e )
	case e: LeanCoPLeanPredWrongArityException =>
	  lean_pred_error += 1
	  LeanCoPImportLogger.warn( "File: " + f.getPath + nLine + e )
	case e: NoSuchElementException =>
	  sk_fun_error += 1
	  LeanCoPImportLogger.warn( "File: " + f.getPath + nLine + e )
	case e: TimeOutException =>
	  timeout_error += 1;
	  LeanCoPImportLogger.warn( "File: " + f.getPath + nLine + e )
	case e: Throwable => 
	  fail += 1; 
	  LeanCoPImportLogger.error( "File: " + f.getPath + nLine + e )
      }
    }

    LeanCoPImportLogger.info( "==========================" )
    LeanCoPImportLogger.info( "leanCoP import results:" )
    LeanCoPImportLogger.info( "success " + success + " (no TSTP proof " + no_proof + ")" )
    LeanCoPImportLogger.info( "no_match " + no_match )
    LeanCoPImportLogger.info( "lean_pred_error " + lean_pred_error )
    LeanCoPImportLogger.info( "no_lean_pred " + no_lean_pred )
    LeanCoPImportLogger.info( "sk_fun_error " + sk_fun_error )
    LeanCoPImportLogger.info( "syntax_error " + syntax_error )
    LeanCoPImportLogger.info( "timeout_error " + timeout_error )
    LeanCoPImportLogger.info( "failure " + fail )
    LeanCoPImportLogger.info( "==========================" )

  }

  def getAllProofFiles( file: File ): List[File] = {
    if ( file.isDirectory ) {
      file.listFiles.toList.flatMap( f => getAllProofFiles( f ) )
    }
    else {
      if ( file.getName.endsWith( ".out" ) ) List( file )
      else List()
    }
  }

}
