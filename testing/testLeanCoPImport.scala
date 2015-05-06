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
  var success = 0
  var no_proof = 0

  def apply( str: String, timeout: Int ) = {
    
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
	  LeanCoPImportLogger.warn( "File: " + f.getPath + "\n" + e )
	case e: LeanCoPNoMatchException =>
	  no_match += 1;
	  LeanCoPImportLogger.warn( "File: " + f.getPath + "\n" + e )
	case e: TimeOutException =>
	  timeout_error += 1;
	  LeanCoPImportLogger.warn( "File: " + f.getPath + "\n" + e )
	case e: Throwable => 
	  fail += 1; 
	  LeanCoPImportLogger.error( "File: " + f.getPath + "\n" + e )
      }
    }

    LeanCoPImportLogger.info( "==========================" )
    LeanCoPImportLogger.info( "leanCoP import results:" )
    LeanCoPImportLogger.info( "success " + success + " (no TSTP proof " + no_proof + ")" )
    LeanCoPImportLogger.info( "no_match " + no_match )
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
