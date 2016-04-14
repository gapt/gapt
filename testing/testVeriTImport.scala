import java.io.{ File, FileReader }
import org.slf4j.LoggerFactory

import at.logic.gapt.utils.executionModels.timeout._
import at.logic.gapt.formats.veriT._

/**
 * Usage: 
 *
 * gapt> :load testing/testVeriTImport.scala
 * gapt> testVeriTImport("testing/veriT-SMT-LIB", 60)
 */

val VeriTImportLogger = LoggerFactory.getLogger("VeriTImportLogger")

object testVeriTImport {

  var fail = 0
  var syntax_error = 0
  var unfold_error = 0
  var success = 0
  
  private val nLine = sys.props("line.separator")
  
  def apply( str: String, timeout: Int ) = {
    
    val top_dir = new File( str )
    val proof_files = getAllProofFiles( top_dir )

    proof_files.foreach { case f =>
      try { withTimeout( timeout * 1000 ) { 
	VeriTParser.getExpansionProof( new FileReader( f ) ) match {
	  case _ => success += 1
	}
      } } catch {
	case e: VeriTParserException =>
	  syntax_error += 1;
	  VeriTImportLogger.warn( "File: " + f.getPath + nLine + e )
	case e: VeriTUnfoldingTransitivityException =>
	  unfold_error += 1;
	  VeriTImportLogger.warn( "File: " + f.getPath + nLine + e )
	case e: Throwable => 
	  fail += 1; 
	  VeriTImportLogger.error( "File: " + f.getPath + nLine + e )
      }
    }

    VeriTImportLogger.info( "==========================" )
    VeriTImportLogger.info( "VeriT import results:" )
    VeriTImportLogger.info( "success " + success )
    VeriTImportLogger.info( "unfold_error " + unfold_error )
    VeriTImportLogger.info( "syntax_error " + syntax_error )
    VeriTImportLogger.info( "failure " + fail )
    VeriTImportLogger.info( "==========================" )

  }

  def getAllProofFiles( file: File ): List[File] = {
    if ( file.isDirectory ) {
      file.listFiles.toList.flatMap( f => getAllProofFiles( f ) )
    }
    else {
      if ( file.getName.endsWith( ".proof_flat" ) ) List( file )
      else List()
    }
  }

}
