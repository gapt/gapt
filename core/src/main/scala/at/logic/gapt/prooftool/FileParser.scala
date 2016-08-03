package at.logic.gapt.prooftool

import java.io.{ FileInputStream, InputStream, InputStreamReader }
import java.util.zip.GZIPInputStream

import at.logic.gapt.formats.ivy.IvyParser
import at.logic.gapt.formats.ivy.conversion.IvyToResolution
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ HOLSequent, SequentProof, lk }
import at.logic.gapt.formats.llk.{ ExtendedProofDatabase, loadLLK }
import at.logic.gapt.proofs.resolution.ResolutionProof

import scala.swing.Dialog

class FileParser( main: ProofToolViewer[_] ) {

  def ivyFileReader( path: String ) {
    val ivy = IvyToResolution( IvyParser( path ) )
    resProofs = ( "ivy_proof", ivy ) :: Nil
  }

  def llkFileReader( filename: String ) {
    resProofs = Nil
    proofdb = loadLLK( filename )
  }

  def parseFile( path: String ) {
    val dnLine = sys.props( "line.separator" ) + sys.props( "line.separator" )
    try {
      if ( path.endsWith( ".llk" ) ) llkFileReader( path )
      else if ( path.endsWith( ".ivy" ) ) ivyFileReader( path )
      else main.warningMessage( "Can not recognize file extension: " + path.substring( path.lastIndexOf( "." ) ) )
    } catch {
      case err: Throwable =>
        main.errorMessage( "Could not load file: " + path + "!" + dnLine + main.getExceptionString( err ) )
    }
  }

  def getProofs = proofdb.proofs

  def getResolutionProofs = resProofs

  private var proofdb = ExtendedProofDatabase( Map(), Map(), Map() )
  private var resProofs: List[( String, ResolutionProof )] = Nil

  object TermType extends Enumeration {
    val ClauseTerm, ProjectionTerm, ResolutionTerm, Unknown = Value
  }
}
