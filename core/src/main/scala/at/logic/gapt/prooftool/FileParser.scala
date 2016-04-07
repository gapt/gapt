/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 4:42 PM
 */

package at.logic.gapt.prooftool

import java.io.{ FileInputStream, InputStream, InputStreamReader }
import java.util.zip.GZIPInputStream

import at.logic.gapt.formats.ivy.IvyParser
import at.logic.gapt.formats.ivy.conversion.IvyToRobinson
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ HOLSequent, SequentProof, lk }
import at.logic.gapt.utils.ds.trees.{ BinaryTree, LeafTree, Tree }
import at.logic.gapt.formats.llkNew.{ ExtendedProofDatabase, loadLLK }

import scala.swing.Dialog

class FileParser( main: ProofToolViewer[_] ) {

  def ivyFileReader( path: String ) {
    val ivy = IvyToRobinson( IvyParser( path ) )
    termTrees = Nil
    // proofdb = new ProofDatabase(Map(), ("ivy_proof", RobinsonToLK(ivy))::Nil, Nil, Nil)
    resProofs = ( "ivy_proof", ivy ) :: Nil
  }

  def llkFileReader( filename: String ) {
    resProofs = Nil
    termTrees = Nil
    //  val start = System.currentTimeMillis()
    proofdb = loadLLK( filename )
    //  val end = System.currentTimeMillis()
    //  println("parsing took " + (end - start).toString)
  }

  def parseFile( path: String ) {
    val dnLine = sys.props( "line.separator" ) + sys.props( "line.separator" )
    try {
      if ( path.endsWith( ".llk" ) ) llkFileReader( path )
      //      else if ( path.endsWith( ".lksc" ) ) lksCNTFileReader( fileStreamReader( path ) )
      //      else if ( path.endsWith( ".lks" ) ) lksFileReader( fileStreamReader( path ) )
      //      else if ( path.endsWith( ".lks.gz" ) ) lksFileReader( gzFileStreamReader( path ) )
      else if ( path.endsWith( ".ivy" ) ) ivyFileReader( path )
      //  else if (path.endsWith(".ivy.gz")) ivyFileReader(path) // This will be added later
      else main.warningMessage( "Can not recognize file extension: " + path.substring( path.lastIndexOf( "." ) ) )
      main.publisher.publish( ProofDbChanged )
    } catch {
      case err: Throwable =>
        main.errorMessage( "Could not load file: " + path + "!" + dnLine + main.getExceptionString( err ) )
    }
  }

  def getProofs = proofdb.proofs

  def getResolutionProofs = resProofs

  def getTermTrees = termTrees

  private var proofdb = ExtendedProofDatabase( Map(), Map(), Map() )
  private var termTrees: List[( String, TermType.Value, Tree[_] )] = Nil
  private var resProofs: List[( String, SequentProof[_, _] )] = Nil

  object TermType extends Enumeration {
    val ClauseTerm, ProjectionTerm, ResolutionTerm, Unknown = Value
  }
}
