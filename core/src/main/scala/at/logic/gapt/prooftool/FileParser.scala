/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 4:42 PM
 */

package at.logic.gapt.prooftool

import java.io.{ InputStream, FileInputStream, InputStreamReader }
import java.util.zip.GZIPInputStream

import at.logic.gapt.formats.llk.HybridLatexParser
import at.logic.gapt.formats.ParsingException
import at.logic.gapt.formats.ivy.IvyParser
import at.logic.gapt.formats.ivy.conversion.IvyToRobinson
import at.logic.gapt.formats.simple.SimpleXMLProofParser
import at.logic.gapt.formats.xml.{ XMLParser, ProofDatabase }
import XMLParser.XMLProofDatabaseParser
import at.logic.gapt.formats.readers.XMLReaders._
import at.logic.gapt.formats.shlk.SCHOLParser
import at.logic.gapt.formats.shlk_parsing.sFOParser
import at.logic.gapt.formats.xml.ProofDatabase
import at.logic.gapt.expr._
import at.logic.gapt.expr.schema.dbTRS
import at.logic.gapt.proofs.{ lk, SequentProof, HOLSequent }
import at.logic.gapt.proofs.ceres_schema.clauseSchema._
import at.logic.gapt.proofs.lkOld.base.{ LKProof }
import at.logic.gapt.proofs.proofs.{ Proof, TreeProof }
import at.logic.gapt.proofs.shlk.SchemaProofDB
import at.logic.gapt.utils.ds.trees.{ BinaryTree, LeafTree, Tree }

import scala.swing.Dialog

class FileParser( main: ProofToolViewer[_] ) {

  def fileStreamReader( f: String ) = new InputStreamReader( new FileInputStream( f ), "UTF8" )

  def gzFileStreamReader( f: String ) = new InputStreamReader( new GZIPInputStream( new FileInputStream( f ) ), "UTF8" )

  def ceresFileReader( input: InputStream ) =
    loadProofDatabase( ( new XMLReader( input ) with XMLProofDatabaseParser ).getProofDatabase() )

  def loadProofDatabase( db: ProofDatabase ) {
    SchemaProofDB.clear
    resolutionProofSchemaDB.clear
    proofs = Nil
    termTrees = Nil
    proofdb = db
  }

  def stabFileReader( input: InputStream ) {
    SchemaProofDB.clear
    resolutionProofSchemaDB.clear
    termTrees = Nil
    proofdb = new ProofDatabase( Map(), Nil, Nil, Nil )
    proofs = ( new XMLReader( input ) with SimpleXMLProofParser ).getNamedTrees()
  }

  //  def lksFileReader( input: InputStreamReader ) {
  //    resolutionProofSchemaDB.clear
  //    proofs = Nil
  //    termTrees = Nil
  //    val ps = sFOParser.parseProofs( input ) // constructs dbTRS as a side effect.
  //    val defs = dbTRS.map.map( p => p._2._1 :: p._2._2 :: Nil ).flatten.toMap[LambdaExpression, LambdaExpression]
  //    //  val start = System.currentTimeMillis()
  //    proofdb = new ProofDatabase( defs, ps, Nil, Nil )
  //    //  val end = System.currentTimeMillis()
  //    //  println("parsing took " + (end - start).toString)
  //  }
  //
  //  def lksCNTFileReader( input: InputStreamReader ) {
  //    resolutionProofSchemaDB.clear
  //    proofs = Nil
  //    termTrees = Nil
  //    val ps = SCHOLParser.parseProofs( input ) // constructs dbTRS as a side effect.
  //    val defs = dbTRS.map.map( p => p._2._1 :: p._2._2 :: Nil ).flatten.toMap[LambdaExpression, LambdaExpression]
  //    //  val start = System.currentTimeMillis()
  //    proofdb = new ProofDatabase( defs, ps, Nil, Nil )
  //    //  val end = System.currentTimeMillis()
  //    //  println("parsing took " + (end - start).toString)
  //  }

  def rsFileReader( input: InputStreamReader ) {
    ParseResSchema( input ) // constructs resolutionProofSchemaDB and dbTRS as a side effect.
    termTrees = resolutionProofSchemaDB.map.map( p => {
      val p212 = p._2._1._2
      val p222 = p._2._2._2
      ( p._1, TermType.ResolutionTerm, rTermToTree( p212 ) ) :: ( p._1, TermType.ResolutionTerm, rTermToTree( p222 ) ) :: Nil
    } ).flatten.toList ::: termTrees.filterNot( tpl => tpl._2 == TermType.ResolutionTerm ) // The filter removes old resolution terms.
    val defs = dbTRS.map.map( p => p._2._1 :: p._2._2 :: Nil ).flatten.toMap[LambdaExpression, LambdaExpression]
    addDefinitions( defs )
  }

  // This function should be improved and probably moved to some other place!
  def rTermToTree( term: sResolutionTerm ): Tree[AnyRef] = term match {
    case rTerm( t1, t2, f ) =>
      val p1 = rTermToTree( t1 )
      val p2 = rTermToTree( t2 )
      new BinaryTree[AnyRef]( "Resolve " + DrawSequent.formulaToLatexString( f ), p1, p2 )
    case _ => new LeafTree[AnyRef]( term.toString.replace( Console.RED + " \u22a2 " + Console.RESET, " \\vdash " ) )
  }

  def ivyFileReader( path: String ) {
    val ivy = IvyToRobinson( IvyParser( path ) )
    proofs = Nil
    termTrees = Nil
    // proofdb = new ProofDatabase(Map(), ("ivy_proof", RobinsonToLK(ivy))::Nil, Nil, Nil)
    resProofs = ( "ivy_proof", ivy ) :: Nil
  }

  def llkFileReader( filename: String ) {
    SchemaProofDB.clear
    resolutionProofSchemaDB.clear
    proofs = Nil
    resProofs = Nil
    termTrees = Nil
    //  val start = System.currentTimeMillis()
    proofdb = HybridLatexParser.createLKProof( HybridLatexParser.parseFile( filename ) )
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
      else if ( path.endsWith( ".rs" ) ) rsFileReader( fileStreamReader( path ) )
      else if ( path.endsWith( ".rs.gz" ) ) rsFileReader( gzFileStreamReader( path ) )
      else if ( path.endsWith( ".xml" ) ) try {
        ceresFileReader( new FileInputStream( path ) )
      } catch {
        case pe: ParsingException =>
          main.questionMessage( "There was a parsing exception:" + dnLine + " \t " + pe.getMessage + dnLine + "Continue with another parser?" ) match {
            case Dialog.Result.Yes => stabFileReader( new FileInputStream( path ) )
            case _                 =>
          }
      }
      else if ( path.endsWith( ".xml.gz" ) ) try {
        ceresFileReader( new GZIPInputStream( new FileInputStream( path ) ) )
      } catch {
        case pe: ParsingException =>
          main.questionMessage( "There was a parsing exception:" + dnLine + " \t " + pe.getMessage + dnLine + "Continue with another parser?" ) match {
            case Dialog.Result.Yes => stabFileReader( new GZIPInputStream( new FileInputStream( path ) ) )
            case _                 =>
          }
      }
      else if ( path.endsWith( ".ivy" ) ) ivyFileReader( path )
      //  else if (path.endsWith(".ivy.gz")) ivyFileReader(path) // This will be added later
      else main.warningMessage( "Can not recognize file extension: " + path.substring( path.lastIndexOf( "." ) ) )
      main.publisher.publish( ProofDbChanged )
    } catch {
      case err: Throwable =>
        main.errorMessage( "Could not load file: " + path + "!" + dnLine + main.getExceptionString( err ) )
    }
  }

  def addProofs( proofs: List[( String, lk.LKProof )] ) {
    proofdb = new ProofDatabase( proofdb.Definitions, proofdb.proofs ::: proofs, proofdb.axioms, proofdb.sequentLists )
  }

  def addSeqList( seqList: List[HOLSequent] ) {
    addSeqList( "sequentList ", seqList )
  }

  def addSeqList( name: String, seqList: List[HOLSequent] ) {
    proofdb = new ProofDatabase( proofdb.Definitions, proofdb.proofs, proofdb.axioms,
      ( name + proofdb.sequentLists.size.toString, seqList ) :: proofdb.sequentLists )
  }

  def addTermTree( struct: Tree[_] ) {
    termTrees = ( "struct " + termTrees.size.toString, TermType.Unknown, struct ) :: termTrees
  }

  def addTermTree( name: String, term: Tree[_] ) {
    termTrees = ( name, TermType.Unknown, term ) :: termTrees
  }

  def addTrees( list: List[( String, TermType.Value, Tree[_] )] ) {
    termTrees = list ::: termTrees
  }

  def addDefinitions( defs: Map[LambdaExpression, LambdaExpression] ) {
    val map = proofdb.Definitions ++ defs
    proofdb = new ProofDatabase( map, proofdb.proofs, proofdb.axioms, proofdb.sequentLists )
  }

  def getDefinitions = proofdb.Definitions //._1.toList ::: proofdb.Definitions._2.toList ::: proofdb.Definitions._3.toList

  def getSequentLists = proofdb.sequentLists

  def getProofs = proofdb.proofs ::: proofs

  def getResolutionProofs = resProofs

  def getProofDB = proofdb

  def getTermTrees = termTrees

  private var proofdb = new ProofDatabase( Map(), Nil, Nil, Nil )
  private var proofs: List[( String, TreeProof[_] )] = Nil
  private var termTrees: List[( String, TermType.Value, Tree[_] )] = Nil
  private var resProofs: List[( String, SequentProof[_, _] )] = Nil

  object TermType extends Enumeration {
    val ClauseTerm, ProjectionTerm, ResolutionTerm, Unknown = Value
  }
}
