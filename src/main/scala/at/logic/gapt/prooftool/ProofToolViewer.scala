/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Oct 27, 2010
 * Time: 12:08:33 PM
 */

package at.logic.gapt.prooftool

import java.awt.event.{ ActionEvent, KeyEvent }

import at.logic.gapt.formats.xml.{ ProofDatabase, XMLExporter }
import at.logic.gapt.proofs.expansionTrees.{ ExpansionProofToLK, ExpansionSequent }
import at.logic.gapt.proofs.lk.UnfoldException
import at.logic.gapt.proofs.lk.base.OccSequent
import at.logic.gapt.proofs.lk.base.RichOccSequent
import at.logic.gapt.proofs.lkNew._
import at.logic.gapt.proofs.lk
import at.logic.gapt.proofs.{ Sequent, DagProof, SequentProof, HOLSequent }
import at.logic.gapt.proofs.lksk.eliminateDefinitions
import at.logic.gapt.proofs.shlk.{ applySchemaSubstitution2, applySchemaSubstitution }
import com.itextpdf.awt.PdfGraphics2D
import scala.swing._
import BorderPanel._
import scala.swing.event.Key
import swing.Dialog.Message
import swing.Swing.EmptyIcon
import java.io.{ BufferedWriter => JBufferedWriter, FileWriter => JFileWriter, ByteArrayInputStream, InputStreamReader, File }
import javax.swing.filechooser.FileFilter
import javax.swing.{ KeyStroke, WindowConstants, SwingUtilities }
import at.logic.gapt.proofs.proofs.TreeProof
import at.logic.gapt.expr.hol._
import at.logic.gapt.expr.schema.IntVar
import at.logic.gapt.formats.latex.{ ProofToLatexExporter, SequentsListLatexExporter }
import at.logic.gapt.formats.arithmetic.HOLTermArithmeticalExporter
import at.logic.gapt.formats.writers.FileWriter
import at.logic.gapt.proofs.ceres_schema.clauseSets.{ renameCLsymbols, StandardClauseSet }
import at.logic.gapt.proofs.ceres_schema.struct.{ structToExpressionTree, StructCreators }
import at.logic.gapt.proofs.ceres_schema.projections.{ Projections, DeleteTautology, DeleteRedundantSequents }
import at.logic.gapt.proofs.ceres_schema.{ UnfoldProjectionTerm, ProjectionTermCreators }
import at.logic.gapt.utils.ds.trees.Tree
import at.logic.gapt.proofs.ceres_schema.clauseSchema.{ resolutionProofSchemaDB, InstantiateResSchema }
import at.logic.gapt.proofs.ceres_schema.ACNF.ACNF
import at.logic.gapt.proofs.shlk.SchemaProofDB
import at.logic.gapt.proofs.proofs.Proof
import java.awt.image.BufferedImage
import javax.imageio.ImageIO
import java.awt.Color
import at.logic.gapt.algorithms.rewriting.DefinitionElimination
import at.logic.gapt.formats.llk.HybridLatexExporter
import at.logic.gapt.formats.tptp.TPTPFOLExporter

object ProofToolViewer {
  /**
   * Displays various objects in prooftool. Creates an instance of the appropriate viewer.
   * @param name The title to be displayed.
   * @param obj The object to be displayed.
   */
  def display( name: String, obj: AnyRef ) {
    val mainWindow = obj match {
      case p: LKProof             => new LKProofViewer( name, p )
      case p: SequentProof[a, b]  => new SequentProofViewer[a, b]( name, p )
      case es: ExpansionSequent   => new ExpansionSequentViewer( name, es )
      case p: TreeProof[_]        => new TreeProofViewer( name, p )
      case p: Proof[_]            => new ResolutionProofViewer( name, p )
      case list: List[HOLSequent] => new ListViewer( name, list )
      case seq: HOLSequent        => new ListViewer( name, List( seq ) )
      case set: Set[HOLSequent]   => new ListViewer( name, set.toList )
      case tree: Tree[a]          => new TreeViewer[a]( name, tree )
      case _                      => throw new IllegalArgumentException( s"Objects of type ${obj.getClass} can't be displayed." )
    }
    mainWindow.showFrame()
  }

  //tries to display some proof from the db
  /* def selectProofFromDB( fontSize: Int ) {
    val db = new FileParser(new PTMain[])
    val proofs = db.getProofs
    if ( proofs.nonEmpty )
      updateLauncher( proofs.head._1, proofs.head._2, fontSize )
    else if ( db.getSequentLists.size > 0 )
      updateLauncher( "", db.getSequentLists.head, fontSize )
    else if ( db.getTermTrees.size > 0 )
      updateLauncher( db.getTermTrees.head._1, db.getTermTrees.head._3, fontSize )
    else if ( db.getResolutionProofs.size > 0 )
      updateLauncher( "", db.getResolutionProofs.head, fontSize )
    else clearLauncher()

  }*/

}

/**
 * The main window of the ProofTool application.
 * @param name The name to be displayed at the top.
 * @param content The object to be displayed.
 * @tparam T The type of content.
 */
abstract class ProofToolViewer[+T]( val name: String, val content: T ) extends Reactor {
  type MainComponentType <: Component // The type of the mainComponent object (e.g., DrawSequentProof in the case of LK proofs).
  val nLine = sys.props( "line.separator" )
  val dnLine = nLine + nLine
  var DEBUG = false
  val defaultFontSize = 12
  var currentFontSize = defaultFontSize
  var launcher_history = List[( String, AnyRef, Int )]()
  val publisher = new ProofToolPublisher
  val mBar = new MenuBar {
    focusable = true

    contents += new Menu( "File" ) {
      mnemonic = Key.F
      contents ++= fileMenuContents
    }

    contents += new Menu( "View" ) {
      mnemonic = Key.V
      contents ++= viewMenuContents
    }
  }

  val scrollPane = new PTScrollPane
  val db = new FileParser( this )

  def showFrame() {
    top.preferredSize = new Dimension( 700, 500 )
    top.pack()
    top.centerOnScreen()
    top.open()
    top.maximize()
  }

  lazy val top = new Frame {
    title = "ProofTool"
    menuBar = mBar
    contents = new BorderPanel {
      // layout(toolbar) = Position.North
      layout( scrollPane ) = Position.Center
      // layout(new ProgressBar { indeterminate = true }) = Position.South
    }
    peer setDefaultCloseOperation WindowConstants.DISPOSE_ON_CLOSE
  }

  var mainComponent = createMainComponent( defaultFontSize )
  protected var contentPanel_ = new PTContentPanel( this, name, mainComponent, defaultFontSize )
  scrollPane.contentPanel = contentPanel_
  def contentPanel = contentPanel_

  // Function that creates the main component from the content object, e.g., put an LKProof in a DrawSequentProof object.
  // Subclasses need to implement this!
  def createMainComponent( fSize: Int ): MainComponentType

  /**
   * Resizes the content to a new font size.
   * @param fSize The new font size.
   */
  def resizeContent( fSize: Int ): Unit = {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    mainComponent = createMainComponent( fSize )
    contentPanel_ = new PTContentPanel( this, name, mainComponent, fSize )
    scrollPane.contentPanel = contentPanel_
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  /*def fOpen() {
    chooser.fileFilter = chooser.acceptAllFileFilter
    chooser.showOpenDialog( mBar ) match {
      case FileChooser.Result.Approve => loadProof( chooser.selectedFile.getPath, defaultFontSize )
      case _                          =>
    }
  }*/

  def fSaveAll() {
    chooser.fileFilter = chooser.acceptAllFileFilter
    chooser.showSaveDialog( mBar ) match {
      case FileChooser.Result.Approve =>
        scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
        val result = chooser.selectedFile.getPath
        try {
          if ( result.endsWith( ".xml" ) || chooser.fileFilter.getDescription == ".xml" ) {
            XMLExporter( result, db.getProofDB )
          } else if ( result.endsWith( ".tex" ) || chooser.fileFilter.getDescription == ".tex" ) {
            val filename = if ( result.endsWith( ".tex" ) ) result else result + ".tex"
            val file = new JBufferedWriter( new JFileWriter( filename ) )
            file.write( ProofToLatexExporter( db.getProofs.map( pair => ( pair._1, lkNew2Old( pair._2.asInstanceOf[LKProof] ) ) ) ) )
            file.close()
          } else infoMessage( "Proofs cannot be saved in this format." )
        } catch {
          case e: Throwable => errorMessage( "Cannot save the file! " + dnLine + getExceptionString( e ) )
        } finally { scrollPane.cursor = java.awt.Cursor.getDefaultCursor }
      case _ =>
    }
  }

  /**
   * Exports a component as a pdf.
   * @param component The component to be exported.
   */
  def fExportPdf( component: Component ) {
    chooser.fileFilter = chooser.peer.getChoosableFileFilters.find( f => f.getDescription == ".pdf" ).get
    chooser.showSaveDialog( mBar ) match {
      case FileChooser.Result.Approve => try {
        scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
        import java.io.FileOutputStream
        import com.itextpdf.text.{ Document, Rectangle => PdfRectangle }
        import com.itextpdf.text.pdf.PdfWriter

        val width = component.size.width
        val height = component.size.height
        val document = new Document( new PdfRectangle( width, height + 20 ) )
        val result = chooser.selectedFile.getPath
        val path = if ( result.endsWith( ".pdf" ) ) result else result + ".pdf"
        val writer = PdfWriter.getInstance( document, new FileOutputStream( path ) )
        document.open()
        val content = writer.getDirectContent
        val template = content.createTemplate( width, height )
        val g2 = new PdfGraphics2D( template, width, height, true )
        component.paint( g2 )
        g2.dispose()
        content.addTemplate( template, 0, 10 )
        document.close()
      } catch {
        case e: Throwable => errorMessage( "Can't export to pdf! " + dnLine + getExceptionString( e ) )
      } finally { scrollPane.cursor = java.awt.Cursor.getDefaultCursor }
      case _ =>
    }
  }

  /**
   * Exports a component as a PNG.
   * @param component The component to be exported.
   */
  def fExportPng( component: Component ) {
    chooser.fileFilter = chooser.peer.getChoosableFileFilters.find( f => f.getDescription == ".png" ).get
    chooser.showSaveDialog( mBar ) match {
      case FileChooser.Result.Approve => try {
        scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )

        val width = component.size.width
        val height = component.size.height
        val img = new BufferedImage( width, height, BufferedImage.TYPE_INT_RGB )
        val g = img.createGraphics()
        g.setBackground( new Color( 255, 255, 255 ) )
        g.fillRect( 0, 0, width, height )
        component.paint( g )
        val result = chooser.selectedFile.getPath
        val path = if ( result.endsWith( ".png" ) ) result else result + ".png"
        ImageIO.write( img, "png", new File( path ) )
      } catch {
        case e: Throwable => errorMessage( "Can't export to png! " + dnLine + getExceptionString( e ) )
      } finally { scrollPane.cursor = java.awt.Cursor.getDefaultCursor }
      case _ =>
    }
  }

  /**
   * Zooms in by multiplying font size by 3/2.
   */
  def zoomIn() {
    currentFontSize * 3 / 2 match {
      case j: Int if j > 72 =>
      case j: Int =>
        currentFontSize = j
        resizeContent( j )
    }
  }

  /**
   * Zooms out by multiplying font size by 2/3.
   */
  def zoomOut() {
    currentFontSize / 3 * 2 match {
      case j: Int if j < 1 =>
      case j: Int =>
        currentFontSize = j
        resizeContent( j )
    }
  }
  /*
  def search() {
    val input_str = inputMessage( "Please enter string to search:", Seq() ) match {
      case Some( str ) => str
      case _           => ""
    }
    if ( !input_str.isEmpty ) try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      scrollPane.getContent.contents.head match {
        // FIXME
        case dp: DrawProof =>
          dp.search = input_str
          if ( dp.proof.root.isInstanceOf[OccSequent] )
            ProofToolPublisher.publish( ChangeFormulaColor( Search.inTreeProof( input_str, dp.proof ), Color.green, reset = true ) )
          else dp.searchNotInLKProof()
          dp.revalidate()
        case dt: DrawTree =>
          dt.search = input_str
          dt.revalidate()
        case dl: DrawList =>
          dl.search = input_str
          dl.revalidate()
        case _ => throw new Exception( "Cannot search in this object!" )
      }
    } catch {
      case e: Throwable => errorMessage( getExceptionString( e ) )
    } finally {
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    }
  }

  def scrollToProof( proof: SequentProof[_, _] ) {
    val launcher = scrollPane.getContent
    val pos = launcher.getLocationOfProof( proof ).get
    val centered = new Rectangle( pos.x - scrollPane.bounds.width / 2, pos.y - scrollPane.bounds.height, scrollPane.bounds.width, scrollPane.bounds.height )
    launcher.peer.scrollRectToVisible( centered )
  }
*/

  // Used by startup and open dialog
  /*def loadProof( path: String, fontSize: Int ) {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    db.parseFile( path )
    selectProofFromDB( fontSize )
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    publisher.publish( EnableMenus )
  }*/

  /*
  // Used by View Clause List menu
  def loadClauseSet( clList: ( String, List[_] ) ) {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    updateLauncher( "clauses", clList, defaultFontSize )
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used by View Struct menu
  def loadStruct( struct: ( String, Tree[_] ) ) {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    updateLauncher( "struct", struct, defaultFontSize )
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used for Zooming
  def load( option: Option[( String, AnyRef )], fontSize: Int ) {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    option match {
      case Some( ( name, obj ) ) => updateLauncher( name, obj, fontSize )
      case None                  => clearLauncher()
    }
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used by "Cycle through cuts"
  private var searchResult: List[LKProof] = null
  private var currentResult: Iterator[LKProof] = null

  def focusNextCut() = {
    // TODO: reset cuts when loading a proof
    if ( PTMain.currentResult != null ) {
      if ( PTMain.currentResult.hasNext ) {
        val cut = PTMain.currentResult.next()
        PTMain.scrollToProof( cut )
      } else {
        PTMain.currentResult = PTMain.searchResult.iterator
      }
    }
  }

  // Should be called whenever the proof is changed.
  def resetCuts() {
    searchResult = null
    currentResult = null
  }

  def setSearchResult( l: List[LKProof] ) = if ( l != null ) {
    searchResult = l
    currentResult = l.iterator
  }



  def specifyResolutionSchema() {
    val t = TextAreaDialog( "Please enter resolution proof schema:" )
    if ( t != None && t.get != "" ) try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      db.rsFileReader( new InputStreamReader( new ByteArrayInputStream( t.get.getBytes( "UTF-8" ) ) ) )
      val tp = db.getTermTrees.head
      updateLauncher( tp._1, tp._3, 14 )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
      ProofToolPublisher.publish( ProofDbChanged )
    } catch {
      case e: Throwable =>
        errorMessage( "Cannot parse the specified resolution schema!" + dnLine + getExceptionString( e ) )
    }
  }
*/

  /*
  def skolemizeProof() {
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val data = scrollPane.getContent.getData.get
      val proof = skolemize( data._2.asInstanceOf[LKProof] )
      db.addProofs( ( data._1 + "_sk", proof ) :: Nil )
      updateLauncher( data._1 + "_sk", proof, 14 )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    } catch {
      case e: Throwable =>
        errorMessage( "Cannot skolemize the proof!" + dnLine + getExceptionString( e ) )
    } finally ProofToolPublisher.publish( ProofDbChanged )
  }

  def regularizeProof() {
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val data = scrollPane.getContent.getData.get
      val proof = regularize( data._2.asInstanceOf[LKProof] )
      db.addProofs( ( data._1 + "_reg", proof ) :: Nil )
      updateLauncher( data._1 + "_reg", proof, 14 )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    } catch {
      case e: Throwable =>
        errorMessage( "Cannot regularize the proof!" + dnLine + getExceptionString( e ) )
    } finally ProofToolPublisher.publish( ProofDbChanged )
  }

  def extractCutFormulas() {
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val list = scrollPane.getContent.getData.get._2.asInstanceOf[DagProof[_]].subProofs.toList collect {
        case c: CutRule => Sequent() :+ c.cutFormula
      }
      db.addSeqList( "cutFormulaList ", list )
      updateLauncher( "Cut-formula List", list, 16 )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    } catch {
      case e: Throwable =>
        errorMessage( "Couldn't extract CutFormula List!" + dnLine + getExceptionString( e ) )
    } finally ProofToolPublisher.publish( ProofDbChanged )
  }

  def computeProjections() {
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val proof = scrollPane.getContent.getData.get
      val proof_projs = Projections( proof._2.asInstanceOf[lk.base.LKProof] ).filterNot( p =>
        p.root.antecedent.exists( fo1 => p.root.succedent.exists( fo2 => fo1.formula == fo2.formula ) ) ).toList
      val proofs = proof_projs.map( p => ( proof._1 + "_prj_" + proof_projs.indexOf( p ), p ) )
      db.addProofs( proofs )
      updateLauncher( proofs.head._1, proofs.head._2, defaultFontSize )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    } catch {
      case e: Throwable =>
        errorMessage( "Cannot compute Projections!" + dnLine + getExceptionString( e ) )
    } finally ProofToolPublisher.publish( ProofDbChanged )
  }

  def computeClList() {
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val proof_sk = lk.LKToLKsk( scrollPane.getContent.getData.get._2.asInstanceOf[lk.base.LKProof] )
      val s = StructCreators.extract( proof_sk )
      val csPre: List[OccSequent] = DeleteRedundantSequents( DeleteTautology( StandardClauseSet.transformStructToClauseSet( s ) ) )

      db.addSeqList( csPre.map( x => x.toHOLSequent ) )
      updateLauncher( "cllist", csPre, 16 )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    } catch {
      case e: Throwable =>
        errorMessage( "Couldn't compute ClList!" + dnLine + getExceptionString( e ) )
    } finally ProofToolPublisher.publish( ProofDbChanged )
  }

  def computeSchematicClauseSet() {
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val n = IntVar( "n" )

      val s = StructCreators.extractStruct( scrollPane.getContent.getData.get._1, n )
      val cs: List[OccSequent] = DeleteRedundantSequents( DeleteTautology( StandardClauseSet.transformStructToClauseSet( s ) ) )
      val pair = renameCLsymbols( cs )

      db.addSeqList( pair._1 ) //.map(x => x.toHOLSequent))
      db.addDefinitions( pair._2 )
      updateLauncher( "Schematic Clause Set", pair._1, 16 )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    } catch {
      case e: Throwable =>
        errorMessage( "Couldn't compute clause set!" + dnLine + getExceptionString( e ) )
    } finally ProofToolPublisher.publish( ProofDbChanged )
  }

  def computeSchematicStruct() {
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val n = IntVar( "n" )
      val s = StructCreators.extractRelevantStruct( scrollPane.getContent.getData.get._1, n )
      val structs_base = s._2.map( pair => ( pair._1, db.TermType.ClauseTerm, structToExpressionTree.prunedTree( pair._2 ) ) )
      val structs_step = s._1.map( pair => ( pair._1, db.TermType.ClauseTerm, structToExpressionTree.prunedTree( pair._2 ) ) )
      db.addTrees( structs_step ::: structs_base )
      updateLauncher( structs_step.head._1, structs_step.head._3, defaultFontSize )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    } catch {
      case e: Throwable =>
        errorMessage( "Couldn't compute Struct!" + dnLine + getExceptionString( e ) )
    } finally ProofToolPublisher.publish( ProofDbChanged )
  }

  def computeSchematicProjectionTerm() {
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val proof_name = scrollPane.getContent.getData.get._1
      val pterms = ProjectionTermCreators( proof_name )
      db.addTrees( pterms.map( pair => ( pair._1, db.TermType.ProjectionTerm, pair._2 ) ) )
      updateLauncher( pterms.head._1, pterms.head._2, defaultFontSize )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    } catch {
      case e: Throwable =>
        errorMessage( "Couldn't compute Projection Terms!" + dnLine + getExceptionString( e ) )
    } finally ProofToolPublisher.publish( ProofDbChanged )
  }

  def computeClListOnlyQuantifiedCuts() {
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val proof_sk = lk.eliminateDefinitions( lk.LKToLKsk( scrollPane.getContent.getData.get._2.asInstanceOf[lk.base.LKProof] ) )
      val s = StructCreators.extract( proof_sk, f => containsQuantifier( f ) )
      val csPre: List[OccSequent] = DeleteRedundantSequents( DeleteTautology( StandardClauseSet.transformStructToClauseSet( s ) ) )
      db.addSeqList( csPre.map( x => x.toHOLSequent ) )
      updateLauncher( "cllist", csPre, 16 )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    } catch {
      case e: Throwable =>
        errorMessage( "Couldn't compute clause list!" + dnLine + getExceptionString( e ) )
    } finally ProofToolPublisher.publish( ProofDbChanged )
  }

  def computeStruct() {
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val proof_sk = lk.LKToLKsk( scrollPane.getContent.getData.get._2.asInstanceOf[lk.base.LKProof] )
      val s = structToExpressionTree.prunedTree( StructCreators.extract( proof_sk ) )
      db.addTermTree( s )
      updateLauncher( "Struct", s, defaultFontSize )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    } catch {
      case e: Throwable =>
        errorMessage( "Couldn't compute Struct!" + dnLine + getExceptionString( e ) )
    } finally ProofToolPublisher.publish( ProofDbChanged )
  }

  // Computes the struct, ignoring propositional cuts
  def computeStructOnlyQuantifiedCuts() {
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val proof_sk = lk.eliminateDefinitions( lk.LKToLKsk( scrollPane.getContent.getData.get._2.asInstanceOf[lk.base.LKProof] ) )
      val s = structToExpressionTree.prunedTree( StructCreators.extract( proof_sk, f => containsQuantifier( f ) ) )
      db.addTermTree( s )
      updateLauncher( "Struct", s, defaultFontSize )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    } catch {
      case e: Throwable =>
        errorMessage( "Couldn't compute Struct!" + dnLine + getExceptionString( e ) )
    } finally ProofToolPublisher.publish( ProofDbChanged )
  }

  def eliminateDefsLK() {
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val pair = scrollPane.getContent.getData.get
      val new_proof = lk.AtomicExpansion( DefinitionElimination( db.getDefinitions, pair._2.asInstanceOf[lk.base.LKProof] ) )
      db.addProofs( ( pair._1 + " without def rules", new_proof ) :: Nil )
      updateLauncher( pair._1 + " without Definitions", new_proof, 14 )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    } catch {
      case e: Throwable =>
        errorMessage( "Couldn't eliminate definitions!" + dnLine + getExceptionString( e ) )
    } finally ProofToolPublisher.publish( ProofDbChanged )
  }

  def eliminateDefsLKsk() {
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val pair = scrollPane.getContent.getData.get
      val new_proof = lk.eliminateDefinitions( lk.LKToLKsk( pair._2.asInstanceOf[lk.base.LKProof] ) )
      db.addProofs( ( pair._1 + " without def rules", new_proof ) :: Nil )
      updateLauncher( "Proof without Definitions", new_proof, 14 )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    } catch {
      case e: Throwable =>
        errorMessage( "Couldn't eliminate definitions!" + dnLine + getExceptionString( e ) )
    } finally ProofToolPublisher.publish( ProofDbChanged )
  }

  def newgentzen( proof: lk.base.LKProof ) {
    import lk._
    import lk.base._
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val newSubproof = ReductiveCutElim( proof, true, { x => true }, { ( _, cut ) => cut == proof } )
      val oldProof = scrollPane.getContent.getData.get._2.asInstanceOf[LKProof]
      val newProof = replaceSubproof( oldProof, proof, newSubproof )
      //if (newProof != newSubproof) ReductiveCutElim.proofs = ReductiveCutElim.proofs ::: (newProof::Nil)
      loadProof( ( "Gentzen Result:", newProof ) )

      // need to scroll after UI has finished updating
      // to get the correct coordinates.
      SwingUtilities.invokeLater( new Runnable() {
        def run() {
          // FIXME scrollToProof( newSubproof )
        }
      } )

    } catch {
      case e: Throwable =>
        errorMessage( "Couldn't eliminate all cuts!" + dnLine + getExceptionString( e ) )
    } finally {
      db.addProofs( ReductiveCutElim.proofs.map( x => ( x.name, x ) ) )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
      ProofToolPublisher.publish( ProofDbChanged )
    }
  }

  def gentzen( proof: lk.base.LKProof ) {
    import lk._
    import lk.base._
    try {
      val steps = questionMessage( "Do you want to see intermediary steps?" ) match {
        case Dialog.Result.Yes => true
        case _                 => false
      }
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val newSubproof = ReductiveCutElim.eliminateAllByUppermost( proof, steps )
      val oldProof = scrollPane.getContent.getData.get._2.asInstanceOf[LKProof]
      val newProof = replaceSubproof( oldProof, proof, newSubproof )
      if ( newProof != newSubproof ) ReductiveCutElim.proofs = ReductiveCutElim.proofs ::: ( newProof :: Nil )
      updateLauncher( "Gentzen Result:", newProof, 14 )
    } catch {
      case e: Throwable =>
        errorMessage( "Couldn't eliminate all cuts!" + dnLine + getExceptionString( e ) )
    } finally {
      db.addProofs( ReductiveCutElim.proofs.map( x => ( x.name, x ) ) )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
      ProofToolPublisher.publish( ProofDbChanged )
    }
  }

  //TODO: Must calculate omega ancestors, currently it marks nothing
  def markOmegaAncestors() {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    scrollPane.getContent.getData match {
      case Some( ( _, proof: LKProof ) ) =>
        ProofToolPublisher.publish( ChangeFormulaColor( Set(), Color.red, reset = false ) )
      case _ => errorMessage( "LK proof not found!" )
    }
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }
*/

  /*def computeInstance() {
    val input = inputMessage( "Please enter number of the instance:", Seq() ) match {
      case Some( str ) => str.replaceAll( """[a-z,A-Z]*""", "" )
      case _           => ""
    }
    if ( !input.isEmpty ) try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val number = if ( input.size > 10 ) input.dropRight( 10 ).toInt else input.toInt
      scrollPane.getContent.getData.get match {
        case ( name: String, p: LKProof ) =>
          val proof = try { // This is a hack! In the future these two functions should be merged.
            applySchemaSubstitution2( name, number, List() )
          } catch {
            case e: UnfoldException => applySchemaSubstitution( name, number )
          }
          db.addProofs( ( name + "↓" + number, proof ) :: Nil )
          updateLauncher( name + "↓" + number, proof, defaultFontSize )
        case ( name: String, pt: Tree[_] ) if db.getTermTrees.exists( p => name == p._1 && p._2 == db.TermType.ProjectionTerm ) =>
          val ( term, list ) = UnfoldProjectionTerm( name, number )
          val gterm_name = name.replace( "_step", "" ).replace( "_base", "" ) + "↓" + number
          db.addTermTree( gterm_name, term )
          db.addProofs( list )
          updateLauncher( gterm_name, term, defaultFontSize )
          infoMessage( "The proof projections, corresponding to this term, are also computed." + nLine +
            "They can be found in the View Proof menu!" )
        case ( name: String, pt: Tree[_] ) if db.getTermTrees.exists( p => name == p._1 && p._2 == db.TermType.ClauseTerm ) => errorMessage( "Not yet implemented!" )
        case ( name: String, pt: Tree[_] ) if db.getTermTrees.exists( p => name == p._1 && p._2 == db.TermType.ResolutionTerm ) =>
          val proof = InstantiateResSchema( name, number )
          db.addProofs( proof :: Nil )
          updateLauncher( proof._1, proof._2, defaultFontSize )
        case _ => errorMessage( "Cannot instantiate the object!" )
      }
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
      ProofToolPublisher.publish( ProofDbChanged )
    } catch {
      case e: Throwable =>
        errorMessage( "Could not construct the instance!" + dnLine + getExceptionString( e ) )
    }
  }

  def computeACNF() {
    if ( SchemaProofDB.proofs.isEmpty )
      warningMessage( "Proof schema is missing!" )
    else if ( resolutionProofSchemaDB.map.isEmpty ) {
      warningMessage( "Please specify the resolution refutation schema!" )
      specifyResolutionSchema()
    } else try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val result = ACNFDialog(
        SchemaProofDB.proofs.map( pair => pair._1 ).toSeq.reverse,
        resolutionProofSchemaDB.map.map( pair => pair._1 ).toSeq.reverse
      )
      if ( result != None ) {
        val input = result.get
        val proof = ACNF( input._1, input._2, input._3 )
        db.addProofs( ( input._1 + "↓" + input._3 + "_acnf", proof ) :: Nil )
        updateLauncher( input._1 + "↓" + input._3 + "_acnf", proof, defaultFontSize )
      }
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
      ProofToolPublisher.publish( ProofDbChanged )
    } catch {
      case e: Throwable =>
        errorMessage( "Could not construct the ACNF!" + dnLine + getExceptionString( e ) )
    }
  }*/

  def inputMessage( message: String, values: Seq[String] ) =
    Dialog.showInput[String]( scrollPane, message, "ProofTool Input", Dialog.Message.Plain, EmptyIcon, values,
      if ( values.isEmpty ) "" else values.head )

  /**
   * Displays an info message.
   * @param info The text of the message.
   */
  def infoMessage( info: String ) {
    Dialog.showMessage( scrollPane, info, "ProofTool Information" )
  }

  /**
   * Displays a warning message.
   * @param warning The text of the message.
   */
  def warningMessage( warning: String ) {
    Dialog.showMessage( scrollPane, warning, "ProofTool Warning", Dialog.Message.Warning )
  }

  /**
   * Displays an error message.
   * @param error The text of the message.
   */
  def errorMessage( error: String ) {
    Dialog.showMessage( scrollPane, error, "ProofTool Error", Dialog.Message.Error )
  }

  /**
   * Displays a question.
   * @param question The text of the question.
   */
  def questionMessage( question: String ) =
    Dialog.showConfirmation( scrollPane, question, "ProofTool Question", Dialog.Options.YesNo, Message.Question )

  def getExceptionString( e: Throwable ): String = {
    val st = e.toString.replaceAll( ",", "," + nLine ) + nLine
    val trace = e.getStackTrace
    if ( trace.length > 10 )
      Range( 0, 10 ).map( i => trace.apply( i ) ).foldLeft( st )( ( s, x ) => s + nLine + "   at " + x.toString ) + nLine + "   ......."
    else e.getStackTrace.toString
  }

  protected val chooser = new FileChooser {
    val extensions = List( ".gz", ".ivy", ".lks", ".lksc", ".llk", ".pdf", ".png", ".rs", ".tex", ".tptp", ".xml" )
    extensions.foreach( fe => peer.addChoosableFileFilter(
      new FileFilter {
        def accept( f: File ): Boolean = {
          if ( f.getName.endsWith( fe ) || f.isDirectory ) true
          else false
        }
        def getDescription = fe
      }
    ) )

    fileFilter = acceptAllFileFilter
  }

  /*
  val toolbar = new BoxPanel(Orientation.Horizontal) {
    val tmp = new ButtonGroup
    val lens = new ToggleButton("Lens") {
    //  icon = new ImageIcon("../tu.gif")
      size = new Dimension(30,10)
    }
    val zIn = new Button(Action("Zoom In") { zoomIn })
    val zOut = new Button(Action("Zoom Out") { zoomOut })
    tmp.buttons ++= List(lens, zIn, zOut)
    contents ++= tmp.buttons
    border = Swing.EmptyBorder(0,0,0,0)
  }
  */

  // Menus and menu items

  protected def exportToPDFButton = MenuButtons.exportToPDFButton( this )

  protected def exportToPNGButton = MenuButtons.exportToPNGButton( this )

  protected def zoomInButton = MenuButtons.zoomInButton( this )

  protected def zoomOutButton = MenuButtons.zoomOutButton( this )

  /**
   *
   * @return The contents of the "File" menu.
   */
  def fileMenuContents: Seq[Component] = Seq( exportToPDFButton, exportToPNGButton )

  /**
   *
   * @return The contents of the "View" menu.
   */
  def viewMenuContents: Seq[Component] = Seq( zoomInButton, zoomOutButton )

}

object prooftool {
  /**
   * Starts prooftool from the cli.
   * @param x The object to be displayed.
   */
  def apply( x: AnyRef ) = ProofToolViewer.display( "From CLI", x )
}