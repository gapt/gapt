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
import at.logic.gapt.proofs.lkOld.UnfoldException
import at.logic.gapt.proofs.lkOld.base.OccSequent
import at.logic.gapt.proofs.lkOld.base.RichOccSequent
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lkOld
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
import at.logic.gapt.formats.llk.HybridLatexExporter
import at.logic.gapt.formats.tptp.TPTPFOLExporter

object ProofToolViewer {
  /**
   * Displays various objects in prooftool. Creates an instance of the appropriate viewer.
   * @param name The title to be displayed.
   * @param obj The object to be displayed.
   */
  def display( name: String, obj: AnyRef ) {
    obj match {
      case p: LKProof             => new LKProofViewer( name, p ).showFrame()
      case p: SequentProof[a, b]  => new SequentProofViewer[a, b]( name, p ).showFrame()
      case es: ExpansionSequent   => new ExpansionSequentViewer( name, es ).showFrame()
      case p: lkOld.base.LKProof  => new OldLKViewer( name, p ).showFrame()
      case p: TreeProof[_]        => new TreeProofViewer( name, p ).showFrame()
      case p: Proof[_]            => new ResolutionProofViewer( name, p ).showFrame()
      case list: List[HOLSequent] => new ListViewer( name, list ).showFrame()
      case seq: HOLSequent        => new ListViewer( name, List( seq ) ).showFrame()
      case set: Set[HOLSequent]   => new ListViewer( name, set.toList ).showFrame()
      case tree: Tree[a]          => new TreeViewer[a]( name, tree ).showFrame()
      case db: ProofDatabase =>
        for ( p <- db.proofs )
          display( p._1, p._2 )

      case _ => throw new IllegalArgumentException( s"Objects of type ${obj.getClass} can't be displayed." )
    }
  }
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

  /**
   * Opens a proof db and displays all its contents.
   */
  def fOpen() {
    chooser.fileFilter = chooser.acceptAllFileFilter
    chooser.showOpenDialog( mBar ) match {
      case FileChooser.Result.Approve =>
        def display = ( ProofToolViewer.display _ ).tupled
        scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
        val parser = new FileParser( this )
        parser.parseFile( chooser.selectedFile.getPath )
        for ( p <- parser.getProofs )
          display( p )

        for ( l <- parser.getSequentLists )
          display( l )

        for ( t <- parser.getTermTrees )
          display( ( t._1, t._3 ) )

        for ( p <- parser.getResolutionProofs )
          display( p )

        scrollPane.cursor = java.awt.Cursor.getDefaultCursor
        publisher.publish( EnableMenus )
      case _ =>
    }
  }

  def fSaveAll() {
    chooser.fileFilter = chooser.acceptAllFileFilter
    chooser.showSaveDialog( mBar ) match {
      case FileChooser.Result.Approve =>
        val db = new FileParser( this )
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

  // Menus and menu items

  protected def openButton = MenuButtons.openButton( this )

  protected def exportToPDFButton = MenuButtons.exportToPDFButton( this )

  protected def exportToPNGButton = MenuButtons.exportToPNGButton( this )

  protected def zoomInButton = MenuButtons.zoomInButton( this )

  protected def zoomOutButton = MenuButtons.zoomOutButton( this )

  /**
   *
   * @return The contents of the "File" menu.
   */
  def fileMenuContents: Seq[Component] = Seq( openButton, new Separator, exportToPDFButton, exportToPNGButton )

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