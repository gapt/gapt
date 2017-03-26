package at.logic.gapt.prooftool

import ammonite.ops._
import at.logic.gapt.expr.Formula
import at.logic.gapt.formats.latex.LatexExporter
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lk.{ LKProof, LKToExpansionProof }
import at.logic.gapt.formats.llk.exportLLK

import scala.swing._

/**
 * A ProofToolViewer for dag proofs.
 *
 * @param name The name to be displayed at the top.
 * @param proof The proof to be displayed.
 * @tparam T The type of dag proof.
 */
abstract class DagProofViewer[T <: DagProof[T]]( name: String, proof: DagProof[T] ) extends ScrollableProofToolViewer[DagProof[T]]( name, proof ) {
  override val content = proof

}

/**
 * A ProofToolViewer for sequent proofs.
 *
 * @param name The name to be displayed at the top.
 * @param proof The proof to be displayed.
 * @tparam F
 * @tparam T The type of sequent proof.
 */
class SequentProofViewer[F, T <: SequentProof[F, T]]( name: String, proof: SequentProof[F, T], sequent_element_renderer: F => String ) extends DagProofViewer[T]( name, proof ) with ContainsSequentProof {
  override type MainComponentType = DrawSequentProof[F, T]
  override def createMainComponent = new DrawSequentProof(
    this,
    proof,
    Set(),
    Set(),
    sequent_element_renderer,
    Nil
  )

  scrollPane.border = Swing.EmptyBorder( 0, 0, 10, 0 )

  override def viewMenuContents = super.viewMenuContents ++ Seq( removeAllMarkingsButton, new Separator(), sunburstViewButton, new Separator(), hideContextsButton )

  def hideSequentContext() = publisher.publish( HideSequentContexts )

  def showAllFormulas() = publisher.publish( ShowAllFormulas )

  /**
   * Displays the dag proof in sunburst form.
   */
  def sunburstView() {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    initSunburstDialog( name, content )
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  def initSunburstDialog( name: String, proof: DagProof[T] ) {
    val d = new SunburstTreeDialog( this, name, proof, sequent_element_renderer )
    d.pack()
    d.centerOnScreen()
    d.open()
  }

  def sunburstViewButton = new MenuItem( Action( "Sunburst View" ) {
    sunburstView()
  } )

  /**
   * Marks the ancestors of the given formulas in the given proof.
   * @param pos The position of a subproof.
   * @param is A set of indices in the end sequent of the subproof at pos.
   */
  def markAncestors( pos: List[Int], is: Set[SequentIndex] ): Unit = {
    publisher.publish( MarkAncestors( pos, is ) )
    val p = proof.subProofAt( pos )

    for ( j <- p.immediateSubProofs.indices ) {
      val subPos = j :: pos
      val parents = is flatMap { p.occConnectors( j ).parents }
      if ( parents.nonEmpty )
        markAncestors( subPos, parents )
    }
  }

  /**
   * Marks the descendants of the given formulas in the given proof.
   * @param pos The position of a subproof.
   * @param is A set of indices in the end sequent of the subproof at pos.
   */
  def markDescendants( pos: List[Int], is: Set[SequentIndex] ): Unit = {
    publisher.publish( MarkDescendants( pos, is ) )

    val p = proof.subProofAt( pos )

    pos match {
      case Nil => // reached the bottom of the proof
      case j :: js =>
        val s = proof.subProofAt( js )
        val children = is flatMap { s.occConnectors( j ).children }
        if ( children.nonEmpty )
          markDescendants( js, children )
    }
  }

  /**
   * Marks the ancestors and descendants of the given formulas in the given proof.
   * @param pos The position of a subproof.
   * @param is A set of indices in the end sequent of the subproof at pos.
   */
  def markAncestorsAndDescendants( pos: List[Int], is: Set[SequentIndex] ): Unit = {
    markAncestors( pos, is )
    markDescendants( pos, is )
  }

  def removeAllMarkings(): Unit = {
    publisher.publish( UnmarkAllFormulas )
  }

  def hideContextsButton = MenuButtons.hideContextsButton( this )

  def removeAllMarkingsButton = MenuButtons.removeAllMarkingsButton( this )

}

/**
 * A ProofToolViewer for LK proofs.
 *
 * @param name The name to be displayed at the top.
 * @param proof The proof to be displayed.
 */
class LKProofViewer( name: String, proof: LKProof ) extends SequentProofViewer[Formula, LKProof]( name, proof, LatexExporter( _ ) ) with Savable[LKProof] with ContainsLKProof {
  override val content: LKProof = proof
  override def fileMenuContents = Seq( openButton, saveAsButton, new Separator, exportToPDFButton, exportToPNGButton )
  override def viewMenuContents = super.viewMenuContents ++ Seq( hideStructuralRulesButton, markCutAncestorsButton, new Separator(), viewExpansionProofButton )

  /**
   * Displays the expansion proof of proof in a new window.
   */
  def expansionTree() {
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      prooftool( LKToExpansionProof( content ), "Expansion tree" )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    } catch {
      case e: Throwable =>
        errorMessage( "Cannot extract expansion tree." + dnLine + getExceptionString( e ) )
    } finally { scrollPane.cursor = java.awt.Cursor.getDefaultCursor }

  }

  override def fSave( name: String, proof: LKProof ) {
    chooser.fileFilter = chooser.acceptAllFileFilter
    chooser.showSaveDialog( mBar ) match {
      case FileChooser.Result.Approve =>
        scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
        val result = chooser.selectedFile.getAbsolutePath
        // val pair = body.getContent.getData.get
        try {
          if ( result.endsWith( ".llk" ) || chooser.fileFilter.getDescription == ".llk" ) {
            val filename = if ( result.endsWith( ".llk" ) ) result else result + ".llk"
            write( Path( filename ), exportLLK( proof ) )
          } else if ( result.endsWith( ".tex" ) || chooser.fileFilter.getDescription == ".tex" ) {
            val filename = if ( result.endsWith( ".tex" ) ) result else result + ".tex"
            write( Path( filename ), LatexExporter( proof ) )
          } else infoMessage( "Proofs cannot be saved in this format." )
        } catch { case e: Throwable => errorMessage( "Cannot save the proof! " + dnLine + getExceptionString( e ) ) }
        finally { scrollPane.cursor = java.awt.Cursor.getDefaultCursor }
      case _ =>
    }
  }

  def hideStructuralRules(): Unit = publisher.publish( HideStructuralRules )
  def showAllRules(): Unit = publisher.publish( ShowAllRules( Nil ) )

  def markCutAncestors() {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    publisher.publish( MarkCutAncestors )
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  def unmarkCutAncestors(): Unit = {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    publisher.publish( UnmarkCutAncestors )
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  // New menu buttons
  def saveAsButton = MenuButtons.saveAsButton[LKProof]( this.asInstanceOf[ProofToolViewer[LKProof] with Savable[LKProof]] )

  def markCutAncestorsButton = MenuButtons.marCutAncestorsButton( this )

  def viewExpansionProofButton = new MenuItem( Action( "View expansion proof" ) {
    expansionTree()
  } )

  def hideStructuralRulesButton = MenuButtons.hideStructuralRulesButton( this )

}
