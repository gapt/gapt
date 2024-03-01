package gapt.prooftool

import os._
import gapt.expr.formula.Formula
import gapt.formats.json._
import gapt.formats.latex.LatexExporter
import gapt.proofs._
import gapt.proofs.lk.LKProof
import gapt.formats.llk.exportLLK
import gapt.proofs.lk.transformations.LKToExpansionProof
import gapt.proofs.lk.util.isMaeharaMG3i
import gapt.proofs.nd.NDProof

import scala.swing._

/**
 * A ProofToolViewer for dag proofs.
 *
 * @param name The name to be displayed at the top.
 * @param proof The proof to be displayed.
 * @tparam T The type of dag proof.
 */
abstract class DagProofViewer[T <: DagProof[T]]( name: String, proof: DagProof[T] )
  extends ScrollableProofToolViewer[DagProof[T]]( name, proof ) {
}

/**
 * A ProofToolViewer for sequent proofs.
 *
 * @param name The name to be displayed at the top.
 * @param proof The proof to be displayed.
 * @tparam F
 * @tparam T The type of sequent proof.
 */
class SequentProofViewer[F, T <: SequentProof[F, T]]( name: String, proof: SequentProof[F, T],
                                                      sequent_element_renderer: F => String )
  extends DagProofViewer[T]( name, proof ) with ContainsSequentProof {
  override type MainComponentType = DrawSequentProof[F, T]
  override def createMainComponent = new DrawSequentProof(
    this,
    proof,
    Set(),
    Set(),
    sequent_element_renderer,
    Nil )

  scrollPane.border = Swing.EmptyBorder( 0, 0, 10, 0 )

  override def viewMenuContents = super.viewMenuContents ++ Seq(
    removeAllMarkingsButton, new Separator(),
    sunburstViewButton, new Separator(),
    hideContextsButton )

  def hideSequentContext() = publisher.publish( HideSequentContexts )

  def showAllFormulas() = publisher.publish( ShowAllFormulas )

  /**
   * Displays the dag proof in sunburst form.
   */
  def sunburstView(): Unit = {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    initSunburstDialog( name, content )
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  def initSunburstDialog( name: String, proof: DagProof[T] ): Unit = {
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
    publisher.publish( MarkOccurrences( pos, is ) )
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
    publisher.publish( MarkOccurrences( pos, is ) )

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
class LKProofViewer( name: String, proof: LKProof )
  extends SequentProofViewer[Formula, LKProof]( name, proof, LatexExporter( _ ) )
  with Savable[DagProof[LKProof]] with ContainsLKProof {
  override def viewMenuContents = super.viewMenuContents ++ Seq(
    hideStructuralRulesButton, markCutAncestorsButton, markNonIntuitionisticInferencesButton, new Separator(),
    viewExpansionProofButton )

  /**
   * Displays the expansion proof of proof in a new window.
   */
  def expansionTree(): Unit = {
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      prooftool( LKToExpansionProof( proof ), "Expansion tree" )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    } catch {
      case e: Throwable =>
        errorMessage( "Cannot extract expansion tree." + dnLine + getExceptionString( e ) )
    } finally { scrollPane.cursor = java.awt.Cursor.getDefaultCursor }

  }

  def saveFormats = Map(
    ".llk" -> { (p: DagProof[LKProof]) => exportLLK( p.subProofAt(Nil) ) },
    ".tex" -> { (p: DagProof[LKProof]) => LatexExporter( p.subProofAt(Nil) ) },
    ".json" -> { (p: DagProof[LKProof]) => JsonExporter( p.subProofAt(Nil) ).toString } )

  def hideStructuralRules(): Unit = publisher.publish( HideStructuralRules )
  def showAllRules(): Unit = publisher.publish( ShowAllRules( Nil ) )

  def markCutAncestors(): Unit = {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    publisher.publish( MarkCutAncestors )
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  def unmarkCutAncestors(): Unit = {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    publisher.publish( UnmarkCutAncestors )
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  def markNonIntuitionisticInferences( p: LKProof, pos: List[Int] ): Unit = {
    for ( is <- isMaeharaMG3i.checkInference( p ).left )
      publisher.publish( MarkOccurrences( pos, is.toSet ) )

    for ( ( q, j ) <- p.immediateSubProofs.zipWithIndex )
      markNonIntuitionisticInferences( q, j :: pos )
  }
  def markNonIntuitionisticInferences(): Unit =
    markNonIntuitionisticInferences( proof, Nil )
  def markNonIntuitionisticInferencesButton =
    new MenuItem( Action( "Mark non-intuitionistic inferences" ) {
      markNonIntuitionisticInferences()
    } )

  // New menu buttons
  def markCutAncestorsButton = MenuButtons.marCutAncestorsButton( this )

  def viewExpansionProofButton = new MenuItem( Action( "View expansion proof" ) {
    expansionTree()
  } )

  def hideStructuralRulesButton = MenuButtons.hideStructuralRulesButton( this )

}

class NDProofViewer( name: String, proof: NDProof )
  extends SequentProofViewer[Formula, NDProof]( name, proof, LatexExporter( _ ) ) with Savable[DagProof[NDProof]] {

  def saveFormats = Map(
    ".json" -> { (p: DagProof[NDProof]) => JsonExporter( p.subProofAt(Nil) ).toString } )
}
