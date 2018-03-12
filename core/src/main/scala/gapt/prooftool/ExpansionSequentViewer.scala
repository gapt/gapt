package gapt.prooftool

import gapt.proofs.expansion.{ ExpansionProof, ExpansionProofToLK, ExpansionSequent }

import scala.swing.{ Separator, Menu, Action, MenuItem }

/**
 * ProofToolViewer for expansion sequents.
 *
 * @param name The name to be displayed at the top.
 * @param es The expansion sequent to be displayed.
 */
class ExpansionSequentViewer( name: String, es: ExpansionSequent ) extends ProofToolViewer[ExpansionSequent]( name, es ) {
  override type MainComponentType = DrawExpansionSequent

  override def createMainComponent = new DrawExpansionSequent( this, es )

  override def viewMenuContents = super.viewMenuContents ++ Seq( new Separator(), viewLKProofButton )

  def lkproof() {
    try {
      mainPanel.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val Right( p ) = ExpansionProofToLK( ExpansionProof( content ) )
      val viewer = new LKProofViewer( "LK proof", p )
      viewer.showFrame()
      mainPanel.cursor = java.awt.Cursor.getDefaultCursor
    } catch {
      case e: Throwable =>
        errorMessage( "Cannot extract LK proof!" + dnLine + getExceptionString( e ) )
    }
  }

  // New menu button
  def viewLKProofButton = new MenuItem( Action( "View LK proof" ) {
    lkproof()
  } )
}