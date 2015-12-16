package at.logic.gapt.prooftool

import at.logic.gapt.proofs.expansionTrees.{ ExpansionProofToLK, ExpansionSequent }

import scala.swing.event.Key
import scala.swing.{ Separator, Menu, Action, MenuItem }

/**
 * Created by sebastian on 12/13/15.
 */

/**
 * ProofToolViewer for expansion sequents.
 * @param name The name to be displayed at the top.
 * @param es The expansion sequent to be displayed.
 */
class ExpansionSequentViewer( name: String, es: ExpansionSequent ) extends ProofToolViewer[ExpansionSequent]( name, es ) {
  override type MainComponentType = DrawExpansionSequent

  override def createMainComponent( fSize: Int ) = new DrawExpansionSequent( this, es, fSize )

  override def viewMenuContents = super.viewMenuContents ++ Seq( new Separator(), viewLKProofButton )

  def lkproof() {
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      val p = ExpansionProofToLK( content )
      val viewer = new LKProofViewer( "LK proof", p )
      viewer.showFrame()
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
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