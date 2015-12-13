package at.logic.gapt.prooftool

import at.logic.gapt.proofs.expansionTrees.{ ExpansionProofToLK, ExpansionSequent }

import scala.swing.{ Action, MenuItem }

/**
 * Created by sebastian on 12/13/15.
 */
class ExpansionSequentViewer( name: String, es: ExpansionSequent ) extends PTMain[ExpansionSequent]( name, es ) { outer =>
  override type MainComponentType = DrawExpansionSequent
  override def createMainComponent( fSize: Int ) = new DrawExpansionSequent( this, es, fSize )

  /*  override val mBar = new PTMenuBar( this ) {
    override def viewMenu = {
      val viewMenu_ = super.viewMenu
      viewMenu_.contents += new MenuItem( Action( "View LK proof" ) {
        outer.lkproof()
      } )
      viewMenu_
    }
  }
*/
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
}
