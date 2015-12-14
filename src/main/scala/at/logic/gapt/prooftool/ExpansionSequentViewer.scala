package at.logic.gapt.prooftool

import at.logic.gapt.proofs.expansionTrees.{ ExpansionProofToLK, ExpansionSequent }

import scala.swing.event.Key
import scala.swing.{ Separator, Menu, Action, MenuItem }

/**
 * Created by sebastian on 12/13/15.
 */
class ExpansionSequentViewer( name: String, es: ExpansionSequent ) extends PTMain[ExpansionSequent]( name, es ) {
  override type MainComponentType = DrawExpansionSequent

  override def createMainComponent( fSize: Int ) = new DrawExpansionSequent( this, es, fSize )

  override val mBar = new ESMenuBar( this )

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

class ESMenuBar( main: ExpansionSequentViewer ) extends PTMenuBar( main ) {

  contents += new Menu( "File" ) {
    mnemonic = Key.F

    contents ++= Seq( exportToPDFButton, exportToPNGButton )
  }

  contents += new Menu( "View" ) {
    mnemonic = Key.V

    contents ++= Seq( zoomInButton, zoomOutButton, new Separator() )

    contents += new MenuItem( Action( "View LK proof" ) {
      main.lkproof()
    } )
  }

  contents += helpMenu
}
