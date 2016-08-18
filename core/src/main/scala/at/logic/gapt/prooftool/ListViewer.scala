package at.logic.gapt.prooftool

import better.files._

import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.proofs.{ HOLSequent, Sequent }

import at.logic.gapt.expr.hol.existsclosure

import scala.swing.{ Action, FileChooser, Menu, Separator }

class ListViewer( name: String, list: List[HOLSequent] ) extends ScrollableProofToolViewer[List[HOLSequent]]( name, list ) with Savable[List[HOLSequent]] {
  override type MainComponentType = DrawList
  override def createMainComponent = new DrawList( this, list )
  override def fileMenuContents = Seq( openButton, saveAsButton, new Separator, exportToPDFButton, exportToPNGButton )

  def fSave( name: String, list: List[HOLSequent] ) {
    chooser.fileFilter = chooser.acceptAllFileFilter
    chooser.showSaveDialog( mBar ) match {
      case FileChooser.Result.Approve =>
        mainPanel.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
        val result = chooser.selectedFile.getPath

        try {
          val ls = list.map {
            case fs: HOLSequent => fs
            case _              => throw new Exception( "Cannot save this kind of lists." )
          }
          if ( result.endsWith( ".tptp" ) || chooser.fileFilter.getDescription == ".tptp" ) {
            val filename = if ( result.endsWith( ".tptp" ) ) result else result + ".tptp"
            filename.toFile < TPTPFOLExporter( existsclosure( ls.map( _.toImplication ) ++: Sequent() ) ).toString
          } else infoMessage( "Lists cannot be saved in this format." )
        } catch { case e: Throwable => errorMessage( "Cannot save the list! " + dnLine + getExceptionString( e ) ) }
        finally { mainPanel.cursor = java.awt.Cursor.getDefaultCursor }
      case _ =>
    }
  }

  // Menu buttons
  def saveAsButton = MenuButtons.saveAsButton( this )

}
