package gapt.prooftool

import ammonite.ops._

import gapt.formats.tptp.TptpFOLExporter
import gapt.proofs.{ HOLSequent, Sequent }

import gapt.expr.hol.existentialClosure

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
            write( Path( filename, pwd ), TptpFOLExporter( existentialClosure( ls.map( _.toImplication ) ++: Sequent() ) ).toString )
          } else infoMessage( "Lists cannot be saved in this format." )
        } catch { case e: Throwable => errorMessage( "Cannot save the list! " + dnLine + getExceptionString( e ) ) }
        finally { mainPanel.cursor = java.awt.Cursor.getDefaultCursor }
      case _ =>
    }
  }

  // Menu buttons
  def saveAsButton = MenuButtons.saveAsButton( this )

}
