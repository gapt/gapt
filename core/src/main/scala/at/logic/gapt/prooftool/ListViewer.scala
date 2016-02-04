package at.logic.gapt.prooftool

import java.awt.event.{ ActionEvent, KeyEvent }
import javax.swing.KeyStroke

import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.proofs.{ HOLSequent, Sequent }
import java.io.{ ByteArrayInputStream, File, InputStreamReader, BufferedWriter => JBufferedWriter, FileWriter => JFileWriter }

import at.logic.gapt.expr.hol.existsclosure

import scala.swing.{ Action, FileChooser, Menu, Separator }
import scala.swing.event.Key

class ListViewer( name: String, list: List[HOLSequent] ) extends ProofToolViewer[List[HOLSequent]]( name, list ) with Savable[List[HOLSequent]] {
  override type MainComponentType = DrawList
  override def createMainComponent( fSize: Int ) = new DrawList( this, list, fSize )
  override def fileMenuContents = Seq( openButton, saveAsButton, new Separator, exportToPDFButton, exportToPNGButton )

  def fSave( name: String, list: List[HOLSequent] ) {
    chooser.fileFilter = chooser.acceptAllFileFilter
    chooser.showSaveDialog( mBar ) match {
      case FileChooser.Result.Approve =>
        scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
        val result = chooser.selectedFile.getPath
        // val pair = body.getContent.getData.get

        try {
          val ls = list.map {
            case fs: HOLSequent => fs
            case _              => throw new Exception( "Cannot save this kind of lists." )
          }
          if ( result.endsWith( ".tptp" ) || chooser.fileFilter.getDescription == ".tptp" ) {
            val filename = if ( result.endsWith( ".tptp" ) ) result else result + ".tptp"
            val file = new JBufferedWriter( new JFileWriter( filename ) )
            file.write( TPTPFOLExporter( existsclosure( ls.map( _.toImplication ) ++: Sequent() ) ).toString )
            file.close()
          } else infoMessage( "Lists cannot be saved in this format." )
        } catch { case e: Throwable => errorMessage( "Cannot save the list! " + dnLine + getExceptionString( e ) ) }
        finally { scrollPane.cursor = java.awt.Cursor.getDefaultCursor }
      case _ =>
    }
  }

  // Menu buttons
  def saveAsButton = MenuButtons.saveAsButton( this )

}
