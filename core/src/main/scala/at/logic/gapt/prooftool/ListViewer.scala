package at.logic.gapt.prooftool

import java.awt.event.{ KeyEvent, ActionEvent }
import javax.swing.KeyStroke

import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.proofs.HOLSequent
import java.io.{ BufferedWriter => JBufferedWriter, FileWriter => JFileWriter, ByteArrayInputStream, InputStreamReader, File }

import scala.swing.{ Separator, Menu, FileChooser, Action }
import scala.swing.event.Key

/**
 * Created by sebastian on 12/13/15.
 */
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
            file.write( TPTPFOLExporter.tptp_problem( ls ) )
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
