package at.logic.gapt.prooftool

import java.awt.Color

import at.logic.gapt.formats.latex.ProofToLatexExporter
import at.logic.gapt.formats.llk.HybridLatexExporter
import at.logic.gapt.formats.xml.XMLExporter
import at.logic.gapt.proofs.lk.base.LKProof
import at.logic.gapt.proofs.lk.{ getAuxFormulas, getCutAncestors }
import at.logic.gapt.proofs.proofs.TreeProof
import java.io.{ BufferedWriter => JBufferedWriter, FileWriter => JFileWriter, ByteArrayInputStream, InputStreamReader, File }

import scala.swing.event.Key
import scala.swing.{ Menu, FileChooser, Action, Separator }

/**
 * Created by sebastian on 12/13/15.
 */
class TreeProofViewer[T]( name: String, proof: TreeProof[T] ) extends ProofToolViewer[TreeProof[T]]( name, proof ) {
  override type MainComponentType = DrawProof[T]
  override def createMainComponent( fSize: Int ) = new DrawProof( this, proof, fSize, None, "" )

}

class OldLKViewer( name: String, proof: LKProof ) extends TreeProofViewer( name, proof ) { main =>

  override val mBar = new PTMenuBar( this ) {

    contents += new Menu( "File" ) {
      mnemonic = Key.F
      contents ++= Seq( exportToPDFButton, exportToPNGButton )
    }

    contents += new Menu( "View" ) {
      mnemonic = Key.V

      contents ++= Seq( zoomInButton, zoomOutButton, new Separator() )

      contents += new PTCheckMenuItem( main, canBeDisabled = false, "Hide structural rules" ) {
        outer =>

        action = Action( "Hide structural rules" ) {
          if ( outer.selected )
            main.publisher.publish( HideStructuralRules )
          else
            main.publisher.publish( ShowAllRulesOld( main.content ) )
        }
      }

      contents += new PTCheckMenuItem( main, canBeDisabled = false, "Hide sequent contexts" ) {
        outer =>

        action = Action( "Hide sequent contexts" ) {
          if ( outer.selected )
            main.hideSequentContext()
          else
            main.showAllFormulas()
        }
      }

      contents += new PTCheckMenuItem( main, canBeDisabled = false, "Mark cut ancestors" ) {
        outer =>

        action = Action( "Mark cut ancestors" ) {
          if ( outer.selected )
            main.markCutAncestors()
          else
            main.removeMarking()
        }
      }
    }

    contents += helpMenu
  }

  def fSave( name: String, proof: LKProof ) {
    chooser.fileFilter = chooser.acceptAllFileFilter
    chooser.showSaveDialog( mBar ) match {
      case FileChooser.Result.Approve =>
        scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
        val result = chooser.selectedFile.getPath
        // val pair = body.getContent.getData.get
        try {
          if ( result.endsWith( ".xml" ) || chooser.fileFilter.getDescription == ".xml" ) {
            XMLExporter( result, name, proof )
          } else if ( result.endsWith( ".llk" ) || chooser.fileFilter.getDescription == ".llk" ) {
            val filename = if ( result.endsWith( ".llk" ) ) result else result + ".llk"
            val file = new JBufferedWriter( new JFileWriter( filename ) )
            file.write( HybridLatexExporter( proof, escape_latex = true ) )
            file.close()
          } else if ( result.endsWith( ".tex" ) || chooser.fileFilter.getDescription == ".tex" ) {
            val filename = if ( result.endsWith( ".tex" ) ) result else result + ".tex"
            val file = new JBufferedWriter( new JFileWriter( filename ) )
            file.write( ProofToLatexExporter( proof ) )
            file.close()
          } else infoMessage( "Proofs cannot be saved in this format." )
        } catch { case e: Throwable => errorMessage( "Cannot save the proof! " + dnLine + getExceptionString( e ) ) }
        finally { scrollPane.cursor = java.awt.Cursor.getDefaultCursor }
      case _ =>
    }
  }
  def markCutAncestors() {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    publisher.publish( ChangeFormulaColor( getCutAncestors( proof ), Color.green, reset = false ) )
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  def removeMarking(): Unit = {
    publisher.publish( ChangeFormulaColor( Set(), Color.white, reset = true ) )
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  def hideSequentContext() {
    mainComponent.setVisibleOccurrences( Some( getAuxFormulas( proof ) ) )
    mainComponent.revalidate()
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  def hideAllFormulas() {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    mainComponent.setVisibleOccurrences( Some( Set() ) )
    mainComponent.revalidate()
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  def showAllFormulas() {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    mainComponent.setVisibleOccurrences( None )
    mainComponent.revalidate()
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }
}