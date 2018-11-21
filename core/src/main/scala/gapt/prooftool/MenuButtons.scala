package gapt.prooftool

import java.awt.event.{ ActionEvent, KeyEvent }

import javax.swing.KeyStroke

import scala.swing.event.Key
import scala.swing.{ Action, CheckMenuItem, FileChooser, MenuItem }

/**
 * An object that contains some common menu buttons.
 */
object MenuButtons {

  /**
   *
   * @param main An instance of ProoftoolViewer
   * @return A menu button that calls main's fOpen function.
   */
  def openButton( main: ProofToolViewer[_] ) = new MenuItem( Action( "Open ..." ) {
    main.fOpen()

  } ) {
    mnemonic = Key.O
    this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_O, ActionEvent.CTRL_MASK ) )
  }

  /**
   *
   * @param main An instance of ProoftoolViewer
   * @return A menu button that calls main's exportToPDF function.
   */
  def exportToPDFButton( main: ProofToolViewer[_] ) = new MenuItem( Action( "Export to PDF" ) {
    main.fExportPdf( main.mainComponent )
  } ) {
    mnemonic = Key.D
    this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_D, ActionEvent.CTRL_MASK ) )
  }

  /**
   *
   * @param main An instance of ProoftoolViewer
   * @return A menu button that calls main's exportToPNG function.
   */
  def exportToPNGButton( main: ProofToolViewer[_] ) = new MenuItem( Action( "Export to PNG" ) {
    main.fExportPng( main.mainComponent )
  } ) {
    mnemonic = Key.N
    this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_N, ActionEvent.CTRL_MASK ) )
  }

  /**
   *
   * @param main An instance of ProoftoolViewer
   * @return A menu button that calls main's increaseFontSize function.
   */
  def increaseFontSizeButton( main: ProofToolViewer[_] ) = new MenuItem( Action( "Increase font size" ) {
    main.increaseFontSize()
  } ) {
    this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_UP, ActionEvent.ALT_MASK ) )

  }

  /**
   *
   * @param main An instance of ProoftoolViewer
   * @return A menu button that calls main's decreaseFontSize function.
   */
  def decreaseFontSizeButton( main: ProofToolViewer[_] ) = new MenuItem( Action( "Decrease font size" ) {
    main.decreaseFontSize()
  } ) {
    this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_DOWN, ActionEvent.ALT_MASK ) )
  }

  /**
   *
   * @param main An instance of ProoftoolViewer with Savable.
   * @return A menu button that calls main's saveAs function.
   */
  def saveAsButton[T]( main: ProofToolViewer[T] with Savable[T] ) = new MenuItem( Action( "Save as..." ) {
    main.fSave( main.name, main.content )
  } ) {
    mnemonic = Key.S
    this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_S, ActionEvent.CTRL_MASK ) )
  }

  /**
   *
   * @param main An instance of ProoftoolViewer with ContainsLKProof.
   * @return A menu button that calls main's hideStructuralRules/showAllRules function.
   */
  def hideStructuralRulesButton( main: ProofToolViewer[_] with ContainsLKProof ) = new CheckMenuItem( "Hide structural rules" ) {
    outer =>

    action = Action( "Hide structural rules" ) {
      if ( outer.selected )
        main.hideStructuralRules()
      else
        main.showAllRules()
    }
  }

  /**
   *
   * @param main An instance of ProoftoolViewer with ContainsSequentProof.
   * @return A menu button that calls main's hideSequentContext/showAllFormulas function.
   */
  def hideContextsButton( main: ProofToolViewer[_] with ContainsSequentProof ) = new CheckMenuItem( "Hide sequent contexts" ) {
    outer =>

    action = Action( "Hide sequent contexts" ) {
      if ( outer.selected )
        main.hideSequentContext()
      else
        main.showAllFormulas()
    }
  }

  /**
   *
   * @param main An instance of ProoftoolViewer with ContainsLKProof.
   * @return A menu button that calls main's markCutAncestors/removeMarking function.
   */
  def marCutAncestorsButton( main: ProofToolViewer[_] with ContainsLKProof ) = new CheckMenuItem( "Mark cut ancestors" ) {
    outer =>

    action = Action( "Mark cut ancestors" ) {
      if ( outer.selected )
        main.markCutAncestors()
      else
        main.unmarkCutAncestors()
    }
  }

  def removeAllMarkingsButton( main: ProofToolViewer[_] with ContainsSequentProof ) = new MenuItem( Action( "Remove all markings" ) {
    main.removeAllMarkings()
  } )

  def ShowDebugBordersButton( main: ProofToolViewer[_] ) = new CheckMenuItem( "Show debug borders" ) {
    outer =>

    action = Action( "Show debug borders" ) {
      if ( outer.selected )
        main.publisher.publish( ShowDebugBorders )
      else
        main.publisher.publish( HideDebugBorders )
    }
  }
}

trait ContainsSequentProof {
  /**
   * Hides all formulas except main and auxiliary ones.
   */
  def hideSequentContext(): Unit

  /**
   * Shows all formulas in the proof
   */
  def showAllFormulas(): Unit

  /**
   * Removes all markings.
   */
  def removeAllMarkings(): Unit
}

/**
 * A trait for ProofToolViewer objects that contain (old or new) LK proofs.
 */
trait ContainsLKProof extends ContainsSequentProof {
  /**
   * Hides structural rules in the proof.
   */
  def hideStructuralRules(): Unit

  /**
   * Shows all rules in the proof.
   */
  def showAllRules(): Unit

  /**
   * Marks the ancestors of cut formulas.
   */
  def markCutAncestors(): Unit

  /**
   * Unmarks the ancestors of cut formulas.
   */
  def unmarkCutAncestors(): Unit
}