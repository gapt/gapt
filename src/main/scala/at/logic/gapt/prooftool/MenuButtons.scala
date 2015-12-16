package at.logic.gapt.prooftool

import java.awt.event.{ ActionEvent, KeyEvent }
import javax.swing.KeyStroke

import scala.swing.event.Key
import scala.swing.{ CheckMenuItem, Action, MenuItem }

/**
 * Created by sebastian on 12/14/15.
 */

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
   * @return A menu button that calls main's zoomIn function.
   */
  def zoomInButton( main: ProofToolViewer[_] ) = new MenuItem( Action( "Zoom in" ) {
    main.zoomIn()
  } ) {
    this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_UP, ActionEvent.ALT_MASK ) )

  }

  /**
   *
   * @param main An instance of ProoftoolViewer
   * @return A menu button that calls main's zoomOUt function.
   */
  def zoomOutButton( main: ProofToolViewer[_] ) = new MenuItem( Action( "Zoom out" ) {
    main.zoomOut()
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
   * @param main An instance of ProoftoolViewer with ContainsLKProof.
   * @return A menu button that calls main's hideSequentContext/showAllFormulas function.
   */
  def hideContextsButton( main: ProofToolViewer[_] with ContainsLKProof ) = new CheckMenuItem( "Hide sequent contexts" ) {
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
        main.removeMarking()
    }
  }
}

/**
 * A trait for ProofToolViewer objects that can save their contents.
 * @tparam T The type of the content object.
 */
trait Savable[-T] {
  /**
   * Saves an object to disk.
   * @param name
   * @param obj The object to be saved.
   */
  def fSave( name: String, obj: T ): Unit
}

/**
 * A trait for ProofToolViewer objects that contain (old or new) LK proofs.
 */
trait ContainsLKProof {
  /**
   * Hides structural rules in the proof.
   */
  def hideStructuralRules(): Unit

  /**
   * Shows all rules in the proof.
   */
  def showAllRules(): Unit

  /**
   * Hides all formulas except main and auxiliary ones.
   */
  def hideSequentContext(): Unit

  /**
   * Shows all formulas in the proof
   */
  def showAllFormulas(): Unit

  /**
   * Marks the ancestors of cut formulas.
   */
  def markCutAncestors(): Unit

  /**
   * Removes all markings.
   */
  def removeMarking(): Unit
}