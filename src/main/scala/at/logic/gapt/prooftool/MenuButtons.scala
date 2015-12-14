package at.logic.gapt.prooftool

import java.awt.event.{ ActionEvent, KeyEvent }
import javax.swing.KeyStroke

import scala.swing.event.Key
import scala.swing.{ CheckMenuItem, Action, MenuItem }

/**
 * Created by sebastian on 12/14/15.
 */
object MenuButtons {
  def exportToPDFButton( main: ProofToolViewer[_] ) = new MenuItem( Action( "Export to PDF" ) {
    main.fExportPdf( main.mainComponent )
  } ) {
    mnemonic = Key.D
    this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_D, ActionEvent.CTRL_MASK ) )
  }

  def exportToPNGButton( main: ProofToolViewer[_] ) = new MenuItem( Action( "Export to PNG" ) {
    main.fExportPng( main.mainComponent )
  } ) {
    mnemonic = Key.N
    this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_N, ActionEvent.CTRL_MASK ) )
  }

  def zoomInButton( main: ProofToolViewer[_] ) = new MenuItem( Action( "Zoom in" ) {
    main.zoomIn()
  } ) {
    this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_UP, ActionEvent.ALT_MASK ) )

  }

  def zoomOutButton( main: ProofToolViewer[_] ) = new MenuItem( Action( "Zoom out" ) {
    main.zoomOut()
  } ) {
    this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_DOWN, ActionEvent.ALT_MASK ) )
  }

  def saveAsButton[T]( main: ProofToolViewer[T] with Savable[T] ) = new MenuItem( Action( "Save as..." ) {
    main.fSave( main.name, main.content )
  } ) {
    mnemonic = Key.S
    this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_S, ActionEvent.CTRL_MASK ) )
  }

  def hideStructuralRulesButton( main: ProofToolViewer[_] with ContainsLKProof ) = new CheckMenuItem( "Hide structural rules" ) {
    outer =>

    action = Action( "Hide structural rules" ) {
      if ( outer.selected )
        main.hideStructuralRules()
      else
        main.showAllRules()
    }
  }

  def hideContextsButton( main: ProofToolViewer[_] with ContainsLKProof ) = new CheckMenuItem( "Hide sequent contexts" ) {
    outer =>

    action = Action( "Hide sequent contexts" ) {
      if ( outer.selected )
        main.hideSequentContext()
      else
        main.showAllFormulas()
    }
  }

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

trait Savable[-T] {
  def fSave( name: String, obj: T ): Unit
}

trait ContainsLKProof {
  def hideStructuralRules(): Unit
  def showAllRules(): Unit
  def hideSequentContext(): Unit
  def showAllFormulas(): Unit
  def markCutAncestors(): Unit
  def removeMarking(): Unit
}