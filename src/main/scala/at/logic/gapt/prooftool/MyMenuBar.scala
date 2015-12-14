package at.logic.gapt.prooftool

import java.awt.Color
import java.awt.event.{ ActionEvent, KeyEvent }
import javax.swing.KeyStroke
import at.logic.gapt.proofs.DagProof
import at.logic.gapt.proofs.lkNew.{ CutRule, LKProof }

import scala.swing.event.Key
import scala.swing._

/**
 * Created by marty on 10/14/14.
 * The Menubar has not too much logic and mainly calls the Main object to perform tasks.
 */
class PTMenuBar( main: ProofToolViewer[_] ) extends MenuBar {
  focusable = true

  val exportToPDFButton = new PTMenuItem( main, canBeDisabled = true, Action( "Export to PDF" ) {
    main.fExportPdf( main.mainComponent )
  } ) {
    mnemonic = Key.D
    this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_D, ActionEvent.CTRL_MASK ) )
  }

  val exportToPNGButton = new PTMenuItem( main, canBeDisabled = true, Action( "Export to PNG" ) {
    main.fExportPng( main.mainComponent )
  } ) {
    mnemonic = Key.N
    this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_N, ActionEvent.CTRL_MASK ) )
  }

  val zoomInButton = new MenuItem( Action( "Zoom in" ) {
    main.zoomIn()
  } ) {
    this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_UP, ActionEvent.ALT_MASK ) )

  }

  val zoomOutButton = new MenuItem( Action( "Zoom out" ) {
    main.zoomOut()
  } ) {
    this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_DOWN, ActionEvent.ALT_MASK ) )

  }

  val aboutButton = new MenuItem( Action( "About" ) { new About( main ).apply() } ) {
    mnemonic = Key.A
  }

  val helpMenu = new Menu( "Help" ) {
    mnemonic = Key.H
    contents += aboutButton
  }
}

/*class HistoryMenu(main: PTMain[_]) extends Menu("History") {
  mnemonic = Key.I
  def update( history: List[( String, AnyRef, Int )] ) = {
    contents.clear()
    contents += new MenuItem( Action( "Clear History" ) {
      main.clearLauncherHistory()
    } )
    contents += new Separator
    for ( ( name, obj, size ) <- history )
      contents += new MenuItem(
        Action( name + " (" + size + ")" ) {
          main.updateLauncher( name, obj, size )
        }
      )
  }
}*/

class PTMenuItem( main: ProofToolViewer[_], canBeDisabled: Boolean, action: Action ) extends MenuItem( action ) {
  border = Swing.EmptyBorder( 5, 3, 5, 3 )
  listenTo( main.publisher )

  if ( canBeDisabled )
    reactions += {
      case DisableMenus => enabled = false
      case EnableMenus  => enabled = true
    }
}

class PTCheckMenuItem( main: ProofToolViewer[_], canBeDisabled: Boolean, title0: String ) extends CheckMenuItem( title0 ) {
  border = Swing.EmptyBorder( 5, 3, 5, 3 )
  listenTo( main.publisher )

  if ( canBeDisabled )
    reactions += {
      case DisableMenus => enabled = false
      case EnableMenus  => enabled = true
    }
}