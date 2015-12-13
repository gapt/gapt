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
class PTMenuBar( main: PTMain[_] ) extends MenuBar {
  focusable = true

  contents += fileMenu
  contents += viewMenu
  //contents += historyMenu
  contents += helpMenu

  def fileMenu = new Menu( "File" ) {
    mnemonic = Key.F
    /*contents += new PTMenuItem(main, canBeDisabled = false, Action( "Open..." ) {
    main.fOpen()
  } ) {
    mnemonic = Key.O
    this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_O, ActionEvent.CTRL_MASK ) )

  }*/

    contents += new PTMenuItem( main, canBeDisabled = true, Action( "Save all as..." ) {
      main.fSaveAll()
    } ) {
      mnemonic = Key.A
      this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_A, ActionEvent.CTRL_MASK ) )
    }
    contents += new Separator

    contents += new PTMenuItem( main, canBeDisabled = true, Action( "Export to PDF" ) {
      main.fExportPdf( main.mainComponent )
    } ) {
      mnemonic = Key.D
      this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_D, ActionEvent.CTRL_MASK ) )
    }
    contents += new PTMenuItem( main, canBeDisabled = true, Action( "Export to PNG" ) {
      main.fExportPng( main.mainComponent )
    } ) {
      mnemonic = Key.N
      this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_N, ActionEvent.CTRL_MASK ) )
    }
  }

  def viewMenu = new Menu( "View" ) {
    mnemonic = Key.V
    listenTo( main.publisher )
    reactions += {
      case DisableMenus => enabled = false
      case EnableMenus  => enabled = true
    }
    contents += new MenuItem( Action( "Zoom In" ) {
      main.zoomIn()
    } ) {
      this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_UP, ActionEvent.ALT_MASK ) )

    }
    contents += new MenuItem( Action( "Zoom Out" ) {
      main.zoomOut()
    } ) {
      this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_DOWN, ActionEvent.ALT_MASK ) )

    }
  }

  def helpMenu = new Menu( "Help" ) {
    mnemonic = Key.H
    contents += new MenuItem( Action( "About" ) { new About( main ).apply() } ) {
      mnemonic = Key.A

    }
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

class PTMenuItem( main: PTMain[_], canBeDisabled: Boolean, action: Action ) extends MenuItem( action ) {
  border = Swing.EmptyBorder( 5, 3, 5, 3 )
  listenTo( main.publisher )

  if ( canBeDisabled )
    reactions += {
      case DisableMenus => enabled = false
      case EnableMenus  => enabled = true
    }
}

class PTCheckMenuItem( main: PTMain[_], canBeDisabled: Boolean, title0: String ) extends CheckMenuItem( title0 ) {
  border = Swing.EmptyBorder( 5, 3, 5, 3 )
  listenTo( main.publisher )

  if ( canBeDisabled )
    reactions += {
      case DisableMenus => enabled = false
      case EnableMenus  => enabled = true
    }
}