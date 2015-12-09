package at.logic.gapt.prooftool

import java.awt.Color
import at.logic.gapt.proofs.DagProof
import at.logic.gapt.proofs.lkNew.{ CutRule, LKProof }

import scala.swing.event.Key
import scala.swing._

/**
 * Created by marty on 10/14/14.
 * The Menubar has not too much logic and mainly calls the Main object to perform tasks.
 */
class MyMenubar extends MenuBar {
  import javax.swing.KeyStroke
  import java.awt.event.{ KeyEvent, ActionEvent => JActionEvent }

  val history_menu = new Menu( "History" ) {
    mnemonic = Key.I
  }

  def updateHistoryMenu( history: List[( String, AnyRef, Int )] ) = {
    history_menu.contents.clear()
    history_menu.contents += new MenuItem( Action( "Clear History" ) {
      Main.clearLauncherHistory()
    } )
    history_menu.contents += new Separator
    for ( ( name, obj, size ) <- history )
      history_menu.contents += new MenuItem(
        Action( name + " (" + size + ")" ) {
          Main.updateLauncher( name, obj, size )
        }
      )
  }

  focusable = true
  val customBorder = Swing.EmptyBorder( 5, 3, 5, 3 )
  contents += new Menu( "File" ) {
    mnemonic = Key.F
    contents += new MenuItem( Action( "Open..." ) { Main.fOpen() } ) {
      mnemonic = Key.O
      this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_O, JActionEvent.CTRL_MASK ) )
      border = customBorder
    }
    contents += new MenuItem( Action( "Save as..." ) { Main.fSave( Main.body.getContent.getData.get ) } ) {
      mnemonic = Key.S
      this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_S, JActionEvent.CTRL_MASK ) )
      border = customBorder
      enabled = false
      listenTo( ProofToolPublisher )
      reactions += {
        case Loaded   => enabled = true
        case UnLoaded => enabled = false
      }
    }
    contents += new MenuItem( Action( "Save all as..." ) { Main.fSaveAll() } ) {
      mnemonic = Key.A
      this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_A, JActionEvent.CTRL_MASK ) )
      border = customBorder
      listenTo( ProofToolPublisher )
      reactions += {
        case DisableMenus => enabled = false
        case EnableMenus  => enabled = true
      }
    }
    contents += new Separator
    contents += new MenuItem( Action( "Export to PDF" ) { Main.fExportPdf( Main.body.getContent.contents.headOption ) } ) {
      mnemonic = Key.D
      this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_D, JActionEvent.CTRL_MASK ) )
      border = customBorder
      listenTo( ProofToolPublisher )
      reactions += {
        case DisableMenus => enabled = false
        case EnableMenus  => enabled = true
      }
    }
    contents += new MenuItem( Action( "Export to PNG" ) { Main.fExportPng( Main.body.getContent.contents.headOption ) } ) {
      mnemonic = Key.N
      this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_N, JActionEvent.CTRL_MASK ) )
      border = customBorder
      listenTo( ProofToolPublisher )
      reactions += {
        case DisableMenus => enabled = false
        case EnableMenus  => enabled = true
      }
    }
  }

  contents += new Menu( "View" ) {
    mnemonic = Key.V
    listenTo( ProofToolPublisher )
    reactions += {
      case DisableMenus => enabled = false
      case EnableMenus  => enabled = true
    }
    contents += new MenuItem( Action( "Zoom In" ) {
      Main.zoomIn()
    } ) {
      this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_UP, JActionEvent.ALT_MASK ) )
      border = customBorder
    }
    contents += new MenuItem( Action( "Zoom Out" ) {
      Main.zoomOut()
    } ) {
      this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_DOWN, JActionEvent.ALT_MASK ) )
      border = customBorder
    }

    contents += new Separator()

    contents += new CheckMenuItem( "Hide structural rules" ) {
      outer =>
      border = customBorder
      enabled = false
      listenTo( ProofToolPublisher )
      reactions += {
        case Loaded   => this.enabled = true
        case UnLoaded => this.enabled = false
      }

      action = Action( "Hide structural rules" ) {
        if ( outer.selected )
          ProofToolPublisher.publish( HideStructuralRules )
        else
          Main.body.getContent.getData.get._2 match {
            case p: DagProof[a] => ProofToolPublisher.publish( ShowAllRules( p ) )
          }
      }
    }

    contents += new CheckMenuItem( "Hide sequent contexts" ) {
      outer =>
      border = customBorder
      enabled = false
      listenTo( ProofToolPublisher )
      reactions += {
        case Loaded   => this.enabled = true
        case UnLoaded => this.enabled = false
      }

      action = Action( "Hide sequent contexts" ) {
        if ( outer.selected )
          Main.hideSequentContext()
        else
          Main.showAllFormulas()
      }
    }

    contents += new CheckMenuItem( "Mark cut ancestors" ) {
      outer =>
      border = customBorder
      enabled = false
      listenTo( ProofToolPublisher )
      reactions += {
        case Loaded   => this.enabled = true
        case UnLoaded => this.enabled = false
      }

      action = Action( "Mark cut ancestors" ) {
        if ( outer.selected )
          Main.markCutAncestors()
        else
          Main.removeMarking()
      }
    }

    contents += new Separator()

    contents += new MenuItem( Action( "View LK proof" ) {
      Main.lkproof()
    } ) {
      border = customBorder
      enabled = false
      listenTo( ProofToolPublisher )
      reactions += {
        case Loaded   => enabled = false
        case UnLoaded => enabled = true
      }
    }

    contents += new MenuItem( Action( "View expansion proof" ) {
      Main.expansionTree()
    } ) {
      border = customBorder
      enabled = false
      listenTo( ProofToolPublisher )
      reactions += {
        case Loaded   => enabled = true
        case UnLoaded => enabled = false
      }
    }

    contents += new MenuItem( Action( "Sunburst View" ) {
      Main.sunburstView()
    } ) {
      border = customBorder
      enabled = false
      listenTo( ProofToolPublisher )
      reactions += {
        case Loaded   => enabled = true
        case UnLoaded => enabled = false
      }

    }
  }

  contents += history_menu

  contents += new Menu( "Help" ) {
    mnemonic = Key.H
    contents += new MenuItem( Action( "About" ) { About() } ) {
      mnemonic = Key.A
      border = customBorder
    }
  }
}
