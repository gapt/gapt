package at.logic.gapt.prooftool

/**
 * Created with IntelliJ IDEA.
 * User: mrukhaia
 * Date: 4/12/14
 * Time: 2:13 PM
 */

import javax.swing.WindowConstants

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.proofs.{ SequentProof, DagProof }

import scala.swing._
import scala.swing.event._
import java.awt.Color

class SunburstTreeDialog[T <: DagProof[T]]( name: String, proof: DagProof[T] ) extends Frame {
  title = "Sunburst view of " + name
  //modal = false
  preferredSize = new Dimension( 700, 500 )
  peer setDefaultCloseOperation WindowConstants.DISPOSE_ON_CLOSE
  menuBar = new MenuBar() {
    import javax.swing.KeyStroke
    import java.awt.event.{ KeyEvent, ActionEvent => JActionEvent }

    val customBorder = Swing.LineBorder( Color.lightGray, 2 ) // .EmptyBorder(5, 3, 5, 3)
    contents += new Label( "Export as:" ) { border = Swing.EmptyBorder( 5 ) }
    // contents += new Menu("Export") {
    //   mnemonic = Key.E
    contents += new MenuItem( Action( "PDF" ) { Main.fExportPdf( Some( main ) ) } ) {
      mnemonic = Key.D
      this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_D, JActionEvent.CTRL_MASK ) )
      border = customBorder
      preferredSize = new Dimension( 50, 20 )
    }
    contents += new Separator
    contents += new MenuItem( Action( "PNG" ) { Main.fExportPng( Some( main ) ) } ) {
      mnemonic = Key.N
      this.peer.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_N, JActionEvent.CTRL_MASK ) )
      border = customBorder
      preferredSize = new Dimension( 50, 20 )
    }
    contents += Swing.HGlue
    // }
  }

  val main = new SplitPane( Orientation.Vertical ) {
    focusable = true // required to get events from keyboard
    preferredSize = SunburstTreeDialog.this.preferredSize
    dividerLocation = preferredSize.height

    //sunburst model
    val model = new ReactiveSunburstModel( new ProofNode[T]( proof ), new ProofNodeInfo[T]() )
    val sunView = model.getView()
    // inference information
    val info = new DrawSingleSequentInference( Orientation.Vertical )

    sunView.setToolTipEnabled( true )
    sunView.reactions += {
      case NodeSelectedEvent( null ) =>
        info.p_=( Some( model.root.asInstanceOf[ProofNode[T]].proof.asInstanceOf[SequentProof[Nothing, Nothing]] ) )
      case NodeSelectedEvent( p: ProofNode[_] ) =>
        info.p_=( Some( p.proof.asInstanceOf[SequentProof[Nothing, Nothing]] ) )
    }
    sunView.setSelectedNode( null )

    leftComponent = Component.wrap( sunView )
    rightComponent = info

    listenTo( keys, SunburstTreeDialog.this, Main.top, ProofToolPublisher )
    reactions += {
      case WindowClosing( Main.top ) => dispose()
      case UIElementResized( source ) =>
        preferredSize = SunburstTreeDialog.this.size
        if ( preferredSize.width > preferredSize.height ) {
          dividerLocation = preferredSize.height
          orientation = Orientation.Vertical
          info.adjustOrientation( orientation )
        } else {
          dividerLocation = preferredSize.width
          orientation = Orientation.Horizontal
          info.adjustOrientation( orientation )
        }
        revalidate()
      case KeyPressed( _, Key.Up, Key.Modifier.Control, _ ) =>
        val node = sunView.selected match {
          case Some( nd ) => nd
          case None       => model.sunroot.getRoot
        }
        if ( node.children().size() == 1 ) {
          val sel_node = node.children().get( 0 )
          sunView.setSelectedNode( sel_node )
          model.getInfo.asInstanceOf[ProofNodeInfo[T]].genShowAction( sel_node.getNode.asInstanceOf[ProofNode[T]].proof ).apply()
        }
        sunView.repaintView()
      case KeyPressed( _, Key.Down, Key.Modifier.Control, _ ) =>
        val node = sunView.selected.getOrElse( null )
        if ( node == null || model.sunroot.getRoot.children().contains( node ) ) {
          sunView.setSelectedNode( null )
          model.getInfo.asInstanceOf[ProofNodeInfo[T]].genShowAction(
            model.root.asInstanceOf[ProofNode[T]].proof
          ).apply()
        } else {
          sunView.setSelectedNode( model.sunroot.getRoot.findNode( node.getDepth - 2, node.getLeft ) )
          model.getInfo.asInstanceOf[ProofNodeInfo[T]].genShowAction(
            sunView.selected_proof.get.asInstanceOf[ProofNode[T]].proof
          ).apply()
        }
        sunView.repaintView()
      case KeyPressed( _, Key.Left, Key.Modifier.Control, _ ) =>
        val node = sunView.selected match {
          case Some( nd ) => nd
          case None       => model.sunroot.getRoot
        }
        if ( node.children().size() == 2 ) {
          val sel_node = node.children().get( 0 )
          sunView.setSelectedNode( sel_node )
          model.getInfo.asInstanceOf[ProofNodeInfo[T]].genShowAction( sel_node.getNode.asInstanceOf[ProofNode[T]].proof ).apply()
        }
        sunView.repaintView()
      case KeyPressed( _, Key.Right, Key.Modifier.Control, _ ) =>
        val node = sunView.selected match {
          case Some( nd ) => nd
          case None       => model.sunroot.getRoot
        }
        if ( node.children().size() == 2 ) {
          val sel_node = node.children().get( 1 )
          sunView.setSelectedNode( sel_node )
          model.getInfo.asInstanceOf[ProofNodeInfo[T]].genShowAction( sel_node.getNode.asInstanceOf[ProofNode[T]].proof ).apply()
        }
        sunView.repaintView()
      case Loaded | UnLoaded => dispose()
    }
  }

  contents = main

  override def closeOperation() {
    ProofToolPublisher.publish( ChangeSequentColor( null, null, reset = true ) )
  }
}
