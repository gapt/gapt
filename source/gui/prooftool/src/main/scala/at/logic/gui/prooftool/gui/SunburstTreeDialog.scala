package at.logic.gui.prooftool.gui

/**
 * Created with IntelliJ IDEA.
 * User: mrukhaia
 * Date: 4/12/14
 * Time: 2:13 PM
 */

import scala.swing._
import at.logic.calculi.treeProofs.TreeProof
import scala.swing.event.{Key, KeyPressed, UIElementResized}
import at.logic.calculi.lk.base.LKProof
import ch.randelshofer.tree.sunburst.SunburstNode
import at.logic.gui.prooftool.parser.{ChangeSequentColor, ProofToolPublisher}


class SunburstTreeDialog[T](name: String, proof: TreeProof[T]) extends Dialog {
  title = "Sunburst view of " + name
  modal = true
  preferredSize = new Dimension(700,500)
  peer.setDefaultCloseOperation(2) //DISPOSE_ON_CLOSE

  contents = new SplitPane(Orientation.Vertical) {
    focusable = true  // required to get events from keyboard
    preferredSize = SunburstTreeDialog.this.preferredSize
    dividerLocation = preferredSize.height

    //sunburst model
    val model = new ReactiveSunburstModel(new ProofNode[T](proof), new ProofNodeInfo[T]())
    val sunView = model.getView()
    // inference information
    val info = new DrawSingleSequentInference(Orientation.Vertical)

    sunView.setToolTipEnabled(true)
    sunView.reactions += {
      case NodeSelectedEvent(null) =>
        info.p_= (Some(model.root.asInstanceOf[ProofNode[T]].proof.asInstanceOf[LKProof]))
      case NodeSelectedEvent(p : ProofNode[_]) =>
        info.p_= (Some(p.proof.asInstanceOf[LKProof]))
    }
    sunView.setSelectedNode(null)

    leftComponent = Component.wrap(sunView)
    rightComponent = info

    listenTo(keys,SunburstTreeDialog.this)
    reactions += {
      case UIElementResized(source) =>
        preferredSize = SunburstTreeDialog.this.size
        if (preferredSize.width > preferredSize.height) {
          dividerLocation = preferredSize.height
          orientation = Orientation.Vertical
          info.adjustOrientation(orientation)
        } else {
          dividerLocation = preferredSize.width
          orientation = Orientation.Horizontal
          info.adjustOrientation(orientation)
        }
        revalidate()
      case KeyPressed(_,Key.Up,Key.Modifier.Control,_) =>
        val node = sunView.selected match {
          case Some(nd) => nd
          case None => model.sunroot.getRoot
        }
        if (node.children().size() == 1) sunView.setSelectedNode(node.children().get(0))
        sunView.repaintView()
      case KeyPressed(_, Key.Down, Key.Modifier.Control,_) =>
        val node = sunView.selected.getOrElse(null)
        if (node == null || model.sunroot.getRoot.children().contains(node)) sunView.setSelectedNode(null)
        else sunView.setSelectedNode(model.sunroot.getRoot.findNode(node.getDepth - 2, node.getLeft))
        sunView.repaintView()
      case KeyPressed(_,Key.Left,Key.Modifier.Control,_) =>
        val node = sunView.selected match {
          case Some(nd) => nd
          case None => model.sunroot.getRoot
        }
        if (node.children().size() == 2) sunView.setSelectedNode(node.children().get(0))
        sunView.repaintView()
      case KeyPressed(_,Key.Right,Key.Modifier.Control,_) =>
        val node = sunView.selected match {
          case Some(nd) => nd
          case None => model.sunroot.getRoot
        }
        if (node.children().size() == 2) sunView.setSelectedNode(node.children().get(1))
        sunView.repaintView()
    }
  }

  override def closeOperation() {
    ProofToolPublisher.publish(ChangeSequentColor(null,null,true))
  }
}
