package at.logic.gui.prooftool.gui

import ch.randelshofer.tree.sunburst.{SunburstNode, SunburstTree, SunburstView, SunburstModel}
import ch.randelshofer.tree.{NodeInfo, TreeNode}
import scala.swing.Publisher
import scala.swing.event.Event

/**
 * This is a wrapper around the Sunburst Tree from the treeviz library. It provides a listener for the
 * selection of a node in tree.
 */
trait ReactiveSunburstView extends SunburstView with Publisher {
  var selected : Option[SunburstNode] = None
  var selected_proof : Option[TreeNode] = None

  override def setSelectedNode(newValue : SunburstNode) = {
    super.setSelectedNode(newValue)
    if (newValue == null) {
      selected = None
      selected_proof = None
    } else {
      selected = Some(newValue)
      selected_proof = Some(newValue.getNode)
    }

    this.publish(NodeSelectedEvent(selected_proof.getOrElse(null)))

  }

}

case class NodeSelectedEvent(node : TreeNode) extends Event

class ReactiveSunburstModel(val root : TreeNode, info : NodeInfo)
 extends SunburstModel(root,info) {
  val sunroot = new SunburstTree(root, info)
  override def getView = new SunburstView(sunroot) with ReactiveSunburstView
}
