package at.logic.gui.prooftool.gui

import ch.randelshofer.tree.sunburst.{SunburstNode, SunburstTree, SunburstView, SunburstModel}
import ch.randelshofer.tree.{NodeInfo, TreeNode}
import scala.swing.Action

/**
 * Created by marty on 3/24/14.
 */
trait ReactiveSunburstView extends SunburstView {
  private var listeners = List[Action]()

  override def setSelectedNode(newValue : SunburstNode) = {
    super.setSelectedNode(newValue)
    for (l <- listeners) {
      l()
    }
  }

  def addListener(action : Action) = {
    listeners = action :: listeners
  }

  def removeListener(action : Action) = {
    //TODO: decide if we really want to remove all actions or just the first occurrence
    listeners = listeners.filterNot(_ == action)
  }


}

class ReactiveSunburstModel(val root : TreeNode, info : NodeInfo) extends SunburstModel(root,info) {
  val sunroot = new SunburstTree(root, info)
  override def getView() = new SunburstView(sunroot) with ReactiveSunburstView

}
