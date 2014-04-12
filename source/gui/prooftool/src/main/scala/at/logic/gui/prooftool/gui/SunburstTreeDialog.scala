package at.logic.gui.prooftool.gui

/**
 * Created with IntelliJ IDEA.
 * User: mrukhaia
 * Date: 4/12/14
 * Time: 2:13 PM
 */

import scala.swing._
import at.logic.calculi.treeProofs.TreeProof
import scala.swing.event.{Event, UIElementResized}
import scala.swing.Reactions._
import scala.Some
import at.logic.calculi.lk.base.LKProof


class SunburstTreeDialog[T](name: String, proof: TreeProof[T]) extends Dialog {
  title = "Sunburst view of " + name
  modal = true
  preferredSize = new Dimension(700,500)
  peer.setDefaultCloseOperation(2) //DISPOSE_ON_CLOSE

  contents = new SplitPane(Orientation.Vertical) {
    preferredSize = SunburstTreeDialog.this.preferredSize
    dividerLocation = preferredSize.height

    //sunburst model
    val model = new ReactiveSunburstModel(new ProofNode[T](proof), new ProofNodeInfo[T]())
    val sunView = model.getView()
    // inference information
    val info = new DrawSingleSequentInference(Orientation.Vertical)

    sunView.reactions += new Reaction  {
      def apply(e:Event) : Unit = {
        e match {
          case NodeSelectedEvent(null) =>
            info.p_= (Some(model.root.asInstanceOf[ProofNode[T]].proof.asInstanceOf[LKProof]))
          case NodeSelectedEvent(p : ProofNode[_]) =>
            info.p_= (Some(p.proof.asInstanceOf[LKProof]))
          case NodeSelectedEvent(_) =>
        }
      }

      override def isDefinedAt(e: Event) = e.isInstanceOf[NodeSelectedEvent]
    }
    sunView.setToolTipEnabled(true)
    sunView.setSelectedNode(null)

    leftComponent = Component.wrap(sunView)
    rightComponent = info

    listenTo(SunburstTreeDialog.this)
    reactions += {
      case UIElementResized(source) =>
        preferredSize = SunburstTreeDialog.this.size
        if (preferredSize.width > preferredSize.height) {
          dividerLocation = preferredSize.height
          orientation = Orientation.Vertical
          info.changeOrientation(orientation)
        } else {
          dividerLocation = preferredSize.width
          orientation = Orientation.Horizontal
          info.changeOrientation(orientation)
        }
        revalidate()
    }

  }

}
