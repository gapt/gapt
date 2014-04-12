package at.logic.gui.prooftool.gui

import at.logic.calculi.treeProofs.TreeProof
import scala.swing._
import java.awt.Dimension
import at.logic.calculi.lk.base.{LKProof, Sequent}
import scala.swing.event.{Event, UIElementResized}
import scala.swing.Reactions.Reaction

/**
 * Provides a combination of DrawProof and SunburstTrees with a SingleInferenceViewer
 */

/*
class CombinedProofView[T](proof : TreeProof[T], fSize : Int) extends BorderPanel {
  //draw proof
  //val drawproof = new DrawProof(proof, fSize, Set(), Set(), Set(), "")

  //sunburst model
  val root = new ProofNode[T](proof)
  val info = new ProofNodeInfo[T]()
  val model = new ReactiveSunburstModel(root, info)
  val view = model.getView()

  view.setToolTipEnabled(true)

  def init() {
    this.layout(Component.wrap(view)) = BorderPanel.Position.Center
  }


}

class CombinedSequentProofView[T <: Sequent](proof : TreeProof[T], fSize : Int) extends CombinedProofView[T](proof, fSize) {
  var iv : DrawSingleSequentInference = null
  var box : BoxPanel = null
  var last_revalidate_size : Dimension = null


  val reactor = new Reaction  {
    def apply(e:Event) : Unit = {
      e match {
        case NodeSelectedEvent(null)  if iv != null && box != null =>
          iv.p_= (Some(model.root.asInstanceOf[ProofNode[T]].proof.asInstanceOf[LKProof]))
          box.revalidate()
          box.repaint()

        case NodeSelectedEvent(p : ProofNode[_])  if iv != null && box != null =>
          iv.p_= (Some(p.proof.asInstanceOf[LKProof]))
          box.revalidate()
          box.repaint()

        case NodeSelectedEvent(_) =>

      }

    }

    override def isDefinedAt(e: Event) = e.isInstanceOf[NodeSelectedEvent]

  }

  this.view.reactions += reactor


  this.reactions += {
    case UIElementResized(source) =>
      println("Handling resize!")
      this.init()
  }

  override def init() {
    super.init()
    this.last_revalidate_size = this.size
    println("initializing")
    if (size.getHeight > size.getWidth) {
      this.iv = new DrawSingleSequentInference(Orientation.Horizontal)
      val height = Math.max(size.height / 10, size.height - size.width)
      val restheight = size.getHeight.toInt - height
      iv.preferredSize = new Dimension(size.width, height)
      //iv.p_=(Some(proof.root))
      view.setPreferredSize(new Dimension(size.width, restheight))
      this.box = new BoxPanel(Orientation.Vertical)
      box.contents ++= List(iv, Component.wrap(view))
      //box.contents(0).preferredSize = new Dimension(size.getWidth.toInt, size.getWidth.toInt)

    } else {
      this.iv = new DrawSingleSequentInference(Orientation.Vertical)
      val width = Math.max(size.width / 10, size.width - size.height)
      val restwidth = size.width - width
      println("Setting iv "+width+"x"+size.height)
      println("Setting view "+restwidth+"x"+size.height)
      iv.preferredSize = new Dimension(width, size.height)
      view.setPreferredSize(new Dimension(restwidth, size.height))
      this.box = new BoxPanel(Orientation.Horizontal)
      this.box.contents ++= List(Component.wrap(view), iv)
      //box.contents(0).preferredSize = new Dimension(size.getHeight.toInt, size.getHeight.toInt)
    }

    this.layout(box) = BorderPanel.Position.Center
    this.revalidate()
    view.repaintView()
    this.repaint()

  }

  override def revalidate() = {
    if (last_revalidate_size != size) init()
    box.revalidate()
    iv.revalidate()
    view.revalidate()
  }




}
   */