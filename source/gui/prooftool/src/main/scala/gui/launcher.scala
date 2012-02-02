package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Oct 30, 2010
 * Time: 5:43:38 PM
 */

import scala.swing._
import event.MouseDragged
import java.awt.Font._
import javax.swing.border.TitledBorder
import at.logic.gui.prooftool.parser.{UnLoaded, Loaded, ProofToolPublisher, StructPublisher}
import at.logic.utils.ds.trees.Tree
import at.logic.calculi.treeProofs.TreeProof
import java.awt.event.{MouseEvent, MouseMotionListener}
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.lk.base.{LKProof, Sequent}

class MyScrollPane extends ScrollPane {
  background = new Color(255,255,255)

  def getContent: Launcher = contents.last.asInstanceOf[Launcher]
}

class Launcher(private val option: Option[(String, AnyRef)], private val fSize: Int) extends GridBagPanel
with MouseMotionListener with javax.swing.Scrollable {
  option match {
    case Some((name: String, obj: AnyRef)) =>
      val c = new Constraints
      c.grid = (0,0)
      c.insets.set(15, 15, 15, 15)
      obj match {
        case proof: TreeProof[_] =>
          layout(new DrawProof(proof, fSize, Set(), Set())) = c
          ProofToolPublisher.publish(Loaded)
          StructPublisher.publish(UnLoaded)
        case tree: Tree[_] =>
          layout(new DrawTree(tree, fSize)) = c
          ProofToolPublisher.publish(UnLoaded)
          StructPublisher.publish(Loaded)
        case clList: List[Sequent] =>
          layout(new DrawClList(clList, fSize)) = c
          ProofToolPublisher.publish(UnLoaded)
          StructPublisher.publish(UnLoaded)
        case _ =>
          layout(new Label("Can't match case: "+option.get._2.getClass.toString)) = c
          ProofToolPublisher.publish(UnLoaded)
          StructPublisher.publish(UnLoaded)
      }
      val bd: TitledBorder = Swing.TitledBorder(Swing.LineBorder(new Color(0,0,0), 2), " "+name+" ")
      bd.setTitleFont(new Font(SANS_SERIF, BOLD, 16))
      border = bd
    case _ =>
  }

  background = new Color(255,255,255)

  def fontSize = fSize
  def getData = option

  // From here starts test code, trying to scroll normally.
	def getPreferredScrollableViewportSize = preferredSize

	def getScrollableTracksViewportHeight: Boolean = false
	def getScrollableTracksViewportWidth: Boolean = false

	def getScrollableBlockIncrement(visibleRect: Rectangle, orientation: Int, direction: Int): Int =
    3 * getScrollableUnitIncrement(visibleRect, orientation, direction)
	  // scrollablePeer.getScrollableBlockIncrement(visibleRect, orientation.id, direction)

	def getScrollableUnitIncrement(visibleRect: Rectangle, orientation: Int, direction: Int): Int = 10 * fSize
    // scrollablePeer.getScrollableUnitIncrement(visibleRect, orientation.id, direction)

  this.peer.setAutoscrolls(true)
  this.peer.addMouseMotionListener(this)

  def mouseMoved(e: MouseEvent) {}
  def mouseDragged(e: MouseEvent) {
    //The user is dragging us, so scroll!
    val r = new Rectangle(e.getX(), e.getY(), 1, 1);
    this.peer.scrollRectToVisible(r);
  }


}
