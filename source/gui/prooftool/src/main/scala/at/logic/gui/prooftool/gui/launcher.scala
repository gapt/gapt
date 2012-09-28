package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Oct 30, 2010
 * Time: 5:43:38 PM
 */

import scala.swing._
import event.{MouseWheelMoved, MouseReleased, MouseDragged}
import java.awt.Font._
import java.awt.event.{MouseEvent, MouseMotionListener}
import javax.swing.border.TitledBorder
import at.logic.gui.prooftool.parser.{UnLoaded, Loaded, ProofToolPublisher, StructPublisher}
import at.logic.utils.ds.trees.Tree
import at.logic.calculi.treeProofs.TreeProof
import at.logic.calculi.lk.base.types.FSequent

class MyScrollPane extends ScrollPane {
  background = new Color(255,255,255)

  peer.getVerticalScrollBar.setUnitIncrement( 20 )
  peer.getHorizontalScrollBar.setUnitIncrement( 20 )

  def getContent: Launcher = contents.last.asInstanceOf[Launcher]
//  def content_=(c : Component) { viewportView = c }
//  def content = viewportView.get.asInstanceOf[Launcher]
}

class Launcher(private val option: Option[(String, AnyRef)], private val fSize: Int) extends GridBagPanel with MouseMotionListener {
  option match {
    case Some((name: String, obj: AnyRef)) =>
      val c = new Constraints
      c.grid = (0,0)
      c.insets.set(15, 15, 15, 15)
      obj match {
        case proof: TreeProof[_] =>
          layout(new DrawProof(proof, fSize, Set(), Set(), "")) = c
          ProofToolPublisher.publish(Loaded)
          StructPublisher.publish(UnLoaded)
        case tree: Tree[_] =>
          layout(new DrawTree(tree, fSize, "")) = c
          ProofToolPublisher.publish(UnLoaded)
          StructPublisher.publish(Loaded)
        case list: List[_] =>
          layout(new DrawList(list, fSize)) = c
          ProofToolPublisher.publish(UnLoaded)
          StructPublisher.publish(UnLoaded)
        case expansionTree: FSequent =>
          layout(new DrawExpansionTree(expansionTree, fSize)) = c
          ProofToolPublisher.publish(UnLoaded)
          StructPublisher.publish(UnLoaded)
        case _ =>
          layout(new Label("Can't match case: "+option.get._2.getClass.toString + "\n\n" + option.get._2)) = c
          ProofToolPublisher.publish(UnLoaded)
          StructPublisher.publish(UnLoaded)
      }
//      val bd: TitledBorder = Swing.TitledBorder(Swing.LineBorder(new Color(0,0,0), 2), " "+name+" ")
      val nice_name:String = name match {
        case s:String if s == "\\psi" || s == "psi" => "ψ"
        case s:String if s == "\\chi" || s == "chi" => "χ"
        case s:String if s == "\\varphi" || s == "varphi" => "φ"
        case s:String if s == "\\phi" || s == "phi" => "ϕ"
        case s:String if s == "\\rho" || s == "rho" => "ρ"
        case s:String if s == "\\sigma" || s == "sigma" => "σ"
        case s:String if s == "\\tau" || s == "tau" => "τ"
        case _ => name
      }
      val bd: TitledBorder = Swing.TitledBorder(Swing.LineBorder(new Color(0,0,0), 2), " "+nice_name+" ")
      bd.setTitleFont(new Font(SANS_SERIF, BOLD, 16))
      border = bd
    case _ =>
  }

  background = new Color(255,255,255)

  def fontSize = fSize
  def getData = option

  listenTo(mouse.moves, mouse.clicks, mouse.wheel)
  reactions += {
    case e: MouseDragged =>
      Main.body.cursor = new java.awt.Cursor(java.awt.Cursor.MOVE_CURSOR)
    case e: MouseReleased =>
      Main.body.cursor = java.awt.Cursor.getDefaultCursor
    case e: MouseWheelMoved =>
      Main.body.peer.dispatchEvent(e.peer)
  }

  this.peer.setAutoscrolls(true)
  this.peer.addMouseMotionListener(this)

  def mouseMoved(e: MouseEvent) {}
  def mouseDragged(e: MouseEvent) {
    //The user is dragging us, so scroll!
    val r = new Rectangle(e.getX(), e.getY(), 1, 1);
    this.peer.scrollRectToVisible(r);
  }
}
