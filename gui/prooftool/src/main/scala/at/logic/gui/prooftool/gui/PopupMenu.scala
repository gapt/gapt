package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 8/12/11
 * Time: 1:24 PM
 */

import swing.SequentialContainer.Wrapper
import javax.swing.JPopupMenu
import swing._
import at.logic.calculi.treeProofs.TreeProof
import at.logic.calculi.lk.base.LKProof


class PopupMenu extends Component with Wrapper {
  override lazy val peer : JPopupMenu = new JPopupMenu

  def show(invoker: Component, x: Int, y: Int): Unit = peer.show(invoker.peer, x, y)
}

object PopupMenu {

  def apply(tproof: TreeProof[_], component: Component, x: Int, y: Int) {
    proof = Some(tproof.asInstanceOf[LKProof])
    popupMenu.show(component, x, y)
  }

  private var proof: Option[LKProof] = None

  private val popupMenu = new PopupMenu {
    contents += new MenuItem(Action("Apply Gentzen's Method") { Main.gentzen(proof.get) })
    contents += new MenuItem(Action("Export Subproof in XML") { Main.fSaveProof(proof.get) })
/*  This functions can be added later:
    contents += new MenuItem("Compute Clause Set")
    contents += new MenuItem("Compute Clause Term")
    contents += new Separator
    contents += new MenuItem("Show Proof Above")
    contents += new MenuItem("Hide Proof Above")
*/
  }
}

