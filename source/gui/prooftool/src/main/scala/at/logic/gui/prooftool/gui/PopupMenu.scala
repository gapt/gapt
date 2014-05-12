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
import at.logic.calculi.proofs.TreeProof
import at.logic.calculi.lk.base.LKProof
import at.logic.gui.prooftool.parser.{ProofDbChanged, ProofToolPublisher, ShowProof, HideProof}
import at.logic.language.hol.HOLFormula


class PopupMenu extends Component with Wrapper {
  override lazy val peer : JPopupMenu = new JPopupMenu

  def show(invoker: Component, x: Int, y: Int) { peer.show(invoker.peer, x, y) }
}

object PopupMenu {

  // PopupMenu for LKProofs.
  def apply(tproof: TreeProof[_], component: Component, x: Int, y: Int) {
    lazy val proof = tproof.asInstanceOf[LKProof]
    val popupMenu = new PopupMenu {
      contents += new MenuItem(Action("View Subproof as Sunburst Tree") {
        Main.initSunburstDialog("subproof "+proof.name, tproof)
      })
      contents += new Separator
      contents += new MenuItem(Action("Apply Gentzen's Method (new)") { Main.newgentzen(proof) })
      contents += new MenuItem(Action("Apply Gentzen's Method") { Main.gentzen(proof) })
      contents += new Separator
      contents += new MenuItem(Action("Save Subproof as...") { Main.fSave((proof.name,proof)) })
      contents += new Separator
      contents += new MenuItem(Action("Show Proof Above") { ProofToolPublisher.publish(new ShowProof(tproof)) } )
      contents += new MenuItem(Action("Hide Proof Above") { ProofToolPublisher.publish(new HideProof(tproof)) } )
      contents += new Separator
      contents += new MenuItem(Action("Split Proof") {
        Main.db.addProofs((proof.name,proof)::Nil)
        Main.loadProof(proof)
        ProofToolPublisher.publish(ProofDbChanged)
      })
    }
    popupMenu.show(component, x, y)
  }

  // PopupMenu for Expansion Trees.
  def apply(det: DrawExpansionTree, f: HOLFormula, component: Component, x: Int, y: Int) {
    val popupMenu = new PopupMenu {
      contents += new MenuItem(Action("Close") { det.close(f) })
      contents += new MenuItem(Action("Open") { det.open(f) })
      contents += new MenuItem(Action("Expand") { det.expand(f) })
    }
    popupMenu.show(component, x, y)
  }
}

