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
import at.logic.gui.prooftool.parser.{ProofDbChanged, ProofToolPublisher, ShowProof, HideProof}


class PopupMenu extends Component with Wrapper {
  override lazy val peer : JPopupMenu = new JPopupMenu

  def show(invoker: Component, x: Int, y: Int): Unit = peer.show(invoker.peer, x, y)
}

object PopupMenu {

  // PopupMenu for LKProofs.
  def apply(tproof: TreeProof[_], component: Component, x: Int, y: Int) {
    lazy val proof = tproof.asInstanceOf[LKProof]
    val popupMenu = new PopupMenu {
      contents += new MenuItem(Action("Apply Gentzen's Method") { Main.gentzen(proof) })
      contents += new MenuItem(Action("Export Subproof in XML") { Main.fSaveProof(proof) })
      contents += new MenuItem(Action("Export Subproof in TeX") { Main.fExportProofToTex(proof, false) })
    //  contents += new MenuItem(Action("Compute Clause Set") {} )
    //  contents += new MenuItem(Action("Compute Clause Term") {} )
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
  def apply(det: DrawExpansionTree, component: Component, x: Int, y: Int) {
    val popupMenu = new PopupMenu {
      contents += new MenuItem(Action("Close") { det.closed })
      contents += new MenuItem(Action("Open") { det.opened })
      contents += new MenuItem(Action("Expand") { det.expanded })
    }
    popupMenu.show(component, x, y)
  }
}

