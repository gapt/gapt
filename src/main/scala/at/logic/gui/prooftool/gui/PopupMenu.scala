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
import at.logic.language.hol.{HOLFormula, Neg, And, Imp, Or, ExVar, AllVar, Atom}


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

  // PopupMenu for the title label of either cedent
  def apply(ced: CedentPanel, x: Int, y: Int) {
    val popupMenu = new PopupMenu {
      val trees = ced.treeList.drawnTrees
      contents += new MenuItem(Action("Close all") { trees.foreach(det => det.close(det.expansionTree.toShallow)) })
      contents += new MenuItem(Action("Open all") {
        for (det <- trees) {
          val subFs = firstQuantifiers(det.expansionTree.toShallow)
          subFs.foreach(det.open)
        }
      })
      
      contents += new MenuItem(Action("Expand all") { trees.foreach(det => expandRecursive(det, det.expansionTree.toShallow)) })
      contents += new MenuItem(Action("Reset") {
        ced.treeList = new TreeListPanel(ced.cedent, ced.ft)
        ced.scrollPane.contents = ced.treeList
        ced.revalidate()
      })
    }
    popupMenu.show(ced.titleLabel, x, y)
  }
  
  def firstQuantifiers(f: HOLFormula): List[HOLFormula] = f match {
    case Atom(_,_) => Nil
    case And(l,r) => firstQuantifiers(l) ++ firstQuantifiers(r)
    case Imp(l,r) => firstQuantifiers(l) ++ firstQuantifiers(r)
    case Or(l,r) => firstQuantifiers(l) ++ firstQuantifiers(r)
    case Neg(l) => firstQuantifiers(l)
    case AllVar(_,_) | ExVar(_,_) => List(f)
  }
  
  def expandRecursive(det: DrawExpansionTree, f: HOLFormula): Unit = f match {
    case Atom(_,_) =>
    case And(l,r) => expandRecursive(det,l); expandRecursive(det,r)
    case Imp(l,r) => expandRecursive(det,l); expandRecursive(det,r)
    case Or(l,r) => expandRecursive(det,l); expandRecursive(det,r)
    case Neg(l) => expandRecursive(det,l)
    case AllVar(_,l) => det.expand(f); expandRecursive(det,l)
    case ExVar(_,l) => det.expand(f); expandRecursive(det,l)
  }
}

