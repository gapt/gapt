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
import swing.Dialog.Message
import at.logic.calculi.treeProofs.TreeProof
import at.logic.calculi.lk.base.LKProof
import at.logic.transformations.ReductiveCutElim
import at.logic.gui.prooftool.parser.{GentzenLoaded, ProofToolPublisher}
import at.logic.algorithms.lk.replaceSubproof
import Main.body


class PopupMenu extends Component with Wrapper {
  override lazy val peer : JPopupMenu = new JPopupMenu

  def show(invoker: Component, x: Int, y: Int): Unit = peer.show(invoker.peer, x, y)
}


object PopupMenu {

  def apply(tproof: TreeProof[_], component: Component, x: Int, y: Int) = {
    proof = Some(tproof)
    popupMenu.show(component, x, y)
  }

  private var proof: Option[TreeProof[_]] = None

  private val popupMenu = new PopupMenu {
    contents += new MenuItem(Action("Apply Gentzen's Method") { gentzen(proof.get) })
/*  This functions can be added later:
    contents += new MenuItem("Compute Clause Set")
    contents += new MenuItem("Compute Clause Term")
    contents += new Separator
    contents += new MenuItem("Show Proof Above")
    contents += new MenuItem("Hide Proof Above")
*/
  }

  def gentzen(proof: TreeProof[_]) = try {
    val steps = Dialog.showConfirmation(body, "Do you want to see intermediary steps?",
      "ProofTool", Dialog.Options.YesNo, Message.Question) match {
      case Dialog.Result.Yes => true
      case _ => false
    }
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val newSubproof = ReductiveCutElim(proof.asInstanceOf[LKProof], steps)
    val oldProof = body.getContent.getData.get._2.asInstanceOf[LKProof]
    val newProof = replaceSubproof(oldProof, proof.asInstanceOf[LKProof], newSubproof)
    ReductiveCutElim.proofs = ReductiveCutElim.proofs ::: (oldProof::newProof::Nil)
    body.contents = new Launcher(Some("Result:", newProof),14)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
    case e: Exception =>
        val t = e.toString + "\n\n" + e.getStackTraceString
        var k = 0
        val index = t.indexWhere( (x => {if (x == '\n') k += 1; if (k == 51) true; else false}))
        Dialog.showMessage(body, t.dropRight(t.size - index - 1))
  } finally ProofToolPublisher.publish(GentzenLoaded)
}

