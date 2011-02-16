package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Oct 30, 2010
 * Time: 5:43:38 PM
 */

import scala.swing._
import java.awt.Font._
import javax.swing.border.TitledBorder
import at.logic.calculi.proofs.Proof
import at.logic.calculi.lk.base.{Sequent, SequentOccurrence}
import at.logic.gui.prooftool.parser.{ProofUnLoaded, ProofLoaded, ProofToolPublisher}
import at.logic.language.hol.HOLExpression
import at.logic.utils.ds.trees.Tree
import at.logic.calculi.treeProofs.TreeProof

class MyScrollPane extends ScrollPane {
  background = new Color(255,255,255)

  def getContent: Launcher = contents.last.asInstanceOf[Launcher]
}

class Launcher(private val option: Option[(String, AnyRef)], private val fSize: Int) extends GridBagPanel {
  option match {
    case Some((name: String, obj: AnyRef)) =>
      val c = new Constraints
      c.grid = (0,0)
      c.insets.set(15, 15, 15, 15)
      obj match {
        case proof: TreeProof[SequentOccurrence] =>
          layout(new DrawProof(proof, fSize)) = c
          ProofToolPublisher.publish(ProofLoaded)
        case struct: Tree[HOLExpression] =>
          layout(new DrawTree(struct, fSize)) = c
          ProofToolPublisher.publish(ProofUnLoaded)
        case clList: List[Sequent] =>
          layout(new DrawClList(clList, fSize)) = c
          ProofToolPublisher.publish(ProofUnLoaded)
        case _ =>
          layout(new Label("Can't match case: "+option.get._2.getClass.toString)) = c
          ProofToolPublisher.publish(ProofUnLoaded)
      }
      val bd: TitledBorder = Swing.TitledBorder(Swing.LineBorder(new Color(0,0,0), 2), " "+name+" ")
      bd.setTitleFont(new Font(SANS_SERIF, BOLD, 16))
      border = bd
    case _ =>
  }

  background = new Color(255,255,255)

  def fontSize = fSize
  def getData = option
}
