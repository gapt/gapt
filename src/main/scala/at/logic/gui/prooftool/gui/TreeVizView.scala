package at.logic.gui.prooftool.gui

import scala.swing.{Action, BorderPanel}
import at.logic.calculi.proofs.TreeProof
import ch.randelshofer.tree._
import at.logic.utils.ds.trees.{BinaryTree, UnaryTree, LeafTree}
import javax.swing.event.ChangeListener
import java.awt.Color
import at.logic.algorithms.llk.HybridLatexExporter.fsequentString
import at.logic.calculi.lksk.{ExistsSkLeftRuleType, ForallSkRightRuleType, ExistsSkRightRuleType, ForallSkLeftRuleType}
import at.logic.calculi.lk._
import at.logic.parsing.calculi.xml.{BinaryRuleType, UnaryRuleType, NullaryRuleType}
import at.logic.calculi.lk.base._
import at.logic.gui.prooftool.parser.{ChangeSequentColor, ProofToolPublisher}

/**
 *
 * Created by marty on 3/18/14.
 */

/* Wapper from gapt proofs to TreeViz trees */
case class ProofNode[T](proof : TreeProof[T]) extends TreeNode {
  import collection.convert.wrapAsJava.seqAsJavaList
  val children : java.util.List[TreeNode] = proof match {
    case LeafTree(v) => List[TreeNode]()
    case UnaryTree(v, parent) => List(ProofNode(parent.asInstanceOf[TreeProof[T]]))
    case BinaryTree(v, p1, p2) => List(p1,p2).map(x => ProofNode(x.asInstanceOf[TreeProof[T]]))
  }

  val getAllowsChildren = ! children.isEmpty

}

class ProofNodeInfo[T] extends NodeInfo {
  var root : Option[ProofNode[T]] = None
  var weighter : Option[Weighter] = None
  val colorizer = new ProofColorizer
  private var actions = Map[TreeProof[T], Array[Action]]()


  def genShowAction(x: TreeProof[T]) = new Action("Show node in LK Viewer") {
    def apply() = {
      root match {
        case Some(node) =>
          Main.scrollToProof(x)
          try {
            ProofToolPublisher.publish(
              ChangeSequentColor(x.asInstanceOf[LKProof].root, new Color(0,255,255), reset=true)
            )
          } catch { case _: Throwable => }
        case None =>
      }
    }
  }

  def genShowSubtreeAction(x: TreeProof[T]) = new Action("Focus on subproof") {
    def apply() = {
      root match {
        case Some(node) =>
          Main.body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
          Main.body.getContent.getData match {
            case Some((name, proof : TreeProof[_]) ) => Main.initSunburstDialog(name, x)
            case _ => Main.errorMessage("Proof not found!")
          }
          Main.body.cursor = java.awt.Cursor.getDefaultCursor
        case None =>
      }
    }
  }

  def init(root : TreeNode) = root match {
    case p : ProofNode[T] =>
      this.root = Some(p)
      this.weighter = Some(new ProofWeighter())
      this.weighter.get.init(this.root.get)
      this.actions = Map[TreeProof[T], Array[Action]]()

    case _ =>
      throw new Exception("ProofNodeInfo only accepts ProofNodes as tree!")
  }

  def getName(path : TreePath2[TreeNode]) = path.getLastPathComponent match {
    case ProofNode( p : TreeProof[_]) =>
      p.name
  }



  def getColor(path : TreePath2[TreeNode]) = {
    import Rainbow._
    val rule = path.getLastPathComponent.asInstanceOf[ProofNode[T]].proof.rule
    if (rule == CutRuleType) {
      green
    }
    else if (rule == InitialRuleType || rule == WeakeningLeftRuleType || rule == WeakeningRightRuleType || rule == ContractionLeftRuleType || rule == ContractionRightRuleType) {
      Color.LIGHT_GRAY
    }
    else if (rule == AndLeft1RuleType || rule == AndLeft2RuleType || rule == OrRight1RuleType || rule == OrRight2RuleType || rule == ImpRightRuleType || rule == NegLeftRuleType || rule == NegRightRuleType) {
      orange
    }
    else if (rule == AndRightRuleType || rule == OrLeftRuleType || rule == ImpLeftRuleType) {
      yellow
    }
    else if (rule == ForallLeftRuleType || rule == ExistsRightRuleType || rule == ForallSkLeftRuleType || rule == ExistsSkRightRuleType) {
      blue
    }
    else if (rule == ForallRightRuleType || rule == ExistsLeftRuleType || rule == ForallSkRightRuleType || rule == ExistsSkLeftRuleType) {
      red
    }
    else if (rule == EquationLeft1RuleType || rule == EquationLeft2RuleType || rule == EquationRight1RuleType || rule == EquationRight2RuleType) {
      violet
    } else{
      Color.MAGENTA
    }
  }

  def getWeight(path : TreePath2[TreeNode]) = {
    1
  }

  def getCumulatedWeight(path : TreePath2[TreeNode]) = {
    path.getLastPathComponent.asInstanceOf[ProofNode[T]].proof.size()
  }

  def getWeightFormatted(path : TreePath2[TreeNode]) = {
    getWeight(path).toString
  }

  val sequentNameCache = collection.mutable.Map[FSequent, String]()
  def getTooltip(path : TreePath2[TreeNode]) = {
    val es = path.getLastPathComponent.asInstanceOf[ProofNode[T]].proof.root
    es match {
      case s : Sequent =>
        val fs = s.toFSequent
        if (! (sequentNameCache contains fs))
          sequentNameCache(fs) = fsequentString(s.toFSequent, escape_latex = false)
        sequentNameCache(fs)

      case _ => es.toString
    }

  }

  def getActions(path : TreePath2[TreeNode]) = {
    val node = path.getLastPathComponent.asInstanceOf[ProofNode[T]].proof
    if (! (this.actions contains node))
      this.actions = this.actions + ((node, Array[Action]( genShowAction(node), genShowSubtreeAction(node) )))
    this.actions(node).map(_.peer)
  }

  def getImage(path : TreePath2[TreeNode]) = null

  def addChangeListener(l : ChangeListener) = {

  }

  def removeChangeListener(l : ChangeListener) = {

  }

  def getWeighter = this.weighter match {
    case None => null
    case Some(w) => w
  }

  def toggleColorWeighter() = {

  }

  def getColorizer = this.colorizer

}


object Rainbow {
  val red = new Color(255,0,0)
  val orange = new Color(255,128,0)
  val yellow = new Color(255,255,0)
  val green = new Color(0,128,0)
  val blue = new Color(0,0,255)
  val indigo = new Color(75,0,130)
  val violet = new Color(148,0,211)
}

class ProofWeighter[T] extends Weighter {
  var root : Option[ProofNode[T]] = None
  var histogram : Option[Array[Int]] = None

  def init(root: TreeNode) = {
    root match  {
      case p : ProofNode[T] =>
        this.root = Some(p)
      case _ =>
        throw new Exception("Proof Weighter only works for ProofTrees!")
    }


  }

  def getWeight(path: TreePath2[_]) : Float = {
    1.0f
  }

  def getHistogram: Array[Int] = histogram.getOrElse(Array[Int]())

  def getHistogramLabel(index: Int): String = index.toString

  def getMinimumWeightLabel: String = "0"

  def getMaximumWeightLabel: String = "max"

  def getMedianWeight: Float = 1.0f
}

class ProofColorizer extends Colorizer {
  def get(w:Float) = new Color(255*w, 255*w, 255*w)
}


// Comment from Mikheil: for what this class is used???
class FormulaBox[V](var inference : TreeProof[V]) extends BorderPanel {
  inference match {
    case a:AuxiliaryFormulas =>
      if (inference.rule == NullaryRuleType) {
      } else if (inference.rule == UnaryRuleType) {
        a.aux
      } else if (inference.rule == BinaryRuleType) {

      } else {

      }

  }
}
