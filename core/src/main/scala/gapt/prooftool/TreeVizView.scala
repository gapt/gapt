package gapt.prooftool

import gapt.proofs.lk._
import gapt.proofs.{DagProof, HOLSequent, SequentProof}

import scala.swing.{Action, BorderPanel}
import ch.randelshofer.tree._
import javax.swing.event.ChangeListener
import java.awt.Color

import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ContractionRightRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.EqualityRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.InitialSequent
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.SkolemQuantifierRule
import gapt.proofs.lk.rules.StrongQuantifierRule
import gapt.proofs.lk.rules.WeakQuantifierRule
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule
import gapt.proofs.resolution.{AvatarComponent, AvatarContradiction, AvatarSplit, Factor, Paramod, Refl, Resolution, Subst, Taut}

import scala.reflect.classTag

/** Wrapper from gapt proofs to TreeViz trees */
case class ProofNode[T <: DagProof[T]](proof: DagProof[T]) extends TreeNode {
  import scala.jdk.CollectionConverters._
  val children: java.util.List[TreeNode] = proof.immediateSubProofs.map { ProofNode(_): TreeNode }.asJava

  val getAllowsChildren = !children.isEmpty

}

class ProofNodeInfo[T <: DagProof[T]] extends NodeInfo {
  var root: Option[ProofNode[T]] = None
  var weighter: Option[Weighter] = None
  val colorizer = new ProofColorizer
  private var actions = Map[DagProof[T], Array[Action]]()

  /*def genShowAction( x: DagProof[T] ) = new Action( "Show node in LK Viewer" ) {
    def apply() = {
      root match {
        case Some( node ) =>
          main.scrollToProof( x.asInstanceOf[SequentProof[_, _]] )
          try {
            // FIXME
            main.publisher.publish(
              ChangeSequentColor( ???, new Color( 0, 255, 255 ), reset = true )
            )
          } catch { case _: Throwable => }
        case None =>
      }
    }
  }

  def genShowSubtreeAction( x: DagProof[T] ) = new Action( "Focus on subproof" ) {
    def apply() = {
      root match {
        case Some( node ) =>
          main.scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
          main.scrollPane.getContent.getData match {
            case Some( ( name, proof: DagProof[_] ) ) => PTMain.initSunburstDialog( name, x )
            case _                                    => PTMain.errorMessage( "Proof not found!" )
          }
          main.scrollPane.cursor = java.awt.Cursor.getDefaultCursor
        case None =>
      }
    }
  }*/

  def init(root: TreeNode) = {
    if (classTag[ProofNode[T]].runtimeClass.isInstance(root)) {
      this.root = Some(root.asInstanceOf[ProofNode[T]])
      this.weighter = Some(new ProofWeighter())
      this.weighter.get.init(this.root.get)
      this.actions = Map[DagProof[T], Array[Action]]()
    } else {
      throw new Exception("ProofNodeInfo only accepts ProofNodes as tree!")
    }
  }

  def getName(path: TreePath2[TreeNode]) = path.getLastPathComponent match {
    case ProofNode(p) =>
      p.name
  }

  def getColor(path: TreePath2[TreeNode]) = {
    import Rainbow._
    path.getLastPathComponent.asInstanceOf[ProofNode[T]].proof match {
      case _: CutRule | _: Resolution => green
      case _: InitialSequent | _: WeakeningLeftRule | _: WeakeningRightRule |
          _: ContractionLeftRule | _: ContractionRightRule |
          _: Factor | _: Taut => Color.LIGHT_GRAY
      case _: AndLeftRule | _: OrRightRule | _: ImpRightRule | _: NegLeftRule | _: NegRightRule => orange
      case _: AndRightRule | _: OrLeftRule | _: ImpLeftRule                                     => yellow
      case WeakQuantifierRule(_, _, _, _, _, _)                                                 => blue
      case StrongQuantifierRule(_, _, _, _, _) | _: SkolemQuantifierRule                        => red
      case _: EqualityRule | _: Paramod | _: Refl | _: Factor                                   => violet
      case _: AvatarComponent | _: AvatarContradiction | _: AvatarSplit                         => yellow
      case _: Subst                                                                             => orange
      case _                                                                                    => Color.MAGENTA
    }
  }

  def getWeight(path: TreePath2[TreeNode]) = 1

  def getCumulatedWeight(path: TreePath2[TreeNode]) =
    path.getLastPathComponent.asInstanceOf[ProofNode[T]].proof.treeLike.size.toLong

  def getWeightFormatted(path: TreePath2[TreeNode]) = getWeight(path).toString

  val sequentNameCache = collection.mutable.Map[HOLSequent, String]()
  def getTooltip(path: TreePath2[TreeNode]) =
    path.getLastPathComponent.asInstanceOf[ProofNode[T]].proof match {
      case p: SequentProof[_, _] => p.conclusion.toString
      case p                     => s"${p.productPrefix}(${p.productIterator mkString ", "})"
    }

  def getActions(path: TreePath2[TreeNode]) = {
    val node = path.getLastPathComponent.asInstanceOf[ProofNode[T]].proof
    // if ( !( this.actions contains node ) )
    //  this.actions = this.actions + ( ( node, Array[Action]( genShowAction( node ), genShowSubtreeAction( node ) ) ) )
    this.actions(node).map(_.peer)
  }

  def getImage(path: TreePath2[TreeNode]) = null

  def addChangeListener(l: ChangeListener) = {}

  def removeChangeListener(l: ChangeListener) = {}

  def getWeighter = this.weighter match {
    case None    => null
    case Some(w) => w
  }

  def toggleColorWeighter() = {}

  def getColorizer = this.colorizer

}

object Rainbow {
  val red = new Color(255, 0, 0)
  val orange = new Color(255, 128, 0)
  val yellow = new Color(255, 255, 0)
  val green = new Color(0, 128, 0)
  val blue = new Color(0, 0, 255)
  val indigo = new Color(75, 0, 130)
  val violet = new Color(148, 0, 211)
}

class ProofWeighter[T <: DagProof[T]] extends Weighter {
  var root: Option[ProofNode[T]] = None
  var histogram: Option[Array[Int]] = None

  def init(root: TreeNode) =
    if (classTag[ProofNode[T]].runtimeClass.isInstance(root))
      this.root = Some(root.asInstanceOf[ProofNode[T]])
    else
      throw new Exception("Proof Weighter only works for ProofTrees!")

  def getWeight(path: TreePath2[_]): Float = {
    1.0f
  }

  def getHistogram: Array[Int] = histogram.getOrElse(Array[Int]())

  def getHistogramLabel(index: Int): String = index.toString

  def getMinimumWeightLabel: String = "0"

  def getMaximumWeightLabel: String = "max"

  def getMedianWeight: Float = 1.0f
}

class ProofColorizer extends Colorizer {
  def get(w: Float) = new Color(255 * w, 255 * w, 255 * w)
}
