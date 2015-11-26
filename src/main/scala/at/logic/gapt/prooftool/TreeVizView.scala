package at.logic.gapt.prooftool

import at.logic.gapt.proofs.lkNew._
import at.logic.gapt.proofs.lkskNew.{ WeakeningRight, WeakeningLeft }
import at.logic.gapt.proofs.{ SequentProof, DagProof, HOLSequent }

import scala.swing.{ Action, BorderPanel }
import ch.randelshofer.tree._
import javax.swing.event.ChangeListener
import java.awt.Color

/** Wrapper from gapt proofs to TreeViz trees */
case class ProofNode[T <: DagProof[T]]( proof: DagProof[T] ) extends TreeNode {
  import scala.collection.JavaConversions._
  val children: java.util.List[TreeNode] = proof.immediateSubProofs map { ProofNode( _ ) }

  val getAllowsChildren = !children.isEmpty

}

class ProofNodeInfo[T <: DagProof[T]] extends NodeInfo {
  var root: Option[ProofNode[T]] = None
  var weighter: Option[Weighter] = None
  val colorizer = new ProofColorizer
  private var actions = Map[DagProof[T], Array[Action]]()

  def genShowAction( x: DagProof[T] ) = new Action( "Show node in LK Viewer" ) {
    def apply() = {
      root match {
        case Some( node ) =>
          Main.scrollToProof( x.asInstanceOf[SequentProof[_, _]] )
          try {
            // FIXME
            ProofToolPublisher.publish(
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
          Main.body.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
          Main.body.getContent.getData match {
            case Some( ( name, proof: DagProof[_] ) ) => Main.initSunburstDialog( name, x )
            case _                                    => Main.errorMessage( "Proof not found!" )
          }
          Main.body.cursor = java.awt.Cursor.getDefaultCursor
        case None =>
      }
    }
  }

  def init( root: TreeNode ) = root match {
    case p: ProofNode[T] =>
      this.root = Some( p )
      this.weighter = Some( new ProofWeighter() )
      this.weighter.get.init( this.root.get )
      this.actions = Map[DagProof[T], Array[Action]]()

    case _ =>
      throw new Exception( "ProofNodeInfo only accepts ProofNodes as tree!" )
  }

  def getName( path: TreePath2[TreeNode] ) = path.getLastPathComponent match {
    case ProofNode( p: DagProof[_] ) =>
      p.name
  }

  def getColor( path: TreePath2[TreeNode] ) = {
    import Rainbow._
    path.getLastPathComponent.asInstanceOf[ProofNode[T]].proof match {
      case _: CutRule => green
      case _: InitialSequent | _: WeakeningLeftRule | _: WeakeningRightRule | _: ContractionLeftRule | _: ContractionRightRule => Color.LIGHT_GRAY
      case _: AndLeftRule | _: OrRightRule | _: ImpRightRule | _: NegLeftRule | _: NegRightRule => orange
      case _: AndRightRule | _: OrLeftRule | _: ImpLeftRule => yellow
      case WeakQuantifierRule( _, _, _, _, _, _ ) => blue
      case StrongQuantifierRule( _, _, _, _, _ ) => red
      case _: EqualityRule => violet
      case _ => Color.MAGENTA
    }
  }

  def getWeight( path: TreePath2[TreeNode] ) = 1

  def getCumulatedWeight( path: TreePath2[TreeNode] ) =
    path.getLastPathComponent.asInstanceOf[ProofNode[T]].proof.treeSize.toLong

  def getWeightFormatted( path: TreePath2[TreeNode] ) = getWeight( path ).toString

  val sequentNameCache = collection.mutable.Map[HOLSequent, String]()
  def getTooltip( path: TreePath2[TreeNode] ) =
    path.getLastPathComponent.asInstanceOf[ProofNode[T]].proof match {
      case p: SequentProof[_, _] => p.conclusion.toString
      case p                     => s"${p.productPrefix}(${p.productIterator mkString ", "})"
    }

  def getActions( path: TreePath2[TreeNode] ) = {
    val node = path.getLastPathComponent.asInstanceOf[ProofNode[T]].proof
    if ( !( this.actions contains node ) )
      this.actions = this.actions + ( ( node, Array[Action]( genShowAction( node ), genShowSubtreeAction( node ) ) ) )
    this.actions( node ).map( _.peer )
  }

  def getImage( path: TreePath2[TreeNode] ) = null

  def addChangeListener( l: ChangeListener ) = {

  }

  def removeChangeListener( l: ChangeListener ) = {

  }

  def getWeighter = this.weighter match {
    case None      => null
    case Some( w ) => w
  }

  def toggleColorWeighter() = {

  }

  def getColorizer = this.colorizer

}

object Rainbow {
  val red = new Color( 255, 0, 0 )
  val orange = new Color( 255, 128, 0 )
  val yellow = new Color( 255, 255, 0 )
  val green = new Color( 0, 128, 0 )
  val blue = new Color( 0, 0, 255 )
  val indigo = new Color( 75, 0, 130 )
  val violet = new Color( 148, 0, 211 )
}

class ProofWeighter[T <: DagProof[T]] extends Weighter {
  var root: Option[ProofNode[T]] = None
  var histogram: Option[Array[Int]] = None

  def init( root: TreeNode ) = {
    root match {
      case p: ProofNode[T] =>
        this.root = Some( p )
      case _ =>
        throw new Exception( "Proof Weighter only works for ProofTrees!" )
    }

  }

  def getWeight( path: TreePath2[_] ): Float = {
    1.0f
  }

  def getHistogram: Array[Int] = histogram.getOrElse( Array[Int]() )

  def getHistogramLabel( index: Int ): String = index.toString

  def getMinimumWeightLabel: String = "0"

  def getMaximumWeightLabel: String = "max"

  def getMedianWeight: Float = 1.0f
}

class ProofColorizer extends Colorizer {
  def get( w: Float ) = new Color( 255 * w, 255 * w, 255 * w )
}
