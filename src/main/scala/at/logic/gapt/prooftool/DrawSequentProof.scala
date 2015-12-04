package at.logic.gapt.prooftool

import java.awt.Font._
import java.awt.{ Color, RenderingHints }
import java.awt.event.{ MouseEvent, MouseMotionListener }

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.proofs.lkNew._
import at.logic.gapt.proofs.{ SequentIndex, SequentProof }

import scala.swing.BorderPanel._
import scala.swing._
import scala.swing.event._

class DrawSequentProof[F, T <: SequentProof[F, T]](
    val proof:              SequentProof[F, T],
    private val fSize:      Int,
    var hideContexts:       Boolean,
    val auxIndices:         Set[SequentIndex],
    var markCutAncestors:   Boolean,
    val cutAncestorIndices: Set[SequentIndex],
    private var str:        String
) extends BorderPanel with MouseMotionListener {
  private val blue = new Color( 0, 0, 255 )
  private val black = new Color( 0, 0, 0 )
  private val white = new Color( 255, 255, 255 )

  background = white
  opaque = false

  private val bd = Swing.EmptyBorder( 0, fSize * 2, 0, fSize * 2 )
  private val ft = new Font( SANS_SERIF, PLAIN, fSize )
  private val labelFont = new Font( SANS_SERIF, ITALIC, fSize - 2 )
  private var drawLines = true
  // The following is a hack to be able to apply searching to the end-sequent. Think about better solution.
  // The problem is that I need to "recalculate" end-sequent and need def for this reason.
  // But then since def is a function, size of tx1 cannot be calculated and lines are not drawn correctly.

  private var tx = tx1
  private def tx1 = {
    val visibleFormulas = if ( hideContexts ) proof.mainIndices.toSet ++ auxIndices else proof.conclusion.indices.toSet
    val colors = proof.conclusion.indicesSequent map { i => if ( markCutAncestors && cutAncestorIndices.contains( i ) ) Color.green else Color.white }
    val ds = DrawSequent(
      proof.conclusion map {
        case f: HOLFormula            => f
        case ( label, f: HOLFormula ) => f
      },
      proof.conclusion.indicesSequent map visibleFormulas.contains,
      colors,
      ft
    )
    ds.listenTo( mouse.moves, mouse.clicks, mouse.wheel, ProofToolPublisher )
    ds.reactions += {
      case e: MouseEntered => ds.contents.foreach( x => x.foreground = blue )
      case e: MouseExited  => ds.contents.foreach( x => x.foreground = black )
      //        This functionality can be written later if needed
      //        case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 => PopupMenu(proof, this, e.point.x, e.point.y)
    }
    ds
  }

  listenTo( mouse.moves, mouse.clicks, mouse.wheel, ProofToolPublisher )
  reactions += {
    case e: MouseDragged =>
      Main.body.cursor = new java.awt.Cursor( java.awt.Cursor.MOVE_CURSOR )
    case e: MouseReleased =>
      Main.body.cursor = java.awt.Cursor.getDefaultCursor
    case e: MouseWheelMoved =>
      Main.body.peer.dispatchEvent( e.peer )
    case e: ShowProof[_] if e.proof == proof =>
      drawLines = true
      layout.foreach( pair => pair._1.visible = true )
    case e: HideProof[_] if e.proof == proof =>
      drawLines = false
      layout.foreach( pair => if ( pair._2 != Position.South ) pair._1.visible = false )
    case HideStructuralRules => //Fix: contraction is still drawn when a weakening is followed by a contraction.
      proof match {
        case _: WeakeningLeftRule | _: WeakeningRightRule =>
          drawLines = false
          tx.visible = false
        case cl: ContractionLeftRule =>
          val subProof = cl.subProof
          if ( !subProof.isInstanceOf[WeakeningLeftRule] && !subProof.isInstanceOf[WeakeningRightRule] ) drawLines = false
          val dp = layout.find( _._2 == Position.Center ).get._1.asInstanceOf[DrawSequentProof[F, T]]
          dp.tx.visible = false
          dp.border = Swing.EmptyBorder( 0, 0, 3, 0 )
        case cr: ContractionRightRule =>
          val subProof = cr.subProof
          if ( !subProof.isInstanceOf[WeakeningLeftRule] && !subProof.isInstanceOf[WeakeningRightRule] ) drawLines = false
          val dp = layout.find( _._2 == Position.Center ).get._1.asInstanceOf[DrawSequentProof[F, T]]
          dp.tx.visible = false
          dp.border = Swing.EmptyBorder( 0, 0, 3, 0 )
        case _ =>
      }
    case e: ShowAllRules[_] if e.proof == proof =>
      drawLines = true
      initialize()
      revalidate()
  }

  initialize()
  // end of constructor

  def initialize() {
    proof.immediateSubProofs match {
      case Seq( uProof: SequentProof[_, _] ) =>
        val cutAncestorIndicesNew = cutAncestorIndices flatMap { proof.occConnectors.head.parents }
        border = bd
        layout( new DrawSequentProof( uProof, fSize, hideContexts, proof.auxIndices.head.toSet, markCutAncestors, cutAncestorIndicesNew, str ) ) = Position.Center
        layout( tx ) = Position.South
      case Seq( uProof1, uProof2 ) =>
        val ( cutAncestorIndicesLeft, cutAncestorIndicesRight ) = proof match {
          case p: CutRule =>
            ( cutAncestorIndices.flatMap( proof.occConnectors.head.parents ) + p.aux1, cutAncestorIndices.flatMap( proof.occConnectors.tail.head.parents ) + p.aux2 )
          case _ =>
            ( cutAncestorIndices.flatMap( proof.occConnectors.head.parents ), cutAncestorIndices.flatMap( proof.occConnectors.tail.head.parents ) )
        }
        border = bd
        layout( new DrawSequentProof( uProof1, fSize, hideContexts, proof.auxIndices.head.toSet, markCutAncestors, cutAncestorIndicesLeft, str ) ) = Position.West
        layout( new DrawSequentProof( uProof2, fSize, hideContexts, proof.auxIndices.tail.head.toSet, markCutAncestors, cutAncestorIndicesRight, str ) ) = Position.East
        layout( tx ) = Position.South
      case Seq() =>
        tx.border = Swing.EmptyBorder( 0, fSize, 0, fSize )
        layout( tx ) = Position.South
    }
  }

  def getSequentWidth( g: Graphics2D ) = tx.contents.foldLeft( 0 )( ( width, x ) => width + x.size.width + 5 )

  def search_=( s: String ) {
    str = s
  }

  def search = str

  def searchNotInLKProof() {
    tx = tx1
    initialize()
  }

  override def paintComponent( g: Graphics2D ) {
    import scala.math.max

    super.paintComponent( g )

    val metrics = g.getFontMetrics( labelFont )
    // val em = metrics.charWidth('M')
    g.setFont( labelFont )
    // g.setStroke(new BasicStroke(fSize / 25))
    g.setRenderingHint( RenderingHints.KEY_TEXT_ANTIALIASING, RenderingHints.VALUE_TEXT_ANTIALIAS_LCD_HRGB )
    if ( !str.isEmpty && proof.name.contains( str ) ) g.setColor( new Color( 0, 255, 0 ) )

    if ( drawLines ) proof.immediateSubProofs match {
      case Seq( uProof ) =>
        val center = this.layout.find( x => x._2 == Position.Center ).get._1.asInstanceOf[DrawSequentProof[_, _]]
        val width = center.size.width + fSize * 4
        val height = center.size.height
        val seqLength = max( center.getSequentWidth( g ), getSequentWidth( g ) )

        g.drawLine( ( width - seqLength ) / 2, height, ( width + seqLength ) / 2, height )
        g.drawString( proof.name, ( fSize / 4 + width + seqLength ) / 2, height + metrics.getMaxDescent )
      case Seq( uProof1, uProof2 ) =>
        val left = this.layout.find( x => x._2 == Position.West ).get._1.asInstanceOf[DrawSequentProof[_, _]]
        val leftWidth = left.size.width + fSize * 4
        val right = this.layout.find( x => x._2 == Position.East ).get._1.asInstanceOf[DrawSequentProof[_, _]]
        val rightWidth = right.size.width
        val height = max( left.size.height, right.size.height )
        val leftSeqLength = left.getSequentWidth( g )
        val rightSeqLength = right.getSequentWidth( g )
        val lineLength = right.location.x + ( rightWidth + rightSeqLength ) / 2

        g.drawLine( ( leftWidth - leftSeqLength ) / 2, height, lineLength, height )
        g.drawString( proof.name, lineLength + fSize / 4, height + metrics.getMaxDescent )
      case _ =>
    }
  }

  this.peer.setAutoscrolls( true )
  this.peer.addMouseMotionListener( this )

  def mouseMoved( e: MouseEvent ) {}
  def mouseDragged( e: MouseEvent ) {
    //The user is dragging us, so scroll!
    val r = new Rectangle( e.getX, e.getY, 1, 1 )
    this.peer.scrollRectToVisible( r )
  }

  def getLocationOfProof( p: SequentProof[_, _] ): Option[Point] = {
    if ( p == proof ) {
      Some( new Point( location.x + bounds.width / 2, location.y + bounds.height ) )
    } else {
      contents.view.
        collect { case dp: DrawSequentProof[_, _] => dp.getLocationOfProof( p ) }.
        flatten.headOption
    }
  }
}
