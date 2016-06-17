package at.logic.gapt.prooftool

import java.awt.Font._
import java.awt.{ Color, RenderingHints }
import java.awt.event.{ ComponentEvent, MouseEvent, MouseMotionListener }

import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.{ Sequent, SequentIndex, SequentProof, lk }

import scala.swing._
import scala.swing.event._

class DrawSequentProof[F, T <: SequentProof[F, T]](
    val main:                 SequentProofViewer[F, T],
    val proof:                SequentProof[F, T],
    private val fSize:        Int,
    var hideContexts:         Boolean,
    val auxIndices:           Set[SequentIndex],
    var markCutAncestors:     Boolean,
    val cutAncestorIndices:   Set[SequentIndex],
    private var str:          String,
    sequent_element_renderer: F => String,
    val pos:                  List[Int]
) extends BoxPanel( Orientation.Vertical ) with MouseMotionListener {
  opaque = false
  border = Swing.EmptyBorder

  private val bd = Swing.EmptyBorder( 0, fSize * 2, 0, fSize * 2 )
  private val ft = new Font( SANS_SERIF, PLAIN, fSize )
  private val labelFont = new Font( SANS_SERIF, ITALIC, fSize - 2 )
  // The following is a hack to be able to apply searching to the end-sequent. Think about better solution.
  // The problem is that I need to "recalculate" end-sequent and need def for this reason.
  // But then since def is a function, size of tx1 cannot be calculated and lines are not drawn correctly.

  private var tx = tx1
  private def tx1 = {
    val visibleFormulas = if ( hideContexts ) proof.mainIndices.toSet ++ auxIndices else proof.conclusion.indices.toSet
    val colors = proof.conclusion.indicesSequent map { i => if ( markCutAncestors && cutAncestorIndices.contains( i ) ) Color.green else Color.white }
    val ds = DrawSequent(
      main,
      proof.conclusion,
      ft,
      proof.conclusion.indicesSequent map visibleFormulas.contains,
      colors,
      sequent_element_renderer
    )
    ds.listenTo( mouse.moves, mouse.clicks, mouse.wheel, main.publisher )
    ds.reactions += {
      case e: MouseEntered => ds.contents.foreach( x => x.foreground = Color.BLUE )
      case e: MouseExited  => ds.contents.foreach( x => x.foreground = Color.BLACK )
      //        This functionality can be written later if needed
      case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
        PopupMenu( DrawSequentProof.this, e.point.x, e.point.y )
    }
    ds
  }

  listenTo( mouse.moves, mouse.clicks, mouse.wheel, main.publisher )
  reactions += {
    case e: MouseDragged =>
      main.scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.MOVE_CURSOR )

    case e: MouseReleased =>
      main.scrollPane.cursor = java.awt.Cursor.getDefaultCursor

    case e: MouseWheelMoved =>
      main.scrollPane.peer.dispatchEvent( e.peer )

    case ShowSequentProof( p ) if p == pos =>
      contents( 1 ) = subProofsPanel
      linePanel.visible = true
    //tx.visible = true

    case HideSequentProof( p ) if p == pos =>
      contents( 1 ) = new BoxPanel( Orientation.Vertical ) {
        border = Swing.LineBorder( Color.GRAY )
        opaque = false

        contents += Swing.VGlue
        contents += new Label( "CollapsedProof" ) {
          xLayoutAlignment = java.awt.Component.CENTER_ALIGNMENT
          text = "(...)"
        }
      }
      linePanel.visible = false
    //tx.visible = false

    case HideStructuralRules => //Fix: contraction is still drawn when a weakening is followed by a contraction.
      proof match {
        case _: WeakeningLeftRule | _: WeakeningRightRule | _: ContractionLeftRule | _: ContractionRightRule =>
          linePanel.visible = false
          main.publisher.publish( HideEndSequent( pos :+ 0 ) )
        case _ =>
      }

    case HideEndSequent( p ) if p == pos =>
      tx.visible = false

    case ShowAllRules( p ) if pos startsWith p =>
      linePanel.visible = true
      revalidate()

    case ShowDebugBorders =>
      border = Swing.LineBorder( Color.BLUE ) // DEBUG
      tx.border = Swing.LineBorder( Color.MAGENTA ) // DEBUG

    case HideDebugBorders =>
      border = Swing.EmptyBorder
      tx.border = Swing.EmptyBorder
  }

  val cutAncestorIndicesNew = proof match {
    case p: CutRule =>
      List( cutAncestorIndices.flatMap( proof.occConnectors.head.parents ) + p.aux1, cutAncestorIndices.flatMap( proof.occConnectors.tail.head.parents ) + p.aux2 )
    case _ =>
      for ( ( p, i ) <- proof.immediateSubProofs.zipWithIndex ) yield cutAncestorIndices flatMap proof.occConnectors( i ).parents
  }

  val subProofs = for ( ( p, i ) <- proof.immediateSubProofs.zipWithIndex ) yield {
    new DrawSequentProof(
      main,
      p,
      fSize,
      hideContexts,
      proof.auxIndices.head.toSet,
      markCutAncestors,
      cutAncestorIndicesNew( i ),
      str,
      sequent_element_renderer,
      pos :+ i
    )
  }

  val subProofsPanel = new SubproofsPanel( this, subProofs, fSize )
  val linePanel = new ProofLinePanel( this, proof.name, fSize )
  initialize()
  // end of constructor

  def initialize() {
    tx.border = Swing.EmptyBorder

    contents += Swing.VGlue
    contents += subProofsPanel
    contents += linePanel
    contents += tx
  }

  def search_=( s: String ) {
    str = s
  }

  def search = str

  def searchNotInLKProof() {
    tx = tx1
    initialize()
  }

  def endSequentWidth = tx.width
  def endSequentMarginWidth = ( size.width - endSequentWidth ) / 2

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

class SubproofsPanel[F, T <: SequentProof[F, T]](
    val parent:    DrawSequentProof[F, T],
    val subProofs: Seq[DrawSequentProof[F, T]],
    val fSize:     Int
) extends BoxPanel( Orientation.Horizontal ) {
  border = Swing.EmptyBorder( 0, 0, 0, 0 )
  opaque = false
  val collapsedProof = new Label( "CollapsedProof" ) { text = "(...)" }

  subProofs.foreach( contents += _ )

  def getEndSequentWidth() = subProofs match {
    case Seq() => 0
    case _ =>
      val leftMargin = subProofs.head.endSequentMarginWidth
      val rightMargin = subProofs.last.endSequentMarginWidth

      // FIXME: consider both sides separately
      size.width - 2 * math.min( leftMargin, rightMargin )
  }

  listenTo( parent.main.publisher )

  reactions += {
    case ShowDebugBorders =>
      border = Swing.LineBorder( Color.GREEN ) // DEBUG

    case HideDebugBorders =>
      border = Swing.EmptyBorder
  }
}

class ProofLinePanel[F, T <: SequentProof[F, T]](
    val parent:    DrawSequentProof[F, T],
    val proofName: String,
    val fSize:     Int
) extends FlowPanel {
  border = Swing.EmptyBorder

  val labelFont = new Font( SANS_SERIF, ITALIC, fSize - 2 )
  val labelFontMetrics = peer.getFontMetrics( labelFont )

  def computeLineWidth() = {
    val newLineWidth = scala.math.max( parent.subProofsPanel.getEndSequentWidth(), parent.endSequentWidth )
    if ( newLineWidth != lineWidth ) {
      lineWidth = newLineWidth
      val width = lineWidth + labelFontMetrics.stringWidth( proofName ) * 2 + fSize
      val height = labelFontMetrics.getHeight + fSize / 4
      preferredSize = new Dimension( width, height )
      minimumSize = preferredSize
      maximumSize = preferredSize
      revalidate()
    }
  }

  var lineWidth = 0; computeLineWidth()

  listenTo( parent.subProofsPanel, parent.main.publisher )
  reactions += {
    case UIElementShown( _ ) | UIElementResized( _ ) => computeLineWidth()

    case ShowDebugBorders =>
      border = Swing.LineBorder( Color.RED ) // DEBUG

    case HideDebugBorders =>
      border = Swing.EmptyBorder

  }

  override def paintComponent( g: Graphics2D ): Unit = {
    val leftPoint = ( size.width - lineWidth ) / 2
    val rightPoint = ( size.width + lineWidth ) / 2

    g.drawLine( leftPoint, size.height / 2, rightPoint, size.height / 2 )
    g.setFont( labelFont )
    g.drawString( proofName, rightPoint + fSize / 8, size.height / 2 + labelFontMetrics.getMaxDescent )
  }
}