package at.logic.gapt.prooftool

import java.awt.Font._
import java.awt.{ Color, RenderingHints }
import java.awt.event.{ ComponentEvent, MouseEvent, MouseMotionListener }

import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.{ Sequent, SequentIndex, SequentProof, lk }

import scala.swing._
import scala.swing.event._

/**
 * A panel containing a sequent proof.
 * @param main The instance of [[at.logic.gapt.prooftool.SequentProofViewer]] that this belongs to.
 * @param proof The proof being displayed.
 * @param fSize The font size.
 * @param hideContexts Whether the contexts of sequents should be hidden.
 * @param auxIndices The indices of the auxiliary formulas of the bottommost inference.
 * @param markCutAncestors Whether the ancestors of cut formulas should be marked.
 * @param cutAncestorIndices The indices of ancestors of cut formulas in the end sequent.
 * @param sequent_element_renderer
 * @param pos The position of this proof relative to the main proof being displayed.
 */
class DrawSequentProof[F, T <: SequentProof[F, T]](
    val main:                 SequentProofViewer[F, T],
    val proof:                SequentProof[F, T],
    private val fSize:        Int,
    var hideContexts:         Boolean,
    val auxIndices:           Set[SequentIndex],
    var markCutAncestors:     Boolean,
    val cutAncestorIndices:   Set[SequentIndex],
    sequent_element_renderer: F => String,
    val pos:                  List[Int]
) extends BoxPanel( Orientation.Vertical ) with MouseMotionListener {
  var collapsed = false
  private val ft = new Font( SANS_SERIF, PLAIN, fSize )
  private var lineHidden_ = 0
  def lineHidden = lineHidden_
  def lineHidden_=( i: Int ) = {
    require( i >= 0 )
    lineHidden_ = i
    linePanel.visible = lineHidden == 0
  }

  private val endSequentPanel = {
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
    ds.border = Swing.EmptyBorder
    ds.listenTo( ds.mouse.moves, ds.mouse.clicks, ds.mouse.wheel, main.publisher )
    ds.reactions += {
      case e: MouseEntered => ds.contents.foreach( x => x.foreground = Color.BLUE )
      case e: MouseExited  => ds.contents.foreach( x => x.foreground = Color.BLACK )
      //        This functionality can be written later if needed
      case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
        PopupMenu( DrawSequentProof.this, e.point.x, e.point.y )
    }
    ds
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
      sequent_element_renderer,
      pos :+ i
    )
  }

  val subProofsPanel = new SubproofsPanel( this, subProofs, fSize )
  val linePanel = new ProofLinePanel( this, proof.name, fSize )

  contents += Swing.VGlue
  contents += subProofsPanel
  contents += linePanel
  contents += endSequentPanel

  def endSequentWidth = endSequentPanel.width
  def endSequentMarginWidth = ( size.width - endSequentWidth ) / 2

  //FIXME: What is this used for?
  def getLocationOfProof( p: SequentProof[_, _] ): Option[Point] = {
    if ( p == proof ) {
      Some( new Point( location.x + bounds.width / 2, location.y + bounds.height ) )
    } else {
      contents.view.
        collect { case dp: DrawSequentProof[_, _] => dp.getLocationOfProof( p ) }.
        flatten.headOption
    }
  }

  /*
   * Window management stuff & reactions
   */
  opaque = false
  border = Swing.EmptyBorder

  this.peer.setAutoscrolls( true )
  this.peer.addMouseMotionListener( this )

  def mouseMoved( e: MouseEvent ) {}
  def mouseDragged( e: MouseEvent ) {
    //The user is dragging us, so scroll!
    val r = new Rectangle( e.getX, e.getY, 1, 1 )
    this.peer.scrollRectToVisible( r )
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
      collapsed = false
      contents( 1 ) = subProofsPanel
      lineHidden -= 1

    case HideSequentProof( p ) if p == pos =>
      collapsed = true
      contents( 1 ) = new BoxPanel( Orientation.Vertical ) {
        opaque = false

        contents += Swing.VGlue
        contents += new Label( "CollapsedProof" ) {
          xLayoutAlignment = java.awt.Component.CENTER_ALIGNMENT
          text = "(...)"
        }
        lineHidden += 1
      }

    case HideStructuralRules => //Fix: contraction is still drawn when a weakening is followed by a contraction.
      proof match {
        case _: WeakeningLeftRule | _: WeakeningRightRule | _: ContractionLeftRule | _: ContractionRightRule =>
          lineHidden += 1
          main.publisher.publish( HideEndSequent( pos :+ 0 ) )
        case _ =>
      }

    case HideEndSequent( p ) if p == pos =>
      endSequentPanel.visible = false

    case ShowAllRules( p ) if pos startsWith p =>
      lineHidden = if ( lineHidden > 0 ) lineHidden - 1 else 0
      endSequentPanel.visible = true

    case ShowDebugBorders =>
      border = Swing.LineBorder( Color.BLUE ) // DEBUG
      endSequentPanel.border = Swing.LineBorder( Color.MAGENTA ) // DEBUG

    case HideDebugBorders =>
      border = Swing.EmptyBorder
      endSequentPanel.border = Swing.EmptyBorder
  }

}

/**
 * A panel containing the subproofs of a proof arranged side by side.
 * @param parent The [[at.logic.gapt.prooftool.DrawSequentProof]] instance that this belongs to.
 * @param subProofs The The [[at.logic.gapt.prooftool.DrawSequentProof]] instances containing the subproofs.
 * @param fSize The font size.
 */
class SubproofsPanel[F, T <: SequentProof[F, T]](
    val parent:    DrawSequentProof[F, T],
    val subProofs: Seq[DrawSequentProof[F, T]],
    val fSize:     Int
) extends BoxPanel( Orientation.Horizontal ) {

  subProofs.foreach( contents += _ )

  def getEndSequentWidth() = subProofs match {
    case Seq() => 0
    case _ =>
      val leftMargin = subProofs.head.endSequentMarginWidth
      val rightMargin = subProofs.last.endSequentMarginWidth

      // FIXME: consider both sides separately
      size.width - 2 * math.min( leftMargin, rightMargin )
  }

  border = Swing.EmptyBorder( 0, 0, 0, 0 )
  opaque = false
  listenTo( parent.main.publisher )
  reactions += {
    case ShowDebugBorders =>
      border = Swing.LineBorder( Color.GREEN ) // DEBUG

    case HideDebugBorders =>
      border = Swing.EmptyBorder
  }
}

/**
 * Panel that contains an inference line and the name of the inference.
 * @param parent The [[at.logic.gapt.prooftool.DrawSequentProof]] instance that this belongs to.
 * @param proofName The name of the inference.
 * @param fSize The font size.
 */
class ProofLinePanel[F, T <: SequentProof[F, T]](
    val parent:    DrawSequentProof[F, T],
    val proofName: String,
    val fSize:     Int
) extends FlowPanel {

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

  override def paintComponent( g: Graphics2D ): Unit = {
    val leftPoint = ( size.width - lineWidth ) / 2
    val rightPoint = ( size.width + lineWidth ) / 2

    g.setRenderingHint( RenderingHints.KEY_TEXT_ANTIALIASING, RenderingHints.VALUE_TEXT_ANTIALIAS_LCD_HRGB )
    g.drawLine( leftPoint, size.height / 2, rightPoint, size.height / 2 )
    g.setFont( labelFont )
    g.drawString( proofName, rightPoint + fSize / 8, size.height / 2 + labelFontMetrics.getMaxDescent )
  }

  border = Swing.EmptyBorder
  listenTo( parent.subProofsPanel, parent.main.publisher )
  reactions += {
    case UIElementShown( _ ) | UIElementResized( _ ) => computeLineWidth()

    case ShowDebugBorders =>
      border = Swing.LineBorder( Color.RED ) // DEBUG

    case HideDebugBorders =>
      border = Swing.EmptyBorder

  }
}
