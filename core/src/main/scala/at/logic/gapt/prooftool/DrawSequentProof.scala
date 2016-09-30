package at.logic.gapt.prooftool

import java.awt.Font._
import java.awt.event.{ MouseEvent, MouseMotionListener }
import java.awt.{ Color, RenderingHints }

import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.{ SequentIndex, SequentProof }

import scala.swing._
import scala.swing.event._

/**
 * A panel containing a sequent proof.
 * @param main The instance of [[at.logic.gapt.prooftool.SequentProofViewer]] that this belongs to.
 * @param proof The proof being displayed.
 * @param auxIndices The indices of the auxiliary formulas of the bottommost inference.
 * @param cutAncestorIndices The indices of ancestors of cut formulas in the end sequent.
 * @param pos The position of this proof relative to the main proof being displayed.
 */
class DrawSequentProof[F, T <: SequentProof[F, T]](
    val main:               SequentProofViewer[F, T],
    val proof:              SequentProof[F, T],
    val auxIndices:         Set[SequentIndex],
    val cutAncestorIndices: Set[SequentIndex],
    sequentElementRenderer: F => String,
    val pos:                List[Int]
) extends BoxPanel( Orientation.Vertical ) with MouseMotionListener {
  var collapsed = false
  private var lineHideLevel_ = 0
  def lineHideLevel = lineHideLevel_
  def lineHideLevel_=( i: Int ) = {
    require( i >= 0 )
    lineHideLevel_ = i
    linePanel.visible = lineHideLevel == 0
  }

  private val endSequentPanel = {
    val mainAuxIndices = proof.mainIndices.toSet ++ auxIndices
    val ds = DrawSequent(
      main,
      proof.conclusion,
      mainAuxIndices,
      cutAncestorIndices,
      sequentElementRenderer
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
      proof.auxIndices.head.toSet,
      cutAncestorIndicesNew( i ),
      sequentElementRenderer,
      i :: pos
    )
  }

  val subProofsPanel = new SubproofsPanel( this, subProofs )
  val subProofsHiddenPanel = new BoxPanel( Orientation.Vertical ) {
    opaque = false
    contents += new Label( "CollapsedProof" ) {
      xLayoutAlignment = java.awt.Component.CENTER_ALIGNMENT
      text = "(...)"
    }

  }
  val linePanel = new ProofLinePanel( this, proof.name )

  val subProofsPanelIndex = if ( pos.isEmpty ) 1 else 0

  if ( pos.isEmpty ) contents += Swing.VGlue
  contents += subProofsPanel
  contents += linePanel
  contents += endSequentPanel
  if ( pos.isEmpty ) contents += Swing.VGlue

  def lineWidth() = linePanel.width
  def endSequentWidth = endSequentPanel.width
  def subProofsWidth() = subProofsPanel.width()

  def width() = {
    val lowerWidth = math.max( lineWidth(), endSequentWidth )

    if ( collapsed ) lowerWidth else math.max( lowerWidth, subProofsWidth() )
  }

  def endSequentLeftMarginWidth(): Int = {
    ( width() / 2 - endSequentWidth * ( 1 - endSequentPanel.xLayoutAlignment ) ).toInt
  }

  def endSequentRightMarginWidth(): Int = {
    ( width() / 2 - endSequentWidth * endSequentPanel.xLayoutAlignment ).toInt
  }

  subProofsPanel.xLayoutAlignment = 0.5
  endSequentPanel.xLayoutAlignment = {
    if ( subProofs.isEmpty )
      0.5
    else {
      val y = subProofsPanel.endSequentRightMarginWidth().toDouble

      ( subProofsPanel.endSequentWidth() / 2 + y ) / subProofsPanel.width()
    }
  }

  linePanel.xLayoutAlignment = {
    if ( subProofs.isEmpty )
      0.5
    else {
      val y = subProofsPanel.endSequentRightMarginWidth().toDouble

      ( subProofsPanel.endSequentWidth() / 2 + y ) / subProofsPanel.width()
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
      contents( subProofsPanelIndex ) = subProofsPanel
      lineHideLevel -= 1

    case HideSequentProof( p ) if p == pos =>
      collapsed = true
      contents( subProofsPanelIndex ) = subProofsHiddenPanel
      lineHideLevel += 1

    case HideStructuralRules => //Fix: contraction is still drawn when a weakening is followed by a contraction.
      proof match {
        case _: WeakeningLeftRule | _: WeakeningRightRule | _: ContractionLeftRule | _: ContractionRightRule =>
          lineHideLevel += 1
          main.publisher.publish( HideEndSequent( 0 :: pos ) )
        case _ =>
      }

    case HideEndSequent( p ) if p == pos =>
      endSequentPanel.visible = false

    case ShowAllRules( p ) if pos endsWith p =>
      lineHideLevel = if ( lineHideLevel > 0 ) lineHideLevel - 1 else 0
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
 */
class SubproofsPanel[F, T <: SequentProof[F, T]](
    val parent:    DrawSequentProof[F, T],
    val subProofs: Seq[DrawSequentProof[F, T]]
) extends BoxPanel( Orientation.Horizontal ) {

  subProofs.foreach( contents += )
  subProofs.foreach( _.yLayoutAlignment = 1 ) // Forces the subproof panels to align along their bottom edges

  def width(): Int = subProofs.map( _.width() ).sum

  def endSequentLeftMarginWidth() = subProofs match {
    case Seq() => 0
    case _ =>
      subProofs.head.endSequentLeftMarginWidth()
  }

  def endSequentRightMarginWidth() = subProofs match {
    case Seq() => 0
    case _ =>
      subProofs.last.endSequentRightMarginWidth()
  }

  def endSequentWidth() = {
    width() - endSequentLeftMarginWidth() - endSequentRightMarginWidth()
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
 */
class ProofLinePanel[F, T <: SequentProof[F, T]](
    val parent:    DrawSequentProof[F, T],
    val proofName: String
) extends FlowPanel {
  private var fSize_ = parent.main.currentFontSize
  def fSize = fSize_
  def fSize_=( sz: Int ) = {
    fSize_ = sz
    labelFont = new Font( SANS_SERIF, ITALIC, fSize - 2 )
  }
  private var labelFont_ = new Font( SANS_SERIF, ITALIC, fSize - 2 )
  def labelFont = labelFont_
  def labelFont_=( ft: Font ) = {
    labelFont_ = ft
    computeLineWidth( fontSizeHasChanged = true )
  }
  def labelFontMetrics = peer.getFontMetrics( labelFont )

  def computeLineWidth( fontSizeHasChanged: Boolean = false ): Unit = {
    val newLineWidth = math.max( parent.subProofsPanel.endSequentWidth(), parent.endSequentWidth )
    if ( !fontSizeHasChanged && lineWidth >= newLineWidth ) return // ensure convergence
    lineWidth = newLineWidth
    labelWidth = labelFontMetrics.stringWidth( proofName ) * 2 + fSize
    width = lineWidth + labelWidth
    height = labelFontMetrics.getHeight + fSize / 4
    preferredSize = new Dimension( width, height )
    minimumSize = preferredSize
    maximumSize = preferredSize
    revalidate()
  }

  var width = 0; var height = 0; var lineWidth = 0; var labelWidth = 0; computeLineWidth()

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

    case FontChanged =>
      fSize = parent.main.currentFontSize
  }
}
