package gapt.prooftool

import java.awt.Font._
import java.awt.event.{ MouseEvent, MouseMotionListener }
import java.awt.{ BasicStroke, Color, RenderingHints, Stroke }

import gapt.expr.Expr
import gapt.formats.latex.LatexExporter
import gapt.proofs.lk._
import gapt.proofs.{ SequentIndex, SequentProof }

import scala.swing._
import scala.swing.event._

/**
 * A panel containing a sequent proof.
 * @param main The instance of [[gapt.prooftool.SequentProofViewer]] that this belongs to.
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
    val pos:                List[Int] ) extends BoxPanel( Orientation.Vertical ) with MouseMotionListener {
  val defaultBorder = Swing.LineBorder( Color.WHITE )

  private var lineHideLevel = 0

  private def showLine() = {
    lineHideLevel = if ( lineHideLevel == 0 ) 0 else lineHideLevel - 1
    assert( lineHideLevel >= 0 )

    linePanel.visible = lineHideLevel == 0
  }

  private def hideLine() = {
    lineHideLevel += 1
    linePanel.visible = false
  }

  val endSequentPanel = {
    val mainAuxIndices = proof.mainIndices.toSet ++ auxIndices
    DrawSequent(
      this,
      proof.conclusion,
      mainAuxIndices,
      cutAncestorIndices,
      sequentElementRenderer )
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
      proof.auxIndices( i ).toSet,
      cutAncestorIndicesNew( i ),
      sequentElementRenderer,
      i :: pos )
  }

  val subProofsPanel = new SubproofsPanel( this, subProofs )
  var aboveLinePanel: AboveLinePanel[F, T] = proof match {
    case p: ProofLink =>
      new ProoflinkLabelPanel( this, p.referencedProof )
    case _ => subProofsPanel
  }

  val linePanel = new ProofLinePanel( this, proof.name )

  val aboveLinePanelIndex = if ( pos.isEmpty ) 1 else 0

  if ( pos.isEmpty ) contents += Swing.VGlue
  contents += aboveLinePanel
  contents += linePanel
  contents += endSequentPanel
  if ( pos.isEmpty ) contents += Swing.VGlue

  def endSequentWidth() = endSequentPanel.width()
  def subProofsWidth() = subProofsPanel.width()
  def width() = size.width
  def endSequentLeftMarginWidth() = ( width * subProofsPanel.xLayoutAlignment - endSequentWidth * endSequentPanel.xLayoutAlignment ).toInt
  def endSequentRightMarginWidth() = ( width * ( 1 - subProofsPanel.xLayoutAlignment ) - endSequentWidth * ( 1 - endSequentPanel.xLayoutAlignment ) ).toInt

  linePanel.xLayoutAlignment = 0.5
  endSequentPanel.xLayoutAlignment = 0.5
  subProofsPanel.xLayoutAlignment = 0.5

  updateSubProofAlignment()
  revalidate()
  repaint()

  /**
   * Recomputes the alignments of the subproofs, line, and end sequent panels.
   */
  private def updateSubProofAlignment() = {

    // This value is equal to the middle of the end sequents of the subproofs as a fraction of the width of the subproofs.
    val subProofsAligmentNew = if ( subProofs.isEmpty )
      0.5
    else
      ( subProofsPanel.endSequentWidth().toDouble / 2 + subProofsPanel.endSequentLeftMarginWidth() ) / subProofsPanel.width()

    if ( subProofsPanel.xLayoutAlignment != subProofsAligmentNew ) {
      subProofsPanel.xLayoutAlignment = subProofsAligmentNew
      publish( AlignmentChanged )

    }
    revalidate()
    repaint()
  }

  /*
   * Window management stuff & reactions
   */
  opaque = false
  border = defaultBorder

  this.peer.setAutoscrolls( true )
  this.peer.addMouseMotionListener( this )

  def mouseMoved( e: MouseEvent ) {}
  def mouseDragged( e: MouseEvent ) {
    //The user is dragging us, so scroll!
    val r = new Rectangle( e.getX, e.getY, 1, 1 )
    this.peer.scrollRectToVisible( r )
  }

  listenTo( mouse.moves, mouse.clicks, mouse.wheel, main.publisher, endSequentPanel, linePanel, subProofsPanel )
  deafTo( this )
  reactions += {
    case e: MouseDragged =>
      main.scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.MOVE_CURSOR )

    case e: MouseReleased =>
      main.scrollPane.cursor = java.awt.Cursor.getDefaultCursor

    case e: MouseWheelMoved =>
      main.scrollPane.peer.dispatchEvent( e.peer )

    case HideStructuralRules => //Fix: contraction is still drawn when a weakening is followed by a contraction.
      proof match {
        case _: WeakeningLeftRule | _: WeakeningRightRule | _: ContractionLeftRule | _: ContractionRightRule =>
          hideLine()
          main.publisher.publish( HideEndSequent( 0 :: pos ) )
        case _ =>
      }

    case HideEndSequent( p ) if p == pos =>
      endSequentPanel.visible = false

    case ShowAllRules( p ) if pos endsWith p =>
      showLine()
      endSequentPanel.visible = true

    case ShowSequentProof( p ) if p == pos =>
      showLine()
      contents( aboveLinePanelIndex ) = subProofsPanel

      revalidate()
      repaint()

    case HideSequentProof( p ) if p == pos =>
      hideLine()
      contents( aboveLinePanelIndex ) = new CollapsedSubproofsPanel( this )

      revalidate()
      repaint()

    case ShowDebugBorders =>
      border = Swing.LineBorder( Color.BLUE ) // DEBUG
      endSequentPanel.border = Swing.LineBorder( Color.MAGENTA ) // DEBUG

    case HideDebugBorders =>
      border = defaultBorder
      endSequentPanel.border = Swing.EmptyBorder

    case FontChanged =>
      revalidate()
      repaint()

    case UIElementResized( _ ) | UIElementHidden( _ ) | UIElementShown( _ ) =>
      updateSubProofAlignment()

    case AlignmentChanged =>
      updateSubProofAlignment()

    case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
      PopupMenu( this, e.point.x, e.point.y )

  }
}

/**
 * Abstract class for things that can be placed above a proof line (subproofs, labels).
 */
abstract class AboveLinePanel[F, T <: SequentProof[F, T]]( val parent: DrawSequentProof[F, T] ) extends BoxPanel( Orientation.Horizontal ) {
  final def width() = size.width
  def endSequentLeftMarginWidth(): Int
  def endSequentRightMarginWidth(): Int
  final def endSequentWidth() = width() - endSequentLeftMarginWidth() - endSequentRightMarginWidth()

  border = Swing.EmptyBorder
  opaque = false

  listenTo( parent.main.publisher )
  deafTo( this )

  reactions += {
    case ShowDebugBorders =>
      border = Swing.LineBorder( Color.GREEN ) // DEBUG

    case HideDebugBorders =>
      border = Swing.EmptyBorder

    case AlignmentChanged =>
      publish( AlignmentChanged )

  }
}

/**
 * Class that puts the name of a proof link above the proof line.
 * @param referencedProof The name of the link.
 */
class ProoflinkLabelPanel[F, T <: SequentProof[F, T]]( parent: DrawSequentProof[F, T], referencedProof: Expr ) extends AboveLinePanel[F, T]( parent ) {
  private val proofLinkLabel = new LatexLabel( parent.main, LatexExporter( referencedProof ) )

  override def endSequentLeftMarginWidth() = 0
  override def endSequentRightMarginWidth() = 0

  contents += proofLinkLabel
}

/**
 * Class that puts "(...)" above the proof line for a collapsed proof.
 */
class CollapsedSubproofsPanel[F, T <: SequentProof[F, T]]( parent: DrawSequentProof[F, T] ) extends AboveLinePanel[F, T]( parent ) {
  private val subProofsHiddenLabel = new LatexLabel( parent.main, "(...)" )
  subProofsHiddenLabel.listenTo( mouse.clicks )
  subProofsHiddenLabel.reactions += {
    case e: MouseClicked =>
      parent.main.publisher.publish( ShowSequentProof( parent.pos ) )
  }

  override def endSequentLeftMarginWidth() = 0
  override def endSequentRightMarginWidth() = 0

  contents += subProofsHiddenLabel
}

/**
 * A panel containing the subproofs of a proof arranged side by side.
 * @param parent The [[gapt.prooftool.DrawSequentProof]] instance that this belongs to.
 * @param subProofs The The [[gapt.prooftool.DrawSequentProof]] instances containing the subproofs.
 */
class SubproofsPanel[F, T <: SequentProof[F, T]](
    parent:        DrawSequentProof[F, T],
    val subProofs: Seq[DrawSequentProof[F, T]] ) extends AboveLinePanel[F, T]( parent ) {

  subProofs.foreach( contents += )
  subProofs.foreach( listenTo( _ ) )
  subProofs.foreach( _.yLayoutAlignment = 1 ) // Forces the subproof panels to align along their bottom edges

  override def endSequentLeftMarginWidth() = if ( subProofs.isEmpty ) 0 else subProofs.head.endSequentLeftMarginWidth()
  override def endSequentRightMarginWidth() = if ( subProofs.isEmpty ) 0 else subProofs.last.endSequentRightMarginWidth()
}

/**
 * Panel that contains an inference line and the name of the inference.
 * @param parent The [[gapt.prooftool.DrawSequentProof]] instance that this belongs to.
 * @param proofName The name of the inference.
 */
class ProofLinePanel[F, T <: SequentProof[F, T]](
    val parent:    DrawSequentProof[F, T],
    val proofName: String ) extends BoxPanel( Orientation.Horizontal ) {
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
    updateWidth( fontSizeHasChanged = true )
  }
  def labelFontMetrics = peer.getFontMetrics( labelFont )

  private def updateWidth( fontSizeHasChanged: Boolean = false ): Unit = {
    val newLineWidth = math.max( parent.subProofsPanel.endSequentWidth(), parent.endSequentPanel.width() )
    if ( fontSizeHasChanged || math.abs( lineWidth - newLineWidth ) > 2 ) {
      lineWidth = newLineWidth
      val labelWidth = labelFontMetrics.stringWidth( proofName ) * 2 + fSize
      _width = lineWidth + labelWidth
      val height = labelFontMetrics.getHeight + fSize / 4
      preferredSize = new Dimension( _width, height )
      minimumSize = preferredSize
      maximumSize = preferredSize
      repaint()
    }
  }
  def width() = _width
  private var _width = 0; private var lineWidth = 0; updateWidth()

  override def paintComponent( g: Graphics2D ): Unit = {
    val leftPoint = ( size.width - lineWidth ) / 2
    val rightPoint = ( size.width + lineWidth ) / 2

    g.setRenderingHint( RenderingHints.KEY_TEXT_ANTIALIASING, RenderingHints.VALUE_TEXT_ANTIALIAS_LCD_HRGB )
    g.drawLine( leftPoint, size.height / 2, rightPoint, size.height / 2 )
    g.setFont( labelFont )
    g.drawString( proofName, rightPoint + fSize / 8, size.height / 2 + labelFontMetrics.getMaxDescent )
  }

  border = Swing.EmptyBorder
  listenTo( parent.main.publisher, parent.endSequentPanel, parent.subProofsPanel )
  deafTo( this )
  reactions += {
    case UIElementShown( _ ) | UIElementResized( _ ) | AlignmentChanged => updateWidth()

    case ShowDebugBorders =>
      border = Swing.LineBorder( Color.RED ) // DEBUG

    case HideDebugBorders =>
      border = Swing.EmptyBorder

    case FontChanged =>
      fSize = parent.main.currentFontSize
  }
}
