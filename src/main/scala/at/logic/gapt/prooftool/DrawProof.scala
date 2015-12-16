package at.logic.gapt.prooftool

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 4:24 PM
 */

import scala.swing._
import BorderPanel._
import event._
import java.awt.Font._
import at.logic.gapt.proofs.proofs._
import java.awt.event.{ MouseMotionListener, MouseEvent }
import at.logic.gapt.proofs.shlk.SchemaProofLinkRule
import at.logic.gapt.proofs.lkOld.base.OccSequent
import java.awt.RenderingHints
import at.logic.gapt.proofs.lkOld._
import at.logic.gapt.proofs.occurrences.FormulaOccurrence

class DrawProof[T](
  val main:                        TreeProofViewer[T],
  val proof:                       TreeProof[T],
  private val fSize:               Int,
  private var visible_occurrences: Option[Set[FormulaOccurrence]],
  private var str:                 String
)
    extends BorderPanel with MouseMotionListener {
  private val blue = new Color( 0, 0, 255 )
  private val black = new Color( 0, 0, 0 )
  private val white = new Color( 255, 255, 255 )

  background = white
  opaque = false

  private val labelFont = new Font( SERIF, ITALIC, fSize - 2 )
  private val bd = Swing.EmptyBorder( 0, fSize * 2, 0, fSize * 2 )
  private val ft = new Font( SERIF, PLAIN, fSize )
  private var drawLines = true
  // The following is a hack to be able to apply searching to the end-sequent. Think about better solution.
  // The problem is that I need to "recalculate" end-sequent and need def for this reason.
  // But then since def is a function, size of tx1 cannot be calculated and lines are not drawn correctly.
  private var tx = tx1
  private def tx1 = proof.root match {
    case so: OccSequent =>
      val ds = DrawSequent( main, so, ft, visible_occurrences )
      ds.listenTo( mouse.moves, mouse.clicks, mouse.wheel, main.publisher )
      ds.reactions += {
        case e: MouseEntered => ds.contents.foreach( x => x.foreground = blue )
        case e: MouseExited => ds.contents.foreach( x => x.foreground = black )
        case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 => //PopupMenu( proof, this, e.point.x, e.point.y )
      }
      ds
    case _ => new Label( proof.root.toString ) {
      font = ft
      if ( !str.isEmpty && proof.root.toString.contains( str ) ) foreground = new Color( 0, 225, 0 )
    }
  }

  listenTo( mouse.moves, mouse.clicks, mouse.wheel, main.publisher )
  reactions += {
    case e: MouseDragged =>
      main.scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.MOVE_CURSOR )
    case e: MouseReleased =>
      main.scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    case e: MouseWheelMoved =>
      main.scrollPane.peer.dispatchEvent( e.peer )
    case HideStructuralRules => //Fix: contraction is still drawn when a weakening is followed by a contraction.
      proof.rule match {
        case WeakeningLeftRuleType | WeakeningRightRuleType | ContractionLeftRuleType | ContractionRightRuleType =>
          drawLines = false
          tx.visible = false
        case _ =>
      }
    case e: ShowAllRulesOld[_] if e.proof == proof =>
      drawLines = true
      initialize()
      revalidate()
    case e: ShowProof[_] if e.proof == proof =>
      drawLines = true
      layout.foreach( pair => pair._1.visible = true )
    case e: HideProof[_] if e.proof == proof =>
      drawLines = false
      layout.foreach( pair => if ( pair._2 != Position.South ) pair._1.visible = false )
  }

  initialize()
  // end of constructor

  def setVisibleOccurrences( s: Option[Set[FormulaOccurrence]] ) {
    visible_occurrences = s
    // tx = tx1 // Uncomment this line if you want to include the end-sequent.
    initialize()
    repaint()
  }

  def initialize() {
    proof match {
      case p: UnaryTreeProof[_] =>
        border = bd
        layout( new DrawProof( main, p.uProof.asInstanceOf[TreeProof[T]], fSize, visible_occurrences, str ) ) = Position.Center
        layout( tx ) = Position.South
      case p: BinaryTreeProof[_] =>
        border = bd
        layout( new DrawProof( main, p.uProof1.asInstanceOf[TreeProof[T]], fSize, visible_occurrences, str ) ) = Position.West
        layout( new DrawProof( main, p.uProof2.asInstanceOf[TreeProof[T]], fSize, visible_occurrences, str ) ) = Position.East
        layout( tx ) = Position.South
      case p: NullaryTreeProof[_] => p match {
        case SchemaProofLinkRule( _, link, indices ) =>
          layout( new BoxPanel( Orientation.Vertical ) {
            background = white
            opaque = false
            border = Swing.EmptyBorder( 0, fSize, 0, fSize )
            val pLink = LatexLabel( main, ft, "(\\textbf{" + link + "}" + indices.foldRight( "" )( ( i, rez ) => ", " + DrawSequent.formulaToLatexString( i ) + rez ) + ")", null )
            pLink.xLayoutAlignment = 0.5
            pLink.opaque = false
            pLink.border = Swing.EmptyBorder( 0, 0, 5, 0 )
            tx.xLayoutAlignment = 0.5
            tx.border = Swing.MatteBorder( 1, 0, 0, 0, new Color( 255, 0, 0 ) )
            contents += pLink
            contents += tx
          } ) = Position.South
        case _ =>
          tx.border = Swing.EmptyBorder( 0, fSize, 0, fSize )
          layout( tx ) = Position.South
      }
    }
  }

  def getSequentWidth( g: Graphics2D ) = tx match {
    case label: Label      => g.getFontMetrics( ft ).stringWidth( label.text )
    case fPanel: FlowPanel => fPanel.contents.foldLeft( 0 )( ( width, x ) => width + x.size.width + 5 )
  }

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

    if ( drawLines ) proof match {
      case p: UnaryTreeProof[_] =>
        val center = this.layout.find( x => x._2 == Position.Center ).get._1.asInstanceOf[DrawProof[T]]
        val width = center.size.width + fSize * 4
        val height = center.size.height
        val seqLength = max( center.getSequentWidth( g ), getSequentWidth( g ) )

        g.drawLine( ( width - seqLength ) / 2, height, ( width + seqLength ) / 2, height )
        g.drawString( p.name, ( fSize / 4 + width + seqLength ) / 2, height + metrics.getMaxDescent )
      case p: BinaryTreeProof[_] =>
        val left = this.layout.find( x => x._2 == Position.West ).get._1.asInstanceOf[DrawProof[T]]
        val leftWidth = left.size.width + fSize * 4
        val right = this.layout.find( x => x._2 == Position.East ).get._1.asInstanceOf[DrawProof[T]]
        val rightWidth = right.size.width
        val height = max( left.size.height, right.size.height )
        val leftSeqLength = left.getSequentWidth( g )
        val rightSeqLength = right.getSequentWidth( g )
        val lineLength = right.location.x + ( rightWidth + rightSeqLength ) / 2

        if ( main.DEBUG ) { // draw bounding box around children for debugging
          g.setColor( new Color( 200, 200, 50 ) )
          g.drawRect( left.location.x, left.location.y, left.size.width - 1, left.size.height )
          g.setColor( new Color( 200, 50, 200 ) )
          g.drawRect( right.location.x, right.location.y, right.size.width, right.size.height )
          g.setColor( new Color( 0, 0, 0 ) )

          assert( this.size.width >= left.size.width, "Left child must not be wider than parent." )
          assert( this.size.width >= right.size.width, "Right child must not be wider than parent." )
        }

        g.drawLine( ( leftWidth - leftSeqLength ) / 2, height, lineLength, height )
        g.drawString( p.name, lineLength + fSize / 4, height + metrics.getMaxDescent )
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

  def getLocationOfProof( p: TreeProof[_] ): Option[Point] = {
    if ( p == proof ) {
      val newloc = new Point( location.x + bounds.width / 2, location.y + bounds.height )
      Some( newloc )
    } else contents.foldLeft[Option[Point]]( None )( ( res, dp ) =>
      if ( res == None ) dp match {
        case x: DrawProof[_] =>
          x.getLocationOfProof( p ) match {
            case Some( loc ) => // need to translate
              val newloc = new Point( loc.x + location.x, loc.y + location.y )
              Some( newloc )
            case _ => None
          }
        case _ => None
      }
      else res // we have found the proof already
      )
  }
}
