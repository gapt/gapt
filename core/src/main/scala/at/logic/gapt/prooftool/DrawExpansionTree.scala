package at.logic.gapt.prooftool

import at.logic.gapt.expr._

import swing._
import scala.swing.event.{ MouseClicked, MouseEntered, MouseExited }
import java.awt.{ Color, Font }
import java.awt.event.MouseEvent

import at.logic.gapt.proofs.expansion._
import org.scilab.forge.jlatexmath.{ TeXConstants, TeXFormula }
import java.awt.image.BufferedImage

import at.logic.gapt.formats.latex.LatexExporter
import at.logic.gapt.utils.Logger
import org.slf4j.LoggerFactory

object ExpansionTreeState extends Enumeration {
  val Closed, Open, Expanded = Value
}

/**
 * Draws an expansion tree. Abstract because most of the work is done by subclasses for quantifier and non-quantifier nodes.
 * @param main The main prooftool window that this belongs to.
 * @param expansionTree The expansion tree being displayed.
 * @param outerQuantifier The object drawing the innermost enclosing quantifier (if any).
 */
abstract class DrawExpansionTree(
    val main:            ProofToolViewer[_],
    val expansionTree:   ExpansionTree,
    val outerQuantifier: Option[DrawETQuantifierBlock] = None
) extends BoxPanel( Orientation.Horizontal ) {

  background = new Color( 255, 255, 255 )
  yLayoutAlignment = 0.5
  xLayoutAlignment = 0
  val highlightColor = Color.red
  val ft = main.font
  def subTrees: Vector[DrawExpansionTree]

  def drawFormula( formula: HOLFormula ): BoxPanel = new BoxPanel( Orientation.Horizontal ) {
    background = new Color( 255, 255, 255 )
    yLayoutAlignment = 0.5
    opaque = false

    formula match {
      case Neg( f ) =>
        val conn = label( "¬" )
        val subF = drawFormula( f )
        this.listenTo( conn.mouse.moves )
        this.reactions += {
          case _: MouseEntered =>
            conn.foreground = highlightColor
          case _: MouseExited =>
            conn.foreground = Color.black
        }
        contents += conn
        contents += subF
      case And( f1, f2 ) =>
        val parenthesis = connectedParentheses()
        val conn = label( "∧" )
        val subF1 = drawFormula( f1 )
        val subF2 = drawFormula( f2 )
        this.listenTo( conn.mouse.moves, parenthesis._1.mouse.moves, parenthesis._2.mouse.moves )
        this.reactions += {
          case _: MouseEntered =>
            conn.foreground = highlightColor
            parenthesis._1.foreground = highlightColor
            parenthesis._2.foreground = highlightColor
          case _: MouseExited =>
            conn.foreground = Color.black
            parenthesis._1.foreground = Color.black
            parenthesis._2.foreground = Color.black
        }
        contents += parenthesis._1
        contents += subF1
        contents += conn
        contents += subF2
        contents += parenthesis._2
      case Or( f1, f2 ) =>
        val parenthesis = connectedParentheses()
        val conn = label( "∨" )
        val subF1 = drawFormula( f1 )
        val subF2 = drawFormula( f2 )
        this.listenTo( conn.mouse.moves, parenthesis._1.mouse.moves, parenthesis._2.mouse.moves )
        this.reactions += {
          case _: MouseEntered =>
            conn.foreground = highlightColor
            parenthesis._1.foreground = highlightColor
            parenthesis._2.foreground = highlightColor
          case _: MouseExited =>
            conn.foreground = Color.black
            parenthesis._1.foreground = Color.black
            parenthesis._2.foreground = Color.black
        }
        contents += parenthesis._1
        contents += subF1
        contents += conn
        contents += subF2
        contents += parenthesis._2
      case Imp( f1, f2 ) =>
        val parenthesis = connectedParentheses()
        val conn = label( "⊃" )
        val subF1 = drawFormula( f1 )
        val subF2 = drawFormula( f2 )
        this.listenTo( conn.mouse.moves, parenthesis._1.mouse.moves, parenthesis._2.mouse.moves )
        this.reactions += {
          case _: MouseEntered =>
            conn.foreground = highlightColor
            parenthesis._1.foreground = highlightColor
            parenthesis._2.foreground = highlightColor
          case _: MouseExited =>
            conn.foreground = Color.black
            parenthesis._1.foreground = Color.black
            parenthesis._2.foreground = Color.black
        }
        contents += parenthesis._1
        contents += subF1
        contents += conn
        contents += subF2
        contents += parenthesis._2
      case Ex( v, f ) =>
        contents += label( "\\exists " + LatexExporter.escapeName( v.name ) + " " )
        contents += drawFormula( f )
      case All( v, f ) =>
        contents += label( "\\forall " + LatexExporter.escapeName( v.name ) + " " )
        contents += drawFormula( f )
      case _ =>
        val lbl = LatexLabel( main, LatexExporter( formula ) )
        lbl.deafTo( lbl.mouse.moves, lbl.mouse.clicks )
        contents += lbl
    }
  }

  def label( s: String ) = if ( s == "," )
    new CommaLabel( main )
  else new LatexLabel( main, s ) {
    if ( s == "(" || s == ")" ) {
      opaque = true
      tooltip = "Click to mark/unmark."
      listenTo( mouse.clicks )
      reactions += {
        case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
          val color = RGBColorChooser( this, e.point.x, e.point.y )
          if ( color.isDefined ) {
            background = color.get
            peer.dispatchEvent( new MouseEvent( peer, e.peer.getID, e.peer.getWhen, e.modifiers, e.point.x, e.point.y, e.clicks, e.triggersPopup, MouseEvent.BUTTON1 ) )
          }
      }
    }

  }

  def connectedParentheses() = {
    val left = label( "(" )
    val right = label( ")" )
    left.reactions += {
      case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
        if ( left.background == Color.white || left.background != left.background ) {
          left.background = left.background
          right.background = left.background
        } else {
          left.background = Color.white
          right.background = Color.white
        }
    }
    right.reactions += {
      case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
        if ( right.background == Color.white || right.background != right.background ) {
          left.background = right.background
          right.background = right.background
        } else {
          left.background = Color.white
          right.background = Color.white
        }
    }

    ( left, right )
  }

  /**
   * Expands this node (if it's a quantifier node) and all below it.
   */
  def expandAll(): Unit = subTrees.foreach( _.expandAll() )

  /**
   * Closes this node (if it's a quantifier node) and all below it.
   */
  def closeAll(): Unit = subTrees.foreach( _.closeAll() )

  /**
   * Opens this node (if it's a quantifier node) and all below it.
   */
  def openAll(): Unit = subTrees.foreach( _.openAll() )
}

/**
 * Factory object.
 */
object DrawExpansionTree {
  def apply(
    main:            ProofToolViewer[_],
    expansionTree:   ExpansionTree,
    outerQuantifier: Option[DrawETQuantifierBlock] = None
  ): DrawExpansionTree = expansionTree match {
    case ETQuantifierBlock( _, _, _ ) =>
      new DrawETQuantifierBlock( main, expansionTree, outerQuantifier )
    case _ =>
      new DrawETNonQuantifier( main, expansionTree, outerQuantifier )
  }
}

/**
 * Draws an expansion tree beginning with a quantifier block.
 * @param main The main prooftool window that this belongs to.
 * @param expansionTree The expansion tree being displayed.
 * @param outerQuantifier The object drawing the quantifier imeediately outside this one (if any).
 */
class DrawETQuantifierBlock(
    main:            ProofToolViewer[_],
    expansionTree:   ExpansionTree,
    outerQuantifier: Option[DrawETQuantifierBlock] = None
) extends DrawExpansionTree( main, expansionTree, outerQuantifier ) {
  import ExpansionTreeState._

  val ETQuantifierBlock( formula, depth, instances ) = expansionTree
  val terms = instances.toVector.map( i => i._1 )
  val subTrees = for ( et <- instances.toVector.map( i => i._2 ) ) yield DrawExpansionTree( main, et, Some( this ) )
  val quantifiers = quantifierBlockString( takeQuants( formula, depth ), formula ) // quantifiers is a string containing the quantifier block represented by this weak node.
  val subF = dropQuants( formula, depth )
  val headLabelExpanded = formula match {
    case Ex( _, _ )  => LatexLabel( main, "\\bigvee" )
    case All( _, _ ) => LatexLabel( main, "\\bigwedge" )
    case _           => throw new Exception( "Something went wrong in DrawExpansionTree!" )
  }

  headLabelExpanded.reactions += {
    case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 => close()
    case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
      PopupMenu( DrawETQuantifierBlock.this, headLabelExpanded, e.point.x, e.point.y )
  }

  private var _headLabel = LatexLabel( main, quantifiers ) // Head symbol of the expansion tree. Quantifiers if open or closed, bigvee/bigwedge if expanded.
  def headLabel = _headLabel
  def headLabel_=( newLabel: LatexLabel ) = {
    _headLabel = newLabel
    contents( 0 ) = newLabel
  }

  val termPanel = drawTerms( terms )

  private var _instancesPanel = drawFormula( subF ) // Panel containing the instances.
  def instancesPanel = _instancesPanel
  def instancesPanel_=( newPanel: BoxPanel ) = {
    _instancesPanel = newPanel
    contents( 2 ) = newPanel
  }

  var state: ExpansionTreeState.Value = Open // The state of this quantifier node.

  contents += headLabel
  contents += termPanel
  contents += instancesPanel

  close()

  def close() {
    if ( state != Closed ) {
      state = Closed
      headLabel = LatexLabel( main, quantifiers )
      headLabel.reactions += {
        case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
          PopupMenu( this, headLabel, e.point.x, e.point.y )
        case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
          if ( state == Open ) expand()
          else open()
      }

      termPanel.visible = false
      instancesPanel = drawFormula( subF )

      revalidate()
    }
  }

  def open() {
    if ( state != Open ) {
      outerQuantifier.foreach { _.expand() }
      state = Open
      headLabel = LatexLabel( main, quantifiers )
      headLabel.reactions += {
        case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
          PopupMenu( this, headLabel, e.point.x, e.point.y )
        case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
          if ( state == Open ) expand()
          else open()
      }

      termPanel.visible = true
      instancesPanel = drawFormula( subF )

      revalidate()
    }
  }

  def expand() {
    if ( state != Expanded ) {
      outerQuantifier.foreach { _.expand() }
      state = Expanded
      if ( subTrees != Nil ) {
        headLabel = headLabelExpanded
        termPanel.visible = false
        instancesPanel = subtreeMatrix
      } else {
        headLabel.visible = false
        termPanel.visible = false
        instancesPanel = drawFormula( instances.head._2.shallow ) // If there are no terms to expand the quantifier with, we can safely call drawFormula.
      }
      revalidate()
    }
  }

  /**
   *
   * @return A BoxPanel containing the subtrees stacked on top of each other and surrounded by angle brackets.
   */
  def subtreeMatrix = new BoxPanel( Orientation.Vertical ) {
    background = new Color( 255, 255, 255 )
    yLayoutAlignment = 0.5
    border = Swing.EmptyBorder( 0, ft.getSize, 0, ft.getSize )

    subTrees.foreach( bp => {
      bp.border = Swing.EmptyBorder( 3 )
      contents += bp
    } )

    override def paintComponent( g: Graphics2D ) {
      import java.awt.{ BasicStroke, RenderingHints }
      super.paintComponent( g )

      val fSize = ft.getSize
      val strokeSize = if ( fSize / 25 < 1 ) 1 else ft.getSize / 25

      g.setStroke( new BasicStroke( strokeSize, BasicStroke.CAP_ROUND, BasicStroke.JOIN_ROUND ) )
      g.setRenderingHint( RenderingHints.KEY_TEXT_ANTIALIASING, RenderingHints.VALUE_TEXT_ANTIALIAS_LCD_HRGB )
      g.setRenderingHint( RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON )

      val leftAngleNodeX = fSize / 3
      val leftAngleEdgesX = fSize - 1

      val rightAngleNodeX = size.width - fSize / 3
      val rightAngleEdgesX = size.width - ( fSize - 1 )

      val anglesEdge1Y = 0
      val anglesNodeY = size.height / 2
      val anglesEdge2Y = size.height

      g.drawLine( leftAngleNodeX, anglesNodeY, leftAngleEdgesX, anglesEdge1Y )
      g.drawLine( leftAngleNodeX, anglesNodeY, leftAngleEdgesX, anglesEdge2Y )

      g.drawLine( rightAngleNodeX, anglesNodeY, rightAngleEdgesX, anglesEdge1Y )
      g.drawLine( rightAngleNodeX, anglesNodeY, rightAngleEdgesX, anglesEdge2Y )
    }

  }

  /**
   * @param vars
   * @param f
   * @return A string containing the quantifier block represented by this quantifier node.
   */
  def quantifierBlockString( vars: List[Var], f: HOLFormula ): String = f match {
    case All( _, _ ) => vars.map( v => "\\forall " + LatexExporter( v ) + "\\:" ).mkString
    case Ex( _, _ )  => vars.map( v => "\\exists " + LatexExporter( v ) + "\\:" ).mkString
  }

  def dropQuants( formula: HOLFormula, howMany: Int ): HOLFormula =
    if ( howMany == 0 ) formula
    else formula match {
      case All( _, f ) => dropQuants( f, howMany - 1 )
      case Ex( _, f )  => dropQuants( f, howMany - 1 )
    }

  def takeQuants( formula: HOLFormula, howMany: Int ): List[Var] =
    if ( howMany == 0 ) Nil
    else formula match {
      case All( x, f ) => x +: takeQuants( f, howMany - 1 )
      case Ex( x, f )  => x +: takeQuants( f, howMany - 1 )
    }

  def drawTerms( list: Seq[Seq[LambdaExpression]] ) = new BoxPanel( Orientation.Vertical ) {
    background = new Color( 255, 255, 255 )
    yLayoutAlignment = 0.5

    for ( v <- list )
      contents += drawTermVector( v )
  }

  def drawTermVector( list: Seq[LambdaExpression] ) = new BoxPanel( Orientation.Horizontal ) {
    background = new Color( 255, 255, 255 )
    yLayoutAlignment = 0.5

    contents += label( "\\langle" )
    var firstTerm = true

    for ( t <- list ) {
      if ( !firstTerm ) {
        val lbl = label( "," )
        //lbl.yLayoutAlignment = 0
        contents += lbl
      } else firstTerm = false
      contents += label( LatexExporter( t ) )
    }

    contents += label( "\\rangle" )
  }

  override def expandAll() = {
    expand()
    super.expandAll()
  }

  override def closeAll() = close()

  override def openAll() = open()
}

/**
 * Draws an expansion tree not beginning with a quantifier block.
 * @param main The main prooftool window that this belongs to.
 * @param expansionTree The expansion tree being displayed.
 * @param outerQuantifier The object drawing the quantifier imeediately outside this one (if any).
 */
class DrawETNonQuantifier(
    main:            ProofToolViewer[_],
    expansionTree:   ExpansionTree,
    outerQuantifier: Option[DrawETQuantifierBlock] = None
) extends DrawExpansionTree( main, expansionTree, outerQuantifier ) {

  override val subTrees = expansionTree match {
    case ETAtom( _, _ ) | ETTop( _ ) | ETBottom( _ ) | ETWeakening( _, _ ) | ETDefinition( _, _, _ ) =>
      val lbl = LatexLabel( main, LatexExporter( expansionTree.shallow ) )
      lbl.deafTo( lbl.mouse.moves, lbl.mouse.clicks ) // We don't want atoms to react to mouse behavior.
      contents += lbl
      Vector()

    case ETNeg( t ) =>
      val conn = label( "¬" )
      val subF = DrawExpansionTree( main, t, outerQuantifier )
      this.listenTo( conn.mouse.moves )
      this.reactions += {
        case _: MouseEntered =>
          conn.foreground = highlightColor
        case _: MouseExited =>
          conn.foreground = Color.black
      }
      contents += conn
      contents += subF
      Vector( subF )

    case ETAnd( t1, t2 ) =>
      val parentheses = connectedParentheses()
      val conn = label( "∧" )
      val subF1 = DrawExpansionTree( main, t1, outerQuantifier )
      val subF2 = DrawExpansionTree( main, t2, outerQuantifier )
      this.listenTo( conn.mouse.moves, parentheses._1.mouse.moves, parentheses._2.mouse.moves )
      this.reactions += {
        case _: MouseEntered =>
          conn.foreground = highlightColor
          parentheses._1.foreground = highlightColor
          parentheses._2.foreground = highlightColor
        case _: MouseExited =>
          conn.foreground = Color.black
          parentheses._1.foreground = Color.black
          parentheses._2.foreground = Color.black
      }
      contents += parentheses._1
      contents += subF1
      contents += conn
      contents += subF2
      contents += parentheses._2
      Vector( subF1, subF2 )

    case ETOr( t1, t2 ) =>
      val parentheses = connectedParentheses()
      val conn = label( "∨" )
      val subF1 = DrawExpansionTree( main, t1, outerQuantifier )
      val subF2 = DrawExpansionTree( main, t2, outerQuantifier )
      this.listenTo( conn.mouse.moves, parentheses._1.mouse.moves, parentheses._2.mouse.moves )
      this.reactions += {
        case _: MouseEntered =>
          conn.foreground = highlightColor
          parentheses._1.foreground = highlightColor
          parentheses._2.foreground = highlightColor
        case _: MouseExited =>
          conn.foreground = Color.black
          parentheses._1.foreground = Color.black
          parentheses._2.foreground = Color.black
      }
      contents += parentheses._1
      contents += subF1
      contents += conn
      contents += subF2
      contents += parentheses._2
      Vector( subF1, subF2 )

    case ETImp( t1, t2 ) =>
      val parentheses = connectedParentheses()
      val conn = label( "⊃" )
      val subF1 = DrawExpansionTree( main, t1, outerQuantifier )
      val subF2 = DrawExpansionTree( main, t2, outerQuantifier )
      this.listenTo( conn.mouse.moves, parentheses._1.mouse.moves, parentheses._2.mouse.moves )
      this.reactions += {
        case _: MouseEntered =>
          conn.foreground = highlightColor
          parentheses._1.foreground = highlightColor
          parentheses._2.foreground = highlightColor
        case _: MouseExited =>
          conn.foreground = Color.black
          parentheses._1.foreground = Color.black
          parentheses._2.foreground = Color.black
      }
      contents += parentheses._1
      contents += subF1
      contents += conn
      contents += subF2
      contents += parentheses._2
      Vector( subF1, subF2 )
  }
}

object ETStrongQuantifierBlock {
  def unapply( et: ExpansionTree ): Some[( HOLFormula, Int, Map[Seq[LambdaExpression], ExpansionTree] )] = et match {
    case ETStrongQuantifier( _, eigen, ETStrongQuantifierBlock( _, depth, children ) ) =>
      Some( ( et.shallow, depth + 1, for ( ( t, child ) <- children ) yield ( eigen +: t, child ) ) )
    case ETSkolemQuantifier( _, st, _, ETStrongQuantifierBlock( _, depth, children ) ) =>
      Some( ( et.shallow, depth + 1, for ( ( t, child ) <- children ) yield ( st +: t, child ) ) )
    case _ => Some( ( et.shallow, 0, Map( Seq[LambdaExpression]() -> et ) ) )
  }
}

object ETQuantifierBlock {
  def unapply( et: ExpansionTree ): Option[( HOLFormula, Int, Map[Seq[LambdaExpression], ExpansionTree] )] = et match {
    case ETStrongQuantifierBlock( shallow, depth, children ) if depth > 0 => Some( ( shallow, depth, children ) )
    case ETWeakQuantifierBlock( shallow, depth, children ) if depth > 0 => Some( ( shallow, depth, children ) )
    case _ => None
  }
}