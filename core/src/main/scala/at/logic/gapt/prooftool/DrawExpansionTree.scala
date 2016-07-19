package at.logic.gapt.prooftool

import at.logic.gapt.expr._
import at.logic.gapt.utils.logging.Logger

import swing._
import scala.swing.event.{ MouseClicked, MouseEntered, MouseExited }
import java.awt.{ Color, Font }
import java.awt.event.MouseEvent

import at.logic.gapt.proofs.expansion._
import org.scilab.forge.jlatexmath.{ TeXConstants, TeXFormula }
import java.awt.image.BufferedImage

import at.logic.gapt.formats.latex.LatexExporter
import org.slf4j.LoggerFactory

object ExpansionTreeState extends Enumeration {
  val Close, Open, Expand = Value
}

class DrawExpansionTree( main: ProofToolViewer[_], val expansionTree: ExpansionTree, private val ft: Font ) extends BoxPanel( Orientation.Horizontal ) {

  import ExpansionTreeState._

  background = new Color( 255, 255, 255 )
  yLayoutAlignment = 0.5
  xLayoutAlignment = 0
  private val state = scala.collection.mutable.Map.empty[HOLFormula, ExpansionTreeState.Value]
  val highlightColor = Color.red
  initialize

  def initialize = {
    contents += treeToComponent( expansionTree, allow = true )
  }

  def close( f: HOLFormula ) {
    contents.clear()
    state += ( ( f, Close ) )
    initialize
    revalidate()
  }

  def open( f: HOLFormula ) {
    contents.clear()
    state += ( ( f, Open ) )
    initialize
    revalidate()
  }

  def expand( f: HOLFormula ) {
    contents.clear()
    state += ( ( f, Expand ) )
    initialize
    revalidate()
  }

  /**
   * This function is responsible for converting an expansion tree to a component.
   *
   * @param expTree The tree to be converted.
   * @param allow Whether the root node of expTree should be clickable. Might be obsolete.
   * @return A BoxPanel representing expTree.
   */
  def treeToComponent( expTree: ExpansionTree, allow: Boolean ): BoxPanel = new BoxPanel( Orientation.Horizontal ) {
    background = new Color( 255, 255, 255 )
    yLayoutAlignment = 0.5
    opaque = false

    expTree match {
      case ETAtom( _, _ ) | ETTop( _ ) | ETBottom( _ ) | ETWeakening( _, _ ) | ETDefinition( _, _, _ ) =>
        val lbl = LatexLabel( main, ft, LatexExporter( expTree.shallow ) )
        lbl.deafTo( lbl.mouse.moves, lbl.mouse.clicks ) // We don't want atoms to react to mouse behavior.
        contents += lbl
      case ETNeg( t ) =>
        val conn = label( "¬", ft )
        val subF = treeToComponent( t, allow )
        this.listenTo( conn.mouse.moves )
        this.reactions += {
          case _: MouseEntered =>
            conn.foreground = highlightColor
          case _: MouseExited =>
            conn.foreground = Color.black
        }
        contents += conn
        contents += subF
      case ETAnd( t1, t2 ) =>
        val parenthesis = connectParenthesis( label( "(", ft ), label( ")", ft ) )
        val conn = label( "∧", ft )
        val subF1 = treeToComponent( t1, allow )
        val subF2 = treeToComponent( t2, allow )
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
      case ETOr( t1, t2 ) =>
        val parenthesis = connectParenthesis( label( "(", ft ), label( ")", ft ) )
        val conn = label( "∨", ft )
        val subF1 = treeToComponent( t1, allow )
        val subF2 = treeToComponent( t2, allow )
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
      case ETImp( t1, t2 ) =>
        val parenthesis = connectParenthesis( label( "(", ft ), label( ")", ft ) )
        val conn = label( "⊃", ft )
        val subF1 = treeToComponent( t1, allow )
        val subF2 = treeToComponent( t2, allow )
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

      case ETQuantBlock( formula, depth, instances ) =>
        val terms = instances.toList.map( i => i._1 )
        val subtrees = instances.toList.map( i => i._2 )
        val quantifiers = quantifierBlock( takeQuants( formula, depth ), formula ) // quantifiers is a string containing the quantifier block represented by this weak node.

        if ( state.get( formula ) == Some( Expand ) ) {
          // We first consider the case that the top-level quantifier is expanded.
          if ( subtrees != Nil ) {
            val lbl = LatexLabel( main, ft, getMatrixSymbol( formula ) )
            lbl.reactions += {
              case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 => close( formula )
              case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
                PopupMenu( DrawExpansionTree.this, formula, lbl, e.point.x, e.point.y )
            }
            contents += lbl
            contents += drawMatrix( subtrees )
          } else {
            state -= formula
            contents += drawFormula( instances.head._2.shallow ) // If there are no terms to expand the quantifier with, we can safely call drawFormula.
          }
        } else {
          // The current tree is either open or closed.
          val lbl = LatexLabel( main, ft, quantifiers )
          val subF = dropQuants( formula, depth )

          if ( allow ) lbl.reactions += {
            case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
              PopupMenu( DrawExpansionTree.this, formula, lbl, e.point.x, e.point.y )
            case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
              if ( state.get( formula ) == Some( Open ) ) expand( formula )
              else open( formula )
          }
          else {
            lbl.deafTo( lbl.mouse.clicks )
            lbl.tooltip = "First expand all the quantifiers till the root!" // alternative message "The block of quantifiers is locked!"
          }

          contents += lbl
          if ( state.get( formula ) == Some( Open ) ) contents += drawTerms( terms ) // If the quantifier block is open, we draw its terms.
          contents += drawFormula( subF ) // Since the current quantifier block is not expanded, we needn't worry about the state of child trees and can call drawFormula.
        }
    }
  }

  object ETStrongBlock {
    def unapply( et: ExpansionTree ): Some[( HOLFormula, Int, Map[List[LambdaExpression], ExpansionTree] )] = et match {
      case ETStrongQuantifier( _, eigen, ETStrongBlock( _, depth, children ) ) =>
        Some( ( et.shallow, depth + 1, for ( ( t, child ) <- children ) yield ( eigen +: t, child ) ) )
      case ETSkolemQuantifier( _, st, _, ETStrongBlock( _, depth, children ) ) =>
        Some( ( et.shallow, depth + 1, for ( ( t, child ) <- children ) yield ( st +: t, child ) ) )
      case _ => Some( ( et.shallow, 0, Map( List[LambdaExpression]() -> et ) ) )
    }
  }

  object ETQuantBlock {
    def unapply( et: ExpansionTree ) = et match {
      case ETStrongBlock( shallow, depth, children ) if depth > 0 => Some( ( shallow, depth, children ) )
      case ETWeakQuantifierBlock( shallow, depth, children ) if depth > 0 => Some( ( shallow, depth, children ) )
      case _ => None
    }
  }

  def dropQuants( formula: HOLFormula, howMany: Int ): HOLFormula =
    if ( howMany == 0 ) formula else formula match {
      case All( _, f ) => dropQuants( f, howMany - 1 )
      case Ex( _, f )  => dropQuants( f, howMany - 1 )
    }
  def takeQuants( formula: HOLFormula, howMany: Int ): List[Var] =
    if ( howMany == 0 ) Nil else formula match {
      case All( x, f ) => x +: takeQuants( f, howMany - 1 )
      case Ex( x, f )  => x +: takeQuants( f, howMany - 1 )
    }

  def getMatrixSymbol( formula: HOLFormula ) = formula match {
    case Ex( _, _ )  => "\\bigvee"
    case All( _, _ ) => "\\bigwedge"
    case _           => throw new Exception( "Something went wrong in DrawExpansionTree!" )
  }

  /**
   * @param et A ExpansionTree (either StrongQuantifier or WeakQuantifier)
   * @return A string containing the quantifier block represented by this quantifier node.
   */
  def quantifierBlock( vars: List[Var], f: HOLFormula ): String = f match {
    case All( _, _ ) => vars.foldLeft( "" )( ( str: String, v: Var ) => str + "(\\forall " + LatexExporter( v ) + ")" )
    case Ex( _, _ )  => vars.foldLeft( "" )( ( str: String, v: Var ) => str + "(\\exists " + LatexExporter( v ) + ")" )
  }

  // Draws <t_1,...,t_n ; ... ; s_1,...,s_n>
  // List of terms are separated by ; and terms in a list by ,
  def drawTerms( list: Seq[Seq[LambdaExpression]] ) = new BoxPanel( Orientation.Horizontal ) {
    background = new Color( 255, 255, 255 )
    yLayoutAlignment = 0.5

    contents += label( "\\langle", ft )
    var firstList = true
    list.foreach( l => {
      if ( !firstList ) {
        val lbl = label( "\\; ; \\;", ft )
        lbl.yLayoutAlignment = 0.35
        contents += lbl
      } else firstList = false
      var firstTerm = true
      l.foreach( t => {
        if ( !firstTerm ) {
          val lbl = label( ",", ft )
          lbl.yLayoutAlignment = 0
          contents += lbl
        } else firstTerm = false
        contents += label( LatexExporter( t ), ft )
      } )
    } )
    contents += label( "\\rangle", ft )
  }

  /**
   *
   * @param list A list of ExpansionTrees.
   * @return A BoxPanel containing the elements of list stacked on top of each other and surrounded by angle brackets.
   */
  def drawMatrix( list: List[ExpansionTree] ) = new BoxPanel( Orientation.Vertical ) {
    background = new Color( 255, 255, 255 )
    yLayoutAlignment = 0.5
    border = Swing.EmptyBorder( 0, ft.getSize, 0, ft.getSize )

    list.foreach( et => {
      val bp = new DrawExpansionTree( main, et, ft )
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

  def drawFormula( formula: HOLFormula ): BoxPanel = new BoxPanel( Orientation.Horizontal ) {
    background = new Color( 255, 255, 255 )
    yLayoutAlignment = 0.5
    opaque = false

    formula match {
      case Neg( f ) =>
        val conn = label( "¬", ft )
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
        val parenthesis = connectParenthesis( label( "(", ft ), label( ")", ft ) )
        val conn = label( "∧", ft )
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
        val parenthesis = connectParenthesis( label( "(", ft ), label( ")", ft ) )
        val conn = label( "∨", ft )
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
        val parenthesis = connectParenthesis( label( "(", ft ), label( ")", ft ) )
        val conn = label( "⊃", ft )
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
        contents += label( "\\exists " + LatexExporter.escapeName( v.name ) + " ", ft )
        contents += drawFormula( f )
      case All( v, f ) =>
        contents += label( "\\forall " + LatexExporter.escapeName( v.name ) + " ", ft )
        contents += drawFormula( f )
      case _ =>
        val lbl = LatexLabel( main, ft, LatexExporter( formula ) )
        lbl.deafTo( lbl.mouse.moves, lbl.mouse.clicks )
        contents += lbl
    }
  }

  def label( s: String, fnt: Font ) = new MyLabel {
    background = Color.white
    yLayoutAlignment = 0.5
    font = fnt
    icon = new TeXFormula( s ).createTeXIcon( TeXConstants.STYLE_DISPLAY, fnt.getSize, TeXFormula.SANSSERIF )

    if ( s == "(" || s == ")" ) {
      opaque = true
      tooltip = "Click to mark/unmark."
      listenTo( mouse.clicks )
      reactions += {
        case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
          val color = RGBColorChooser( this, e.point.x, e.point.y )
          if ( color != None ) {
            backgroundColor = color.get
            peer.dispatchEvent( new MouseEvent( peer, e.peer.getID, e.peer.getWhen, e.modifiers, e.point.x, e.point.y, e.clicks, e.triggersPopup, MouseEvent.BUTTON1 ) )
          }
      }
    }
  }

  def connectParenthesis( left: MyLabel, right: MyLabel ) = {
    left.reactions += {
      case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
        if ( left.background == Color.white || left.background != left.backgroundColor ) {
          left.background = left.backgroundColor
          right.background = left.backgroundColor
        } else {
          left.background = Color.white
          right.background = Color.white
        }
    }
    right.reactions += {
      case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
        if ( right.background == Color.white || right.background != right.backgroundColor ) {
          left.background = right.backgroundColor
          right.background = right.backgroundColor
        } else {
          left.background = Color.white
          right.background = Color.white
        }
    }
    ( left, right )
  }
}
