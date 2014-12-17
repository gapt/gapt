package at.logic.gui.prooftool.gui

/**
* Created with IntelliJ IDEA.
* User: mrukhaia
* Date: 9/13/12
* Time: 12:51 PM
*/

import at.logic.language.hol.And
import at.logic.language.hol.Imp
import at.logic.language.hol.Neg
import at.logic.language.hol.Or
import at.logic.utils.logging.Logger

import swing._
import scala.swing.event.{MouseExited, MouseEntered, MouseClicked}
import java.awt.{Font, Color}
import java.awt.event.MouseEvent
import at.logic.calculi.expansionTrees.{MAnd, MAtom, MOr, MImp, MNeg, MWeakQuantifier, MSkolemQuantifier, MStrongQuantifier, MultiExpansionTree}
import org.scilab.forge.jlatexmath.{TeXConstants, TeXFormula}
import java.awt.image.BufferedImage
import at.logic.language.hol._
import org.slf4j.LoggerFactory

object ExpansionTreeState extends Enumeration {
  val Close, Open, Expand = Value
}

class DrawExpansionTree(val expansionTree: MultiExpansionTree, private val ft: Font) extends BoxPanel(Orientation.Horizontal) with Logger {

  import ExpansionTreeState._
  override def loggerName = "DrawExpTreeLogger"

  background = new Color(255, 255, 255)
  yLayoutAlignment = 0.5
  xLayoutAlignment = 0
  private val state = scala.collection.mutable.Map.empty[HOLFormula, ExpansionTreeState.Value]
  val highlightColor = Color.red
  initialize

  def initialize = {
    contents += treeToComponent(expansionTree, allow = true)
  }

  def close(f: HOLFormula) {
    contents.clear()
    state += ((f, Close))
    initialize
    revalidate()
  }

  def open(f: HOLFormula) {
    contents.clear()
    state += ((f, Open))
    initialize
    revalidate()
  }

  def expand(f: HOLFormula) {
    contents.clear()
    state += ((f, Expand))
    initialize
    revalidate()
  }

  /** This function is responsible for converting an expansion tree to a component.
    * @param expTree The tree to be converted.
    * @param allow Whether the root node of expTree should be clickable. Might be obsolete.
    * @return A BoxPanel representing expTree.
    */
  def treeToComponent(expTree: MultiExpansionTree, allow: Boolean): BoxPanel = new BoxPanel(Orientation.Horizontal) {
    background = new Color(255, 255, 255)
    yLayoutAlignment = 0.5
    opaque = false

    expTree match {
      case MAtom(f) =>
        val lbl = DrawSequent.formulaToLabel(f, ft)
        lbl.deafTo(lbl.mouse.moves, lbl.mouse.clicks) // We don't want atoms to react to mouse behavior.
        contents += lbl
      case MNeg(t) =>
        val conn = label("¬", ft)
        val subF = treeToComponent(t, allow)
        this.listenTo(conn.mouse.moves)
        this.reactions += {
          case _: MouseEntered =>
            conn.foreground = highlightColor
          case _: MouseExited =>
            conn.foreground = Color.black
        }
        contents += conn
        contents += subF
      case MAnd(t1, t2) =>
        val parenthesis = connectParenthesis(label("(", ft), label(")", ft))
        val conn = label("∧", ft)
        val subF1 = treeToComponent(t1, allow)
        val subF2 = treeToComponent(t2, allow)
        this.listenTo(conn.mouse.moves, parenthesis._1.mouse.moves, parenthesis._2.mouse.moves)
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
      case MOr(t1, t2) =>
        val parenthesis = connectParenthesis(label("(", ft), label(")", ft))
        val conn = label("∨", ft)
        val subF1 = treeToComponent(t1, allow)
        val subF2 = treeToComponent(t2, allow)
        this.listenTo(conn.mouse.moves, parenthesis._1.mouse.moves, parenthesis._2.mouse.moves)
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
      case MImp(t1, t2) =>
        val parenthesis = connectParenthesis(label("(", ft), label(")", ft))
        val conn = label("⊃", ft)
        val subF1 = treeToComponent(t1, allow)
        val subF2 = treeToComponent(t2, allow)
        this.listenTo(conn.mouse.moves, parenthesis._1.mouse.moves, parenthesis._2.mouse.moves)
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
      case MWeakQuantifier(formula, instances) =>
        val terms = instances.map(i => i._2.toList).toList
        val subtrees = instances.map(i => i._1).toList
        val quantifiers = quantifierBlock(expTree) // quantifiers is a string containing the quantifier block represented by this weak node.

        if (state.get(formula) == Some(Expand)) {
          // We first consider the case that the top-level quantifier is expanded.
          if (subtrees != Nil) {
            val lbl = LatexLabel(ft, getMatrixSymbol(formula))
            lbl.reactions += {
              case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 => close(formula)
              case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
                PopupMenu(DrawExpansionTree.this, formula, lbl, e.point.x, e.point.y)
            }
            contents += lbl
            contents += drawMatrix(subtrees)
          }
          else {
            state -= formula
            contents += drawFormula(instances.head._1.toShallow) // If there are no terms to expand the quantifier with, we can safely call drawFormula.
          }
        }
        else {
          // The current tree is either open or closed.
          val lbl = LatexLabel(ft, quantifiers)
          val subF = expTree.getSubformula

          if (allow) lbl.reactions += {
            case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
              PopupMenu(DrawExpansionTree.this, formula, lbl, e.point.x, e.point.y)
            case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
              if (state.get(formula) == Some(Open)) expand(formula)
              else open(formula)
          }
          else {
            lbl.deafTo(lbl.mouse.clicks)
            lbl.tooltip = "First expand all the quantifiers till the root!" // alternative message "The block of quantifiers is locked!"
          }

          contents += lbl
          if (state.get(formula) == Some(Open)) contents += drawTerms(terms) // If the quantifier block is open, we draw its terms.
          contents += drawFormula(subF) // Since the current quantifier block is not expanded, we needn't worry about the state of child trees and can call drawFormula.
        }

      case MStrongQuantifier(formula, vars, sel) => // This case is mostly analogous to the WeakQuantifier one.
        val terms = List(vars.toList)
        val subtrees = List(sel)
        val quantifiers = quantifierBlock(expTree)

        if (state.get(formula) == Some(Expand)) {
          if (subtrees != Nil) {
            val lbl = LatexLabel(ft, getMatrixSymbol(formula))
            lbl.reactions += {
              case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 => close(formula)
              case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
                PopupMenu(DrawExpansionTree.this, formula, lbl, e.point.x, e.point.y)
            }
            contents += lbl
            contents += drawMatrix(subtrees)
          }
          else {
            state -= formula
            contents += drawFormula(sel.toShallow)
          }
        }
        else {
          val lbl = LatexLabel(ft, quantifiers)
          val subF = expTree.getSubformula

          if (allow) lbl.reactions += {
            case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
              PopupMenu(DrawExpansionTree.this, formula, lbl, e.point.x, e.point.y)
            case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
              if (state.get(formula) == Some(Open)) expand(formula)
              else open(formula)
          }
          else {
            lbl.deafTo(lbl.mouse.clicks)
            lbl.tooltip = "First expand all the quantifiers till the root!" // alternative message "The block of quantifiers is locked!"
          }

          contents += lbl
          if (state.get(formula) == Some(Open)) contents += drawTerms(terms)
          contents += drawFormula(subF)
        }


      case MSkolemQuantifier(formula, vars, sel) => // This case is identical to strong quantifier handling
        val terms = List(vars.toList)
        val subtrees = List(sel)
        val quantifiers = quantifierBlock(expTree)

        if (state.get(formula) == Some(Expand)) {
          if (subtrees != Nil) {
            val lbl = LatexLabel(ft, getMatrixSymbol(formula))
            lbl.reactions += {
              case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 => close(formula)
              case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
                PopupMenu(DrawExpansionTree.this, formula, lbl, e.point.x, e.point.y)
            }
            contents += lbl
            contents += drawMatrix(subtrees)
          }
          else {
            state -= formula
            contents += drawFormula(sel.toShallow)
          }
        }
        else {
          val lbl = LatexLabel(ft, quantifiers)
          val subF = expTree.getSubformula

          if (allow) lbl.reactions += {
            case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
              PopupMenu(DrawExpansionTree.this, formula, lbl, e.point.x, e.point.y)
            case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
              if (state.get(formula) == Some(Open)) expand(formula)
              else open(formula)
          }
          else {
            lbl.deafTo(lbl.mouse.clicks)
            lbl.tooltip = "First expand all the quantifiers till the root!" // alternative message "The block of quantifiers is locked!"
          }

          contents += lbl
          if (state.get(formula) == Some(Open)) contents += drawTerms(terms)
          contents += drawFormula(subF)
        }

    }
  }

  def getMatrixSymbol(formula: HOLFormula) = formula match {
    case ExVar(_, _) => "\\bigvee"
    case AllVar(_, _) => "\\bigwedge"
    case _ => throw new Exception("Something went wrong in DrawExpansionTree!")
  }

  /**
   * @param et A MultiExpansionTree (either StrongQuantifier or WeakQuantifier)
   * @return A string containing the quantifier block represented by this quantifier node.
   */
  def quantifierBlock(et: MultiExpansionTree): String = et match {
    case MStrongQuantifier(_, _, _) | MWeakQuantifier(_, _) | MSkolemQuantifier(_,_,_) =>
      val vars = et.getVars
      val f = et.toShallow
      f match {
        case AllVar(_, _) => vars.foldLeft("")((str: String, v: HOLVar) => str + "(\\forall " + DrawSequent.formulaToLatexString(v) + ")")
        case ExVar(_, _) => vars.foldLeft("")((str: String, v: HOLVar) => str + "(\\exists " + DrawSequent.formulaToLatexString(v) + ")")
      }
  }

  // Draws <t_1,...,t_n ; ... ; s_1,...,s_n>
  // List of terms are separated by ; and terms in a list by ,
  def drawTerms(list: List[List[HOLExpression]]) = new BoxPanel(Orientation.Horizontal) {
    background = new Color(255, 255, 255)
    yLayoutAlignment = 0.5

    contents += label("\\langle", ft)
    var firstList = true
    list.foreach(l => {
      if (!firstList) {
        val lbl = label("\\; ; \\;", ft)
        lbl.yLayoutAlignment = 0.35
        contents += lbl
      } else firstList = false
      var firstTerm = true
      l.foreach(t => {
        if (!firstTerm) {
          val lbl = label(",", ft)
          lbl.yLayoutAlignment = 0
          contents += lbl
        } else firstTerm = false
        contents += label(DrawSequent.formulaToLatexString(t), ft)
      })
    })
    contents += label("\\rangle", ft)
  }

  /**
   *
   * @param list A list of MultiExpansionTrees.
   * @return A BoxPanel containing the elements of list stacked on top of each other and surrounded by angle brackets.
   */
  def drawMatrix(list: List[MultiExpansionTree]) = new BoxPanel(Orientation.Vertical) {
    background = new Color(255,255,255)
    yLayoutAlignment = 0.5
    border = Swing.EmptyBorder(0,ft.getSize,0,ft.getSize)

    list.foreach(et => {
      val bp = new DrawExpansionTree(et,ft)
      bp.border = Swing.EmptyBorder(3)
      contents += bp
    })

    override def paintComponent(g: Graphics2D) {
      import java.awt.{BasicStroke,RenderingHints}
      super.paintComponent(g)

      val fSize = ft.getSize
      val strokeSize = if (fSize / 25 < 1) 1 else ft.getSize / 25

      g.setStroke(new BasicStroke(strokeSize, BasicStroke.CAP_ROUND, BasicStroke.JOIN_ROUND))
      g.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING,RenderingHints.VALUE_TEXT_ANTIALIAS_LCD_HRGB)

      val leftAngleNodeX = location.x - fSize
      val rightAngleNodeX = location.x + size.width - 2 * fSize
      val anglesNodeY = location.y + size.height / 2

      val leftAngleEdgesX = location.x - fSize / 2
      val rightAngleEdgesX = location.x + size.width - 5 * (fSize / 2)
      val anglesEdge1Y = location.y
      val anglesEdge2Y = location.y + size.height

      g.drawLine(leftAngleNodeX, anglesNodeY, leftAngleEdgesX, anglesEdge1Y)
      g.drawLine(leftAngleNodeX, anglesNodeY, leftAngleEdgesX, anglesEdge2Y)

      g.drawLine(rightAngleNodeX, anglesNodeY, rightAngleEdgesX, anglesEdge1Y)
      g.drawLine(rightAngleNodeX, anglesNodeY, rightAngleEdgesX, anglesEdge2Y)
    }
  }


  def drawFormula(formula: HOLFormula): BoxPanel = new BoxPanel(Orientation.Horizontal) {
    trace("drawFormula called on formula " + formula)
    background = new Color(255, 255, 255)
    yLayoutAlignment = 0.5
    opaque = false

    formula match {
      case Neg(f) =>
        val conn = label("¬", ft)
        val subF = drawFormula(f)
        this.listenTo(conn.mouse.moves)
        this.reactions += {
          case _: MouseEntered =>
            conn.foreground = highlightColor
          case _: MouseExited =>
            conn.foreground = Color.black
        }
        contents += conn
        contents += subF
      case And(f1, f2) =>
        val parenthesis = connectParenthesis(label("(", ft), label(")", ft))
        val conn = label("∧", ft)
        val subF1 = drawFormula(f1)
        val subF2 = drawFormula(f2)
        this.listenTo(conn.mouse.moves, parenthesis._1.mouse.moves, parenthesis._2.mouse.moves)
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
      case Or(f1, f2) =>
        val parenthesis = connectParenthesis(label("(", ft), label(")", ft))
        val conn = label("∨", ft)
        val subF1 = drawFormula(f1)
        val subF2 = drawFormula(f2)
        this.listenTo(conn.mouse.moves, parenthesis._1.mouse.moves, parenthesis._2.mouse.moves)
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
      case Imp(f1, f2) =>
        val parenthesis = connectParenthesis(label("(", ft), label(")", ft))
        val conn = label("⊃", ft)
        val subF1 = drawFormula(f1)
        val subF2 = drawFormula(f2)
        this.listenTo(conn.mouse.moves, parenthesis._1.mouse.moves, parenthesis._2.mouse.moves)
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
      case ExVar(v, f) =>
        contents += label("(\\exists " + DrawSequent.formulaToLatexString(v) + ")", ft)
        contents += drawFormula(f)
      case AllVar(v, f) =>
        contents += label("(\\forall " + DrawSequent.formulaToLatexString(v) + ")", ft)
        contents += drawFormula(f)
      case _ =>
        val lbl = DrawSequent.formulaToLabel(formula,ft)
        lbl.deafTo(lbl.mouse.moves, lbl.mouse.clicks)
        contents += lbl
    }
  }

  def label(s: String, fnt: Font) = new MyLabel {
    background = Color.white
    yLayoutAlignment = 0.5
    font = fnt

    val formula = new TeXFormula(s)
    val myicon = formula.createTeXIcon(TeXConstants.STYLE_DISPLAY, fnt.getSize)
    val myimage = new BufferedImage(myicon.getIconWidth, myicon.getIconHeight, BufferedImage.TYPE_INT_ARGB)
    val g2 = myimage.createGraphics()
    g2.setColor(Color.white)
    g2.fillRect(0,0,myicon.getIconWidth,myicon.getIconHeight)
    myicon.paintIcon(peer, g2, 0, 0)

    icon = myicon
    if (s == "(" || s == ")") {
      opaque = true
      tooltip = "Click to mark/unmark."
      listenTo(mouse.clicks)
      reactions += {
        case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
          val color = RGBColorChooser(this,e.point.x,e.point.y)
          if (color != None) {
            backgroundColor = color.get
            peer.dispatchEvent(new MouseEvent(peer,e.peer.getID,e.peer.getWhen,e.modifiers,e.point.x,e.point.y,e.clicks,e.triggersPopup,MouseEvent.BUTTON1))
          }
      }
    }
  }

  def connectParenthesis(left: MyLabel, right: MyLabel) = {
    left.reactions += {
      case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
        if (left.background == Color.white || left.background != left.backgroundColor) {
          left.background = left.backgroundColor
          right.background = left.backgroundColor
        } else {
          left.background = Color.white
          right.background = Color.white
        }
    }
    right.reactions += {
      case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
        if (right.background == Color.white || right.background != right.backgroundColor) {
          left.background = right.backgroundColor
          right.background = right.backgroundColor
        } else {
          left.background = Color.white
          right.background = Color.white
        }
    }
    (left,right)
  }
}