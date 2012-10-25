package at.logic.gui.prooftool.gui

/**
* Created with IntelliJ IDEA.
* User: mrukhaia
* Date: 9/13/12
* Time: 12:51 PM
*/

import swing._
import event.{UIElementResized, MouseClicked}
import java.awt.{Font, Dimension, Color}
import java.awt.Font._
import java.awt.event.MouseEvent
import at.logic.calculi.expansionTrees.{ExpansionTree, WeakQuantifier, StrongQuantifier, And => AndET, Or => OrET, Imp => ImpET, Not => NotET, Atom => AtomET}
import at.logic.utils.ds.trees.{NonTerminalNodeA}
import org.scilab.forge.jlatexmath.{TeXConstants, TeXFormula}
import java.awt.image.BufferedImage
import at.logic.language.hol._

object ExpansionTreeState extends Enumeration {
  val Closed, Opened, Expanded = Value
}

class DrawExpansionTree(val expansionTree: ExpansionTree, private var state: ExpansionTreeState.Value, private val ft: Font) extends BoxPanel(Orientation.Horizontal) {
  import ExpansionTreeState._
  background = new Color(255,255,255)
  yLayoutAlignment = 0.5
  initialize

  def initialize = expansionTree match {
    case WeakQuantifier(f, seq_et_t) =>
      contents += formulaToComponent(f, state, seq_et_t.map(pair => pair._2))
    case StrongQuantifier(f, v, et1) =>
      contents += formulaToComponent(f, state, Seq(v))
    case AndET(left, right) =>
      val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
      contents += parenthesis._1
      contents += new DrawExpansionTree(left,state,ft)
      contents += label("∧",ft)
      contents += new DrawExpansionTree(right,state,ft)
      contents += parenthesis._2
    case OrET(left, right) =>
      val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
      contents += parenthesis._1
      contents += new DrawExpansionTree(left,state,ft)
      contents += label("∨",ft)
      contents += new DrawExpansionTree(right,state,ft)
      contents += parenthesis._2
    case ImpET(left, right) =>
      val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
      contents += parenthesis._1
      contents += new DrawExpansionTree(left,state,ft)
      contents += label("⊃",ft)
      contents += new DrawExpansionTree(right,state,ft)
      contents += parenthesis._2
    case NotET(tree) =>
      contents += label("¬",ft)
      contents += new DrawExpansionTree(tree,state,ft)
    case AtomET(f) =>
      contents += formulaToComponent(f, state, Seq())
  }

  def closed {
    contents.clear
    state = Closed
    initialize
    revalidate
  }

  def opened {
    contents.clear
    state = Opened
    initialize
    revalidate
  }

  def expanded {

  }

//  def quantifierToComponent(t: HOLFormula, st: ExpansionTreeState.Value, seq: Seq[HOLExpression]) = new BoxPanel(Orientation.Horizontal) {
//    background = new Color(255,255,255)
//    yLayoutAlignment = 0.5
//
//    t match {
//      case ExVar(v, f) =>
//        val lbl = DrawSequent.latexToLabel("(" + """\exists """ + DrawSequent.formulaToLatexString(v) + ")",ft)
//        lbl.reactions += {
//          case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 => PopupMenu(DrawExpansionTree.this,lbl, e.point.x, e.point.y)
//        }
//        contents += lbl
//        if (st == Opened) contents += drawTerms(seq)
//        contents += formulaToComponent(f,Closed,Seq())
//      case AllVar(v, f) =>
//        val lbl = DrawSequent.latexToLabel("(" + """\forall """ + DrawSequent.formulaToLatexString(v) + ")",ft)
//        lbl.reactions += {
//          case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 => PopupMenu(DrawExpansionTree.this,lbl, e.point.x, e.point.y)
//        }
//        contents += lbl
//        if (st == Opened) contents += drawTerms(seq)
//        contents += formulaToComponent(f,Closed,Seq())
//      case _ => throw new Exception("Something went wrong in DrawExpansionTree")
//    }
//  }

  def formulaToComponent(t: HOLFormula, st: ExpansionTreeState.Value, seq: Seq[HOLExpression]): BoxPanel = new BoxPanel(Orientation.Horizontal) {
    background = new Color(255,255,255)
    yLayoutAlignment = 0.5

    t match {
      case Neg(f) =>
        contents += label("¬",ft)
        contents += formulaToComponent(f,st,seq)
      case And(f1,f2) =>
        val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
        contents += parenthesis._1
        contents += formulaToComponent(f1,st,seq)
        contents += label("∧",ft)
        contents += formulaToComponent(f2,st,seq)
        contents += parenthesis._2
      case Or(f1,f2) =>
        val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
        contents += parenthesis._1
        contents += formulaToComponent(f1,st,seq)
        contents += label("∨",ft)
        contents += formulaToComponent(f2,st,seq)
        contents += parenthesis._2
      case Imp(f1,f2) =>
        val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
        contents += parenthesis._1
        contents += formulaToComponent(f1,st,seq)
        contents += label("⊃",ft)
        contents += formulaToComponent(f2,st,seq)
        contents += parenthesis._2
      case ExVar(v, f) =>
        val lbl = DrawSequent.latexToLabel("(" + """\exists """ + DrawSequent.formulaToLatexString(v) + ")",ft)
        lbl.reactions += {
          case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 => PopupMenu(DrawExpansionTree.this,lbl, e.point.x, e.point.y)
        }
        contents += lbl
        if (st == Opened) contents += drawTerms(seq)
        contents += formulaToComponent(f,Closed,Seq())
      case AllVar(v, f) =>
        val lbl = DrawSequent.latexToLabel("(" + """\forall """ + DrawSequent.formulaToLatexString(v) + ")",ft)
        lbl.reactions += {
          case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 => PopupMenu(DrawExpansionTree.this,lbl, e.point.x, e.point.y)
        }
        contents += lbl
        if (st == Opened) contents += drawTerms(seq)
        contents += formulaToComponent(f,Closed,Seq())
      case _ =>
        val lbl = DrawSequent.formulaToLabel(t,ft)
        lbl.deafTo(lbl.mouse.moves, lbl.mouse.clicks)
        contents += lbl
    }
  }

  def drawTerms(seq: Seq[HOLExpression]) = new BoxPanel(Orientation.Horizontal) {
    background = new Color(255,255,255)
    yLayoutAlignment = 0.5

    contents += label("\\langle",ft)
    var first = true
    for (t <- seq) {
      if (! first) {
        val lbl = label(",",ft)
        lbl.yLayoutAlignment = 0
        contents += lbl
      }
      else first = false
      contents += label(DrawSequent.formulaToLatexString(t),ft)
    }
    contents += label("\\rangle",ft)
  }

  def label(s: String, fnt: Font) = new MyLabel {
    background = Color.white
    yLayoutAlignment = 0.5
    opaque = true
    font = fnt

    val formula = new TeXFormula(s)
    val myicon = formula.createTeXIcon(TeXConstants.STYLE_DISPLAY, fnt.getSize)
    val myimage = new BufferedImage(myicon.getIconWidth(), myicon.getIconHeight(), BufferedImage.TYPE_INT_ARGB)
    val g2 = myimage.createGraphics()
    g2.setColor(Color.white)
    g2.fillRect(0,0,myicon.getIconWidth(),myicon.getIconHeight())
    myicon.paintIcon(peer, g2, 0, 0)

    icon = myicon
    if (s == "(" || s == ")")
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