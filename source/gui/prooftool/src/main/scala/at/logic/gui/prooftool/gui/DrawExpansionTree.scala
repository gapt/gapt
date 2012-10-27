package at.logic.gui.prooftool.gui

/**
* Created with IntelliJ IDEA.
* User: mrukhaia
* Date: 9/13/12
* Time: 12:51 PM
*/

import swing._
import event.MouseClicked
import java.awt.{Font, Color}
import java.awt.event.MouseEvent
import at.logic.calculi.expansionTrees.{ExpansionTree, WeakQuantifier, StrongQuantifier, And => AndET, Or => OrET, Imp => ImpET, Not => NotET, Atom => AtomET}
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
  xLayoutAlignment = 0
  initialize

  def initialize = expansionTree match {
    case WeakQuantifier(f, seq) =>
      contents += formulaToComponent(f, state, extractTerms(expansionTree))
    case StrongQuantifier(f, v, et1) =>
      contents += formulaToComponent(f, state, extractTerms(expansionTree))
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
      contents += formulaToComponent(f, state, Nil)
  }

  def closed() {
    contents.clear()
    state = Closed
    initialize
    revalidate()
  }

  def opened() {
    contents.clear()
    state = Opened
    initialize
    revalidate()
  }

  def expanded() {

  }

  // Extracts lists of terms from the expansion tree.
  def extractTerms(et: ExpansionTree): List[List[HOLExpression]] = et match {
    case WeakQuantifier(f, seq) =>
      val r: List[List[HOLExpression]] = Nil
      seq.foldLeft(r)((r, pair) => r ::: {
        val tmp = extractTerms(pair._1)
        if (tmp == Nil) List(List(pair._2))
        else tmp.map(l => pair._2 :: l)
      })
    case StrongQuantifier(f, v, et1) =>
      val tmp = extractTerms(et1)
      if (tmp == Nil) List(List(v))
      else tmp.map(l => List(v) ::: l)
    case AndET(left, right) =>
      extractTerms(left) ::: extractTerms(right)
    case OrET(left, right) =>
      extractTerms(left) ::: extractTerms(right)
    case ImpET(left, right) =>
      extractTerms(right) ::: extractTerms(left)
    case NotET(tree) => extractTerms(tree)
    case AtomET(f) => Nil
  }

  def formulaToComponent(holF: HOLFormula, st: ExpansionTreeState.Value, list: List[List[HOLExpression]]): BoxPanel = new BoxPanel(Orientation.Horizontal) {
    background = new Color(255,255,255)
    yLayoutAlignment = 0.5

    holF match {
      case Neg(f) =>
        contents += label("¬",ft)
        contents += formulaToComponent(f,st,list)
      case And(f1,f2) =>
        val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
        contents += parenthesis._1
        contents += formulaToComponent(f1,st,list)
        contents += label("∧",ft)
        contents += formulaToComponent(f2,st,list)
        contents += parenthesis._2
      case Or(f1,f2) =>
        val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
        contents += parenthesis._1
        contents += formulaToComponent(f1,st,list)
        contents += label("∨",ft)
        contents += formulaToComponent(f2,st,list)
        contents += parenthesis._2
      case Imp(f1,f2) =>
        val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
        contents += parenthesis._1
        contents += formulaToComponent(f1,st,list)
        contents += label("⊃",ft)
        contents += formulaToComponent(f2,st,list)
        contents += parenthesis._2
      case ExVar(_,_) | AllVar(_,_) =>
        val (quantifiers, number, formula) = analyzeFormula(holF)
        val (list1, list2) = splitList(number,list)
        val lbl = DrawSequent.latexToLabel(quantifiers, ft)
        lbl.reactions += {
          case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
            PopupMenu(DrawExpansionTree.this, lbl, e.point.x, e.point.y)
        }
        contents += lbl
        if (st == Opened) contents += drawTerms(list1)
        contents += formulaToComponent(formula, Closed, list2)
      case _ =>
        val lbl = DrawSequent.formulaToLabel(holF,ft)
        lbl.deafTo(lbl.mouse.moves, lbl.mouse.clicks)
        contents += lbl
    }
  }

  // String represents the first n quantifiers in a raw,
  // Int is the number n,
  // HOLFormula is the rest of formula
  def analyzeFormula(formula: HOLFormula): (String,Int,HOLFormula) = formula match {
    case ExVar(v,f) =>
      val tuple = analyzeFormula(f)
      ("(" + "\\exists " + DrawSequent.formulaToLatexString(v) + ")" + tuple._1, tuple._2 + 1, tuple._3)
    case AllVar(v,f) =>
      val tuple = analyzeFormula(f)
      ("(" + "\\forall " + DrawSequent.formulaToLatexString(v) + ")" + tuple._1, tuple._2 + 1, tuple._3)
    case _ => ("",0,formula)
  }

  // Splits each list of terms at the position n in the list of lists of terms.
  // This is necessary for nested quantifiers in formulas.
  def splitList(n: Int, list: List[List[HOLExpression]]) = {
    val tmp = list.map(l =>
      if (l.size >= n) l.splitAt(n)
      else throw new Exception("Something went wrong in DrawExpansionTree!")
    )
    val list1 = tmp.map(pair => pair._1)
    val list2 = tmp.filter(pair => pair._2 != Nil).map(pair => pair._2)
    (list1, list2)
  }

  // Draws <t_1,...,t_n ; ... ; s_1,...,s_n>
  // List of terms are separated by ; and terms in a list by ,
  def drawTerms(list: List[List[HOLExpression]]) = new BoxPanel(Orientation.Horizontal) {
    background = new Color(255,255,255)
    yLayoutAlignment = 0.5

    contents += label("\\langle",ft)
    var firstList = true
    list.foreach(l => {
      if (! firstList) {
        val lbl = label("\\; ; \\;",ft)
        lbl.yLayoutAlignment = 0.35
        contents += lbl
      } else firstList = false
      var firstTerm = true
      l.foreach(t => {
        if (! firstTerm) {
          val lbl = label(",",ft)
          lbl.yLayoutAlignment = 0
          contents += lbl
        } else firstTerm = false
        contents += label(DrawSequent.formulaToLatexString(t),ft)
      })
    })
    contents += label("\\rangle",ft)
  }

  def label(s: String, fnt: Font) = new MyLabel {
    background = Color.white
    yLayoutAlignment = 0.5
    opaque = true
    font = fnt

    val formula = new TeXFormula(s)
    val myicon = formula.createTeXIcon(TeXConstants.STYLE_DISPLAY, fnt.getSize)
    val myimage = new BufferedImage(myicon.getIconWidth, myicon.getIconHeight, BufferedImage.TYPE_INT_ARGB)
    val g2 = myimage.createGraphics()
    g2.setColor(Color.white)
    g2.fillRect(0,0,myicon.getIconWidth,myicon.getIconHeight)
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