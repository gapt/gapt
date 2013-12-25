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
import at.logic.calculi.expansionTrees.{ExpansionTree, WeakQuantifier, StrongQuantifier, And => AndET, Or => OrET, Imp => ImpET, Neg => NegET, Atom => AtomET}
import org.scilab.forge.jlatexmath.{TeXConstants, TeXFormula}
import java.awt.image.BufferedImage
import at.logic.language.hol._

object ExpansionTreeState extends Enumeration {
  val Close, Open, Expand = Value
}

class DrawExpansionTree(val expansionTree: ExpansionTree, private val ft: Font) extends BoxPanel(Orientation.Horizontal) {
  import ExpansionTreeState._
  background = new Color(255,255,255)
  yLayoutAlignment = 0.5
  xLayoutAlignment = 0
  private val state = scala.collection.mutable.Map.empty[HOLFormula,ExpansionTreeState.Value]
  initialize

  def initialize = expansionTree match {
    case WeakQuantifier(f, seq) =>
      contents += formulaToComponent(f,extractTerms(expansionTree),seq.map(pair => pair._1).toList,allow = true)
    case StrongQuantifier(f, v, et1) =>
      contents += formulaToComponent(f,extractTerms(expansionTree),List(et1),allow = true)
    case AndET(left, right) =>
      val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
      contents += parenthesis._1
      contents += new DrawExpansionTree(left,ft)
      contents += label("∧",ft)
      contents += new DrawExpansionTree(right,ft)
      contents += parenthesis._2
    case OrET(left, right) =>
      val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
      contents += parenthesis._1
      contents += new DrawExpansionTree(left,ft)
      contents += label("∨",ft)
      contents += new DrawExpansionTree(right,ft)
      contents += parenthesis._2
    case ImpET(left, right) =>
      val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
      contents += parenthesis._1
      contents += new DrawExpansionTree(left,ft)
      contents += label("⊃",ft)
      contents += new DrawExpansionTree(right,ft)
      contents += parenthesis._2
    case NegET(tree) =>
      contents += label("¬",ft)
      contents += new DrawExpansionTree(tree,ft)
    case AtomET(f) =>
      contents += formulaToComponent(f,Nil,Nil,allow = true) // use false to lock the dummy quantifiers.
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

  // Extracts list of lists of terms from the expansion tree.
  // Each list of terms corresponds to an instantiation of all quantifiers.
  def extractTerms(et: ExpansionTree): List[List[HOLExpression]] = et match {
    case WeakQuantifier(f, seq) =>
      seq.foldLeft(List.empty[List[HOLExpression]])((r, pair) => r ::: {
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
      extractTerms(left) ::: extractTerms(right)
    case NegET(tree) => extractTerms(tree)
    case AtomET(f) => Nil
  }

//  // Extracts list of formulas from the expansion tree at depth n.
//  def extractFormulas(et: ExpansionTree, formula: HOLFormula, n: Int, start: Boolean): List[HOLFormula] = et match {
//    case WeakQuantifier(f, seq) =>
//      if (f == formula) seq.foldLeft(List.empty[HOLFormula])((r, pair) => r ::: extractFormulas(pair._1,formula,n,start = true))
//      else if (f.subTerms.contains(formula)) seq.foldLeft(List.empty[HOLFormula])((r, pair) => r ::: extractFormulas(pair._1,formula,n,start))
//      else if (n > 1) seq.foldLeft(List.empty[HOLFormula])((r, pair) => r ::: extractFormulas(pair._1,formula,n-1,start))
//      else if (start) List(f)
//      else Nil
//    case StrongQuantifier(f, v, et1) =>
//      if (f == formula) extractFormulas(et1,formula,n,start = true)
//      else if (f.subTerms.contains(formula)) extractFormulas(et1,formula,n,start)
//      else if (n > 1) extractFormulas(et1,formula,n-1,start)
//      else if (start) List(f)
//      else Nil
//    case AndET(left, right) =>
//      val ll = extractFormulas(left,formula,n,start)
//      val rl = extractFormulas(right,formula,n,start)
//      if (ll == Nil) rl
//      else if (rl == Nil) ll
//      else ll.foldLeft(List.empty[HOLFormula])((r, f1) => r ::: rl.map(f2 => And(f1,f2)))
//    case OrET(left, right) =>
//      val ll = extractFormulas(left,formula,n,start)
//      val rl = extractFormulas(right,formula,n,start)
//      if (ll == Nil) rl
//      else if (rl == Nil) ll
//      else ll.foldLeft(List.empty[HOLFormula])((r, f1) => r ::: rl.map(f2 => Or(f1,f2)))
//    case ImpET(left, right) =>
//      val ll = extractFormulas(left,formula,n,start)
//      val rl = extractFormulas(right,formula,n,start)
//      if (ll == Nil) rl
//      else if (rl == Nil) ll
//      else ll.foldLeft(List.empty[HOLFormula])((r, f1) => r ::: rl.map(f2 => Imp(f1,f2)))
//    case NegET(tree) =>
//      extractFormulas(tree,formula,n,start).map(f => Neg(f))
//    case AtomET(f) => if (start) List(f) else Nil
//  }

  // Extracts list of ExpansionTrees from the expansion tree at depth n.
  def extractET(et: ExpansionTree,n: Int): List[ExpansionTree] = {
    if (n == 1) List(et)
    else et match {
      case WeakQuantifier(f, seq) =>
        seq.map(pair => extractET(pair._1,n-1)).flatten.toList
      case StrongQuantifier(f, v, et1) =>
        extractET(et1,n-1)
      case _ => throw new Exception("Something went wrong in DrawExpansionTree!")
    }
  }

  def formulaToComponent(holF: HOLFormula, list: List[List[HOLExpression]], expTrees: List[ExpansionTree], allow: Boolean): BoxPanel = new BoxPanel(Orientation.Horizontal) {
    background = new Color(255,255,255)
    yLayoutAlignment = 0.5
    opaque = false

    holF match {
      case Neg(f) =>
        contents += label("¬",ft)
        contents += formulaToComponent(f,list,expTrees,allow)
      case And(f1,f2) =>
        val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
        contents += parenthesis._1
        contents += formulaToComponent(f1,list,expTrees,allow)
        contents += label("∧",ft)
        contents += formulaToComponent(f2,list,expTrees,allow)
        contents += parenthesis._2
      case Or(f1,f2) =>
        val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
        contents += parenthesis._1
        contents += formulaToComponent(f1,list,expTrees,allow)
        contents += label("∨",ft)
        contents += formulaToComponent(f2,list,expTrees,allow)
        contents += parenthesis._2
      case Imp(f1,f2) =>
        val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
        contents += parenthesis._1
        contents += formulaToComponent(f1,list,expTrees,allow)
        contents += label("⊃",ft)
        contents += formulaToComponent(f2,list,expTrees,allow)
        contents += parenthesis._2
      case ExVar(_,_) | AllVar(_,_) =>
        val (quantifiers, number, formula) = analyzeFormula(holF)
        val (list1, list2) = splitList(number,list)
        if ( state.get(holF) != Some(Expand) ) {
          val lbl = LatexLabel(ft,quantifiers)
          if (allow) lbl.reactions += {
            case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
              PopupMenu(DrawExpansionTree.this, holF, lbl, e.point.x, e.point.y)
            case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
              if (state.get(holF) == Some(Open)) expand(holF)
              else open(holF)
          } else {
            lbl.deafTo(lbl.mouse.clicks)
            lbl.tooltip = "First expand all the qauntifiers till the root!" // alternative message "The block of quantifiers is locked!"
          }
          contents += lbl
          if ( state.get(holF) == Some(Open) ) contents += drawTerms(list1)
          // according to the paper, nested quantifiers can be opened/expanded only if all the quantifiers till root is expanded.
          contents += formulaToComponent(formula,list2,expTrees,allow = false)
        } else {
          val formulas = expTrees.map(et => extractET(et,number)).flatten
          if (formulas != Nil) { // Assumed that proofs are skolemized, i.e. there is no quantifier alternation.
            val lbl = LatexLabel(ft, getMatrixSymbol(holF))
            lbl.reactions += {
              case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 => close(holF)
              case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
                PopupMenu(DrawExpansionTree.this, holF, lbl, e.point.x, e.point.y)
            }
            contents += lbl
            contents += drawMatrix(formulas)
          } else { // If formulas are empty, quantified formula comes from weakening so leave it unchanged.
            state -= holF
            contents += formulaToComponent(holF,list2,expTrees,allow)
          }
        }
      case _ =>
        val lbl = DrawSequent.formulaToLabel(holF,ft)
        lbl.deafTo(lbl.mouse.moves, lbl.mouse.clicks)
        contents += lbl
    }
  }

  def getMatrixSymbol(formula: HOLFormula) = formula match {
    case ExVar(_,_) => "\\bigvee"
    case AllVar(_,_) => "\\bigwedge"
    case _ => throw new Exception("Something went wrong in DrawExpansionTree!")
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

  // Draws list of formulas like single column matrix surrounded by < >.
  def drawMatrix(list: List[ExpansionTree]) = new BoxPanel(Orientation.Vertical) {
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