package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 4:25 PM
 */

import at.logic.calculi.lk.base.Sequent
import at.logic.language.lambda.types.{To, ->, Ti}
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol._
import at.logic.language.schema.{BigAnd, BigOr, IntegerTerm, IntConst, IntZero, IntVar, Succ}
import org.scilab.forge.jlatexmath.{TeXConstants, TeXFormula}
import java.awt.{Insets, Color, Font}
import java.awt.image.BufferedImage

//import at.logic.language.fol._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.occurrences.FormulaOccurrence
import swing.{Label, FlowPanel}


object ProoftoolSequentFormatter {
 //formats a lambda term to a readable string, distinguishing function and logical symbols
  def formulaToString(f:LambdaExpression) : String = f match {

    // pretty print schemata
    case BigAnd(v, formula, init, end) => 
      "⋀" + formulaToString(v) + "=(" + formulaToString(init) + ".." + formulaToString(end) + ")(" + formulaToString(formula) + ")"
    case BigOr(v, formula, init, end) => 
      "⋁" + formulaToString(v) + "=(" + formulaToString(init) + ".." + formulaToString(end) + ")(" + formulaToString(formula) + ")"
    case t : IntegerTerm  => parseIntegerTerm(t, 0)

    case App(x,y) => x match {
      case App(Var(name,tp),z) =>
        if (name.toString.matches("""[\w\p{InGreek}]*""")) name.toString+"("+formulaToString(z)+","+formulaToString(y)+")"
        else "("+formulaToString(z)+" "+name.toString()+" "+formulaToString(y)+")"
      case Var(name,tp) => tp match {
        case ->(To(), To()) => name.toString+formulaToString(y)
        case _ => y match {
          case Abs(x1,y1) => "("+name.toString+formulaToString(x1)+")"+formulaToString(y1)
          case _ => name.toString()+"("+formulaToString(y)+")"
        }
      }
      case _ => formulaToString(x) +"("+ formulaToString(y) +")"
    }
    case Var(name,t) => name.toString()
    case Abs(x,y) => formulaToString(y)
    case  x : Any    => "(unmatched class: "+x.getClass() + ")"
  }


  // exactly like the function above with only difference : adds a star which means that this formula is a cut-ancestor
  def formulaToStringMarked(f:LambdaExpression) : String = formulaToString(f) + "*";

  def parseIntegerTerm( t: IntegerTerm, n: Int) : String = t match {
    // FIXME: in the first case, we implicitely assume
    // that all IntConsts are 0!
    // this is just done for convenience, and should be changed ASAP
    case z : IntConst => n.toString
    case IntZero() => n.toString

    case v : IntVar => if (n > 0)
        v.toStringSimple + "+" + n.toString
      else
        v.toStringSimple
    case Succ(t) => parseIntegerTerm( t, n + 1 )
    case _ => throw new Exception("Error in parseIntegerTerm(..) in gui")
  }

 /*
  def formulaToString(f:SchemaExpression) : String = f match {
    case AppN(BigAndC, SchemaAbs(i, formula)::lower::upper::Nil) => BigAndC.name + "<sub>" + formulaToString(i) + " = " + formulaToString(lower) + "</sub>" +
      "<sup>" + formulaToString(upper) + "</sup>" + formulaToString(formula)
    case AppN(BigOrC, SchemaAbs(i, formula)::lower::upper::Nil) => BigAndC.name + "<sub>" + formulaToString(i) + " = " + formulaToString(lower) + "</sub>" +
      "<sup>" + formulaToString(upper) + "</sup>" + formulaToString(formula)
    case AppN(pred, indexTerms) => formulaToString(pred)+"<sub>"+indexTerms.map( x => formulaToString(x)).mkString+"</sub>"
  }*/

  // formats a sequent to a readable string
  def sequentToString(s : Sequent) : String = {
    var sb = new scala.StringBuilder()
    var first = true
    for (f <- s.antecedent) {
      if (! first) sb.append(", ")
      else first = false
        sb.append(formulaToString(f))
    }
    sb.append(" \u22a2 ")
    first =true
    for (f <- s.succedent) {
      if (! first) sb.append(", ")
      else first = false
        sb.append(formulaToString(f))    }
    sb.toString
  }

  // marks also the cut-ancestors
  def sequentToStringCutAnc(s : Sequent, cut_anc: Set[FormulaOccurrence]) : String = {
    var sb = new scala.StringBuilder()
    var first = true
    for (f <- s.antecedent) {
      if (! first) sb.append(", ")
      else first = false
      if (cut_anc.contains(f))
        sb.append(formulaToStringMarked(f))
      else
        sb.append(formulaToString(f))
    }
    sb.append(" \u22a2 ")
    first =true
    for (f <- s.succedent) {
      if (! first) sb.append(", ")
      else first = false
    if (cut_anc.contains(f))
        sb.append(formulaToStringMarked(f))
      else
        sb.append(formulaToString(f))    }
    sb.toString
  }
}


object DrawSequent {

  def apply(seq: Sequent, ft: Font) = new FlowPanel {
    background = new Color(255,255,255)
    opaque = false

    private var first = true
    for (f <- seq.antecedent) {
      if (! first) contents += new Label(", ") {font = ft}
      else first = false
      contents += formulaToLabel(f.formula, ft)
    }
    contents += new Label(" \u22a2 ") {font = ft}
    first =true
    for (f <- seq.succedent) {
      if (! first) contents += new Label(", ")  {font = ft}
      else first = false
      contents += formulaToLabel(f.formula, ft)
    }
  }

  def apply(seq: Sequent, ft: Font, cut_anc: Set[FormulaOccurrence]) = new FlowPanel {
    background = new Color(255,255,255)
    opaque = false

    private var first = true
    for (f <- seq.antecedent) {
      if (! first) contents += new Label(", ") {font = ft}
      else first = false
      if (cut_anc.contains(f)) {
        val fl = formulaToLabel(f.formula, ft)
        fl.background = new Color(0,255,0)
        contents += fl
      } else contents += formulaToLabel(f.formula, ft)
    }
    contents += new Label(" \u22a2 ") {font = ft}
    first =true
    for (f <- seq.succedent) {
      if (! first) contents += new Label(", ")  {font = ft}
      else first = false
      if (cut_anc.contains(f)) {
        val fl = formulaToLabel(f.formula, ft)
        fl.background = new Color(0,255,0)
        contents += fl
      } else contents += formulaToLabel(f.formula, ft)
    }
  }

  def formulaToLabel(f: HOLFormula, ft: Font) = new Label {
    background = new Color(255,255,255)
    foreground = new Color(0,0,0)
    font = ft
    opaque = true

    val formula = new TeXFormula(formulaToLatexString(f))
    val myicon = formula.createTeXIcon(TeXConstants.STYLE_DISPLAY, ft.getSize)
    val myimage = new BufferedImage(myicon.getIconWidth(), myicon.getIconHeight(), BufferedImage.TYPE_INT_ARGB)
    val g2 = myimage.createGraphics()
	  g2.setColor(Color.white)
	  g2.fillRect(0,0,myicon.getIconWidth(),myicon.getIconHeight())
	  myicon.paintIcon(peer, g2, 0, 0)

    icon = myicon
  }

  def formulaToLatexString(t: LambdaExpression): String = t match {
    case Neg(f) => """\neg """ + formulaToLatexString(f)
    case And(f1,f2) => "(" + formulaToLatexString(f1) + """ \wedge """ + formulaToLatexString(f2) + ")"
    case Or(f1,f2) => "(" + formulaToLatexString(f1) + """ \vee """ + formulaToLatexString(f2) + ")"
    case Imp(f1,f2) => "(" + formulaToLatexString(f1) + """ \supset """ + formulaToLatexString(f2) + ")"
    case ExVar(v, f) => "(" + """\exists """ + formulaToLatexString(v) + """)""" + formulaToLatexString(f)
    case AllVar(v, f) => "(" + """\forall """ + formulaToLatexString(v) + """)""" + formulaToLatexString(f)
    case BigAnd(v, formula, init, end) =>
      "⋀_{" + formulaToLatexString(v) + "=" + formulaToLatexString(init) + "}^{" + formulaToLatexString(end) + "}" + formulaToLatexString(formula)
    case BigOr(v, formula, init, end) =>
      "⋁_{" + formulaToLatexString(v) + "=" + formulaToLatexString(init) + "}^{" + formulaToLatexString(end) + "}" + formulaToLatexString(formula)
    case t : IntegerTerm  => ProoftoolSequentFormatter.parseIntegerTerm(t, 0)
    case Atom(name, args) => name.toString + {if (args.isEmpty) "" else args.map(x => formulaToLatexString(x)).mkString("(",",",")")}
    case Var(name, _) => name.toString
    case Function(name, args, _) => name.toString + {if (args.isEmpty) "" else args.map(x => formulaToLatexString(x)).mkString("(",",",")")}
    case Abs(v, t) => "(" + """\lambda """ + formulaToLatexString(v) + """.""" + formulaToLatexString(t) + ")"
  }
}