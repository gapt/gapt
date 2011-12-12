package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 4:25 PM
 */

import at.logic.calculi.lk.base.Sequent
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol._
import at.logic.language.schema.{BigAnd, BigOr, IntegerTerm, IntConst, IntZero, IntVar, Succ, IndexedPredicate}
import at.logic.calculi.occurrences.FormulaOccurrence
import org.scilab.forge.jlatexmath.{TeXConstants, TeXFormula}
import java.awt.{Color, Font}
import java.awt.image.BufferedImage
import swing.{Label, FlowPanel}


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

  def formulaToLabel(f: HOLFormula, ft: Font) = latexToLabel(formulaToLatexString(f), ft)

  def latexToLabel(ls: String, ft: Font) = new Label {
    background = new Color(255,255,255)
    foreground = new Color(0,0,0)
    font = ft
    opaque = true

    val formula = new TeXFormula(ls)
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
    case IndexedPredicate(constant, indices) => nameToLatexString(constant.name.toString) + {if (indices.isEmpty) "" else indices.map(x => formulaToLatexString(x)).mkString("_{",",","}")}
    case t : IntegerTerm  => parseIntegerTerm(t, 0)
    case Atom(name, args) =>
      if (args.size == 2 && !name.toString.matches("""[\w\p{InGreek}]*"""))
        "(" + formulaToLatexString(args.head) + nameToLatexString(name.toString) + formulaToLatexString(args.last) + ")"
      else nameToLatexString(name.toString) + {if (args.isEmpty) "" else args.map(x => formulaToLatexString(x)).mkString("(",",",")")}
    case Var(name, _) => name.toString
    case Function(name, args, _) =>
      if (args.size == 2 && !name.toString.matches("""[\w\p{InGreek}]*"""))
        "(" + formulaToLatexString(args.head) + nameToLatexString(name.toString) + formulaToLatexString(args.last) + ")"
      else nameToLatexString(name.toString) + {if (args.isEmpty) "" else args.map(x => formulaToLatexString(x)).mkString("(",",",")")}
    case Abs(v, t) => "(" + """\lambda """ + formulaToLatexString(v) + """.""" + formulaToLatexString(t) + ")"
  }

  def nameToLatexString(name: String) = name match {
    case "~" => """ \sim """
    case _ => name
  }

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
}