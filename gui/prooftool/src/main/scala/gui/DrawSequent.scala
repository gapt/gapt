package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 4:25 PM
 */

import at.logic.calculi.lk.base.{types, Sequent}
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol._
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.language.schema.{BiggerThanC, BigAnd, BigOr, IndexedPredicate, IntegerTerm, IntVar, IntConst, IntZero, Succ}
import at.logic.transformations.ceres.struct.ClauseSetSymbol
import at.logic.transformations.ceres.PStructToExpressionTree.ProjectionSetSymbol
import scala.collection.immutable.Seq
import org.scilab.forge.jlatexmath.{TeXConstants, TeXFormula}
import java.awt.{Color, Font}
import java.awt.image.BufferedImage
import swing.{Label, FlowPanel}

object DrawSequent {

  //used by DrawClList
  def apply(seq: Sequent, ft: Font, str: String): FlowPanel = if (! str.isEmpty) {
    val set: Set[FormulaOccurrence] = ( seq.antecedent.filter( fo => formulaToLatexString(fo.formula).contains(str)) ++
      seq.succedent.filter( fo => formulaToLatexString(fo.formula).contains(str)) ).toSet
    apply(seq, ft, set, Set())
  } else apply(seq, ft, Set(), Set())

  //used by DrawClList to draw FSequents
  def applyF(seq: types.FSequent, ft: Font, str: String): FlowPanel = {
    implicit val factory = defaultFormulaOccurrenceFactory
    implicit def fo2occ(f:HOLFormula) = factory.createFormulaOccurrence(f, Seq[FormulaOccurrence]())
    implicit def fseq2seq(s : types.FSequent) = Sequent(s._1 map fo2occ, s._2 map fo2occ  )
    apply(fseq2seq(seq), ft, str)
  }

  //used by DrawProof
  def apply(seq: Sequent, ft: Font, cut_anc: Set[FormulaOccurrence], vis_occ: Set[FormulaOccurrence]) = new FlowPanel {
    background = new Color(255,255,255)
    opaque = false

    private var first = true
    for (f <- seq.antecedent) {
      if (vis_occ.isEmpty || vis_occ.contains(f) ) {
      if (! first) contents += new Label(", ") {font = ft}
      else first = false
      if (cut_anc.contains(f)) {
        val fl = formulaToLabel(f.formula, ft)
        fl.background = new Color(0,255,0)
        contents += fl
      } else contents += formulaToLabel(f.formula, ft)
      }
    }
    contents += new Label(" \u22a2 ") {font = ft}
    first =true
    for (f <- seq.succedent) {
      if (vis_occ.isEmpty || vis_occ.contains(f) ) {
      if (! first) contents += new Label(", ")  {font = ft}
      else first = false
      if (cut_anc.contains(f)) {
        val fl = formulaToLabel(f.formula, ft)
        fl.background = new Color(0,255,0)
        contents += fl
      } else contents += formulaToLabel(f.formula, ft)
      }
    }
  }

  def formulaToLabel(f: HOLFormula, ft: Font) = latexToLabel(formulaToLatexString(f), ft)

  def latexToLabel(ls: String, ft: Font) = new Label {
    background = new Color(255,255,255)
    foreground = new Color(0,0,0)
    font = ft
    opaque = true

    val latexText = ls
    val formula = new TeXFormula(ls)
    val myicon = formula.createTeXIcon(TeXConstants.STYLE_DISPLAY, ft.getSize)
    val myimage = new BufferedImage(myicon.getIconWidth(), myicon.getIconHeight(), BufferedImage.TYPE_INT_ARGB)
    val g2 = myimage.createGraphics()
	  g2.setColor(Color.white)
	  g2.fillRect(0,0,myicon.getIconWidth(),myicon.getIconHeight())
	  myicon.paintIcon(peer, g2, 0, 0)

    icon = myicon
  }

   // this method is used by DrawTree when drawing projections.
  def sequentToLatexString(seq: Sequent): String = {
    var s = " "
    var first = true
    for (f <- seq.antecedent) {
      if (! first) s = s + ", "
      else first = false
      s = s + formulaToLatexString(f.formula)
    }
    s = s + " \u22a2 "
    first = true
    for (f <- seq.succedent) {
      if (! first) s = s + ", "
      else first = false
      s = s + formulaToLatexString(f.formula)
    }
    s
  }

  def formulaToLatexString(t: LambdaExpression): String = t match {
    case Neg(f) => """\neg """ + formulaToLatexString(f)
    case And(f1,f2) => "(" + formulaToLatexString(f1) + """ \wedge """ + formulaToLatexString(f2) + ")"
    case Or(f1,f2) => "(" + formulaToLatexString(f1) + """ \vee """ + formulaToLatexString(f2) + ")"
    case Imp(f1,f2) => "(" + formulaToLatexString(f1) + """ \supset """ + formulaToLatexString(f2) + ")"
    case ExVar(v, f) => "(" + """\exists """ + formulaToLatexString(v) + """)""" + formulaToLatexString(f)
    case AllVar(v, f) => "(" + """\forall """ + formulaToLatexString(v) + """)""" + formulaToLatexString(f)
    case BigAnd(v, formula, init, end) =>
      """ \bigwedge_{ """ + formulaToLatexString(v) + "=" + formulaToLatexString(init) + "}^{" + formulaToLatexString(end) + "}" + formulaToLatexString(formula)
    case BigOr(v, formula, init, end) =>
      """ \bigvee_{ """ + formulaToLatexString(v) + "=" + formulaToLatexString(init) + "}^{" + formulaToLatexString(end) + "}" + formulaToLatexString(formula)
    case IndexedPredicate(constant, indices) if (constant != BiggerThanC) =>
      {if (constant.name.isInstanceOf[ClauseSetSymbol]) { //parse cl variables to display cut-configuration.
        val cl = constant.name.asInstanceOf[ClauseSetSymbol]
        "cl^{(" + cl.cut_occs._1.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + formulaToLatexString(f) ) + " | " +
          cl.cut_occs._2.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + formulaToLatexString(f) ) + ")," + cl.name +"}"
      } else if (constant.name.isInstanceOf[ProjectionSetSymbol]) { //parse pr variables to display cut-configuration.
        val cl = constant.name.asInstanceOf[ProjectionSetSymbol]
        "pr^{(" + cl.cut_occs._1.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + formulaToLatexString(f) ) + " | " +
          cl.cut_occs._2.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + formulaToLatexString(f) ) + ")," + cl.name +"}"
      }
      else nameToLatexString(constant.name.toString)} + {if (indices.isEmpty) "" else indices.map(x => formulaToLatexString(x)).mkString("_{",",","}")}
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
