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
import at.logic.language.schema.{BiggerThanC, BigAnd, BigOr, IndexedPredicate, indexedFOVar, indexedOmegaVar, IntegerTerm, IntVar, IntConst, IntZero, Succ}
import at.logic.transformations.ceres.struct.ClauseSetSymbol
import at.logic.transformations.ceres.PStructToExpressionTree.ProjectionSetSymbol
import org.scilab.forge.jlatexmath.{TeXIcon, TeXConstants, TeXFormula}
import java.awt.{Color, Font}
import java.awt.image.BufferedImage
import swing._
import event.{MouseClicked, MouseEntered, MouseExited, WindowDeactivated}
import java.awt.event.MouseEvent
import at.logic.language.lambda.types.Tindex
import at.logic.language.lambda.types.Definitions._
import scala.swing.event.WindowDeactivated
import scala.swing.event.MouseClicked
import scala.swing.event.MouseEntered
import scala.swing.event.MouseExited
import at.logic.language.schema.IntZero
import at.logic.utils.latex.nameToLatexString
import collection.mutable

object DrawSequent {


  //used by DrawClList
  def apply(seq: Sequent, ft: Font, str: String): FlowPanel = if (! str.isEmpty) {
    val set: Set[FormulaOccurrence] = ( seq.antecedent.filter( fo => formulaToLatexString(fo.formula).contains(str)) ++
      seq.succedent.filter( fo => formulaToLatexString(fo.formula).contains(str)) ).toSet
    apply(seq, ft, set, Set(), Set())
  } else apply(seq, ft, Set(), Set(), Set())

  //used by DrawClList to draw FSequents
  def applyF(seq: types.FSequent, ft: Font, str: String): FlowPanel = {
    implicit val factory = defaultFormulaOccurrenceFactory
    implicit def fo2occ(f:HOLFormula) = factory.createFormulaOccurrence(f, Seq[FormulaOccurrence]())
    implicit def fseq2seq(s : types.FSequent) = Sequent(s._1 map fo2occ, s._2 map fo2occ  )
    apply(fseq2seq(seq), ft, str)
  }

  //used by DrawProof
  def apply(seq: Sequent, ft: Font, cut_anc: Set[FormulaOccurrence], omega_anc: Set[FormulaOccurrence], vis_occ: Set[FormulaOccurrence]) = new FlowPanel {
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
        }
        else
        if (omega_anc.contains(f)) {
          val fl = formulaToLabel(f.formula, ft)
          fl.background = new Color(255,0,0)
          contents += fl
        }
        else
          contents += formulaToLabel(f.formula, ft)
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
        }
        else
        if (omega_anc.contains(f)) {
          val fl = formulaToLabel(f.formula, ft)
          fl.background = new Color(255,0,0)
          contents += fl
        }
        else contents += formulaToLabel(f.formula, ft)
      }
    }
  }

  def formulaToLabel(f: HOLFormula, ft: Font) : LatexLabel = LatexLabel(ft,formulaToLatexString(f))


  // this method is used by DrawTree when drawing projections.
  // also by ProofToLatexExporter.
  def sequentToLatexString(seq: Sequent): String = {
    var s = " "
    var first = true
    for (f <- seq.antecedent) {
      if (! first) s = s + ", "
      else first = false
      s = s + formulaToLatexString(f.formula)
    }
    s = s + " \\vdash " // \u22a2
    first = true
    for (f <- seq.succedent) {
      if (! first) s = s + ", "
      else first = false
      s = s + formulaToLatexString(f.formula)
    }
    s
  }

  def formulaToLatexString(t: LambdaExpression, outermost : Boolean=true): String = t match {
    case Neg(f) => """\neg """ + formulaToLatexString(f, false)
    case And(f1,f2) => "(" + formulaToLatexString(f1, false) + """ \wedge """ + formulaToLatexString(f2, false) + ")"
    case Or(f1,f2) => "(" + formulaToLatexString(f1, false) + """ \vee """ + formulaToLatexString(f2, false) + ")"
    case Imp(f1,f2) => "(" + formulaToLatexString(f1, false) + """ \supset """ + formulaToLatexString(f2, false) + ")"
    case ExVar(v, f) => {
      if (v.exptype == ind->ind)
        "(" + """\exists^{hyp} """ + formulaToLatexString(v, false) + """)""" + formulaToLatexString(f, false)
      else
        "(" + """\exists """ + formulaToLatexString(v, false) + """)""" + formulaToLatexString(f, false)
    }
    case AllVar(v, f) => {
      if (v.exptype == ind->ind)
        "(" + """\forall^{hyp} """ + formulaToLatexString(v, false) + """)""" + formulaToLatexString(f, false)
      else
        "(" + """\forall """ + formulaToLatexString(v, false) + """)""" + formulaToLatexString(f, false)
    }
    case BigAnd(v, formula, init, end) =>
      """ \bigwedge_{ """ + formulaToLatexString(v, false) + "=" + formulaToLatexString(init) + "}^{" + formulaToLatexString(end, false) + "}" + formulaToLatexString(formula, false)
    case BigOr(v, formula, init, end) =>
      """ \bigvee_{ """ + formulaToLatexString(v, false) + "=" + formulaToLatexString(init, false) + "}^{" + formulaToLatexString(end, false) + "}" + formulaToLatexString(formula)
    case IndexedPredicate(constant, indices) if (constant != BiggerThanC) =>
      {if (constant.name.isInstanceOf[ClauseSetSymbol]) { //parse cl variables to display cut-configuration.
      val cl = constant.name.asInstanceOf[ClauseSetSymbol]
        "cl^{" + cl.name +",(" + cl.cut_occs._1.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + formulaToLatexString(f, false) ) + " | " +
          cl.cut_occs._2.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + formulaToLatexString(f, false) ) + ")}"
      } else if (constant.name.isInstanceOf[ProjectionSetSymbol]) { //parse pr variables to display cut-configuration.
      val pr = constant.name.asInstanceOf[ProjectionSetSymbol]
        "pr^{" + pr.name +",(" + pr.cut_occs._1.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + formulaToLatexString(f, false) ) + " | " +
          pr.cut_occs._2.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + formulaToLatexString(f, false) ) + ")}"
      }  //or return the predicate symbol
      else nameToLatexString(constant.name.toString)
      } + {if (indices.isEmpty) "" else indices.map(x => formulaToLatexString(x)).mkString("_{",",","}")}
    case t : IntegerTerm  => parseIntegerTerm(t, 0)
    case Atom(name, args) =>
      if (args.size == 2 &&  name.toString.matches("""(=|!=|\\neq|<|>|\\leq|\\geq|\\in|\+|-|\*|/)""")) { //!name.toString.matches("""[\w\p{InGreek}]*""")) {
        //formats infix formulas
        if (outermost) {
          //if the whole formula is an infix atom, we can skip parenthesis
          formulaToLatexString(args.head, false) + " "+ nameToLatexString(name.toString) +" "+ formulaToLatexString(args.last, false)
        } else {
          "(" + formulaToLatexString(args.head, false) +" "+ nameToLatexString(name.toString) +" "+ formulaToLatexString(args.last, false) + ")"
        }
      }
      else {
        //formats everything else
        nameToLatexString(name.toString) + {if (args.isEmpty) "" else args.map(x => formulaToLatexString(x, false)).mkString("(",",",")")}
      }
    case vi: indexedFOVar => vi.name.toString + "_{" + formulaToLatexString(vi.index, false) + "}"
    case vi: indexedOmegaVar => vi.name.toString + "_{" + formulaToLatexString(vi.index, false) + "}"
    case Var(name, _) => if (name.isInstanceOf[ClauseSetSymbol]) { //parse cl variables to display cut-configuration.
    val cl = name.asInstanceOf[ClauseSetSymbol]
      "cl^{" + cl.name +",(" + cl.cut_occs._1.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + formulaToLatexString(f) ) + " | " +
        cl.cut_occs._2.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + formulaToLatexString(f, false) ) + ")}"
    } else if (t.asInstanceOf[Var].isBound) "z_{" + t.asInstanceOf[Var].dbIndex.get + "}" // This line is added for debugging reasons!!!
    else if (t.exptype == ind->ind)
      "\\textbf {" + name.toString + "}"
    else  name.toString
    case Function(name, args, _) =>
      if (name.toString == "EXP")
        args.last.asInstanceOf[IntVar].name + "^{" + parseIntegerTerm(args.head.asInstanceOf[IntegerTerm], 0) + "}"
      else if (args.size == 1) parseNestedUnaryFunction(name.toString, args.head, 1)
      else if (args.size == 2 && name.toString.matches("""(=|!=|\\neq|<|>|\\leq|\\geq|\\in|\+|-|\*|/)"""))  //!name.toString.matches("""[\w\p{InGreek}]*"""))
        "(" + formulaToLatexString(args.head, false) + " "+ nameToLatexString(name.toString) +" " + formulaToLatexString(args.last, false) + ")"
      else nameToLatexString(name.toString) + {if (args.isEmpty) "" else args.map(x => formulaToLatexString(x, false)).mkString("(",",",")")}
    case Abs(v, s) => "(" + """ \lambda """ + formulaToLatexString(v, false) + """.""" + formulaToLatexString(s, false) + ")"
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
      v.toStringSimple()
    case Succ(s) => parseIntegerTerm( s, n + 1 )
    case _ => throw new Exception("Error in parseIntegerTerm(..) in gui")
  }

  def parseNestedUnaryFunction(parent_name: String, t: LambdaExpression, n: Int) : String = t match {
    case Function(name, args, _) =>
      if (args.size == 1 && name.toString == parent_name) parseNestedUnaryFunction(parent_name, args.head, n+1)
      else parent_name + {if ( n > 1 ) "^{" + n.toString + "}" else ""} + "(" + formulaToLatexString(t) + ")"
    case _ => parent_name + {if ( n > 1 ) "^{" + n.toString + "}" else ""} + "(" + formulaToLatexString(t) + ")"
  }
}


object LatexLabel {
  private val cache = mutable.Map[(String,Font), TeXIcon]()
  def clearCache() = this.synchronized(cache.clear())

  def apply(font:Font, latexText: String) : LatexLabel = {
    val key = (latexText,font)
    this.synchronized({
      val icon = cache.getOrElseUpdate(key, {
        val formula = try { new TeXFormula(latexText) }
        catch { case e: Exception => throw new Exception("Could not create formula "+latexText+": "+e.getMessage,e)}
        val myicon = formula.createTeXIcon(TeXConstants.STYLE_DISPLAY, font.getSize)
        val myimage = new BufferedImage(myicon.getIconWidth, myicon.getIconHeight, BufferedImage.TYPE_INT_ARGB)
        val g2 = myimage.createGraphics()
        g2.setColor(Color.white)
        g2.fillRect(0,0,myicon.getIconWidth,myicon.getIconHeight)
        myicon.paintIcon(null, g2, 0, 0)
        myicon
      })
      new LatexLabel(font, latexText, icon)
    })
  }
}

class LatexLabel(override val font : Font, val latexText : String, val myicon : TeXIcon)
  extends Label("", myicon, Alignment.Center) {
  background = new Color(255,255,255)
  foreground = new Color(0,0,0)
  opaque = true
  yLayoutAlignment = 0.5
  //icon = myicon

  listenTo(mouse.moves, mouse.clicks)
  reactions += {
    case e: MouseEntered => foreground = new Color(0,0,255)
    case e: MouseExited => foreground = new Color(0,0,0)
    case e: MouseClicked if (e.peer.getButton == MouseEvent.BUTTON3 && e.clicks == 2) =>
      val d = new Dialog {
        resizable = false
        peer.setUndecorated(true)
        contents = new TextField(latexText) {
          editable = false
          border = Swing.EmptyBorder(7)
          tooltip = "Select text and right-click to copy."
          font = font.deriveFont(Font.PLAIN, 14)
          listenTo(mouse.clicks)
          reactions += {
            case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 => copy()
          }
        }
        //  modal = true
        reactions += {
          case e: WindowDeactivated if (e.source == this) => dispose()
        }
      }
      d.location = locationOnScreen
      d.open()
  }
}
