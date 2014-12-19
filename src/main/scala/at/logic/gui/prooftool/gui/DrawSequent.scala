package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 4:25 PM
 */

import at.logic.calculi.lk.base.{FSequent, Sequent}
import at.logic.language.hol._
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.language.schema.{BiggerThanC, BigAnd, BigOr, IndexedPredicate, indexedFOVar, indexedOmegaVar, IntegerTerm, IntVar, IntConst, Succ}
import at.logic.transformations.ceres.struct.ClauseSetSymbol
import at.logic.transformations.ceres.PStructToExpressionTree.ProjectionSetSymbol
import org.scilab.forge.jlatexmath.{TeXIcon, TeXConstants, TeXFormula}
import java.awt.{Color, Font}
import java.awt.image.BufferedImage
import swing._
import event.{MouseClicked, MouseEntered, MouseExited, WindowDeactivated}
import java.awt.event.MouseEvent
import at.logic.language.schema.IntZero
import at.logic.utils.latex.nameToLatexString
import collection.mutable
import at.logic.gui.prooftool.parser.{ChangeFormulaColor, ChangeSequentColor, ProofToolPublisher}
import at.logic.language.lambda.types.Tindex

object DrawSequent {
  implicit val factory = defaultFormulaOccurrenceFactory
  implicit def fo2occ(f:HOLFormula) = factory.createFormulaOccurrence(f, Seq[FormulaOccurrence]())
  implicit def fseq2seq(s : FSequent) = Sequent(s._1 map fo2occ, s._2 map fo2occ  )

  //used by DrawClList
  def apply(seq: Sequent, ft: Font, str: String): FlowPanel = if (! str.isEmpty) {
    val set: Set[FormulaOccurrence] = ( seq.antecedent.filter( fo => formulaToLatexString(fo.formula).contains(str)) ++
      seq.succedent.filter( fo => formulaToLatexString(fo.formula).contains(str)) ).toSet
    val fp = apply(seq, ft, None)  // first create FlowPanel to pass the event
    ProofToolPublisher.publish(ChangeFormulaColor(set,Color.green,reset=false))
    fp
  } else apply(seq, ft, None)

  //used by DrawClList to draw FSequents
  def applyF(seq: FSequent, ft: Font, str: String): FlowPanel = apply(fseq2seq(seq), ft, str)

  //used by DrawProof
  def apply(seq: Sequent, ft: Font, vis_occ: Option[Set[FormulaOccurrence]]) = new FlowPanel {
    opaque = false // Necessary to draw the proof properly
    hGap = 0  // no gap between components

    listenTo(ProofToolPublisher)
    reactions += {
      // since panel is not opaque, it cannot have a background color,
      case ChangeSequentColor(s, color, reset) => // so change background of each component.
        if (s == seq) contents.foreach(c => c.background = color)
        else if (reset) contents.foreach(c => c.background = Color.white)
    }

    private var first = true
    for (f <- seq.antecedent) {
      if (vis_occ == None || vis_occ.get.contains(f) ) {
        if (! first) contents += LatexLabel(ft, ",", null)
        else first = false
        contents += formulaToLabel(f, ft)
      }
    }
    contents += LatexLabel(ft, "\\vdash", null) // \u22a2
    first = true
    for (f <- seq.succedent) {
      if (vis_occ == None || vis_occ.get.contains(f) ) {
        if (! first) contents += LatexLabel(ft, ",", null)
        else first = false
        contents += formulaToLabel(f, ft)
      }
    }
  }

  def formulaToLabel(f: HOLFormula, ft: Font) : LatexLabel = LatexLabel(ft,formulaToLatexString(f),fo2occ(f))
  def formulaToLabel(fo: FormulaOccurrence, ft: Font) : LatexLabel = LatexLabel(ft,formulaToLatexString(fo.formula),fo)

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

  def formulaToLatexString(t: HOLExpression, outermost : Boolean=true): String = t match {
    case Neg(f) => """\neg """ + formulaToLatexString(f, outermost = false)
    case And(f1,f2) =>
      if (outermost)
        formulaToLatexString(f1, outermost = false) + """ \wedge """ + formulaToLatexString(f2, outermost = false)
      else
        "(" + formulaToLatexString(f1, outermost = false) + """ \wedge """ + formulaToLatexString(f2, outermost = false) + ")"
    case Or(f1,f2) =>
      if (outermost)
        formulaToLatexString(f1, outermost = false) + """ \vee """ + formulaToLatexString(f2, outermost = false)
      else
        "(" + formulaToLatexString(f1, outermost = false) + """ \vee """ + formulaToLatexString(f2, outermost = false) + ")"

    case Imp(f1,f2) =>
      if (outermost)
        formulaToLatexString(f1, outermost = false) + """ \supset """ + formulaToLatexString(f2, outermost = false)
      else
        "(" + formulaToLatexString(f1, outermost = false) + """ \supset """ + formulaToLatexString(f2, outermost = false) + ")"
    case ExVar(v, f) =>
      if (v.exptype == Tindex->Tindex)
        "(" + """\exists^{hyp} """ + formulaToLatexString(v, outermost = false) + """)""" + formulaToLatexString(f, outermost = false)
      else
        "(" + """\exists """ + formulaToLatexString(v, outermost = false) + """)""" + formulaToLatexString(f, outermost = false)
    case AllVar(v, f) =>
      if (v.exptype == Tindex->Tindex)
        "(" + """\forall^{hyp} """ + formulaToLatexString(v, outermost = false) + """)""" + formulaToLatexString(f, outermost = false)
      else
        "(" + """\forall """ + formulaToLatexString(v, outermost = false) + """)""" + formulaToLatexString(f, outermost = false)
    case BigAnd(v, formula, init, end) =>
      """ \bigwedge_{ """ + formulaToLatexString(v, outermost = false) + "=" + formulaToLatexString(init) + "}^{" + formulaToLatexString(end, outermost = false) + "}" + formulaToLatexString(formula, outermost = false)

    case BigOr(v, formula, init, end) =>
      """ \bigvee_{ """ + formulaToLatexString(v, outermost = false) + "=" + formulaToLatexString(init, outermost = false) + "}^{" + formulaToLatexString(end, outermost = false) + "}" + formulaToLatexString(formula)
    case IndexedPredicate(constant, indices) if constant != BiggerThanC =>
      {if (constant.sym.isInstanceOf[ClauseSetSymbol]) { //parse cl variables to display cut-configuration.
      val cl = constant.name.asInstanceOf[ClauseSetSymbol]
        "cl^{" + cl.name +",(" + cl.cut_occs._1.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + formulaToLatexString(f, outermost = false) ) + " | " +
          cl.cut_occs._2.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + formulaToLatexString(f, outermost = false) ) + ")}"
      } else if (constant.sym.isInstanceOf[ProjectionSetSymbol]) { //parse pr variables to display cut-configuration.
      val pr = constant.name.asInstanceOf[ProjectionSetSymbol]
        "pr^{" + pr.name +",(" + pr.cut_occs._1.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + formulaToLatexString(f, outermost = false) ) + " | " +
          pr.cut_occs._2.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + formulaToLatexString(f, outermost = false) ) + ")}"
      }  //or return the predicate symbol
      else nameToLatexString(constant.name.toString)
      } + {if (indices.isEmpty) "" else indices.map(x => formulaToLatexString(x)).mkString("_{",",","}")}
    case t : IntegerTerm  => parseIntegerTerm(t, 0)
    case Atom(pred, args) =>
      val name = pred match {
        case HOLConst(n,_) => n
        case HOLVar(n,_) => n
        case _ => throw new Exception("An atom can only contain a const or a var on the outermost level!")
      }
      if (args.size == 2 &&  name.toString.matches("""(=|!=|\\neq|<|>|\\leq|\\geq|\\in|\+|-|\*|/)""")) { //!name.toString.matches("""[\w\p{InGreek}]*""")) {
        //formats infix formulas
        if (outermost) {
          //if the whole formula is an infix atom, we can skip parenthesis
          formulaToLatexString(args.head, outermost = false) + " "+ nameToLatexString(name.toString) +" "+ formulaToLatexString(args.last, outermost = false)
        } else {
          "(" + formulaToLatexString(args.head, outermost = false) +" "+ nameToLatexString(name.toString) +" "+ formulaToLatexString(args.last, outermost = false) + ")"
        }
      }
      else {
        //formats everything else
        nameToLatexString(name.toString) + {if (args.isEmpty) "" else args.map(x => formulaToLatexString(x, outermost = false)).mkString("(",",",")")}
      }
    case vi: indexedFOVar => vi.name.toString + "_{" + formulaToLatexString(vi.index, outermost = false) + "}"
    case vi: indexedOmegaVar => vi.name.toString + "_{" + formulaToLatexString(vi.index, outermost = false) + "}"
    case v:HOLVar  if v.sym.isInstanceOf[ClauseSetSymbol] => //Fixme: never enters here because type of ClauseSetSymbol is changed
      //parse cl variables to display cut-configuration.
      val cl = v.sym.asInstanceOf[ClauseSetSymbol]
      "cl^{" + cl.name +",(" + cl.cut_occs._1.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + formulaToLatexString(f) ) + " | " +
        cl.cut_occs._2.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + formulaToLatexString(f, outermost = false) ) + ")}"
    case HOLVar(name,_) if t.exptype == Tindex -> Tindex =>
      "\\textbf {" + name.toString + "}"
    case HOLVar(name,_) =>  name
    case HOLConst(name,_) => name
    case Function(f, args, _) =>
      val name = f match {
        case HOLConst(n,_) => n
        case HOLVar(n,_) => n
        case _ => throw new Exception("An atom can only contain a const or a var on the outermost level!")
      }

      if (name.toString == "EXP")
        args.last.asInstanceOf[IntVar].name + "^{" + parseIntegerTerm(args.head.asInstanceOf[IntegerTerm], 0) + "}"
      else if (args.size == 1) parseNestedUnaryFunction(name.toString, args.head, 1)
      else if (args.size == 2 && name.toString.matches("""(=|!=|\\neq|<|>|\\leq|\\geq|\\in|\+|-|\*|/)"""))  //!name.toString.matches("""[\w\p{InGreek}]*"""))
        "(" + formulaToLatexString(args.head, outermost = false) + " "+ nameToLatexString(name.toString) +" " + formulaToLatexString(args.last, outermost = false) + ")"
      else nameToLatexString(name.toString) + {if (args.isEmpty) "" else args.map(x => formulaToLatexString(x, outermost = false)).mkString("(",",",")")}
    case HOLAbs(v, s) => "(" + """ \lambda """ + formulaToLatexString(v, outermost = false) + """.""" + formulaToLatexString(s, outermost = false) + ")"
    case HOLApp(s,t) => formulaToLatexString(s, outermost = false) + "(" + formulaToLatexString(t, outermost = false) + ")"
  }

  def parseIntegerTerm( t: IntegerTerm, n: Int) : String = t match {
    // FIXME: in the first case, we implicitely assume that all IntConsts are 0!
    // this is just done for convenience, and should be changed ASAP
    case z : IntConst => n.toString
    case IntZero() => n.toString
    case v : IntVar => if (n > 0)
      v.toPrettyString + "+" + n.toString
    else
      v.toPrettyString
    case Succ(s) => parseIntegerTerm( s, n + 1 )
    case _ => throw new Exception("Error in parseIntegerTerm(..) in gui")
  }

  def parseNestedUnaryFunction(parent_name: String, t: HOLExpression, n: Int) : String = t match {
    case Function(name, args, _) =>
      if (args.size == 1 && name.toString == parent_name) parseNestedUnaryFunction(parent_name, args.head, n+1)
      else parent_name + {if ( n > 1 ) "^{" + n.toString + "}" else ""} + "(" + formulaToLatexString(t) + ")"
    case _ => parent_name + {if ( n > 1 ) "^{" + n.toString + "}" else ""} + "(" + formulaToLatexString(t) + ")"
  }
}


object LatexLabel {
  private val cache = mutable.Map[(String,Font), TeXIcon]()

  def clearCache() = this.synchronized(cache.clear())

  def apply(font:Font, latexText: String) : LatexLabel = apply(font,latexText,null)

  def apply(font:Font, latexText: String, fo: FormulaOccurrence) : LatexLabel = {
    val key = (latexText,font)
    this.synchronized({
      val icon = cache.getOrElseUpdate(key, {
        val formula = try {
          new TeXFormula(latexText)
        } catch {
          case e: Exception =>
            throw new Exception("Could not create formula "+latexText+": "+e.getMessage,e)
        }
        val myicon = formula.createTeXIcon(TeXConstants.STYLE_DISPLAY, font.getSize)
        val myimage = new BufferedImage(myicon.getIconWidth, myicon.getIconHeight, BufferedImage.TYPE_INT_ARGB)
        val g2 = myimage.createGraphics()
        g2.setColor(Color.white)
        g2.fillRect(0,0,myicon.getIconWidth,myicon.getIconHeight)
        myicon.paintIcon(null, g2, 0, 0)
        myicon
      })
      new LatexLabel(font, latexText, icon, fo)
    })
  }
}

class LatexLabel(val ft : Font, val latexText : String, val myicon : TeXIcon, fo: FormulaOccurrence)
  extends Label("", myicon, Alignment.Center) {
  background = Color.white
  foreground = Color.black
  font = ft
  opaque = true
  yLayoutAlignment = 0.5
  if (latexText == ",") {
    border = Swing.EmptyBorder(font.getSize/5,2,0,font.getSize/5)
    icon = null
    text = latexText
  }
  if (latexText == "\\vdash") border = Swing.EmptyBorder(font.getSize/6)

  listenTo(mouse.moves, mouse.clicks, ProofToolPublisher)
  reactions += {
    case e: MouseEntered => foreground = Color.blue
    case e: MouseExited => foreground =  Color.black
    case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 && e.clicks == 2 =>
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
          case e: WindowDeactivated if e.source == this => dispose()
        }
      }
      d.location = locationOnScreen
      d.open()
    case ChangeFormulaColor(set, color, reset) =>
      if (set.contains(fo)) background = color
      else if (reset) background = Color.white
  }
}