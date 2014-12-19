package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 2:34 PM
 */

import java.awt.{Font, Color}
import Font._
import at.logic.calculi.lk.base.{Sequent, FSequent}
import at.logic.language.hol.HOLExpression
import swing.{FlowPanel, GridPanel, Label}

class DrawList(val list: List[Any], val fontSize: Int) extends GridPanel(0, 1) {
  background = new Color(255,255,255)
  private var str: String = ""
  initialize()

  def search_=(string: String) {
    str = string
    contents.clear()
    initialize()
  }
  def search = str

  def initialize() {
    val ft = new Font(SANS_SERIF, PLAIN, fontSize)
    var first = true
    for (x <- list) {
      if (first) {
        first = false
        val component = drawMember(x)
        contents += component
      } else {
        contents += new Label(";")  { font = ft }
        val component = drawMember(x)
        contents += component
      }
    }

    def drawMember(x: Any) = x match {
      case s : Sequent => DrawSequent(s, ft, str)
      case fs : FSequent => DrawSequent.applyF(fs, ft, str)
      case (f1: HOLExpression, f2: HOLExpression) => drawDefinition(f1, f2, ft)
      case _ => new Label(x.toString) {
        background = new Color(255,255,255)
        opaque = true
        font = ft
        if (! str.isEmpty && text.contains(str)) background = new Color(0,255,0)
      }
    }
  }

  def drawDefinition(f1: HOLExpression, f2: HOLExpression, ft: Font) = new FlowPanel {
    background = new Color(255,255,255)
    opaque = false

    val label1 = expressionToLabel(f1)
    val label2 = expressionToLabel(f2)
    
    if (! str.isEmpty && label1.latexText.contains(str)) label1.background = new Color(0,255,0)
    if (! str.isEmpty && label2.latexText.contains(str)) label2.background = new Color(0,255,0)
    
    contents += label1
    contents += new Label(" := ") { font = ft }
    contents += label2

    def expressionToLabel(e: HOLExpression): LatexLabel = LatexLabel(ft, DrawSequent.formulaToLatexString(e))
  }
}
