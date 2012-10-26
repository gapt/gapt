package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 2:34 PM
 */

import java.awt.{Font, Color}
import Font._
import at.logic.calculi.lk.base.{types, Sequent}
import at.logic.language.hol.HOLFormula
import swing.{FlowPanel, GridPanel, Label}

class DrawList(val list: List[_], val fontSize: Int) extends GridPanel(0, 1) {
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
    for (x <- list)
      if (first) {
        first = false
        val component = x match {
          case s : Sequent => DrawSequent(s, ft, str)
          case fs : types.FSequent => DrawSequent.applyF(fs, ft, str)
          case (f1: HOLFormula, f2: HOLFormula) => drawDefinition(f1, f2, ft)
          case _ => new Label(x.toString) {
            background = new Color(255,255,255)
            opaque = true
            font = ft
            if (! str.isEmpty && text.contains(str)) background = new Color(0,255,0)
          }
        }
        contents += component
      } else {
        contents += new Label(";")  { font = ft }
        val component = x match {
          case s : Sequent => DrawSequent(s, ft, str)
          case fs : types.FSequent => DrawSequent.applyF(fs, ft, str)
          case (f1: HOLFormula, f2: HOLFormula) => drawDefinition(f1, f2, ft)
          case _ => new Label(x.toString) {
            background = new Color(255,255,255)
            opaque = true
            font = ft
            if (! str.isEmpty && text.contains(str)) background = new Color(0,255,0)
          }
        }
        contents += component
      }
  }

  def drawDefinition(f1: HOLFormula, f2: HOLFormula, ft: Font) = new FlowPanel {
    background = new Color(255,255,255)
    opaque = false

    val label1 = DrawSequent.formulaToLabel(f1, ft)
    val label2 = DrawSequent.formulaToLabel(f2, ft)
    
    if (! str.isEmpty && label1.latexText.contains(str)) label1.background = new Color(0,255,0)
    if (! str.isEmpty && label2.latexText.contains(str)) label2.background = new Color(0,255,0)
    
    contents += label1
    contents += new Label(" := ") { font = ft }
    contents += label2
  }
}
