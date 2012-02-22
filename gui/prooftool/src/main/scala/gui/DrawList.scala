package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 2:34 PM
 */

import swing.{GridPanel, Label}
import java.awt.{Font, Color}
import Font._
import at.logic.calculi.lk.base.{types, Sequent}

class DrawList(val list: List[_], val fontSize: Int) extends GridPanel(0, 1) {
  background = new Color(255,255,255)
  private var str: String = ""
  initialize

  def search_=(string: String) {
    str = string
    contents.clear
    initialize
  }
  def search = str

  def initialize {
    val ft = new Font(SANS_SERIF, PLAIN, fontSize)
    var first = true
    for (x <- list)
      if (first) {
        first = false
        val component = x match {
          case s : Sequent => DrawSequent(s, ft, str)
          case fs : types.FSequent => DrawSequent.applyF(fs, ft, str)
          case _ => new Label(x.toString) { font = ft }
        }
        contents += component
      } else {
        contents += new Label(";")  { font = ft }
        val component = x match {
          case s : Sequent => DrawSequent(s, ft, str)
          case fs : types.FSequent => DrawSequent.applyF(fs, ft, str)
          case _ => new Label(x.toString) { font = ft }
        }
        contents += component
      }
  }
}
