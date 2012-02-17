package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 2:34 PM
 */

import swing.{Label, GridBagPanel}
import GridBagPanel._
import java.awt.{Font, Color}
import Font._
import at.logic.calculi.lk.base.{types, Sequent}

class DrawClList(private var clList: List[_], val fontSize: Int) extends GridBagPanel {
  background = new Color(255,255,255)

  val c = new Constraints
  c.fill = Fill.Horizontal
  private var y = 0
  private val ft = new Font(SANS_SERIF, PLAIN, fontSize)
  private var first = true
  for (x <- clList)
    if (first) {
      first = false
      c.grid = (0,y)
      val component = x match {
        case s : Sequent => DrawSequent(s, ft)
        case fs : types.FSequent => DrawSequent.applyF(fs, ft)
        case _ => new Label(x.toString) { font = ft }
      }
      layout( component ) = c
    } else {
      y += 1
      c.grid = (0,y)
      layout(new Label(";")  { font = ft }) = c
      y += 1
      c.grid = (0,y)
      val component = x match {
        case s : Sequent => DrawSequent(s, ft)
        case fs : types.FSequent => DrawSequent.applyF(fs, ft)
        case _ => new Label(x.toString) { font = ft }
      }
      layout( component ) = c
    }
}
