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
import at.logic.calculi.lk.base.Sequent


class DrawClList(private var clList: List[Sequent], val fontSize: Int) extends GridBagPanel {
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
      layout(DrawSequent(x, ft)) = c
    } else {
      y += 1
      c.grid = (0,y)
      layout(new Label(";")  { font = ft }) = c
      y += 1
      c.grid = (0,y)
      layout(DrawSequent(x, ft)) = c
    }
}
