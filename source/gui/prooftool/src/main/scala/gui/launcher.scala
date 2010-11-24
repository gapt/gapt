package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Oct 30, 2010
 * Time: 5:43:38 PM
 */

import scala.swing._

class Launcher(val areaText: String, var fontSize: Int) extends TextArea {
  import java.awt.Font._
  
  editable = false
  font = new Font(SANS_SERIF, PLAIN, fontSize)
  text = areaText
}

class MyScrollPane(c: Launcher) extends ScrollPane {
  contents = c

  def getContent: Launcher = contents.last.asInstanceOf[Launcher]
}


/*
class Launcher(val style: Int, val size: Int) extends ScrollPane {
  val table = new Table(height, width)
  val rowHeader = new ListView((1 until height + 1) map (_.toString)) {
    fixedCellWidth = 30
    fixedCellHeight = table.rowHeight
  }
  viewportView = table
  rowHeaderView = rowHeader
} */
