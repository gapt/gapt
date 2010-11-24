package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Nov 16, 2010
 * Time: 2:32:34 PM
 */

import scala.swing._
import event._

object About {
  private val d = new Dialog

  def open = {
    d.setLocationRelativeTo(Main.mBar)
    d.title = "About Prooftool"
    d.contents = new GridBagPanel { grid =>
      import GridBagPanel._
      import javax.swing.ImageIcon

      val img = {
        import java.io.File.separator
        val path = separator+"icons/tu.gif"
        try {
          new ImageIcon(Main.resourceFromClassloader(path))
        } catch {
          case e: Exception =>
            import Dialog._
            showMessage(Main.mBar,"Couldn't load image: "+path+"\n \n"+e.toString+"\n")
            Swing.EmptyIcon
        }
      }
       
      border = Swing.EmptyBorder(10, 10, 10, 10)
      val c = new Constraints
      c.fill = Fill.Horizontal
      c.grid = (1,0)
      layout(new Label("    ")) = c
      c.grid = (2,0)
      c.ipady = 10
      layout(new Label("Version:") { horizontalAlignment = Alignment.Right }) = c
      c.grid = (2,1)
      layout(new Label("Author:") { horizontalAlignment = Alignment.Right }) = c
      c.grid = (3,0)
      layout(new Label(" ")) = c
      c.grid = (3,1)
      layout(new Label(" ")) = c
      c.grid = (4,0)
      layout(new Label("1.0 beta") { horizontalAlignment = Alignment.Left }) = c
      c.grid = (4,1)
      layout(new Label("Mikheil Rukhaia") { horizontalAlignment = Alignment.Left }) = c
      c.grid = (4,2)
      layout(new Label(" ")) = c
      c.grid = (4,3)
      c.ipady = 5
      layout(new Button(Action("OK") { d.close }) {
        listenTo(keys)
        reactions += {
          case KeyPressed(_,Key.Enter,_,_) => d.close
        }
      }) = c
      c.gridheight = 4
      c.ipady = 0
      c.grid = (0,0)
      layout(new Label { icon = img }) = c
    }
    d.open
  }
}