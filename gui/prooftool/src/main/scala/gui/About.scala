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

  def apply() = {
    d.resizable = false
    d.setLocationRelativeTo(Main.mBar)
    d.title = "About Prooftool"
    d.contents = new GridBagPanel { grid =>
      import GridBagPanel._
      import javax.swing.ImageIcon

      val img = {
        import java.io.File.separator
        val path = separator+"icons"+separator+"tu.gif"
        try {
          new ImageIcon(Main.resourceFromClassloader(path))
        } catch {
          case e: Exception =>
            Dialog.showMessage(Main.mBar,"Couldn't load image: "+path+"\n \n"+e.toString+"\n")
            Swing.EmptyIcon
        }
      }

      val uri = "http://code.google.com/p/gapt/"
       
      border = Swing.EmptyBorder(10, 10, 10, 10)
      val c = new Constraints
      c.fill = Fill.Horizontal
      c.insets.set(0, 5, 0, 15)
      c.gridheight = 3
      c.ipady = 0
      c.grid = (0,0)
      layout(new Label { icon = img  }) = c
      c.gridheight = 1
      c.insets.set(7, 5, 3, 5)
      c.ipady = 5
      c.grid = (1,0)
      layout(new Label("Version:") { horizontalAlignment = Alignment.Right }) = c
      c.grid = (1,1)
      layout(new Label("Author:") { horizontalAlignment = Alignment.Right }) = c
      c.grid = (1,2)
      layout(new Label("Vendor:") { horizontalAlignment = Alignment.Right }) = c
      c.grid = (2,0)
      layout(new Label("1.0 beta") { horizontalAlignment = Alignment.Left }) = c
      c.grid = (2,1)
      layout(new Label("Mikheil Rukhaia") { horizontalAlignment = Alignment.Left }) = c
      c.grid = (2,2)
      layout(new Label("<html><a href='"+uri+"'>GAPT Framework</a></html>") {
        horizontalAlignment = Alignment.Left
        listenTo(mouse.clicks, mouse.moves)
        reactions += {
          case e: MouseMoved if e.source.eq(this) =>
            this.cursor = new java.awt.Cursor(java.awt.Cursor.HAND_CURSOR)
          case e: MouseClicked if e.source.eq(this) =>
            java.awt.Desktop.getDesktop().browse(new java.net.URI(uri))
            d.close
        }
      }) = c
      c.grid = (2,3)
      c.ipady = 3
      c.insets.set(15, 5, 5, 5)
      layout(new Button(Action("OK") { d.close }) {
      //  border = Swing.MatteBorder(0,140,0,0, background)
        listenTo(keys)
        reactions += {
          case e: KeyPressed if e.key == Key.Enter => this.doClick
        }
      }) = c
    }
    d.open
  }
}