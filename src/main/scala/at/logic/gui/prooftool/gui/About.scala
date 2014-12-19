package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Nov 16, 2010
 * Time: 2:32:34 PM
 */

import scala.swing._
import event._
import java.awt.Point

object About {
  private lazy val d = new Dialog {
    title = "About Prooftool"
    resizable = false
    modal = true
    location = new Point(Main.top.location.x + 100,Main.top.location.y + 100)
    //setLocationRelativeTo(Main.mBar)
    peer.setDefaultCloseOperation(2) //DISPOSE_ON_CLOSE

    defaultButton = new Button(Action("OK") { dispose() }) {
      //  border = Swing.MatteBorder(0,140,0,0, background)
      listenTo(keys)
      reactions += {
        case e: KeyPressed if e.key == Key.Enter => doClick()
      }
    }

    contents = new GridBagPanel { grid =>
      import GridBagPanel._
      import javax.swing.ImageIcon

      val img = {
        val path = "icons/tu.gif"
        try {
          new ImageIcon(Main.getClass.getClassLoader.getResource(path))
        } catch {
          case e: Exception =>
            Main.errorMessage("Couldn't load image: "+path+"\n\n"+Main.getExceptionString(e))
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
      layout(new Label(Main.getClass.getPackage.getImplementationVersion) { horizontalAlignment = Alignment.Left }) = c
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
            java.awt.Desktop.getDesktop.browse(new java.net.URI(uri))
            dispose()
        }
      }) = c
      c.grid = (2,3)
      c.ipady = 3
      c.insets.set(15, 5, 5, 5)
      layout(defaultButton.get) = c
    }
  }

  def apply() { d.open() }
}