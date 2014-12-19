package at.logic.gui.prooftool.gui

/**
 * Created with IntelliJ IDEA.
 * User: mrukhaia
 * Date: 10/23/12
 * Time: 12:38 PM
 */

import swing._
import java.awt.{Dimension, Point}
import swing.event._
import swing.GridBagPanel.Fill
import javax.swing.SpinnerNumberModel


object RGBColorChooser extends Dialog {
  resizable = false
  modal = true
  peer.setUndecorated(true)
  peer.setDefaultCloseOperation(2) //DISPOSE_ON_CLOSE

  private val red = new Spinner[Int](new SpinnerNumberModel(255, 0, 255, 1))
  private val green = new Spinner[Int](new SpinnerNumberModel(255, 0, 255, 1))
  private val blue = new Spinner[Int](new SpinnerNumberModel(255, 0, 255, 1))
  private var optionColor: Option[Color] = Some(new Color(255,255,255))

  private val CancelButton = new Button(Action("Cancel") {
    optionColor = None
    dispose()
  })
  private val OKButton = new Button(Action("OK") {
    optionColor = Some(new Color(red.value,green.value,blue.value))
    dispose()
  }) {
    listenTo(keys)
    reactions += {
      case e: KeyPressed if e.key == Key.Enter => doClick()
    }
  }

  contents = new GridBagPanel {
    border = Swing.EmptyBorder(10, 10, 10, 10)

    private val coloredArea = new Label("") {
      background = new Color(red.value,green.value,blue.value)
      preferredSize = new Dimension(100,80)
      opaque = true
      listenTo(red,green,blue)
      reactions += {
        case e: ValueChanged =>
          background = new Color(red.value,green.value,blue.value)
      }
    }

    private val c = new Constraints
    c.fill = Fill.Horizontal
    c.insets.set(5, 5, 5, 5)
    c.gridheight = 3
    c.grid = (0,0)
    layout(coloredArea) = c
    c.gridheight = 1
    c.grid = (1,0)
    layout(new Label("Red:") { horizontalAlignment = Alignment.Right }) = c
    c.grid = (1,1)
    layout(new Label("Green:") { horizontalAlignment = Alignment.Right }) = c
    c.grid = (1,2)
    layout(new Label("Blue:") { horizontalAlignment = Alignment.Right }) = c
    c.grid = (2,0)
    layout(red) = c
    c.grid = (2,1)
    layout(green) = c
    c.grid = (2,2)
    layout(blue) = c
    c.grid = (0,3)
    layout(CancelButton) = c
    c.gridwidth = 2
    c.grid = (1,3)
    layout(OKButton) = c
  }
  defaultButton = OKButton

  def apply(c: Component, x: Int, y: Int): Option[Color] = {
    val point = c.locationOnScreen
    location = new Point(point.x + x, point.y + y)
    open() // This trick works only if the Dialog is modal.
    optionColor
  }

  def color = optionColor
}