package at.logic.gui.prooftool.gui

/**
 * Created with IntelliJ IDEA.
 * User: mrukhaia
 * Date: 11/19/12
 * Time: 12:12 PM
 */

import swing._
import BorderPanel.Position

object TextAreaDialog extends Dialog {
  title = "ProofTool Text"
  modal = true
  location = new Point(Main.top.location.x + 200,Main.top.location.y + 100)
  peer.setDefaultCloseOperation(2) //DISPOSE_ON_CLOSE

  private var optionText: Option[String] = None
  private val titleLabel = new Label {
    border = Swing.EmptyBorder(0,0,10,0)
    horizontalAlignment = Alignment.Left
  }
  private val textArea = new TextArea
  private val CancelButton = new Button(Action("Cancel") {
    optionText = None
    dispose()
  })
  private val OKButton = new Button(Action("Parse") {
    optionText = Some(textArea.text)
    dispose()
  })

  contents = new BorderPanel {
    border = Swing.EmptyBorder(10)
    layout(titleLabel) = Position.North
    layout(new ScrollPane(textArea) { preferredSize = new Dimension(400,500) }) = Position.Center
    layout(new BoxPanel(Orientation.Horizontal) {
      border = Swing.EmptyBorder(10,0,0,0)
      contents += CancelButton
      contents += Swing.HStrut(10)
      contents += OKButton
    }) = Position.South
  }

  def apply(title: String): Option[String] = {
    if (titleLabel.text != title) {
      titleLabel.text = title
      textArea.text = ""
    }
    open() // This trick works only if the Dialog is modal.
    optionText
  }

  def text = optionText
}
