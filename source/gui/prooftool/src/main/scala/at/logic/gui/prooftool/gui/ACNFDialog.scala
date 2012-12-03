package at.logic.gui.prooftool.gui

/**
 * Created with IntelliJ IDEA.
 * User: mrukhaia
 * Date: 12/3/12
 * Time: 2:37 PM
 */

import swing._
import java.awt.Point
import swing.GridBagPanel.Fill
import javax.swing.SpinnerNumberModel

object ACNFDialog extends Dialog {
  title = "ACNF Dialog"
  resizable = false
  modal = true
  location = new Point(Main.top.location.x + 200,Main.top.location.y + 100)
  peer.setDefaultCloseOperation(2) //DISPOSE_ON_CLOSE

  def apply(proofs: Seq[String], refutations: Seq[String]): Option[(String,String,Int)] = {
    var optionResult: Option[(String,String,Int)] = None
    val proof = new ComboBox[String](proofs)
    val refutation = new ComboBox[String](refutations)
    val instance = new Spinner[Int](new SpinnerNumberModel(0, 0, 1000, 1))
    val CancelButton = new Button(Action("Cancel") {
      optionResult = None
      dispose()
    })
    val OKButton = new Button(Action("OK") {
      optionResult = Some((proof.item, refutation.item, instance.value))
      dispose()
    })

    contents = new GridBagPanel {
      border = Swing.EmptyBorder(10)
      val c = new Constraints
      c.fill = Fill.Horizontal
      c.insets.set(7, 5, 3, 5)
      c.ipady = 5
      c.grid = (0,0)
      layout(new Label("Proof Schema name:") { horizontalAlignment = Alignment.Left }) = c
      c.grid = (0,1)
      layout(new Label("Resolution Schema name:") { horizontalAlignment = Alignment.Left }) = c
      c.grid = (0,2)
      layout(new Label("The ACNF instance:") { horizontalAlignment = Alignment.Left }) = c
      c.grid = (1,0)
      layout(proof) = c
      c.grid = (1,1)
      layout(refutation) = c
      c.grid = (1,2)
      layout(instance) = c
      c.grid = (1,3)
      layout(new BoxPanel(Orientation.Horizontal) {
        contents += CancelButton
        contents += Swing.HStrut(10)
        contents += OKButton
      }) = c
    }

    open() // This trick works only if the Dialog is modal.
    optionResult
  }
}
