package at.logic.gui.prooftool.gui

/**
 * Created with IntelliJ IDEA.
 * User: mrukhaia
 * Date: 10/23/12
 * Time: 12:29 PM
 */

import swing.{Swing, Component, Label, ScrollPane}
import java.awt.Color
import javax.swing.{JSpinner, SpinnerModel}
import swing.event.ValueChanged
import java.awt.event.FocusAdapter

// This component is used in Launcher
class MyScrollPane extends ScrollPane {
  background = new Color(255,255,255)

  peer.getVerticalScrollBar.setUnitIncrement( 20 )
  peer.getHorizontalScrollBar.setUnitIncrement( 20 )

  def getContent: Launcher = contents.last.asInstanceOf[Launcher]
  //  def content_=(c : Component) { viewportView = c }
  //  def content = viewportView.get.asInstanceOf[Launcher]
}

// This component is used in DrawExpansionTree
class MyLabel extends Label {
  private var varBackgroundColor = Color.cyan
  def backgroundColor = varBackgroundColor
  def backgroundColor_=(c: Color) { varBackgroundColor = c }
}

// This component is used in RGBColorChooser
class Spinner[T](model: SpinnerModel) extends Component {
  override lazy val peer: JSpinner = new JSpinner(model) with SuperMixin

  def value = peer.getValue.asInstanceOf[T]
  def value_=(a: T) { peer.setValue(a) }

  private lazy val changeListener = Swing.ChangeListener { e =>
    publish(new ValueChanged(Spinner.this))
  }

  protected override def onFirstSubscribe() {
    super.onFirstSubscribe()
    peer.addChangeListener(changeListener)
    peer.addFocusListener(new FocusAdapter {
      override def focusLost(e: java.awt.event.FocusEvent) { publish(new ValueChanged(Spinner.this)) }
    })
  }

  protected override def onLastUnsubscribe() {
    super.onLastUnsubscribe()
    peer.removeChangeListener(changeListener)
  }
}
