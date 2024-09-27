package gapt.prooftool

import scala.swing._
import java.awt.Color

import javax.swing.{JComponent, JSpinner, KeyStroke, SpinnerModel}

import scala.swing.event._
import java.awt.event.{FocusAdapter, KeyEvent, MouseEvent, MouseMotionListener}
import java.awt.Font._

import scala.swing.BorderPanel.Position

/**
 * The main scrollpane used in ProofTool
 */
class PTScrollPane extends ScrollPane {
  background = new Color(255, 255, 255)

  peer.getVerticalScrollBar.setUnitIncrement(20)
  peer.getHorizontalScrollBar.setUnitIncrement(20)

  private var contentPanel_ : Option[PTContentPanel] = None

  def contentPanel = contentPanel_.get

  def contentPanel_=(cp: PTContentPanel) = {
    contentPanel_ = Some(cp)
    contents = cp
  }
  //  def content_=(c : Component) { viewportView = c }
  //  def content = viewportView.get.asInstanceOf[Launcher]

  for (
    (key, act) <- Seq(
      KeyEvent.VK_DOWN -> "positiveUnitIncrement",
      KeyEvent.VK_UP -> "negativeUnitIncrement"
    )
  ) peer.getVerticalScrollBar.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW).put(KeyStroke.getKeyStroke(key, 0), act)

  for (
    (key, act) <- Seq(
      KeyEvent.VK_RIGHT -> "positiveUnitIncrement",
      KeyEvent.VK_LEFT -> "negativeUnitIncrement"
    )
  ) peer.getHorizontalScrollBar.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW).put(KeyStroke.getKeyStroke(key, 0), act)
}

/**
 * The panel containing the actual content of a ProofTool window.
 * @param main The main window that this belongs to.
 * @param str
 * @param content An object that displays some content, e.g., a DrawSequentProof
 */
class PTContentPanel(
    val main: ProofToolViewer[_],
    val str: String,
    val content: Component
) extends BorderPanel with MouseMotionListener {
  val niceName: String = str match {
    case s: String if s == "\\psi" || s == "psi"       => "ψ"
    case s: String if s == "\\chi" || s == "chi"       => "χ"
    case s: String if s == "\\varphi" || s == "varphi" => "φ"
    case s: String if s == "\\phi" || s == "phi"       => "ϕ"
    case s: String if s == "\\rho" || s == "rho"       => "ρ"
    case s: String if s == "\\sigma" || s == "sigma"   => "σ"
    case s: String if s == "\\tau" || s == "tau"       => "τ"
    case s: String if s == "\\omega" || s == "omega"   => "Ω"
    case _                                             => str
  }

  val bd = Swing.TitledBorder(Swing.LineBorder(new Color(0, 0, 0), 2), " " + niceName + " ")
  bd.setTitleFont(new Font(SERIF, BOLD, 16))
  border = Swing.CompoundBorder(bd, Swing.EmptyBorder(15))

  background = new Color(255, 255, 255)

  layout(content) = Position.Center

  listenTo(mouse.moves, mouse.clicks, mouse.wheel)
  reactions += {
    case e: MouseDragged =>
      main.mainPanel.cursor = new java.awt.Cursor(java.awt.Cursor.MOVE_CURSOR)
    case e: MouseReleased =>
      main.mainPanel.cursor = java.awt.Cursor.getDefaultCursor
    case e: MouseWheelMoved =>
      main.mainPanel.peer.dispatchEvent(e.peer)
  }

  this.peer.setAutoscrolls(true)
  this.peer.addMouseMotionListener(this)

  def mouseMoved(e: MouseEvent): Unit = {
    // println("mouse: " + e.getX + "/" + e.getY)
  }
  def mouseDragged(e: MouseEvent): Unit = {
    // The user is dragging us, so scroll!
    val r = new Rectangle(e.getX, e.getY, 1, 1)
    this.peer.scrollRectToVisible(r)
  }
}

// This component is used in RGBColorChooser
class Spinner[T](model: SpinnerModel) extends Component {
  override lazy val peer: JSpinner = new JSpinner(model) with SuperMixin

  def value = peer.getValue.asInstanceOf[T]
  def value_=(a: T): Unit = { peer.setValue(a) }

  private lazy val changeListener = Swing.ChangeListener { e =>
    publish(new ValueChanged(Spinner.this))
  }

  protected override def onFirstSubscribe(): Unit = {
    super.onFirstSubscribe()
    peer.addChangeListener(changeListener)
    peer.addFocusListener(new FocusAdapter {
      override def focusLost(e: java.awt.event.FocusEvent): Unit = { publish(new ValueChanged(Spinner.this)) }
    })
  }

  protected override def onLastUnsubscribe(): Unit = {
    super.onLastUnsubscribe()
    peer.removeChangeListener(changeListener)
  }
}
