package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Oct 27, 2010
 * Time: 12:08:33 PM
 */

import scala.swing._
import event._
import at.logic.gui.prooftool.parser._
import BorderPanel._
import at.logic.calculi.lk.base.LKProof

object Main extends SimpleSwingApplication {
  override def startup(args: Array[String]) = {
    val t = top
    t.pack
    t.location = new Point(100,50)
    t.size = new Dimension(700,500)
    t.visible = true
    if (args.length >= 1) loadProof(args(0),12)
  }

  def fOpen: Unit = {
    import FileChooser._
    val e = chooser.showOpenDialog(mBar) match {
      case Result.Cancel =>
      case _ => loadProof(chooser.selectedFile.getPath,12)
    }
  }

  def fExit: Unit = System.exit(0)

  def zoomIn: Unit = {
    val content = body.getContent
    content.fontSize * 3 / 2 match {
      case j: Int if j > 200 =>
      case j: Int => loadProof(content.proof,j)
    }
  }

  def zoomOut: Unit = {
    val content = body.getContent
    content.fontSize / 3 * 2 match {
      case j: Int if j < 10 =>
      case j: Int => loadProof(content.proof,j)
    }
  }

  def top = new MainFrame {
    title = "ProofTool"
    menuBar = mBar
    contents = new BorderPanel {
     // layout(toolbar) = Position.North
      layout(body) = Position.Center
    }
  }

  // Used for ShowProof menu
  def loadProof(proofName: String): Unit = {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof = db.getDB.proofs.find(x => x._1 == proofName)
    body.contents = new Launcher(proof.get._2, 12)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used for Zooming
  def loadProof(proof: LKProof, fontSize: Int): Unit = {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(proof, fontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used by startup and open dialog
  def loadProof(path: String, fontSize: Int): Unit = {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof = db.fileReader(path)
    body.contents = new Launcher(proof, fontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  val mBar: MenuBar = new MenuBar() {
    import javax.swing.KeyStroke
    import java.awt.event.{KeyEvent, ActionEvent => JActionEvent}

    focusable = true
    val customBorder = Swing.EmptyBorder(5,3,5,3)
    contents += new Menu("File") {
      mnemonic = Key.F
      contents += new MenuItem(Action("Open...") { fOpen }) {
        mnemonic = Key.O
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_O, JActionEvent.CTRL_MASK))
        border = customBorder
      }
      contents += new Separator
      contents += new MenuItem(Action("Exit") { fExit }) {
        mnemonic = Key.E
        border = customBorder
      }
    }
    contents += new Menu("View") {
      mnemonic = Key.V
      contents += new MenuItem(Action("Zoom In") { zoomIn }) {
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_PAGE_UP, JActionEvent.ALT_MASK))
        border = customBorder
      }
      contents += new MenuItem(Action("Zoom Out") { zoomOut }) {
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_PAGE_DOWN, JActionEvent.ALT_MASK))
        border = customBorder
      }
      contents += new Separator
      contents += new Menu("Show Proof") {
        mnemonic = Key.P
        border = customBorder
        listenTo(proofDbChanged)
        reactions += {
          case e: ValueChanged  =>
            val l = db.getProofNames
            contents.clear
            for (i <- l) contents += new MenuItem(Action(i) { loadProof(i) }) { border = customBorder }
        }
      }
      contents += new MenuItem(Action("Show Clause Set") {}) {
        mnemonic = Key.C
        border = customBorder
      }
    }
    contents += new Menu("Help") {
      mnemonic = Key.H
      contents += new MenuItem(Action("About") { About.open }) {
        mnemonic = Key.A
        border = customBorder
      }
    }
  }

  val body = new MyScrollPane
  val db = new FileParser
  private val chooser = new FileChooser

  /*
  val toolbar = new BoxPanel(Orientation.Horizontal) {
    val tmp = new ButtonGroup
    val lens = new ToggleButton("Lens") {
    //  icon = new ImageIcon("../tu.gif")
      size = new Dimension(30,10)
    }
    val zIn = new Button(Action("Zoom In") { zoomIn })
    val zOut = new Button(Action("Zoom Out") { zoomOut })
    tmp.buttons ++= List(lens, zIn, zOut)
    contents ++= tmp.buttons
    border = Swing.EmptyBorder(0,0,0,0)
  }
  */
}