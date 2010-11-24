package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Oct 27, 2010
 * Time: 12:08:33 PM
 */

import scala.swing._
import event._
import at.logic.gui.prooftool.parser.FileParser._

object Main extends SimpleGUIApplication {
  override def main(args: Array[String]) = run {
    val t = top
    t.pack
    t.location = new Point(100,50)
    t.size = new Dimension(700,500)
    t.visible = true
    if (args.length >= 1) body.contents = new Launcher(fileReader(args(0)),12)
  }

  def fOpen: Unit = {
    import FileChooser._
    val chooser = new FileChooser
    val e = chooser.showOpenDialog(mBar) match {
      case Result.Cancel =>
      case _ => body.contents = new Launcher(fileReader(chooser.selectedFile.getPath),12)
    }
  }

  def fExit: Unit = System.exit(0)

  def zoomIn: Unit = {
    val content = body.getContent
    val i = content.fontSize*2 match {
      case j: Int if j > 200 => 200
      case _ => content.fontSize*2
    }
    body.contents = new Launcher(content.text,i)
  }

  def zoomOut: Unit = {
    val content = body.getContent
    val i = content.fontSize/2 match {
      case j: Int if j<10 => 10
      case _ => content.fontSize/2
    }
    body.contents = new Launcher(content.text,i)
  }

  def top = new MainFrame {
    title = "ProofTool"
    menuBar = mBar
    contents = new BorderPanel {
      import BorderPanel._
     // layout(toolbar) = Position.North
      layout(body) = Position.Center
    }
  }

  val mBar: MenuBar = new MenuBar() {
    val bd = Swing.EmptyBorder(5,3,5,3)
    contents += new Menu("File") {
      contents += new MenuItem(Action("Open...") { fOpen }) { border = bd }
      contents += new Separator
      contents += new MenuItem(Action("Exit") { fExit }) { border = bd }
    }
    contents += new Menu("View") {
      contents += new MenuItem(Action("Zoom In") { zoomIn }) { border = bd }
      contents += new MenuItem(Action("Zoom Out") { zoomOut }) { border = bd }
      contents += new Separator
      contents += new Menu("Show Proof") {
        border = bd
        listenTo(proofDbChanged)
        reactions += {
          case ValueChanged(_) =>
            val l = getProofNames
            contents.clear
            for (i <- l) contents += new MenuItem(Action(i) { }) { border = bd }
        }
      }
      contents += new MenuItem(Action("Show Clause Set") {}) { border = bd }
    }
    contents += new Menu("Help") {
      contents += new MenuItem(Action("About") { About.open }) { border = bd }
    }
  }

  val body = new MyScrollPane(new Launcher("",12))

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