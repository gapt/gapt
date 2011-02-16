package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Oct 27, 2010
 * Time: 12:08:33 PM
 */

import scala.swing._
import BorderPanel._
import event.Key
import at.logic.gui.prooftool.parser._
import at.logic.calculi.lk.base.{SequentOccurrence, Sequent, LKProof}

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
    val e = chooser.showOpenDialog(mBar) match {
      case FileChooser.Result.Cancel =>
      case _ => loadProof(chooser.selectedFile.getPath,12)
    }
  }

  def fExit: Unit = System.exit(0)

  def zoomIn: Unit = {
    val content = body.getContent
    content.fontSize * 3 / 2 match {
      case j: Int if j > 200 =>
      case j: Int => load(content.getData,j)
    }
  }

  def zoomOut: Unit = {
    val content = body.getContent
    content.fontSize / 3 * 2 match {
      case j: Int if j < 10 =>
      case j: Int => load(content.getData,j)
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
    body.contents = new Launcher(proof, 12)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used by startup and open dialog
  def loadProof(path: String, fontSize: Int): Unit = {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    db.fileReader(path)
    val proofs = db.getDB.proofs
    if (proofs.size > 0) body.contents = new Launcher(Some(proofs.head), fontSize)
    else body.contents = new Launcher(None, fontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used by Show Clause List menu
  def loadClauseSet(clListName: String): Unit = {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val clList = db.getDB.sequentLists.find(x => x._1 == clListName)
    body.contents = new Launcher(clList, 12)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used for Zooming
  def load(option: Option[(String, AnyRef)], fontSize: Int): Unit = {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(option, fontSize)
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
    contents += new Menu("Edit") {
      mnemonic = Key.E
      enabled = false
      listenTo(ProofToolPublisher)
      reactions += {
        case ProofLoaded => this.enabled = true
        case ProofUnLoaded => this.enabled = false
      }

      contents += new MenuItem(Action("Compute ClList") { computeClList }) { border = customBorder }
      contents += new MenuItem(Action("TestRefutation") { testRefutation }) { border = customBorder }
      contents += new MenuItem(Action("ShowStruct") { showStruct }) { border = customBorder }
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
        listenTo(ProofToolPublisher)
        reactions += {
          case ProofDbChanged =>
            val l = db.getProofNames
            contents.clear
            for (i <- l) contents += new MenuItem(Action(i) { loadProof(i) }) { border = customBorder }
        }
      }
      contents += new Menu("Show Clause List") {
        mnemonic = Key.C
        border = customBorder
        listenTo(ProofToolPublisher)
        reactions += {
          case ProofDbChanged =>
            val l = db.getClListNames
            contents.clear
            for (i <- l) contents += new MenuItem(Action(i) { loadClauseSet(i) }) { border = customBorder }
        }
      }
    }
    contents += new Menu("Help") {
      mnemonic = Key.H
      contents += new MenuItem(Action("About") { About() }) {
        mnemonic = Key.A
        border = customBorder
      }
    }
  }

  def computeClList = try {
    import at.logic.transformations.skolemization.lksk.LKtoLKskc
    import at.logic.transformations.ceres.struct.StructCreators
    import at.logic.transformations.ceres.clauseSets.StandardClauseSet

    val proof_sk = LKtoLKskc( body.getContent.getData.get._2.asInstanceOf[LKProof] )
    val s = StructCreators.extract( proof_sk )
    val csPre : List[Sequent] = StandardClauseSet.transformStructToClauseSet(s).map(_.getSequent)
    body.contents = new Launcher(Some("cllist",csPre),16)
  } catch {
      case e: AnyRef =>
        val t = e.toString
        Dialog.showMessage(new Label(t),"Couldn't compute ClList!\n\n"+t.replaceAll(",","\n"))
  }

  def showStruct = try {
    import at.logic.transformations.skolemization.lksk.LKtoLKskc
    import at.logic.transformations.ceres.struct.StructCreators

    val proof_sk = LKtoLKskc( body.getContent.getData.get._2.asInstanceOf[LKProof] )
    val s = StructCreators.extract( proof_sk )
    body.contents = new Launcher(Some("Struct",s),12)
  } catch {
      case e: AnyRef =>
        val t = e.toString
        Dialog.showMessage(new Label(t),"Couldn't compute Struct!\n\n"+t.replaceAll(",","\n"))
  }

  def testRefutation = {
    import at.logic.calculi.resolution.andrews._
    import at.logic.calculi.resolution.base.InitialSequent
    import at.logic.language.hol._
    import logicSymbols.ConstantStringSymbol
    import at.logic.calculi.occurrences.PointerFOFactoryInstance

    implicit val factory = PointerFOFactoryInstance
      val a = Atom(ConstantStringSymbol("p"), Nil)
      val s = Sequent(Nil, Neg(Or(a, Neg(a)))::Nil)
      val p0 = InitialSequent[SequentOccurrence](s)
      val p1 = NotT( p0, p0.root.succedent.head )
      val p2 = OrFL( p1, p1.root.antecedent.head )
      val p3 = OrFR( p1, p1.root.antecedent.head )
      val p4 = NotF( p3, p3.root.antecedent.head )
      val p5 = Cut( p4, p2, p4.root.succedent.head, p2.root.antecedent.head )
    body.contents = new Launcher(Some("resolution refutation",p5),16)
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