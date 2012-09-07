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
import swing.Dialog.Message
import swing.Swing.EmptyIcon
import scala.collection.immutable.Seq
import java.io.{BufferedWriter => JBufferedWriter, FileWriter => JFileWriter, File}
import javax.swing.filechooser.FileFilter
import at.logic.algorithms.lk.{cutformulaExtraction, getAuxFormulas, getCutAncestors, replaceSubproof}
import at.logic.algorithms.lksk.eliminateDefinitions
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.base.{FSequent, Sequent, LKProof}
import at.logic.calculi.treeProofs.TreeProof
import at.logic.gui.prooftool.parser._
import at.logic.language.schema.IntVar
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.parsing.calculi.latex.SequentsListLatexExporter
import at.logic.parsing.language.arithmetic.HOLTermArithmeticalExporter
import at.logic.parsing.language.xml.XMLExporter
import at.logic.parsing.writers.FileWriter
import at.logic.transformations.ReductiveCutElim
import at.logic.transformations.skolemization.lksk.LKtoLKskc
import at.logic.transformations.ceres.clauseSets.StandardClauseSet
import at.logic.transformations.ceres.struct.{structToExpressionTree, StructCreators}
import at.logic.transformations.ceres.projections.{DeleteTautology, DeleteRedundantSequents}
import at.logic.transformations.ceres.ProjectionTermCreators
import at.logic.algorithms.shlk.applySchemaSubstitution
import at.logic.utils.ds.trees.Tree
import at.logic.language.hol.HOLFormula

object Main extends SimpleSwingApplication {
  override def startup(args: Array[String]) {
    showFrame
    if (args.length >= 1) loadProof(args(0),12)
  }

  def showFrame {
    val t = top
    t.pack
    t.location = new Point(100,50)
    t.size = new Dimension(700,500)
    t.visible = true
  }

  // Used for displaying things directly from Scala shell
  def display(name: String, obj: AnyRef) {
    showFrame
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(Some(name, obj), 12)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  def fOpen : Unit = chooser.showOpenDialog(mBar) match {
    case FileChooser.Result.Approve => loadProof(chooser.selectedFile.getPath,12)
    case _ =>
  }

  def fSaveProof(tp: AnyRef) : Unit = chooser.showSaveDialog(mBar) match {
    case FileChooser.Result.Approve =>
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      tp match {
        case proof: LKProof => try {
          val result = chooser.selectedFile.getPath
          val path = if (result.endsWith(".xml")) result else result + ".xml"
          XMLExporter(path, "the-proof", proof)
        } catch {
          case e: Throwable => errorMessage("Can't save the proof! \n\n" + getExceptionString(e))
        }
        case _ => infoMessage("This is not a proof, can't save it!")
      }
      body.cursor = java.awt.Cursor.getDefaultCursor
    case _ =>
  }

  def fSaveAll : Unit = chooser.showSaveDialog(mBar) match {
    case FileChooser.Result.Approve => try {
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      val result = chooser.selectedFile.getPath
      val path = if (result.endsWith(".xml")) result else result + ".xml"
      XMLExporter(path, db.getProofDB)
    } catch {
      case e: Throwable => errorMessage("Can't save the database! \n\n" + getExceptionString(e))
    } finally { body.cursor = java.awt.Cursor.getDefaultCursor }
    case _ =>
  }

  def fExportPdf : Unit = chooser.showSaveDialog(mBar) match {
    case FileChooser.Result.Approve => try {
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      import java.io.FileOutputStream
      import com.itextpdf.text.{Document, Rectangle => PdfRectangle}
      import com.itextpdf.text.pdf.PdfWriter

      val component = body.getContent.contents.head
      val width = component.size.width
      val height = component.size.height
      val document = new Document(new PdfRectangle(width, height + 20))
      val result = chooser.selectedFile.getPath
      val path = if (result.endsWith(".pdf")) result else result + ".pdf"
      val writer = PdfWriter.getInstance(document, new FileOutputStream(path))
      document.open
      val content = writer.getDirectContent
      val template = content.createTemplate(width, height)
      val g2 = template.createGraphicsShapes(width, height)
      component.paint(g2)
      g2.dispose
      content.addTemplate(template, 0, 10)
      document.close
    } catch {
        case e: Throwable => errorMessage("Can't export to pdf! \n\n" + getExceptionString(e))
    } finally { body.cursor = java.awt.Cursor.getDefaultCursor }
    case _ =>
  }

  def fExportTPTP : Unit = chooser.showSaveDialog(mBar) match {
    case FileChooser.Result.Approve =>
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      body.getContent.getData.get._2  match {
        case l : List[_] => try {
          val list = l.map( x => x match {
            case s: Sequent => s.toFSequent
            case fs: FSequent => fs
            case _ => throw new Exception("This is not a clause set.")
          })
          val result = chooser.selectedFile.getPath
          val path = if (result.endsWith(".tptp")) result else result + ".tptp"
          val file = new JBufferedWriter(new JFileWriter( path ))
          file.write(at.logic.parsing.language.tptp.TPTPFOLExporter.tptp_problem( list ))
          file.close
        } catch {
            case e: Throwable => errorMessage("Can't export the clause set! \n\n" + getExceptionString(e))
        }
        case _ => infoMessage("This is not a clause set, can't export it!")
      }
      body.cursor = java.awt.Cursor.getDefaultCursor
    case _ =>
  }

  def fExportTeX : Unit = chooser.showSaveDialog(mBar) match {
    case FileChooser.Result.Approve =>
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      body.getContent.getData.get._2  match {
        case l : List[_] => try {
          val list = l.map( x => x match {
            case s: Sequent => s.toFSequent
            case fs: FSequent => fs
            case _ => throw new Exception("This is not a clause set.")
          })
          val result = chooser.selectedFile.getPath
          val path = if (result.endsWith(".tex")) result else result + ".tex"
          (new FileWriter( path ) with SequentsListLatexExporter with HOLTermArithmeticalExporter)
            .exportSequentList( list , Nil).close
        } catch {
            case e: Throwable => errorMessage("Can't export the clause set! \n\n" + getExceptionString(e))
        }
        case _ => infoMessage("This is not a clause set, can't export it!")
      }
      body.cursor = java.awt.Cursor.getDefaultCursor
    case _ =>
  }

  def fExportProofToTex(tp: AnyRef) : Unit = chooser.showSaveDialog(mBar) match {
    case FileChooser.Result.Approve =>
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      tp match {
        case proof: LKProof => try {
          val result = chooser.selectedFile.getPath
          val path = if (result.endsWith(".tex")) result else result + ".tex"
          val file = new JBufferedWriter(new JFileWriter( path ))
          file.write(ProofToLatexExporter(proof))
          file.close
        } catch {
          case e: Throwable => errorMessage("Can't save the proof! \n\n" + getExceptionString(e))
        }
        case _ => infoMessage("This is not a proof, can't save it!")
      }
      body.cursor = java.awt.Cursor.getDefaultCursor
    case _ =>
  }

  def fExit : Unit = System.exit(0)

  def zoomIn {
    val content = body.getContent
    content.fontSize * 3 / 2 match {
      case j: Int if j > 72 =>
      case j: Int => load(content.getData,j)
    }
  }

  def zoomOut {
    val content = body.getContent
    content.fontSize / 3 * 2 match {
      case j: Int if j < 1 =>
      case j: Int => load(content.getData,j)
    }
  }

  def search {
    val input_str = inputMessage("Please enter string to search:", Seq()) match {
      case Some(str) => str
      case _ => ""
    }
    if (! input_str.isEmpty) try {
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      body.getContent.contents.head match {
        case dp: DrawProof =>
          dp.search = input_str
          if (dp.proof.root.isInstanceOf[Sequent]) dp.setColoredOccurrences(Search.inTreeProof(input_str, dp.proof))
          else dp.searchNotInLKProof
          dp.revalidate
        case dt: DrawTree =>
          dt.search = input_str
          dt.revalidate
        case dl: DrawList =>
          dl.search = input_str
          dl.revalidate
        case _ => throw new Exception("Can not search in this object!")
      }
    } catch {
        case e: Throwable => errorMessage(getExceptionString(e))
    } finally {
      body.cursor = java.awt.Cursor.getDefaultCursor
    }
  }

  def top = new MainFrame {
    title = "ProofTool"
    menuBar = mBar
    contents = new BorderPanel {
     // layout(toolbar) = Position.North
      layout(body) = Position.Center
     // layout(new ProgressBar { indeterminate = true }) = Position.South
    }
  }

  // Used for ShowProof menu, loads proof directly
  def loadProof(proof: LKProof) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(Some(proof.name, proof), 14)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used for ShowProof menu
  def loadProof(proof: (String, TreeProof[_])) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(Some(proof), 12)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used by startup and open dialog
  def loadProof(path: String, fontSize: Int) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    db.parseFile(path)
    val proofs = db.getProofs
    if (proofs.size > 0) body.contents = new Launcher(Some(proofs.head), fontSize)
    else if (db.getSequentLists.size > 0)
      body.contents = new Launcher(Some(db.getSequentLists.head), fontSize)
    else body.contents = new Launcher(None, fontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used by View Clause List menu
  def loadClauseSet(clList: (String, List[_])) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(Some(clList), 12)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used by View Struct menu
  def loadStruct(struct: (String, Tree[_])) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(Some(struct), 12)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used for Zooming
  def load(option: Option[(String, AnyRef)], fontSize: Int) {
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
      contents += new MenuItem(Action("Save Proof as XML") { fSaveProof(body.getContent.getData.get._2) }) {
        mnemonic = Key.P
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_P, JActionEvent.CTRL_MASK))
        border = customBorder
      }
      contents += new MenuItem(Action("Save All as XML") { fSaveAll }) {
        mnemonic = Key.S
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_S, JActionEvent.CTRL_MASK))
        border = customBorder
      }
      contents += new Separator
      contents += new MenuItem(Action("Export as PDF") { fExportPdf }) {
        mnemonic = Key.D
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_D, JActionEvent.CTRL_MASK))
        border = customBorder
      }
      contents += new Separator
      contents += new MenuItem(Action("Export Clause Set as TPTP") { fExportTPTP }) {
        mnemonic = Key.T
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_T, JActionEvent.CTRL_MASK))
        border = customBorder
      }
      contents += new MenuItem(Action("Export Clause Set as TeX") { fExportTeX }) {
        mnemonic = Key.E
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_E, JActionEvent.CTRL_MASK))
        border = customBorder
      }
      contents += new MenuItem(Action("Export Proof as TeX") { fExportProofToTex(body.getContent.getData.get._2) }) {
        mnemonic = Key.A
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_A, JActionEvent.CTRL_MASK))
        border = customBorder
      }
      contents += new Separator
      contents += new MenuItem(Action("Exit") { fExit }) {
        mnemonic = Key.X
        border = customBorder
      }
    }
    contents += new Menu("Edit") {
      mnemonic = Key.E

      contents += new MenuItem(Action("Search...") { search }) {
        mnemonic = Key.S
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_F, JActionEvent.CTRL_MASK))
        border = customBorder
      }
      contents += new Separator
      contents += new MenuItem(Action("Show Leaves") { StructPublisher.publish(ShowLeaf) }) {
        border = customBorder
        enabled = false
        listenTo(StructPublisher)
        reactions += {
          case Loaded => this.enabled = true
          case UnLoaded => this.enabled = false
        }
      }
      contents += new MenuItem(Action("Hide Leaves") { StructPublisher.publish(HideLeaf) }) {
        border = customBorder
        enabled = false
        listenTo(StructPublisher)
        reactions += {
          case Loaded => this.enabled = true
          case UnLoaded => this.enabled = false
        }
      }
      contents += new Separator
      contents += new MenuItem(Action("Hide Structural Rules") {
        warningMessage("This feature is under development and might not work properly!")
        ProofToolPublisher.publish(HideStructuralRules)
      }) {
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => this.enabled = true
          case UnLoaded => this.enabled = false
        }
      }
      contents += new MenuItem(Action("Show All Rules") { ProofToolPublisher.publish(ShowAllRules) }) {
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => this.enabled = true
          case UnLoaded => this.enabled = false
        }
      }
      contents += new Separator
      contents += new MenuItem(Action("Hide Sequent Contexts") { hideSequentContext }) {
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => this.enabled = true
          case UnLoaded => this.enabled = false
        }
      }
      contents += new Separator
      contents += new MenuItem(Action("Mark Cut-Ancestors") { markCutAncestors }) {
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => this.enabled = true
          case UnLoaded => this.enabled = false
        }
      }
      contents += new MenuItem(Action("Extract Cut-Formulas") { extractCutFormulas }) {
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => this.enabled = true
          case UnLoaded => this.enabled = false
        }
      }
    }
    contents += new Menu("View") {
      mnemonic = Key.V
      contents += new MenuItem(Action("Zoom In") { zoomIn }) {
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_UP , JActionEvent.ALT_MASK))
        border = customBorder
      }
      contents += new MenuItem(Action("Zoom Out") { zoomOut }) {
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_DOWN, JActionEvent.ALT_MASK))
        border = customBorder
      }
      contents += new Separator
      contents += new Menu("View Proof") {
        MenuScroller.setScrollerFor(this.peer)
        mnemonic = Key.P
        border = customBorder
        listenTo(ProofToolPublisher)
        reactions += {
          case ProofDbChanged =>
            val l = db.getProofs
            contents.clear
            for (i <- l) contents += new MenuItem(Action(i._1) { loadProof(i) }) { border = customBorder }
        }
      }
      contents += new Menu("View Clause List") {
        MenuScroller.setScrollerFor(this.peer)
        mnemonic = Key.C
        border = customBorder
        listenTo(ProofToolPublisher)
        reactions += {
          case ProofDbChanged =>
            val l = db.getSequentLists
            contents.clear
            for (i <- l) contents += new MenuItem(Action(i._1) { loadClauseSet(i) }) { border = customBorder }
        }
      }
      contents += new MenuItem(Action("View Definition List") { loadClauseSet(("Definition List", db.getDefinitions)) }) {
        mnemonic = Key.D
        border = customBorder
      }
      contents += new Menu("View Term Tree") {
        MenuScroller.setScrollerFor(this.peer)
        mnemonic = Key.T
        border = customBorder
        listenTo(ProofToolPublisher)
        reactions += {
          case ProofDbChanged =>
            val l = db.getStructTrees
            contents.clear
            for (i <- l) contents += new MenuItem(Action(i._1) { loadStruct(i) }) { border = customBorder }
        }
      }
    }
    contents += new Menu("LK Proof") {
      mnemonic = Key.L
      enabled = false
      listenTo(ProofToolPublisher)
      reactions += {
        case Loaded => enabled = true
        case UnLoaded => enabled = false
      }
      contents += new Menu("Compute Clause Set") {
        contents += new MenuItem(Action("All Cuts") { computeClList }) { border = customBorder }
        contents += new MenuItem(Action("Only Quantified Cuts") { computeClListOnlyQuantifiedCuts }) { border = customBorder }
      }
      contents += new Menu("Compute Struct") {
        contents += new MenuItem(Action("All Cuts") { showStruct }) { border = customBorder }
        contents += new MenuItem(Action("Only Quantified Cuts") { showStructOnlyQuantifiedCuts }) { border = customBorder }
      }
      contents += new Separator
      contents += new MenuItem(Action("Apply Gentzen's Method") { gentzen(body.getContent.getData.get._2.asInstanceOf[LKProof]) }) { border = customBorder }
      contents += new Separator
      contents += new MenuItem(Action("Eliminate Definitions") { eliminateDefsLK }) { border = customBorder }
    }
    contents += new Menu("LKS Proof") {
      mnemonic = Key.P
      enabled = false
      listenTo(ProofToolPublisher)
      reactions += {
        case Loaded => enabled = true
        case UnLoaded => enabled = false
      }
      contents += new MenuItem(Action("Compute Clause Set") { computeSchematicClauseSet }) { border = customBorder }
      contents += new MenuItem(Action("Compute Struct") { computeSchematicStruct }) { border = customBorder }
      contents += new MenuItem(Action("Compute Projection Term") { computeSchematicProjectionTerm }) { border = customBorder }
      contents += new MenuItem(Action("Compute Proof Instance") { computeProofInstance } )  { border = customBorder }
    }
    contents += new Menu("Help") {
      mnemonic = Key.H
      contents += new MenuItem(Action("About") { About() }) {
        mnemonic = Key.A
        border = customBorder
      }
    }
    contents += new Menu("Tests") {
      mnemonic = Key.T
      contents += new MenuItem(Action("Pruned Clause Set of Adder") { testSchematicClauseSet }) { border = customBorder }
    }
  }

  def extractCutFormulas : Unit = try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val list = cutformulaExtraction( body.getContent.getData.get._2.asInstanceOf[LKProof] )
    db.addSeqList("cutFormulaList ", list.map(x => x.toFSequent) )
    body.contents = new Launcher(Some("Cut-formula List",list),16)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't extract CutFormula List!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged)

  def computeClList : Unit = try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof_sk = LKtoLKskc( body.getContent.getData.get._2.asInstanceOf[LKProof] )
    val s = StructCreators.extract( proof_sk )
    val csPre : List[Sequent] = DeleteRedundantSequents( DeleteTautology( StandardClauseSet.transformStructToClauseSet(s) ))

    db.addSeqList(csPre.map(x => x.toFSequent))
    body.contents = new Launcher(Some("cllist",csPre),16)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't compute ClList!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged)

  def computeSchematicClauseSet : Unit = try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val n = IntVar(new VariableStringSymbol("n"))

    val s = StructCreators.extractStruct( body.getContent.getData.get._1, n)
    val cs : List[Sequent] = DeleteRedundantSequents( DeleteTautology( StandardClauseSet.transformStructToClauseSet(s) ))

    db.addSeqList(cs.map(x => x.toFSequent))
    body.contents = new Launcher(Some("Schematic Clause Set",cs),16)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't compute clause set!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged)

  def computeSchematicStruct : Unit = try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val n = IntVar(new VariableStringSymbol("n"))
    val s = structToExpressionTree.prunedTree( StructCreators.extractStruct( body.getContent.getData.get._1, n) )
    db.addStructTree( s )
    body.contents = new Launcher(Some("Schematic Struct",s),12)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't compute Struct!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged)

  def computeSchematicProjectionTerm : Unit = try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof_name = body.getContent.getData.get._1
    val pterms = ProjectionTermCreators(proof_name)
    db.addTrees( pterms )
    body.contents = new Launcher(Some( pterms.head ),12)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't compute Projection Terms!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged)

  def computeClListOnlyQuantifiedCuts : Unit = try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof_sk = eliminateDefinitions(LKtoLKskc( body.getContent.getData.get._2.asInstanceOf[LKProof] ))
    val s = StructCreators.extract( proof_sk, f => f.containsQuantifier )
    val csPre : List[Sequent] = DeleteRedundantSequents( DeleteTautology( StandardClauseSet.transformStructToClauseSet(s) ))
    db.addSeqList(csPre.map(x => x.toFSequent))
    body.contents = new Launcher(Some("cllist",csPre),16)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't compute clause list!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged)

  def showStruct : Unit = try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof_sk = LKtoLKskc( body.getContent.getData.get._2.asInstanceOf[LKProof] )
    val s = structToExpressionTree.prunedTree( StructCreators.extract( proof_sk ) )
    db.addStructTree( s )
    body.contents = new Launcher(Some("Struct",s),12)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't compute Struct!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged)

  // Computes the struct, ignoring propositional cuts
  def showStructOnlyQuantifiedCuts : Unit = try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof_sk = eliminateDefinitions( LKtoLKskc( body.getContent.getData.get._2.asInstanceOf[LKProof] ) )
    val s = structToExpressionTree.prunedTree( StructCreators.extract( proof_sk, f => f.containsQuantifier ) )
    db.addStructTree( s )
    body.contents = new Launcher(Some("Struct",s),12)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't compute Struct!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged)

  def eliminateDefsLK : Unit = try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val pair = body.getContent.getData.get
    val new_proof = eliminateDefinitions( pair._2.asInstanceOf[LKProof]   )
    db.addProofs((pair._1+" without def rules", new_proof)::Nil)
    body.contents = new Launcher(Some("Proof without Definitions",new_proof),14)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't eliminate definitions!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged)

  def eliminateDefsLKsk : Unit = try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val pair = body.getContent.getData.get
    val new_proof = eliminateDefinitions( LKtoLKskc( pair._2.asInstanceOf[LKProof] )  )
    db.addProofs((pair._1+" without def rules", new_proof)::Nil)
    body.contents = new Launcher(Some("Proof without Definitions",new_proof),14)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't eliminate definitions!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged)

  def gentzen(proof: LKProof) : Unit = try {
    val steps = questionMessage("Do you want to see intermediary steps?") match {
      case Dialog.Result.Yes => true
      case _ => false
    }
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val newSubproof = ReductiveCutElim(proof, steps)
    val oldProof = body.getContent.getData.get._2.asInstanceOf[LKProof]
    val newProof = replaceSubproof(oldProof, proof, newSubproof)
    if (newProof != newSubproof) ReductiveCutElim.proofs = ReductiveCutElim.proofs ::: (newProof::Nil)
    body.contents = new Launcher(Some("Gentzen Result:", newProof),14)
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't eliminate all cuts!\n\n" + getExceptionString(e))
  } finally {
    db.addProofs(ReductiveCutElim.proofs.map(x => (x.name, x)))
    body.cursor = java.awt.Cursor.getDefaultCursor
    ProofToolPublisher.publish(ProofDbChanged)
  }

  def markCutAncestors {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.getContent.contents.head match {
      case dp: DrawProof => body.getContent.getData match {
        case Some((_, proof : LKProof) ) =>
          dp.setColoredOccurrences(getCutAncestors(proof))
          dp.revalidate
        case _ => errorMessage("This is not an LK proof!")
      }
      case _ => errorMessage("LK proof not found!")
    }
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  def hideSequentContext {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.getContent.contents.head match {
      case dp: DrawProof => body.getContent.getData match {
        case Some((name, proof : LKProof) ) =>
          dp.setVisibleOccurrences(getAuxFormulas(proof))
          dp.revalidate
        case _ => errorMessage("This is not an LK proof!")
      }
      case _ => errorMessage("LK proof not found!")
    }
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  def computeProofInstance {
    val input = inputMessage("Please enter number of the instance:", Seq()) match {
      case Some(str) => str.replaceAll("""[a-z,A-Z]*""","")
      case _ => ""
    }
    if (! input.isEmpty) try {
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      val number = if (input.size > 10) input.dropRight(10).toInt else input.toInt
      val name = body.getContent.getData.get._1
      val proof = applySchemaSubstitution(name, number)
      db.addProofs((name + "_" + number, proof)::Nil)
      body.contents = new Launcher(Some(name + "_" + number, proof), 12)
      body.cursor = java.awt.Cursor.getDefaultCursor
      ProofToolPublisher.publish(ProofDbChanged)
    } catch {
      case e: Throwable =>
        errorMessage("Could not construct proof instance!\n\n" + getExceptionString(e))
    }
  }

  def testSchematicClauseSet : Unit = try {
    import at.logic.transformations.ceres.struct._
    import at.logic.language.schema._
    import at.logic.utils.ds.Multisets.HashMultiset

      val n = IntVar(new VariableStringSymbol("n"))

      val s = StructCreators.extractStruct( "\\psi", n)
      val cs : List[Sequent] = DeleteRedundantSequents( DeleteTautology( StandardClauseSet.transformStructToClauseSet(s) ))

      val m_empty = HashMultiset[HOLFormula]()
      var cc: at.logic.transformations.ceres.struct.TypeSynonyms.CutConfiguration = (m_empty, m_empty)

      val cs_pruned_psi = cs.filter( s => s.antecedent.isEmpty || s.antecedent.exists( fo => fo.formula match {
      case IndexedPredicate(pred, _) => pred.name match {
        case sym : ClauseSetSymbol => sym.cut_occs == cc && sym.name == "\\psi"
        case _ => false
      }
      case _ => false
    } ) )

      cs_pruned_psi.foreach( s => s.succedent.foreach( fo => fo.formula match {
      case IndexedPredicate(pred, _) => pred.name match {
        case sym : ClauseSetSymbol if sym.name == "\\varphi" => cc = sym.cut_occs
        case _ => false
      }
      case _ => false
    } ))

      val cs_pruned_varphi = cs.filter( s => s.antecedent.exists( fo => fo.formula match {
      case IndexedPredicate(pred, _) => pred.name match {
        case sym : ClauseSetSymbol => sym.cut_occs == cc
        case _ => false
      }
      case _ => false
    } ) )

       cs_pruned_varphi.foreach( s => s.succedent.foreach( fo => fo.formula match {
      case IndexedPredicate(pred, _) => pred.name match {
        case sym : ClauseSetSymbol if sym.name == "\\phi" => cc = sym.cut_occs
        case _ => false
      }
      case _ => false
    } ))

       val cs_pruned_phi = cs.filter( s => s.antecedent.exists( fo => fo.formula match {
      case IndexedPredicate(pred, _) => pred.name match {
        case sym : ClauseSetSymbol => sym.cut_occs == cc
        case _ => false
      }
      case _ => false
    } ) )

      cs_pruned_psi.foreach( s => s.succedent.foreach( fo => fo.formula match {
      case IndexedPredicate(pred, _) => pred.name match {
        case sym : ClauseSetSymbol if sym.name == "\\chi" => cc = sym.cut_occs
        case _ => false
      }
      case _ => false
    } ))

      val cs_pruned_chi = cs.filter( s => s.antecedent.exists( fo => fo.formula match {
      case IndexedPredicate(pred, _) => pred.name match {
        case sym : ClauseSetSymbol => sym.cut_occs == cc
        case _ => false
      }
      case _ => false
    } ) )

      val ccs = cs_pruned_psi ::: cs_pruned_varphi ::: cs_pruned_phi ::: cs_pruned_chi

    db.addSeqList(ccs.map(x => x.toFSequent))
    body.contents = new Launcher(Some("cllist",ccs),16)

  } catch {
      case e: Throwable =>
        errorMessage("Couldn't compute clause list!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged)

  def inputMessage(message: String, values: Seq[String]) =
    Dialog.showInput[String](body, message, "ProofTool Input", Dialog.Message.Plain, EmptyIcon, values,
      if (values.isEmpty) "" else values.head)

  def infoMessage(info: String) {
    Dialog.showMessage(body, info, "ProofTool Information")
  }

  def warningMessage(warning: String) {
    Dialog.showMessage(body, warning, "ProofTool Warning", Dialog.Message.Warning)
  }

  def errorMessage(error: String) {
    Dialog.showMessage(body, error, "ProofTool Error", Dialog.Message.Error)
  }

  def questionMessage(question: String) =
    Dialog.showConfirmation(body, question, "ProofTool Question", Dialog.Options.YesNo, Message.Question)

  def getExceptionString(e: Throwable) = {
    val st = e.toString.replaceAll(",",",\n") + "\n"
    val trace = e.getStackTrace
    if (trace.length > 10)
      Range(0,10).map(i => trace.apply(i)).foldLeft(st)((s, x) => s + "\n   at " + x.toString) + "\n   ......."
    else e.getStackTraceString
  }

  val body = new MyScrollPane
  val db = new FileParser
  private val chooser = new FileChooser {
    fileFilter = new FileFilter {
      def accept(f: File): Boolean = {
        if (f.getName.endsWith(".gz") || f.isDirectory) true
        else false
      }

      def getDescription: String = ".gz"
    }

    fileFilter = new FileFilter {
      def accept(f: File): Boolean = {
        if (f.getName.endsWith(".lks") || f.isDirectory) true
        else false
      }

      def getDescription: String = ".lks"
    }

    fileFilter = new FileFilter {
      def accept(f: File): Boolean = {
        if (f.getName.endsWith(".pdf") || f.isDirectory) true
        else false
      }

      def getDescription: String = ".pdf"
    }

    fileFilter = new FileFilter {
      def accept(f: File): Boolean = {
        if (f.getName.endsWith(".tex") || f.isDirectory) true
        else false
      }

      def getDescription: String = ".tex"
    }

    fileFilter = new FileFilter {
      def accept(f: File): Boolean = {
        if (f.getName.endsWith(".tptp") || f.isDirectory) true
        else false
      }

      def getDescription: String = ".tptp"
    }

    fileFilter = new FileFilter {
      def accept(f: File): Boolean = {
        if (f.getName.endsWith(".xml") || f.isDirectory) true
        else false
      }

      def getDescription: String = ".xml"
    }

    fileFilter = acceptAllFileFilter
  }

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