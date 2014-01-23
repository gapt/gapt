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
import java.io.{BufferedWriter => JBufferedWriter, FileWriter => JFileWriter, ByteArrayInputStream, InputStreamReader, File}
import javax.swing.filechooser.FileFilter
import javax.swing.SwingUtilities
import at.logic.algorithms.lk._
import at.logic.algorithms.lksk.eliminateDefinitions
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.base.{Sequent, LKProof}
import at.logic.calculi.treeProofs.TreeProof
import at.logic.gui.prooftool.parser._
import at.logic.language.schema.IntVar
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.parsing.calculi.latex.SequentsListLatexExporter
import at.logic.parsing.language.arithmetic.HOLTermArithmeticalExporter
import at.logic.parsing.language.xml.{ProofDatabase, XMLExporter}
import at.logic.parsing.writers.FileWriter
import at.logic.transformations.ReductiveCutElim
import at.logic.transformations.skolemization.lksk.LKtoLKskc
import at.logic.transformations.ceres.clauseSets.{renameCLsymbols, StandardClauseSet}
import at.logic.transformations.ceres.struct.{structToExpressionTree, StructCreators}
import at.logic.transformations.ceres.projections.{Projections, DeleteTautology, DeleteRedundantSequents}
import at.logic.transformations.ceres.{UnfoldProjectionTerm, ProjectionTermCreators}
import at.logic.algorithms.shlk.{FixedFOccs,CloneLKProof2, applySchemaSubstitution2, applySchemaSubstitution}
import at.logic.utils.ds.trees.Tree
import at.logic.transformations.herbrandExtraction.{ExtractHerbrandSequent, extractExpansionTrees}
import at.logic.transformations.skolemization.skolemize
import at.logic.transformations.ceres.clauseSchema.{resolutionProofSchemaDB, InstantiateResSchema}
import at.logic.transformations.ceres.ACNF.ACNF
import at.logic.calculi.slk.SchemaProofDB
import at.logic.calculi.proofs.Proof
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.language.hol.{HOLFormula, HOLExpression}
import java.awt.image.BufferedImage
import javax.imageio.ImageIO

object Main extends SimpleSwingApplication {
  val body = new MyScrollPane
  val db = new FileParser
  val defaultFontSize = 12

  override def startup(args: Array[String]) {
    showFrame()
    if (args.length >= 1) loadProof(args(0),defaultFontSize)
    else ProofToolPublisher.publish(DisableMenus)
  }

  def showFrame() {
    top.pack()
    top.size = new Dimension(700,500)
    top.centerOnScreen()
    top.maximize()
    top.open()
  }

  lazy val top = new MainFrame {
    title = "ProofTool"
    menuBar = mBar
    contents = new BorderPanel {
      // layout(toolbar) = Position.North
      layout(body) = Position.Center
      // layout(new ProgressBar { indeterminate = true }) = Position.South
    }
  }

  // Used for displaying things directly from Scala shell
  def display(name: String, obj: AnyRef) {
    showFrame()
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    obj match {
        // a full db is not handled by tha launcher, se need some special case
      case pdb : ProofDatabase =>
          db.loadProofDatabase(pdb)
          selectProofFromDB(defaultFontSize)
          ProofToolPublisher.publish(EnableMenus)
      case _ =>
        body.contents = new Launcher(Some(name, obj), defaultFontSize)
    }

    body.cursor = java.awt.Cursor.getDefaultCursor
  }



  def fOpen() { chooser.showOpenDialog(mBar) match {
    case FileChooser.Result.Approve => loadProof(chooser.selectedFile.getPath,defaultFontSize)
    case _ =>
  }}

  def fSaveProof(tp: AnyRef) { chooser.showSaveDialog(mBar) match {
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
  }}

  def fSaveAll() { chooser.showSaveDialog(mBar) match {
    case FileChooser.Result.Approve => try {
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      val result = chooser.selectedFile.getPath
      val path = if (result.endsWith(".xml")) result else result + ".xml"
      XMLExporter(path, db.getProofDB)
    } catch {
      case e: Throwable => errorMessage("Can't save the database! \n\n" + getExceptionString(e))
    } finally { body.cursor = java.awt.Cursor.getDefaultCursor }
    case _ =>
  }}

  def fExportPdf() { chooser.showSaveDialog(mBar) match {
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
      document.open()
      val content = writer.getDirectContent
      val template = content.createTemplate(width, height)
      val g2 = template.createGraphicsShapes(width, height)
      component.paint(g2)
      g2.dispose()
      content.addTemplate(template, 0, 10)
      document.close()
    } catch {
        case e: Throwable => errorMessage("Can't export to pdf! \n\n" + getExceptionString(e))
    } finally { body.cursor = java.awt.Cursor.getDefaultCursor }
    case _ =>
  }}


  def fExportPng() { chooser.showSaveDialog(mBar) match {
    case FileChooser.Result.Approve => try {
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)

      val component = body.getContent.contents.head
      val width = component.size.width
      val height = component.size.height
      val img = new BufferedImage(width, height, BufferedImage.TYPE_INT_RGB)
      val g = img.createGraphics()
      component.paint(g)
      val result = chooser.selectedFile.getPath
      val path = if (result.endsWith(".png")) result else result + ".png"
      ImageIO.write(img, "png", new File(path));
    } catch {
      case e: Throwable => errorMessage("Can't export to png! \n\n" + getExceptionString(e))
    } finally { body.cursor = java.awt.Cursor.getDefaultCursor }
    case _ =>
  }}

  def fExportClauseSetToTPTP() { chooser.showSaveDialog(mBar) match {
    case FileChooser.Result.Approve =>
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      body.getContent.getData.get._2  match {
        case l : List[_] => try {
          val list = l.map( x => x match {
            case s: Sequent => s.toFSequent()
            case fs: FSequent => fs
            case _ => throw new Exception("This is not a clause set.")
          })
          val result = chooser.selectedFile.getPath
          val path = if (result.endsWith(".tptp")) result else result + ".tptp"
          val file = new JBufferedWriter(new JFileWriter( path ))
          file.write(at.logic.parsing.language.tptp.TPTPFOLExporter.tptp_problem( list ))
          file.close()
        } catch {
            case e: Throwable => errorMessage("Can't export the clause set! \n\n" + getExceptionString(e))
        }
        case _ => infoMessage("This is not a clause set, can't export it!")
      }
      body.cursor = java.awt.Cursor.getDefaultCursor
    case _ =>
  }}

  def fExportClauseSetToTeX() { chooser.showSaveDialog(mBar) match {
    case FileChooser.Result.Approve =>
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      body.getContent.getData.get._2  match {
        case l : List[_] => try {
          val list = l.map( x => x match {
            case s: Sequent => s.toFSequent()
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
  }}

  def fExportProofToTex(tp: AnyRef, ask: Boolean) { chooser.showSaveDialog(mBar) match {
    case FileChooser.Result.Approve =>
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      tp match {
        case proof: LKProof => try {
          val result = chooser.selectedFile.getPath
          val path = if (result.endsWith(".tex")) result else result + ".tex"
          val fileContent = if (ask) questionMessage("Would you like to export all proofs?") match {
            case Dialog.Result.Yes => ProofToLatexExporter(db.getProofs.map(pair => (pair._1, pair._2.asInstanceOf[LKProof])))
            case _ => ProofToLatexExporter(proof)
          } else ProofToLatexExporter(proof)
          val file = new JBufferedWriter(new JFileWriter( path ))
          file.write(fileContent)
          file.close()
        } catch {
          case e: Throwable => errorMessage("Can't save the proof! \n\n" + getExceptionString(e))
        }
        case _ => infoMessage("This is not a proof, can't save it!")
      }
      body.cursor = java.awt.Cursor.getDefaultCursor
    case _ =>
  }}

  // This function is changed to dispose for cli.
  // When called from cli, sys.exit forces also cli to exit.
  // The default close button still does sys.exit as it should do.
  def fExit() { top.dispose() } //System.exit(0)

  def zoomIn() {
    val content = body.getContent
    content.fontSize * 3 / 2 match {
      case j: Int if j > 72 =>
      case j: Int => load(content.getData,j)
    }
  }

  def zoomOut() {
    val content = body.getContent
    content.fontSize / 3 * 2 match {
      case j: Int if j < 1 =>
      case j: Int => load(content.getData,j)
    }
  }

  def search() {
    val input_str = inputMessage("Please enter string to search:", Seq()) match {
      case Some(str) => str
      case _ => ""
    }
    if (! input_str.isEmpty) try {
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      body.getContent.contents.head match {
        case dp: DrawProof =>
          dp.search = input_str
          if (dp.proof.root.isInstanceOf[Sequent]) dp.setColoredOccurrences(Search.inTreeProof(input_str, dp.proof), Set.empty[FormulaOccurrence])
          else dp.searchNotInLKProof()
          dp.revalidate()
        case dp: DrawResolutionProof =>
          dp.search = input_str
          if (dp.proof.root.isInstanceOf[Sequent]) dp.setColoredOccurrences(Search.inResolutionProof(input_str, dp.proof))
          else dp.searchNotInLKProof()
          dp.revalidate()
        case dt: DrawTree =>
          dt.search = input_str
          dt.revalidate()
        case dl: DrawList =>
          dl.search = input_str
          dl.revalidate()
        case _ => throw new Exception("Cannot search in this object!")
      }
    } catch {
        case e: Throwable => errorMessage(getExceptionString(e))
    } finally {
      body.cursor = java.awt.Cursor.getDefaultCursor
    }
  }

  def scrollToProof(proof: TreeProof[_]) {
    //val launcher = body.contents.head.asInstanceOf[Launcher]
    val launcher = body.getContent
    val pos = launcher.getLocationOfProof(proof).get
    //val location = launcher.peer.location
    //val newpos = new Point(pos.x + location.x, pos.y + location.y)
    val centered = new Rectangle( pos.x - body.bounds.width/2, pos.y - body.bounds.height, body.bounds.width, body.bounds.height )
    launcher.peer.scrollRectToVisible( centered )
  }

  // Used for PopupMenu, loads proof directly
  def loadProof(proof: LKProof) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(Some(proof.name, proof), defaultFontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used for ViewProof menu
  def loadProof(proof: (String, TreeProof[_])) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(Some(proof), defaultFontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
    resetCuts()
  }

  // Used for ViewResolutionProof menu
  def loadResolutionProof(proof: (String, Proof[_])) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(Some(proof), 14)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used by startup and open dialog
  def loadProof(path: String, fontSize: Int) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    db.parseFile(path)
    selectProofFromDB(fontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
    ProofToolPublisher.publish(EnableMenus)
  }

  //tries to display some proof from the db
  def selectProofFromDB(fontSize:Int){
    val proofs = db.getProofs
    if (proofs.size > 0) body.contents = new Launcher(Some(proofs.head), fontSize)
    else if (db.getSequentLists.size > 0)
      body.contents = new Launcher(Some(db.getSequentLists.head), fontSize)
    else if (db.getTermTrees.size > 0)
      body.contents = new Launcher(Some((db.getTermTrees.head._1,db.getTermTrees.head._3)), fontSize)
    else if (db.getResolutionProofs.size > 0)
      body.contents = new Launcher(Some(db.getResolutionProofs.head), fontSize)
    else body.contents = new Launcher(None, fontSize)

  }

  // Used by View Clause List menu
  def loadClauseSet(clList: (String, List[_])) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(Some(clList), defaultFontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used by View Struct menu
  def loadStruct(struct: (String, Tree[_])) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(Some(struct), defaultFontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used for Zooming
  def load(option: Option[(String, AnyRef)], fontSize: Int) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(option, fontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used by "Cycle through cuts"
  private var searchResult : List[LKProof] = null
  private var currentResult : Iterator[LKProof] = null


  // Should be called whenever the proof is changed.
  def resetCuts() {
    searchResult = null
    currentResult = null
  }

  def setSearchResult(l:List[LKProof]) = if (l != null) {
    searchResult = l
    currentResult = l.iterator
  }

  val mBar: MenuBar = new MenuBar() {
    import javax.swing.KeyStroke
    import java.awt.event.{KeyEvent, ActionEvent => JActionEvent}

    focusable = true
    val customBorder = Swing.EmptyBorder(5,3,5,3)
    contents += new Menu("File") {
      mnemonic = Key.F
      contents += new MenuItem(Action("Open...") { fOpen() }) {
        mnemonic = Key.O
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_O, JActionEvent.CTRL_MASK))
        border = customBorder
      }
      contents += new MenuItem(Action("Save Proof as XML") { fSaveProof(body.getContent.getData.get._2) }) {
        mnemonic = Key.P
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_P, JActionEvent.CTRL_MASK))
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => enabled = true
          case UnLoaded => enabled = false
        }
      }
      contents += new MenuItem(Action("Save All as XML") { fSaveAll() }) {
        mnemonic = Key.S
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_S, JActionEvent.CTRL_MASK))
        border = customBorder
        listenTo(ProofToolPublisher)
        reactions += {
          case DisableMenus => enabled = false
          case EnableMenus => enabled = true
        }
      }
      contents += new Separator
      contents += new MenuItem(Action("Export as PDF") { fExportPdf() }) {
        mnemonic = Key.D
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_D, JActionEvent.CTRL_MASK))
        border = customBorder
        listenTo(ProofToolPublisher)
        reactions += {
          case DisableMenus => enabled = false
          case EnableMenus => enabled = true
        }
      }
      contents += new MenuItem(Action("Export as PNG") { fExportPng() }) {
        mnemonic = Key.N
        //this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_N, JActionEvent.CTRL_MASK))
        border = customBorder
        listenTo(ProofToolPublisher)
        reactions += {
          case DisableMenus => enabled = false
          case EnableMenus => enabled = true
        }
      }
      contents += new Separator
      contents += new MenuItem(Action("Export Clause Set as TPTP") { fExportClauseSetToTPTP() }) {
        mnemonic = Key.T
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_T, JActionEvent.CTRL_MASK))
        border = customBorder
        listenTo(ProofToolPublisher)
        reactions += {
          case DisableMenus => enabled = false
          case EnableMenus => enabled = true
        }
      }
      contents += new MenuItem(Action("Export Clause Set as TeX") { fExportClauseSetToTeX() }) {
        mnemonic = Key.E
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_E, JActionEvent.CTRL_MASK))
        border = customBorder
        listenTo(ProofToolPublisher)
        reactions += {
          case DisableMenus => enabled = false
          case EnableMenus => enabled = true
        }
      }
      contents += new MenuItem(Action("Export Proof as TeX") { fExportProofToTex(body.getContent.getData.get._2, ask = true) }) {
        mnemonic = Key.A
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_A, JActionEvent.CTRL_MASK))
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => enabled = true
          case UnLoaded => enabled = false
        }
      }
      contents += new Separator
      contents += new MenuItem(Action("Exit") { fExit() }) {
        mnemonic = Key.X
        peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_X, JActionEvent.CTRL_MASK))
        border = customBorder
      }
    }
    contents += new Menu("Edit") {
      mnemonic = Key.E
      listenTo(ProofToolPublisher)
      reactions += {
        case DisableMenus => enabled = false
        case EnableMenus => enabled = true
      }
      contents += new MenuItem(Action("Search...") { search() }) {
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
      //  warningMessage("This feature is under development and might not work properly!")
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
      contents += new MenuItem(Action("Show All Rules") {
        ProofToolPublisher.publish(new ShowAllRules(body.getContent.getData.get._2.asInstanceOf[TreeProof[_]]))
      }) {
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => this.enabled = true
          case UnLoaded => this.enabled = false
        }
      }
      contents += new Separator
      contents += new MenuItem(Action("Hide Sequent Contexts") { hideSequentContext() }) {
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => this.enabled = true
          case UnLoaded => this.enabled = false
        }
      }
      contents += new Separator
      contents += new MenuItem(Action("Mark Cut-Ancestors") { markCutAncestors() }) {
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => this.enabled = true
          case UnLoaded => this.enabled = false
        }
      }
      contents += new MenuItem(Action("Extract Cut-Formulas") { extractCutFormulas() }) {
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => this.enabled = true
          case UnLoaded => this.enabled = false
        }
      }
      contents += new Separator
      contents += new Separator
      contents += new Separator
      contents += new Separator
      contents += new MenuItem(Action("Mark Cut- & Ω-Ancestors") { markCutOmegaAncestors(FixedFOccs.foccs) }) {
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
      listenTo(ProofToolPublisher)
      reactions += {
        case DisableMenus => enabled = false
        case EnableMenus => enabled = true
      }
      contents += new MenuItem(Action("Zoom In") { zoomIn() }) {
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_UP , JActionEvent.ALT_MASK))
        border = customBorder
      }
      contents += new MenuItem(Action("Zoom Out") { zoomOut() }) {
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_DOWN, JActionEvent.ALT_MASK))
        border = customBorder
      }
      contents += new MenuItem(Action("Jump To End-sequent") { scrollToProof(body.getContent.getData.get._2.asInstanceOf[LKProof])}) {
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_ENTER, JActionEvent.ALT_MASK))
        border = customBorder
      }
      contents += new MenuItem(Action("Find Cuts") {
        setSearchResult(getCutsAsProofs(body.getContent.getData.get._2.asInstanceOf[LKProof]))
      }) {
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_C, JActionEvent.ALT_MASK))
        border = customBorder
      }
      contents += new MenuItem(Action("Cycle through search results") {
        // TODO: reset cuts when loading a proof
        if ( currentResult != null) {
          if (currentResult.hasNext ) {
            val cut = currentResult.next()
            scrollToProof(cut)

          } else {
            currentResult = searchResult.iterator
          }
        }
      }) {
        this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_N, JActionEvent.ALT_MASK))
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
            contents.clear()
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
            contents.clear()
            for (i <- l) contents += new MenuItem(Action(i._1) { loadClauseSet(i) }) { border = customBorder }
        }
      }
      contents += new Menu("View Resolution Proof") {
        MenuScroller.setScrollerFor(this.peer)
        mnemonic = Key.P
        border = customBorder
        listenTo(ProofToolPublisher)
        reactions += {
          case ProofDbChanged =>
            val l = db.getResolutionProofs
            contents.clear()
            for (i <- l) contents += new MenuItem(Action(i._1) { loadResolutionProof(i) }) { border = customBorder }
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
            val l = db.getTermTrees
            contents.clear()
            for (i <- l) contents += new MenuItem(Action(i._1) { loadStruct((i._1,i._3)) }) { border = customBorder }
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
        contents += new MenuItem(Action("All Cuts") { computeClList() }) { border = customBorder }
        contents += new MenuItem(Action("Only Quantified Cuts") { computeClListOnlyQuantifiedCuts() }) { border = customBorder }
      }
      contents += new Menu("Compute Struct") {
        contents += new MenuItem(Action("All Cuts") { computeStruct() }) { border = customBorder }
        contents += new MenuItem(Action("Only Quantified Cuts") { computeStructOnlyQuantifiedCuts() }) { border = customBorder }
      }
      contents += new MenuItem(Action("Compute Projections") { computeProjections() }) { border = customBorder }
      contents += new Separator
      contents += new MenuItem(Action("Apply Gentzen's Method") { gentzen(body.getContent.getData.get._2.asInstanceOf[LKProof]) }) { border = customBorder }
      contents += new Separator
      contents += new MenuItem(Action("Extract Herbrand Sequent") { herbrandSequent() }) { border = customBorder }
      contents += new MenuItem(Action("Extract Expansion Tree") { expansionTree() }) { border = customBorder }
      contents += new Separator
      contents += new MenuItem(Action("Eliminate Definitions") { eliminateDefsLK() }) { border = customBorder }
      contents += new MenuItem(Action("Skolemize") { skolemizeProof() }) { border = customBorder }
      contents += new MenuItem(Action("Regularize") { regularizeProof() }) { border = customBorder }
    }
    contents += new Menu("LKS Proof") {
      mnemonic = Key.P
      listenTo(ProofToolPublisher)
      reactions += {
        case DisableMenus => enabled = false
        case EnableMenus => enabled = true
      }
      contents += new MenuItem(Action("Compute Clause Set") { computeSchematicClauseSet() }) {
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => enabled = true
          case UnLoaded => enabled = false
        }
      }
      contents += new MenuItem(Action("Compute Struct") { computeSchematicStruct() }) {
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => enabled = true
          case UnLoaded => enabled = false
        }
      }
      contents += new MenuItem(Action("Compute Projection Term") { computeSchematicProjectionTerm() }) {
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => enabled = true
          case UnLoaded => enabled = false
        }
      }
      contents += new MenuItem(Action("Compute ACNF") { computeACNF() }) { border = customBorder }
      contents += new MenuItem(Action("Specify Resolution Schema") { specifyResolutionSchema() } )  { border = customBorder }
      contents += new MenuItem(Action("Compute Instance") { computeInstance() } )  { border = customBorder }
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
      contents += new MenuItem(Action("Non-Prenex Proof 1") {
        import at.logic.language.lambda.types.Definitions._
        import at.logic.language.lambda.symbols.ImplicitConverters._
        import at.logic.language.hol._
        import at.logic.calculi.lk.propositionalRules._
        import at.logic.calculi.lk.quantificationRules._
        val p = HOLVar("p", i -> o)
        val a = HOLVar("a", i)
        val b = HOLVar("b", i)
        val q = HOLVar("q", i -> o)
        val x = HOLVar("x", i)
        val px = HOLAppFormula(p, x) // p(x)
        val pa = HOLAppFormula(p, a) // p(a)
        val pb = HOLAppFormula(p, b) // p(b)
        val qa = HOLAppFormula(q, a) // q(a)
        val substa = a // x -> a
        val substb = b // x -> b
        val all_px = AllVar(x, px) // forall x. p(x)

        val axm1 = Axiom(pa::Nil, pa::Nil)
        val axm2 = Axiom(pb::Nil, pb::Nil)
        val all1 = ForallLeftRule(axm1, pa, all_px, substa)
        val all2 = ForallLeftRule(axm2, pb, all_px, substb)
        val andrght = AndRightRule(all1, all2, pa, pb)
        val contr = ContractionLeftRule(andrght, all_px)
        val andlft = AndLeft1Rule(contr, all_px, qa)

        body.contents = new Launcher(Some(("Proof", andlft)), defaultFontSize)
        ProofToolPublisher.publish(EnableMenus)
      }) { border = customBorder }
      contents += new MenuItem(Action("Non-Prenex Proof 2") {
        import at.logic.language.lambda.types.Definitions._
        import at.logic.language.lambda.symbols.ImplicitConverters._
        import at.logic.language.hol._
        import at.logic.calculi.lk.propositionalRules._
        import at.logic.calculi.lk.quantificationRules._
        val p = HOLVar("p", i -> o)
        val a = HOLVar("a", i)
        val b = HOLVar("b", i)
        val q = HOLVar("q", i -> o)
        val x = HOLVar("x", i)
        val y = HOLVar("y", i)
        val px = HOLAppFormula(p, x) // p(x)
        val pa = HOLAppFormula(p, a) // p(a)
        val pb = HOLAppFormula(p, b) // p(b)
        val qy = HOLAppFormula(q, y) // q(a)
        val substa = a // x -> a
        val substb = b // x -> b
        val ex_px = ExVar(x, px) // exists x. p(x)
        val ex_qy = ExVar(y, qy)

        val axm1 = Axiom(pa::Nil, pa::Nil)
        val axm2 = Axiom(pb::Nil, pb::Nil)
        val exists1 = ExistsRightRule(axm1, pa, ex_px, substa)
        val exists2 = ExistsRightRule(axm2, pb, ex_px, substb)
        val orlft = OrLeftRule(exists1, exists2, pa, pb)
        val contr = ContractionRightRule(orlft, ex_px)
        val orrght = OrRight1Rule(contr, ex_px, ex_qy)

        body.contents = new Launcher(Some(("Proof", orrght)), defaultFontSize)
        ProofToolPublisher.publish(EnableMenus)
      }) { border = customBorder }
      contents += new MenuItem(Action("Nested Proof 1") {
        import at.logic.language.lambda.types.Definitions._
        import at.logic.language.lambda.symbols.ImplicitConverters._
        import at.logic.language.hol._
        import at.logic.calculi.lk.propositionalRules._
        import at.logic.calculi.lk.quantificationRules._
        val p = HOLVar("p", i -> o)
        val a = HOLVar("a", i)
        val b = HOLVar("b", i)
        val q = HOLVar("q", i -> o)
        val x = HOLVar("x", i)
        val y = HOLVar("y", i)
        val px = HOLAppFormula(p, x) // p(x)
        val pa = HOLAppFormula(p, a) // p(a)
        val pb = HOLAppFormula(p, b) // p(b)
        val qa = HOLAppFormula(q, a) // q(a)
        val qy = HOLAppFormula(q, y) // q(a)
        val substa = a // x -> a
        val substb = b // x -> b
        val all_px = AllVar(x, px) // forall x. p(x)

        val axm1 = Axiom(pa::Nil, pa::Nil)
        val axm2 = Axiom(pb::Nil, pb::Nil)
        val all1 = ForallLeftRule(axm1, pa, all_px, substa)
        val all2 = ForallLeftRule(axm2, pb, all_px, substb)
        val andrght = AndRightRule(all1, all2, pa, pb)
        val contr = ContractionLeftRule(andrght, all_px)
        val andlft = AndLeft1Rule(contr, all_px, qa)
        val all3 = ForallLeftRule(andlft, And(all_px,qa), AllVar(y, And(all_px,qy)),a)

        body.contents = new Launcher(Some(("Proof", all3)), defaultFontSize)
        ProofToolPublisher.publish(EnableMenus)
      }) { border = customBorder }
      contents += new MenuItem(Action("Nested Expansion Tree") {
        import at.logic.language.lambda.types.Definitions._
        import at.logic.language.lambda.symbols.ImplicitConverters._
        import at.logic.language.hol._
        import at.logic.calculi.expansionTrees.{WeakQuantifier, And => AndET, Atom => AtomET}
        val p = HOLVar("p", i -> o)
        val a = HOLVar("a", i)
        val b = HOLVar("b", i)
        val a1 = HOLVar("a_1", i)
        val b1 = HOLVar("b_1", i)
        val a2 = HOLVar("a_2", i)
        val b2 = HOLVar("b_2", i)
        val q = HOLVar("q", i -> o)
        val x = HOLVar("x", i)
        val y = HOLVar("y", i)
        val px = HOLAppFormula(p, x) // p(x)
        val pa1 = HOLAppFormula(p, a1) // p(a1)
        val pb1 = HOLAppFormula(p, b1) // p(b1)
        val pa2 = HOLAppFormula(p, a2) // p(a2)
        val pb2 = HOLAppFormula(p, b2) // p(b2)
        val qb = HOLAppFormula(q, b) // q(b)
        val qa = HOLAppFormula(q, a) // q(a)
        val qy = HOLAppFormula(q, y) // q(a)
        val all_px = AllVar(x, px) // forall x. p(x)
        val all_px_and_qy = And(all_px,qy) // forall x. p(x) /\ q(y)
        val all_all_px_and_qy = AllVar(y,all_px_and_qy) // forall y. (forall x. p(x) /\ q(y))
        val ex_px = ExVar(x, px) // exists x. p(x)
        val ex_px_and_qy = And(ex_px,qy) // exists x. p(x) /\ q(y)
        val ex_ex_px_and_qy = ExVar(y,ex_px_and_qy) // exists y. (exists x. p(x) /\ q(y))

        val expTree11 = new WeakQuantifier(all_px,Seq((AtomET(pa1),a1),(AtomET(pb1),b1)))
        val expTree21 = new WeakQuantifier(all_px,Seq((AtomET(pa2),a2),(AtomET(pb2),b2)))
        val expTree1 = new AndET(expTree11,AtomET(qa))
        val expTree2 = new AndET(expTree21,AtomET(qb))
        val expTree = new WeakQuantifier(all_all_px_and_qy,Seq((expTree1,a),(expTree2,b)))

        val expT11 = new WeakQuantifier(ex_px,Seq((AtomET(pa1),a1),(AtomET(pb1),b1)))
        val expT21 = new WeakQuantifier(ex_px,Seq((AtomET(pa2),a2),(AtomET(pb2),b2)))
        val expT1 = new AndET(expT11,AtomET(qa))
        val expT2 = new AndET(expT21,AtomET(qb))
        val expT = new WeakQuantifier(ex_ex_px_and_qy,Seq((expT1,a),(expT2,b)))

        val et = (Seq(expTree,expTree),Seq(expT,expT))

        body.contents = new Launcher(Some(("Expansion Tree", et)), defaultFontSize)
        ProofToolPublisher.publish(EnableMenus)
      }) { border = customBorder }
      contents += new MenuItem(Action("Nested Expansion Tree 1") {
        import at.logic.language.lambda.types.Definitions._
        import at.logic.language.lambda.symbols.ImplicitConverters._
        import at.logic.language.hol._
        import at.logic.calculi.expansionTrees.{WeakQuantifier, And => AndET, Atom => AtomET}
        val p = HOLVar("P", i -> o)
        val a = HOLVar("a", i)
        val b = HOLVar("b", i)
        val f = HOLVar("f", i -> i)
        val g = HOLVar("g", i -> i)
        val q = HOLVar("Q", i -> (i -> o))
        val x = HOLVar("x", i)
        val y = HOLVar("y", i)
        val px = Atom(p, x::Nil) // p(x)
        val pa = Atom(p, a::Nil) // p(a)
        val pb = Atom(p, b::Nil) // p(b)
        val fx = Function(f, x::Nil)
        val fa = Function(f, a::Nil)
        val fb = Function(f, b::Nil)
        val gx = Function(g, x::Nil)
        val ga = Function(g, a::Nil)
        val gb = Function(g, b::Nil)
        val qxfx = Atom(q, x::fx::Nil) // q(x,f(x))
        val qxgx = Atom(q, x::gx::Nil) // q(x,g(x))
        val qbfb = Atom(q, b::fb::Nil) // q(b,f(b))
        val qafa = Atom(q, a::fa::Nil) // q(a,f(a))
        val qbgb = Atom(q, b::gb::Nil) // q(b,g(b))
        val qaga = Atom(q, a::ga::Nil) // q(a,g(a))
        val qxy = Atom(q, x::y::Nil) // q(x,y)
        val ant1F = Or(pa,pb)
        val ant2F = AllVar(x, Or(qxfx,qxgx))
        val conF = ExVar(x, And(px, ExVar(y, qxy)))
        val ex_qay = ExVar(y, Atom(q, a::y::Nil))
        val ex_qby = ExVar(y, Atom(q, b::y::Nil))

        val ant1ET = AtomET(ant1F)
        val ant2ET = AtomET(ant2F)
        val expT11 = new WeakQuantifier(ex_qay,Seq((AtomET(qafa),fa),(AtomET(qaga),ga)))
        val expT21 = new WeakQuantifier(ex_qby,Seq((AtomET(qbfb),fb),(AtomET(qbgb),gb)))
        val expT1 = new AndET(AtomET(pa), expT11)
        val expT2 = new AndET(AtomET(pb), expT21)
        val conET = new WeakQuantifier(conF,Seq((expT1,a),(expT2,b)))

        val et = (Seq(ant1ET,ant2ET),Seq(conET))

        body.contents = new Launcher(Some(("Expansion Tree", et)), defaultFontSize)
        ProofToolPublisher.publish(EnableMenus)
      }) { border = customBorder }
      contents += new MenuItem(Action("Tape Expansion Tree") { // A hack just to get a picture for the paper.
        import at.logic.language.lambda.types.Definitions._
        import at.logic.language.lambda.symbols.ImplicitConverters._
        import at.logic.language.hol._
        import at.logic.calculi.expansionTrees.{WeakQuantifier, And => AndET, Atom => AtomET}
        val eq = HOLVar("=", i -> (i -> o))
        // val leq = HOLVar("<=", i -> (i -> o))
        // val max = HOLVar("max", i -> (i -> i))
        val zero = HOLVar("0", i)
        val O = HOLVar("O", i)
        val I = HOLVar("I", i)
        val f = HOLVar("f", i -> i)
        val s = HOLVar("s", i -> i)
        val x = HOLVar("x", i)
        val y = HOLVar("y", i)
        val j = HOLVar("j", i)

	val sx = Function(s, x::Nil) // s(x)
	val sy = Function(s, y::Nil) // s(y)
	// val m = Function(max, x::y::Nil) // max(x,y)
        val one = Function(s, zero::Nil) // s(0)
        val two = Function(s, one::Nil) // s(s(0))

        val fx = Function(f, x::Nil) // f(x)
        val fy = Function(f, y::Nil) // f(y)
	val f0 = Function(f, zero::Nil) // f(0)
        val f1 = Function(f, one::Nil) // f(s(0))
        val f2 = Function(f, two::Nil) // f(s(s(0)))

        val eqfx0 = Atom(eq, fx::O::Nil) // f(x) = 0
        val eqfx1 = Atom(eq, fx::I::Nil) // f(x) = 1

	// val leqxm = Atom(leq, x::m::Nil) // x <= max(x,y)
	// val leqym = Atom(leq, y::m::Nil) // y <= max(x,y)
	// val leqsxy = Atom(leq, sx::y::Nil) // s(x) <= y
	val eq0sx = Atom(eq, zero::sx::Nil) // 0 = s(x)
        val eqsxsy = Atom(eq, sx::sy::Nil) // s(x) = s(y)

        val eq0y = Atom(eq, x::one::Nil) // 0 = y
        val eq1y = Atom(eq, x::two::Nil) // 1 = y
        val eqxy = Atom(eq, x::y::Nil) // x = y
        val eq01 = Atom(eq, zero::one::Nil) // 0 = 1
        val eq02 = Atom(eq, zero::two::Nil) // 0 = 2
        val eq12 = Atom(eq, one::two::Nil) // 1 = 2

        val eqf0fy = Atom(eq, f0::fy::Nil) // f(0) = f(y)
        val eqf1fy = Atom(eq, f1::fy::Nil) // f(1) = f(y)
        val eqfxfy = Atom(eq, fx::fy::Nil) // f(x) = f(y)
        val eqfxj = Atom(eq, fx::j::Nil) // f(x) = j
        val eqfyj = Atom(eq, fy::j::Nil) // f(x) = j
        val eqf0f1 = Atom(eq, f0::f1::Nil) // f(0) = f(1)
        val eqf0f2 = Atom(eq, f0::f2::Nil) // f(0) = f(2)
        val eqf1f2 = Atom(eq, f1::f2::Nil) // f(1) = f(2)

	val lhs = AtomET(AllVar(x, Or(eqfx0, eqfx1))) // all x (f(x) = 0 or f(x) = 1)
	// val lhs4 = AtomET(AllVar(x, AllVar(y, leqxm))) // all x,y (x <= max(x,y))	
	// val lhs2 = AtomET(AllVar(x, AllVar(y, leqym))) // all x,y (y <= max(x,y))	
	// val lhs3 = AtomET(AllVar(x, AllVar(y, Imp(leqsxy, Neg(eqxy)) ))) // all x,y (s(x) <= y impl - x = y)
	val lhs1 = AtomET(AllVar(j, AllVar(x, AllVar(y, Imp(And(eqfxj, eqfyj), eqfxfy))))) // all j,x,y ((f(x) = j and f(y) = j) impl f(x) = f(y))	
	val lhs2 = AtomET(AllVar(x, Neg(eq0sx))) // all x (- 0 = s(x))	
	val lhs3 = AtomET(AllVar(x, AllVar(y, Imp(eqsxsy, eqxy) ))) // all x,y (s(x) = s(y) impl x = y)


	val and1 = And(Neg(eq01), eqf0f1)
	val and2 = And(Neg(eq02), eqf0f2)
	val and3 = And(Neg(eq12), eqf1f2)

        val all1 = ExVar(y, And(Neg(eq0y), eqf0fy))
        val all2 = ExVar(y, And(Neg(eq1y), eqf1fy))
        val all3 = ExVar(x, ExVar(y, And(Neg(eqxy), eqfxfy)))

	val et1 = new WeakQuantifier(all1, Seq((AtomET(and1), one), (AtomET(and2), two)))
	val et2 = new WeakQuantifier(all2, Seq((AtomET(and3), two)))
	val rhs = new WeakQuantifier(all3, Seq((et1, zero), (et2, one)))

        val et = (Seq(lhs, lhs1, lhs2, lhs3),Seq(rhs))

        body.contents = new Launcher(Some(("Expansion Tree", et)), defaultFontSize)
        ProofToolPublisher.publish(EnableMenus)
      }) { border = customBorder }
    }
  }

  def specifyResolutionSchema() {
    val t = TextAreaDialog("Please enter resolution proof schema:")
    if (t != None && t.get != "") try {
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      db.rsFileReader(new InputStreamReader(new ByteArrayInputStream(t.get.getBytes("UTF-8"))))
      val tp = db.getTermTrees.head
      body.contents = new Launcher(Some((tp._1,tp._3)),14)
      body.cursor = java.awt.Cursor.getDefaultCursor
      ProofToolPublisher.publish(ProofDbChanged)
    } catch {
      case e: Throwable =>
        errorMessage("Cannot parse the specified resolution schema!\n\n" + getExceptionString(e))
    }
  }

  def herbrandSequent() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val hs = ExtractHerbrandSequent(body.getContent.getData.get._2.asInstanceOf[LKProof])
    body.contents = new Launcher(Some("Herbrand Sequent",hs),14)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
    case e: Throwable =>
      errorMessage("Cannot extract Herbrand Sequent!\n\n" + getExceptionString(e))
  }}

  def expansionTree() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val et = extractExpansionTrees(body.getContent.getData.get._2.asInstanceOf[LKProof])
    body.contents = new Launcher(Some("Expansion Tree",et),14)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
    case e: Throwable =>
      errorMessage("Cannot extract Expansion Tree!\n\n" + getExceptionString(e))
  }}

  def skolemizeProof() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val data = body.getContent.getData.get
    val proof = skolemize(data._2.asInstanceOf[LKProof])
    db.addProofs((data._1+"_sk", proof)::Nil)
    body.contents = new Launcher(Some(data._1+"_sk",proof),14)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
    case e: Throwable =>
      errorMessage("Cannot skolemize the proof!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def regularizeProof() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val data = body.getContent.getData.get
    val proof = regularize(data._2.asInstanceOf[LKProof])._1
    db.addProofs((data._1+"_reg", proof)::Nil)
    body.contents = new Launcher(Some(data._1+"_reg",proof),14)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
    case e: Throwable =>
      errorMessage("Cannot regularize the proof!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def extractCutFormulas() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val list = cutformulaExtraction( body.getContent.getData.get._2.asInstanceOf[LKProof] )
    db.addSeqList("cutFormulaList ", list.map(x => x.toFSequent()) )
    body.contents = new Launcher(Some("Cut-formula List",list),16)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't extract CutFormula List!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def computeProjections() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof = body.getContent.getData.get
    val proof_projs = Projections(proof._2.asInstanceOf[LKProof]).filterNot(p =>
      p.root.antecedent.exists(fo1 => p.root.succedent.exists(fo2 => fo1.formula == fo2.formula))
    ).toList
    val proofs = proof_projs.map(p => (proof._1 + "_prj_" + proof_projs.indexOf(p), p))
    db.addProofs( proofs )
    body.contents = new Launcher(Some( proofs.head ),defaultFontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
    case e: Throwable =>
      errorMessage("Cannot compute Projections!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def computeClList() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof_sk = LKtoLKskc( body.getContent.getData.get._2.asInstanceOf[LKProof] )
    val s = StructCreators.extract( proof_sk )
    val csPre : List[Sequent] = DeleteRedundantSequents( DeleteTautology( StandardClauseSet.transformStructToClauseSet(s) ))

    db.addSeqList(csPre.map(x => x.toFSequent()))
    body.contents = new Launcher(Some("cllist",csPre),16)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't compute ClList!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def computeSchematicClauseSet() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val n = IntVar(new VariableStringSymbol("n"))

    val s = StructCreators.extractStruct( body.getContent.getData.get._1, n)
    val cs : List[Sequent] = DeleteRedundantSequents( DeleteTautology( StandardClauseSet.transformStructToClauseSet(s) ))
    val pair = renameCLsymbols( cs )

    db.addSeqList(pair._1) //.map(x => x.toFSequent()))
    db.addDefinitions(pair._2)
    body.contents = new Launcher(Some("Schematic Clause Set",pair._1),16)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't compute clause set!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def computeSchematicStruct() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val n = IntVar(new VariableStringSymbol("n"))
    val s = StructCreators.extractRelevantStruct( body.getContent.getData.get._1, n)
    val structs_base = s._2.map(pair => (pair._1, db.TermType.ClauseTerm, structToExpressionTree.prunedTree(pair._2)) )
    val structs_step = s._1.map(pair => (pair._1, db.TermType.ClauseTerm, structToExpressionTree.prunedTree(pair._2)) )
    db.addTrees( structs_step ::: structs_base )
    body.contents = new Launcher(Some(structs_step.head._1,structs_step.head._3),defaultFontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't compute Struct!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def computeSchematicProjectionTerm() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof_name = body.getContent.getData.get._1
    val pterms = ProjectionTermCreators(proof_name)
    db.addTrees( pterms.map(pair => (pair._1, db.TermType.ProjectionTerm, pair._2)) )
    body.contents = new Launcher(Some( pterms.head ),defaultFontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't compute Projection Terms!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def computeClListOnlyQuantifiedCuts() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof_sk = eliminateDefinitions(LKtoLKskc( body.getContent.getData.get._2.asInstanceOf[LKProof] ))
    val s = StructCreators.extract( proof_sk, f => f.containsQuantifier )
    val csPre : List[Sequent] = DeleteRedundantSequents( DeleteTautology( StandardClauseSet.transformStructToClauseSet(s) ))
    db.addSeqList(csPre.map(x => x.toFSequent()))
    body.contents = new Launcher(Some("cllist",csPre),16)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't compute clause list!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def computeStruct() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof_sk = LKtoLKskc( body.getContent.getData.get._2.asInstanceOf[LKProof] )
    val s = structToExpressionTree.prunedTree( StructCreators.extract( proof_sk ) )
    db.addTermTree( s )
    body.contents = new Launcher(Some("Struct",s),defaultFontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't compute Struct!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  // Computes the struct, ignoring propositional cuts
  def computeStructOnlyQuantifiedCuts() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof_sk = eliminateDefinitions( LKtoLKskc( body.getContent.getData.get._2.asInstanceOf[LKProof] ) )
    val s = structToExpressionTree.prunedTree( StructCreators.extract( proof_sk, f => f.containsQuantifier ) )
    db.addTermTree( s )
    body.contents = new Launcher(Some("Struct",s),defaultFontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't compute Struct!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def eliminateDefsLK() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val pair = body.getContent.getData.get
    val new_proof = eliminateDefinitions( pair._2.asInstanceOf[LKProof]   )
    db.addProofs((pair._1+" without def rules", new_proof)::Nil)
    body.contents = new Launcher(Some("Proof without Definitions",new_proof),14)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't eliminate definitions!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def eliminateDefsLKsk() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val pair = body.getContent.getData.get
    val new_proof = eliminateDefinitions( LKtoLKskc( pair._2.asInstanceOf[LKProof] )  )
    db.addProofs((pair._1+" without def rules", new_proof)::Nil)
    body.contents = new Launcher(Some("Proof without Definitions",new_proof),14)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: Throwable =>
        errorMessage("Couldn't eliminate definitions!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def newgentzen(proof: LKProof) { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val newSubproof = ReductiveCutElim(proof, true, { x => true }, { (_, cut) => cut == proof } )
    val oldProof = body.getContent.getData.get._2.asInstanceOf[LKProof]
    val newProof = replaceSubproof(oldProof, proof, newSubproof)
    //if (newProof != newSubproof) ReductiveCutElim.proofs = ReductiveCutElim.proofs ::: (newProof::Nil)
    loadProof(("Gentzen Result:", newProof))

    // need to scroll after UI has finished updating
    // to get the correct coordinates.
    SwingUtilities.invokeLater(new Runnable() {
      def run() { scrollToProof(newSubproof) }
    })

  } catch {
      case e: Throwable =>
        errorMessage("Couldn't eliminate all cuts!\n\n" + getExceptionString(e))
  } finally {
    db.addProofs(ReductiveCutElim.proofs.map(x => (x.name, x)))
    body.cursor = java.awt.Cursor.getDefaultCursor
    ProofToolPublisher.publish(ProofDbChanged)
  }}

  def gentzen(proof: LKProof) { try {
    val steps = questionMessage("Do you want to see intermediary steps?") match {
      case Dialog.Result.Yes => true
      case _ => false
    }
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val newSubproof = ReductiveCutElim.eliminateAllByUppermost(proof, steps)
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
  }}


  //to mark cut-ancestors + another ancestors which are additionaly specified
  def markCutOmegaAncestors(l: List[FormulaOccurrence]) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.getContent.contents.head match {
      case dp: DrawProof => body.getContent.getData match {
        case Some((_, proof : LKProof) ) =>
          dp.setColoredOccurrences(getCutAncestors(proof), l.map(fo => getAncestors(fo)).flatten.toSet)//mark more than cut-ancestors
          dp.revalidate()
        case _ => errorMessage("This is not an LK proof!")
      }
      case _ => errorMessage("LK proof not found!")
    }
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  def markCutAncestors() {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.getContent.contents.head match {
      case dp: DrawProof => body.getContent.getData match {
        case Some((_, proof : LKProof) ) =>
          dp.setColoredOccurrences(getCutAncestors(proof), Set.empty[FormulaOccurrence])
          dp.revalidate()
        case _ => errorMessage("This is not an LK proof!")
      }
      case _ => errorMessage("LK proof not found!")
    }
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  def hideSequentContext() {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.getContent.contents.head match {
      case dp: DrawProof => body.getContent.getData match {
        case Some((name, proof : LKProof) ) =>
          dp.setVisibleOccurrences(getAuxFormulas(proof))
          dp.revalidate()
        case _ => errorMessage("This is not an LK proof!")
      }
      case _ => errorMessage("LK proof not found!")
    }
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  def computeInstance() {
    val input = inputMessage("Please enter number of the instance:", Seq()) match {
      case Some(str) => str.replaceAll("""[a-z,A-Z]*""","")
      case _ => ""
    }
    if (! input.isEmpty) try {
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      val number = if (input.size > 10) input.dropRight(10).toInt else input.toInt
      body.getContent.getData.get match {
        case (name: String, p: LKProof) =>
          val proof = try { // This is a hack! In the future these two functions should be merged.
            applySchemaSubstitution2(name, number,  List())
          } catch {
            case e: UnfoldException => applySchemaSubstitution(name, number)
          }
          db.addProofs((name + "↓" + number, proof)::Nil)
          body.contents = new Launcher(Some(name + "↓" + number, proof), defaultFontSize)
        case (name: String, pt: Tree[_]) if db.getTermTrees.find(p => name == p._1 && p._2 == db.TermType.ProjectionTerm) != None =>
          val (term,list) = UnfoldProjectionTerm(name,number)
          val gterm_name = name.replace("_step","").replace("_base","")  + "↓" + number
          db.addTermTree( gterm_name, term )
          db.addProofs(list)
          body.contents = new Launcher(Some(gterm_name, term), defaultFontSize)
          infoMessage("The proof projections, corresponding to this term, are also computed.\n" +
            "They can be found in the View Proof menu!")
        case (name: String, pt: Tree[_]) if db.getTermTrees.find(p => name == p._1 && p._2 == db.TermType.ClauseTerm) != None => errorMessage("Not yet implemented!")
        case (name: String, pt: Tree[_]) if db.getTermTrees.find(p => name == p._1 && p._2 == db.TermType.ResolutionTerm) != None =>
          val proof = InstantiateResSchema(name,number)
          db.addProofs(proof::Nil)
          body.contents = new Launcher(Some(proof), defaultFontSize)
        case _ => errorMessage("Cannot instantiate the object!")
      }
      body.cursor = java.awt.Cursor.getDefaultCursor
      ProofToolPublisher.publish(ProofDbChanged)
    } catch {
      case e: Throwable =>
        errorMessage("Could not construct the instance!\n\n" + getExceptionString(e))
    }
  }

  def computeACNF() {
    if (SchemaProofDB.proofs.isEmpty)
      warningMessage("Proof schema is missing!")
    else if (resolutionProofSchemaDB.map.isEmpty) {
      warningMessage("Please specify the resolution refutation schema!")
      specifyResolutionSchema()
    }
    else try {
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      val result = ACNFDialog(SchemaProofDB.proofs.map( pair => pair._1 ).toSeq.reverse,
        resolutionProofSchemaDB.map.map( pair => pair._1 ).toSeq.reverse)
      if (result != None) {
        val input = result.get
        val proof = ACNF(input._1, input._2, input._3)
        db.addProofs((input._1 + "↓" + input._3 + "_acnf", proof)::Nil)
        body.contents = new Launcher(Some(input._1 + "↓" + input._3 + "_acnf", proof), defaultFontSize)
      }
      body.cursor = java.awt.Cursor.getDefaultCursor
      ProofToolPublisher.publish(ProofDbChanged)
    } catch {
      case e: Throwable =>
        errorMessage("Could not construct the ACNF!\n\n" + getExceptionString(e))
    }
  }

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
        if (f.getName.endsWith(".ivy") || f.isDirectory) true
        else false
      }

      def getDescription: String = ".ivy"
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
        if (f.getName.endsWith(".rs") || f.isDirectory) true
        else false
      }

      def getDescription: String = ".rs"
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
