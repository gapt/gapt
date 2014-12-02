package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Oct 27, 2010
 * Time: 12:08:33 PM
 */

import scala.swing._
import BorderPanel._
import swing.Dialog.Message
import swing.Swing.EmptyIcon
import java.io.{BufferedWriter => JBufferedWriter, FileWriter => JFileWriter, ByteArrayInputStream, InputStreamReader, File}
import javax.swing.filechooser.FileFilter
import javax.swing.SwingUtilities
import at.logic.algorithms.lk._
import at.logic.algorithms.lksk.eliminateDefinitions
import at.logic.calculi.lk.base._
import at.logic.calculi.proofs.TreeProof
import at.logic.gui.prooftool.parser._
import at.logic.language.hol._
import at.logic.language.schema.IntVar
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
import at.logic.algorithms.shlk.{applySchemaSubstitution2, applySchemaSubstitution}
import at.logic.utils.ds.trees.Tree
import at.logic.transformations.herbrandExtraction.extractExpansionTrees
import at.logic.transformations.skolemization.skolemize
import at.logic.transformations.ceres.clauseSchema.{resolutionProofSchemaDB, InstantiateResSchema}
import at.logic.transformations.ceres.ACNF.ACNF
import at.logic.calculi.slk.SchemaProofDB
import at.logic.calculi.proofs.Proof
import java.awt.image.BufferedImage
import javax.imageio.ImageIO
import java.awt.Color
import at.logic.gui.prooftool.parser.ChangeFormulaColor
import at.logic.algorithms.rewriting.DefinitionElimination
import at.logic.algorithms.llk.HybridLatexExporter
import at.logic.parsing.language.tptp.TPTPFOLExporter


object Main extends SimpleSwingApplication {
  val body = new MyScrollPane
  val db = new FileParser
  val defaultFontSize = 12
  var launcher_history = List[(String, AnyRef, Int)]()

  override def startup(args: Array[String]) {
    showFrame()
    if (args.length >= 1) loadProof(args(0),defaultFontSize)
    else ProofToolPublisher.publish(DisableMenus)
  }

  def showFrame() {
    top.preferredSize = new Dimension(700,500)
    top.pack()
    top.centerOnScreen()
    top.open()
    top.maximize()
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
        updateLauncher(name, obj, defaultFontSize)
    }
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  def sunburstView() {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.getContent.getData match {
      case Some((name, proof : TreeProof[_]) ) => initSunburstDialog(name, proof)
      case _ => errorMessage("Proof not found!")
    }
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  def initSunburstDialog(name: String, proof: TreeProof[_]) {
    val d = new SunburstTreeDialog(name, proof)
    d.pack()
    d.centerOnScreen()
    d.open()
  }

  def displaySunburst[T](name: String, proof: TreeProof[T]) {
    showFrame()
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    loadProof((name, proof))
    initSunburstDialog(name, proof)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  def updateLauncher(name : String, proofobject : AnyRef, fSize : Int) : Unit = this.synchronized {
    val entry = (name, proofobject, fSize)
    this.launcher_history = entry :: this.launcher_history.filterNot(_ == entry)
    mBar.updateHistoryMenu(launcher_history)
    this.body.contents = new Launcher(Some((name, proofobject)), fSize)
   }

  def clearLauncher() = this.synchronized {
    this.body.contents = new Launcher(None, defaultFontSize)
  }

  def clearLauncherHistory()= this.synchronized {
    this.launcher_history = Nil
    clearLauncher()
  }

  def updateWithLastLauncher() = this.synchronized {
    this.launcher_history match {
      case current :: (last@(name, obj, size) :: rest) =>
        this.launcher_history = rest
        updateLauncher(name, obj, size)
      case _ =>
        ()
    }
  }

  def fOpen() {
    chooser.fileFilter = chooser.acceptAllFileFilter
    chooser.showOpenDialog(mBar) match {
      case FileChooser.Result.Approve => loadProof(chooser.selectedFile.getPath,defaultFontSize)
      case _ =>
    }
  }

  def fSave(pair: (String, AnyRef)) {
    chooser.fileFilter = chooser.acceptAllFileFilter
    chooser.showSaveDialog(mBar) match {
      case FileChooser.Result.Approve =>
        body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
        val result = chooser.selectedFile.getPath
        // val pair = body.getContent.getData.get
        pair._2 match {
          case proof: LKProof =>
            try {
              if (result.endsWith(".xml") || chooser.fileFilter.getDescription == ".xml") {
                XMLExporter(result, pair._1, proof)
              } else if (result.endsWith(".llk") || chooser.fileFilter.getDescription == ".llk") {
                val filename = if (result.endsWith(".llk")) result else result + ".llk"
                val file = new JBufferedWriter(new JFileWriter(filename))
                file.write(HybridLatexExporter(proof, escape_latex = true))
                file.close()
              } else if (result.endsWith(".tex") || chooser.fileFilter.getDescription == ".tex") {
                val filename = if (result.endsWith(".tex")) result else result + ".tex"
                val file = new JBufferedWriter(new JFileWriter(filename))
                file.write(ProofToLatexExporter(proof))
                file.close()
              } else infoMessage("Proofs cannot be saved in this format.")
            }
            catch { case e: Throwable => errorMessage("Cannot save the proof! \n\n" + getExceptionString(e)) }
            finally { body.cursor = java.awt.Cursor.getDefaultCursor }
          case list: List[_] =>
            try {
              val ls = list.map {
                case s: Sequent => s.toFSequent
                case fs: FSequent => fs
                case _ => throw new Exception("Cannot save this kind of lists.")
              }
              if (result.endsWith(".xml") || chooser.fileFilter.getDescription == ".xml") {
                XMLExporter(result, new ProofDatabase(Map(), Nil, Nil, List((pair._1, ls))))
              } else if (result.endsWith(".tex") || chooser.fileFilter.getDescription == ".tex") {
                val filename = if (result.endsWith(".tex")) result else result + ".tex"
                (new FileWriter(filename) with SequentsListLatexExporter with HOLTermArithmeticalExporter)
                  .exportSequentList(ls, Nil).close
              } else if (result.endsWith(".tptp") || chooser.fileFilter.getDescription == ".tptp") {
                val filename = if (result.endsWith(".tptp")) result else result + ".tptp"
                val file = new JBufferedWriter(new JFileWriter( filename ))
                file.write(TPTPFOLExporter.tptp_problem( ls ))
                file.close()
              } else infoMessage("Lists cannot be saved in this format.")
            }
            catch { case e: Throwable => errorMessage("Cannot save the list! \n\n" + getExceptionString(e)) }
            finally { body.cursor = java.awt.Cursor.getDefaultCursor }
          case _ => infoMessage("Cannot save this kind of objects.")
        }
      case _ =>
    }
  }

  def fSaveAll() {
    chooser.fileFilter = chooser.acceptAllFileFilter
    chooser.showSaveDialog(mBar) match {
      case FileChooser.Result.Approve =>
        body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
        val result = chooser.selectedFile.getPath
        try {
          if (result.endsWith(".xml") || chooser.fileFilter.getDescription == ".xml") {
            XMLExporter(result, db.getProofDB)
          } else if (result.endsWith(".tex") || chooser.fileFilter.getDescription == ".tex") {
            val filename = if (result.endsWith(".tex")) result else result + ".tex"
            val file = new JBufferedWriter(new JFileWriter(filename))
            file.write(ProofToLatexExporter(db.getProofs.map(pair => (pair._1, pair._2.asInstanceOf[LKProof]))))
            file.close()
          } else infoMessage("Proofs cannot be saved in this format.")
        } catch { case e: Throwable => errorMessage("Cannot save the file! \n\n" + getExceptionString(e))
        } finally { body.cursor = java.awt.Cursor.getDefaultCursor }
      case _ =>
    }
  }

  def fExportPdf(componentOption: Option[Component]) {
    if (componentOption != None) {
      chooser.fileFilter = chooser.peer.getChoosableFileFilters.find(f => f.getDescription == ".pdf").get
      chooser.showSaveDialog(mBar) match {
        case FileChooser.Result.Approve => try {
          body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
          import java.io.FileOutputStream
          import com.itextpdf.text.{Document, Rectangle => PdfRectangle}
          import com.itextpdf.text.pdf.PdfWriter

          val component = componentOption.get
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
      }
    } else infoMessage("There is nothing to export!")
  }

  def fExportPng(componentOption: Option[Component]) {
    if (componentOption != None) {
      chooser.fileFilter = chooser.peer.getChoosableFileFilters.find(f => f.getDescription == ".png").get
      chooser.showSaveDialog(mBar) match {
        case FileChooser.Result.Approve => try {
          body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)

          val component = componentOption.get
          val width = component.size.width
          val height = component.size.height
          val img = new BufferedImage(width, height, BufferedImage.TYPE_INT_RGB)
          val g = img.createGraphics()
          g.setBackground(new Color(255,255,255))
          g.fillRect(0,0,width,height)
          component.paint(g)
          val result = chooser.selectedFile.getPath
          val path = if (result.endsWith(".png")) result else result + ".png"
          ImageIO.write(img, "png", new File(path))
        } catch {
          case e: Throwable => errorMessage("Can't export to png! \n\n" + getExceptionString(e))
        } finally { body.cursor = java.awt.Cursor.getDefaultCursor }
        case _ =>
      }
    } else infoMessage("There is nothing to export!")
  }

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
          if (dp.proof.root.isInstanceOf[Sequent])
            ProofToolPublisher.publish(ChangeFormulaColor(Search.inTreeProof(input_str, dp.proof), Color.green, reset=true))
          else dp.searchNotInLKProof()
          dp.revalidate()
        case dp: DrawResolutionProof =>
          dp.search = input_str
          if (dp.proof.root.isInstanceOf[Sequent])
            ProofToolPublisher.publish(ChangeFormulaColor(Search.inResolutionProof(input_str, dp.proof), Color.green, reset=true))
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
    val launcher = body.getContent
    val pos = launcher.getLocationOfProof(proof).get
    val centered = new Rectangle( pos.x - body.bounds.width/2, pos.y - body.bounds.height, body.bounds.width, body.bounds.height )
    launcher.peer.scrollRectToVisible( centered )
  }

  // Used for PopupMenu, loads proof directly
  def loadProof(proof: LKProof) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    updateLauncher(proof.name, proof, defaultFontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used for ViewProof menu
  def loadProof(proof: (String, TreeProof[_])) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    updateLauncher(proof._1, proof._2, defaultFontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
    resetCuts()
  }

  // Used for ViewResolutionProof menu
  def loadResolutionProof(proof: (String, Proof[_])) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    updateLauncher(proof._1, proof._2, defaultFontSize)
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
    if (proofs.nonEmpty)
      updateLauncher(proofs.head._1, proofs.head._2, fontSize)
    else if (db.getSequentLists.size > 0)
      updateLauncher("",db.getSequentLists.head, fontSize)
    else if (db.getTermTrees.size > 0)
      updateLauncher(db.getTermTrees.head._1,db.getTermTrees.head._3, fontSize)
    else if (db.getResolutionProofs.size > 0)
      updateLauncher("", db.getResolutionProofs.head, fontSize)
    else clearLauncher()

  }

  // Used by View Clause List menu
  def loadClauseSet(clList: (String, List[_])) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    updateLauncher("clauses", clList, defaultFontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used by View Struct menu
  def loadStruct(struct: (String, Tree[_])) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    updateLauncher("struct", struct, defaultFontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used for Zooming
  def load(option: Option[(String, AnyRef)], fontSize: Int) {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    option match {
      case Some((name, obj)) => updateLauncher(name, obj, fontSize)
      case None => clearLauncher()
    }
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used by "Cycle through cuts"
  private var searchResult : List[LKProof] = null
  private var currentResult : Iterator[LKProof] = null

  def focusNextCut() = {
    // TODO: reset cuts when loading a proof
    if (Main.currentResult != null) {
      if (Main.currentResult.hasNext) {
        val cut = Main.currentResult.next()
        Main.scrollToProof(cut)
      } else {
        Main.currentResult = Main.searchResult.iterator
      }
    }
  }

  // Should be called whenever the proof is changed.
  def resetCuts() {
    searchResult = null
    currentResult = null
  }

  def setSearchResult(l:List[LKProof]) = if (l != null) {
    searchResult = l
    currentResult = l.iterator
  }

  val mBar = new MyMenubar

  def specifyResolutionSchema() {
    val t = TextAreaDialog("Please enter resolution proof schema:")
    if (t != None && t.get != "") try {
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      db.rsFileReader(new InputStreamReader(new ByteArrayInputStream(t.get.getBytes("UTF-8"))))
      val tp = db.getTermTrees.head
      updateLauncher(tp._1, tp._3, 14)
      body.cursor = java.awt.Cursor.getDefaultCursor
      ProofToolPublisher.publish(ProofDbChanged)
    } catch {
      case e: Throwable =>
        errorMessage("Cannot parse the specified resolution schema!\n\n" + getExceptionString(e))
    }
  }

  def expansionTree() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val et = extractExpansionTrees(body.getContent.getData.get._2.asInstanceOf[LKProof], false)
    updateLauncher("Expansion Tree",et, 14)
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
    updateLauncher(data._1+"_sk", proof, 14)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
    case e: Throwable =>
      errorMessage("Cannot skolemize the proof!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def regularizeProof() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val data = body.getContent.getData.get
    val proof = regularize(data._2.asInstanceOf[LKProof])
    db.addProofs((data._1+"_reg", proof)::Nil)
    updateLauncher(data._1+"_reg",proof, 14)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
    case e: Throwable =>
      errorMessage("Cannot regularize the proof!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def extractCutFormulas() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val list = cutformulaExtraction( body.getContent.getData.get._2.asInstanceOf[LKProof] )
    db.addSeqList("cutFormulaList ", list.map(x => x.toFSequent) )
    updateLauncher("Cut-formula List", list, 16)
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
    updateLauncher( proofs.head._1, proofs.head._2 ,defaultFontSize)
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

    db.addSeqList(csPre.map(x => x.toFSequent))
    updateLauncher("cllist", csPre, 16)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
    case e: Throwable =>
      errorMessage("Couldn't compute ClList!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def computeSchematicClauseSet() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val n = IntVar("n")

    val s = StructCreators.extractStruct( body.getContent.getData.get._1, n)
    val cs : List[Sequent] = DeleteRedundantSequents( DeleteTautology( StandardClauseSet.transformStructToClauseSet(s) ))
    val pair = renameCLsymbols( cs )

    db.addSeqList(pair._1) //.map(x => x.toFSequent))
    db.addDefinitions(pair._2)
    updateLauncher("Schematic Clause Set", pair._1, 16)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
    case e: Throwable =>
      errorMessage("Couldn't compute clause set!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def computeSchematicStruct() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val n = IntVar("n")
    val s = StructCreators.extractRelevantStruct( body.getContent.getData.get._1, n)
    val structs_base = s._2.map(pair => (pair._1, db.TermType.ClauseTerm, structToExpressionTree.prunedTree(pair._2)) )
    val structs_step = s._1.map(pair => (pair._1, db.TermType.ClauseTerm, structToExpressionTree.prunedTree(pair._2)) )
    db.addTrees( structs_step ::: structs_base )
    updateLauncher(structs_step.head._1, structs_step.head._3, defaultFontSize)
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
    updateLauncher(pterms.head._1, pterms.head._2, defaultFontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
    case e: Throwable =>
      errorMessage("Couldn't compute Projection Terms!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def computeClListOnlyQuantifiedCuts() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof_sk = eliminateDefinitions(LKtoLKskc( body.getContent.getData.get._2.asInstanceOf[LKProof] ))
    val s = StructCreators.extract( proof_sk, f => containsQuantifier(f) )
    val csPre : List[Sequent] = DeleteRedundantSequents( DeleteTautology( StandardClauseSet.transformStructToClauseSet(s) ))
    db.addSeqList(csPre.map(x => x.toFSequent))
    updateLauncher("cllist", csPre, 16)
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
    updateLauncher("Struct", s, defaultFontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
    case e: Throwable =>
      errorMessage("Couldn't compute Struct!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  // Computes the struct, ignoring propositional cuts
  def computeStructOnlyQuantifiedCuts() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof_sk = eliminateDefinitions( LKtoLKskc( body.getContent.getData.get._2.asInstanceOf[LKProof] ) )
    val s = structToExpressionTree.prunedTree( StructCreators.extract( proof_sk, f => containsQuantifier(f) ) )
    db.addTermTree( s )
    updateLauncher("Struct", s, defaultFontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
    case e: Throwable =>
      errorMessage("Couldn't compute Struct!\n\n" + getExceptionString(e))
  } finally ProofToolPublisher.publish(ProofDbChanged) }

  def eliminateDefsLK() { try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val pair = body.getContent.getData.get
    val new_proof = AtomicExpansion(DefinitionElimination(db.getDefinitions, pair._2.asInstanceOf[LKProof]))
    db.addProofs((pair._1+" without def rules", new_proof)::Nil)
    updateLauncher(pair._1+" without Definitions", new_proof, 14)
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
    updateLauncher("Proof without Definitions", new_proof, 14)
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
    updateLauncher("Gentzen Result:", newProof, 14)
  } catch {
    case e: Throwable =>
      errorMessage("Couldn't eliminate all cuts!\n\n" + getExceptionString(e))
  } finally {
    db.addProofs(ReductiveCutElim.proofs.map(x => (x.name, x)))
    body.cursor = java.awt.Cursor.getDefaultCursor
    ProofToolPublisher.publish(ProofDbChanged)
  }}


  //TODO: Must calculate omega ancestors, currently it marks nothing
  def markOmegaAncestors() {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.getContent.getData match {
      case Some((_, proof : LKProof) ) =>
        ProofToolPublisher.publish(ChangeFormulaColor(Set(), Color.red, reset=false))
      case _ => errorMessage("LK proof not found!")
    }
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  def markCutAncestors() {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.getContent.getData match {
      case Some((_, proof : LKProof) ) =>
        ProofToolPublisher.publish(ChangeFormulaColor(getCutAncestors(proof), Color.green, reset=false))
      case _ => errorMessage("LK proof not found!")
    }
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  def hideSequentContext() {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.getContent.contents.head match {
      case dp: DrawProof => body.getContent.getData match {
        case Some((name, proof : LKProof) ) =>
          dp.setVisibleOccurrences(Some(getAuxFormulas(proof)))
          dp.revalidate()
        case _ => errorMessage("This is not an LK proof!")
      }
      case _ => errorMessage("LK proof not found!")
    }
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  def hideAllFormulas() {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.getContent.contents.head match {
      case dp: DrawProof => body.getContent.getData match {
        case Some((name, proof : LKProof) ) =>
          dp.setVisibleOccurrences(Some(Set()))
          dp.revalidate()
        case _ => errorMessage("This is not an LK proof!")
      }
      case _ => errorMessage("LK proof not found!")
    }
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  def showAllFormulas() {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.getContent.contents.head match {
      case dp: DrawProof => body.getContent.getData match {
        case Some((name, proof : LKProof) ) =>
          dp.setVisibleOccurrences(None)
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
          updateLauncher(name + "↓" + number, proof, defaultFontSize)
        case (name: String, pt: Tree[_]) if db.getTermTrees.exists(p => name == p._1 && p._2 == db.TermType.ProjectionTerm) =>
          val (term,list) = UnfoldProjectionTerm(name,number)
          val gterm_name = name.replace("_step","").replace("_base","")  + "↓" + number
          db.addTermTree( gterm_name, term )
          db.addProofs(list)
          updateLauncher(gterm_name, term, defaultFontSize)
          infoMessage("The proof projections, corresponding to this term, are also computed.\n" +
            "They can be found in the View Proof menu!")
        case (name: String, pt: Tree[_]) if db.getTermTrees.exists(p => name == p._1 && p._2 == db.TermType.ClauseTerm) => errorMessage("Not yet implemented!")
        case (name: String, pt: Tree[_]) if db.getTermTrees.exists(p => name == p._1 && p._2 == db.TermType.ResolutionTerm) =>
          val proof = InstantiateResSchema(name,number)
          db.addProofs(proof::Nil)
          updateLauncher(proof._1, proof._2, defaultFontSize)
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
        updateLauncher(input._1 + "↓" + input._3 + "_acnf", proof, defaultFontSize)
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

  def getExceptionString(e: Throwable): String = {
    val st = e.toString.replaceAll(",",",\n") + "\n"
    val trace = e.getStackTrace
    if (trace.length > 10)
      Range(0,10).map(i => trace.apply(i)).foldLeft(st)((s, x) => s + "\n   at " + x.toString) + "\n   ......."
    else e.getStackTrace.toString
  }

  private val chooser = new FileChooser {
    val extensions = List(".gz",".ivy",".lks",".lksc",".llk",".pdf",".png",".rs",".tex",".tptp",".xml")
    extensions.foreach( fe => peer.addChoosableFileFilter(
      new FileFilter {
        def accept(f: File): Boolean = {
          if (f.getName.endsWith(fe) || f.isDirectory) true
          else false
        }
        def getDescription = fe
      }
    ))

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

