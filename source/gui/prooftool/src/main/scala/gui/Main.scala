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
import java.io.File
import javax.swing.filechooser.FileFilter

import at.logic.algorithms.lk.{cutformulaExtraction, getAuxFormulas, getCutAncestors, replaceSubproof}
import at.logic.algorithms.lksk.eliminateDefinitions
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.base.{Sequent, LKProof}
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.slk.SchemaProofDB
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
import at.logic.transformations.ceres.unfolding.applySchemaSubstitution
import at.logic.transformations.ceres.projections.{DeleteTautology, DeleteRedundantSequents}
import at.logic.transformations.ceres.ProjectionTermCreators
import at.logic.transformations.ceres.autoprop._
import at.logic.utils.ds.trees.Tree

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
    case FileChooser.Result.Cancel =>
    case _ => loadProof(chooser.selectedFile.getPath,12)
  }

  def fSaveProof(tp: AnyRef) : Unit = chooser.showSaveDialog(mBar) match {
    case FileChooser.Result.Cancel =>
    case _ =>
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      tp match {
        case proof: LKProof => try {
          XMLExporter(chooser.selectedFile.getPath, "the-proof", proof)
        } catch {
          case e: AnyRef => errorMessage("Can't save the proof! \n\n" + e.toString)
        }
        case _ => infoMessage("This is not a proof, can't save it!")
      }
      body.cursor = java.awt.Cursor.getDefaultCursor
  }

  def fSaveAll : Unit = chooser.showSaveDialog(mBar) match {
    case FileChooser.Result.Cancel =>
    case _ => try {
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      XMLExporter(chooser.selectedFile.getPath, db.getProofDB)
    } catch {
      case e: AnyRef => errorMessage("Can't save the database! \n\n" + e.toString)
    } finally {  body.cursor = java.awt.Cursor.getDefaultCursor }
  }

  def fExportTPTP : Unit = chooser.showSaveDialog(mBar) match {
    case FileChooser.Result.Cancel =>
    case _ =>
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      body.getContent.getData.get._2  match {
        case l : List[_] => try {
          import java.io.{BufferedWriter => JBufferedWriter, FileWriter => JFileWriter}

          val list = l.map( x => x match {
            case s: Sequent => s.toFSequent
            case fs: FSequent => fs
            case _ => throw new Exception("This is not a clause set.")
          })

          val file = new JBufferedWriter(new JFileWriter( chooser.selectedFile.getPath ))
          file.write(at.logic.parsing.language.tptp.TPTPFOLExporter.tptp_problem( list ))
          file.close
        } catch {
          case e: AnyRef => errorMessage("Can't save the clause set! \n\n" + e.toString)
        }
        case _ => infoMessage("This is not a clause set, can't export it!")
      }
      body.cursor = java.awt.Cursor.getDefaultCursor
  }

  def fExportTeX : Unit = chooser.showSaveDialog(mBar) match {
    case FileChooser.Result.Cancel =>
    case _ =>
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      body.getContent.getData.get._2  match {
        case l : List[_] => try {
          val list = l.map( x => x match {
            case s: Sequent => s.toFSequent
            case fs: FSequent => fs
            case _ => throw new Exception("This is not a clause set.")
          })
          (new FileWriter( chooser.selectedFile.getPath ) with SequentsListLatexExporter with HOLTermArithmeticalExporter)
            .exportSequentList( list , Nil).close
        } catch {
          case e: AnyRef => errorMessage("Can't save the clause set! \n\n" + e.toString)
        }
        case _ => infoMessage("This is not a clause set, can't export it!")
      }
      body.cursor = java.awt.Cursor.getDefaultCursor
  }

  def fExit : Unit = System.exit(0)

  def zoomIn {
    val content = body.getContent
    content.fontSize * 3 / 2 match {
      case j: Int if j > 200 =>
      case j: Int => load(content.getData,j)
    }
  }

  def zoomOut {
    val content = body.getContent
    content.fontSize / 3 * 2 match {
      case j: Int if j < 10 =>
      case j: Int => load(content.getData,j)
    }
  }

  def search {
    val input_str = Dialog.showInput[String](body, "Please enter string to search:",
      "ProofTool", Dialog.Message.Plain, EmptyIcon, Seq(), "") match {
      case Some(str) => str
      case _ => ""
    }
    if (! input_str.isEmpty) try {
      body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
      body.getContent.contents.head match {
        case dp: DrawProof =>
          dp.search = input_str
          dp.setColoredOccurrences(Search.inTreeProof(input_str, dp.proof))
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
      case e: Exception => errorMessage(e.toString)
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
      contents += new Menu("Test Auto Propositional") {
        val list = Autoprop()
        for (i <- list) contents += new MenuItem(Action("Iteration " + list.indexOf(i).toString) {
          body.contents = new Launcher(Some("Number of inferences : "+rulesNumber(i), i), 16)
        }) { border = customBorder }
      }
      contents += new Separator
      contents += new MenuItem(Action("Test Schemata") { testSchemata }) { border = customBorder }
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
      case e: AnyRef =>
        val t = e.toString
        errorMessage("Couldn't extract CutFormula List!\n\n"+t.replaceAll(",","\n"))
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
      case e: AnyRef =>
        val t = e.toString
        errorMessage("Couldn't compute ClList!\n\n"+t.replaceAll(",","\n"))
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
      case e: AnyRef =>
        val t = e.toString
        errorMessage("Couldn't compute clause set!\n\n"+t.replaceAll(",","\n"))
  } finally ProofToolPublisher.publish(ProofDbChanged)

  def computeSchematicStruct : Unit = try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val n = IntVar(new VariableStringSymbol("n"))
    val s = structToExpressionTree.prunedTree( StructCreators.extractStruct( body.getContent.getData.get._1, n) )
    db.addStructTree( s )
    body.contents = new Launcher(Some("Schematic Struct",s),12)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: AnyRef =>
        val t = e.toString
        errorMessage("Couldn't compute Struct!\n\n"+t.replaceAll(",","\n"))
  } finally ProofToolPublisher.publish(ProofDbChanged)

  def computeSchematicProjectionTerm : Unit = try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof_name = body.getContent.getData.get._1
    val pterms = ProjectionTermCreators(proof_name)
    db.addTrees( pterms )
    body.contents = new Launcher(Some( pterms.head ),12)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: AnyRef =>
        val t = e.toString
        errorMessage("Couldn't compute Projection Terms!\n\n"+t.replaceAll(",","\n"))
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
      case e: AnyRef =>
        val t = e.toString
        errorMessage("Couldn't compute ClList!\n\n"+t.replaceAll(",","\n"))
  } finally ProofToolPublisher.publish(ProofDbChanged)

  def showStruct : Unit = try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof_sk = LKtoLKskc( body.getContent.getData.get._2.asInstanceOf[LKProof] )
    val s = structToExpressionTree.prunedTree( StructCreators.extract( proof_sk ) )
    db.addStructTree( s )
    body.contents = new Launcher(Some("Struct",s),12)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: AnyRef =>
        val t = e.toString
        errorMessage("Couldn't compute Struct!\n\n"+t.replaceAll(",","\n"))
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
      case e: AnyRef =>
        val t = e.toString
        errorMessage("Couldn't compute Struct!\n\n"+t.replaceAll(",","\n"))
  } finally ProofToolPublisher.publish(ProofDbChanged)

  def eliminateDefsLK : Unit = try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val pair = body.getContent.getData.get
    val new_proof = eliminateDefinitions( pair._2.asInstanceOf[LKProof]   )
    db.addProofs((pair._1+" without def rules", new_proof)::Nil)
    body.contents = new Launcher(Some("Proof without Definitions",new_proof),14)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: AnyRef =>
        val t = e.toString
        errorMessage("Couldn't eliminate definitions!\n\n"+t.replaceAll(",","\n"))
  } finally ProofToolPublisher.publish(ProofDbChanged)

  def eliminateDefsLKsk : Unit = try {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val pair = body.getContent.getData.get
    val new_proof = eliminateDefinitions( LKtoLKskc( pair._2.asInstanceOf[LKProof] )  )
    db.addProofs((pair._1+" without def rules", new_proof)::Nil)
    body.contents = new Launcher(Some("Proof without Definitions",new_proof),14)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
      case e: AnyRef =>
        val t = e.toString
        errorMessage("Couldn't eliminate definitions!\n\n"+t.replaceAll(",","\n"))
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
    case e: Exception =>
      val t = e.toString + "\n\n" + e.getStackTraceString
      var k = 0
      val index = t.indexWhere( (x => {if (x == '\n') k += 1; if (k == 51) true; else false}))
      Main.errorMessage(t.dropRight(t.size - index - 1))
    case e: AnyRef => Main.errorMessage(e.toString)
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
    val input = Dialog.showInput(body, "Please enter number of the instance:",
      "ProofTool", Dialog.Message.Plain, EmptyIcon, Seq(), "0") match {
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
      case e: AnyRef =>
        val t = e.toString
        errorMessage("Could not construct proof instance!\n\n"+t.replaceAll(",","\n"))
    }
  }

  def testSchemata {
    import at.logic.calculi.lk.macroRules._
    import at.logic.calculi.lk.base._
    import at.logic.language.schema._
    import at.logic.calculi.slk._
    import at.logic.calculi.lk.propositionalRules._
    import at.logic.language.hol.logicSymbols.ConstantStringSymbol
    import at.logic.calculi.occurrences._
    import at.logic.language.hol.{HOLFormula}

    implicit val factory = defaultFormulaOccurrenceFactory
    //--  Create LKS proof as in my presentation --//

    //-- Some formula definitions
    val i = IntVar(new VariableStringSymbol("i"))
    val n = IntVar(new VariableStringSymbol("n"))
    val k = IntVar(new VariableStringSymbol("k"))
    val ai = IndexedPredicate(new ConstantStringSymbol("A"), i::Nil)
    val asi = IndexedPredicate(new ConstantStringSymbol("A"), Succ(i)::Nil)
    val a0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero()::Nil)
    val a1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(IntZero())::Nil)
    val ask = IndexedPredicate(new ConstantStringSymbol("A"), Succ(k)::Nil)
    val assk = IndexedPredicate(new ConstantStringSymbol("A"), Succ(Succ(k))::Nil)
    val not_a0_lor_a1 = Or(Neg(a0), a1)
    val not_ask_lor_assk = Or(Neg(ask), assk)
    val and_0_0_not_ai_lor_asi = BigAnd(i, Or(Neg(ai), asi), IntZero(), IntZero())
    val and_0_k_not_ai_lor_asi = BigAnd(i, Or(Neg(ai), asi), IntZero(), k)
    val and_0_sk_not_ai_lor_asi = BigAnd(i, Or(Neg(ai), asi), IntZero(), Succ(k))
    // end of formula definitions --//

    //-- Definition of psi_base
    val orl0 = OrLeftRule(NegLeftRule( Axiom(a0 +: Seq.empty[HOLFormula], a0 +: Seq.empty[HOLFormula]), a0 ), Axiom( a1 +: Seq.empty[HOLFormula], a1 +: Seq.empty[HOLFormula]), Neg(a0), a1)
    val psi_0 = AndEquivalenceRule3(orl0, not_a0_lor_a1, and_0_0_not_ai_lor_asi)
    // end of definition of psi_base --//

    implicit def fo2occ(f:HOLFormula) = factory.createFormulaOccurrence(f, Seq.empty[FormulaOccurrence])
    implicit def fseq2seq(s : FSequent) = Sequent(s._1 map fo2occ, s._2 map fo2occ  )

    //-- Definition of psi_step
    val psi_k = SchemaProofLinkRule(FSequent(a0 +: and_0_k_not_ai_lor_asi +: Seq.empty[HOLFormula], ask +: Seq.empty[HOLFormula]), "\\psi", k::Nil)
    val orlsk = OrLeftRule(NegLeftRule( Axiom( ask +: Seq.empty[HOLFormula], ask +: Seq.empty[HOLFormula]), ask ), Axiom( assk +: Seq.empty[HOLFormula], assk +: Seq.empty[HOLFormula]), Neg(ask), assk)
    val cut = CutRule(psi_k, orlsk, ask)
    val psi_sk = AndEquivalenceRule1(AndLeftRule(cut, and_0_k_not_ai_lor_asi, not_ask_lor_assk),
      And(and_0_k_not_ai_lor_asi, not_ask_lor_assk), and_0_sk_not_ai_lor_asi)
    // end of definition of psi_step --//

    SchemaProofDB.clear
    SchemaProofDB.put( new SchemaProof( "\\psi", k::Nil,
        FSequent(a0 +: and_0_k_not_ai_lor_asi +: Seq.empty[HOLFormula], ask +: Seq.empty[HOLFormula]),
        psi_0, psi_sk ))

    checkProofLinks( psi_0 )
    checkProofLinks( psi_sk )

    //---------------------------- NEW EXAMPLE -----------------------------//
    val n1 = Succ(k)
    val n2 = Succ(n1)
    val n3 = Succ(n2)
    val zero = IntZero()
    val one = Succ(IntZero())
    val two = Succ(Succ(IntZero()))
    val A0 = IndexedPredicate(new ConstantStringSymbol("A"), zero)
    val A1 = IndexedPredicate(new ConstantStringSymbol("A"), one)
    val A2 = IndexedPredicate(new ConstantStringSymbol("A"), two)
    val Ai = IndexedPredicate(new ConstantStringSymbol("A"), i)
    val Ai1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(i))
    val orneg = Or(Neg(Ai), Ai1)
    val An1 = IndexedPredicate(new ConstantStringSymbol("A"), n1)
    val An2 = IndexedPredicate(new ConstantStringSymbol("A"), n2)
    val An3 = IndexedPredicate(new ConstantStringSymbol("A"), n3)

    //-------- Definition of \psi_base

    val ax1 = Axiom(Sequent(A0::Nil, A0::Nil))
    val negl1 = NegLeftRule(ax1,A0)
    val ax2 = Axiom(Sequent(A1::Nil, A1::Nil))
    val orl1 = OrLeftRule(negl1, ax2, Neg(A0), A1)
    val negl2 = NegLeftRule(orl1,A1)
    val ax3 = Axiom(Sequent(A2::Nil, A2::Nil))
    val orl2 = OrLeftRule(negl2, ax3, Neg(A1), A2)
    val ax4 = Axiom(Sequent(A0::Nil, A0::Nil))
    val negl3 = NegLeftRule(ax4,A0)
    val ax5 = Axiom(Sequent(A1::Nil, A1::Nil))
    val orl3 = OrLeftRule(negl3, ax5, Neg(A0), A1)
    val ax6 = Axiom(Sequent(A0::Nil, A0::Nil))
    val andEqR1 = AndRightEquivalenceRule3(ax6,A0, BigAnd(i,Ai,zero,zero))
    val orl22 = AndRightRule(andEqR1, orl3, BigAnd(i,Ai,zero,zero), A1)
    val contrl1 = ContractionLeftRule(orl22, A0)
    val andEqR2 = AndRightEquivalenceRule1(contrl1, And(BigAnd(i,Ai,zero,zero), A1), BigAnd(i,Ai,zero,one))
    val andr2 = AndRightRule(orl2, andEqR2, A2, BigAnd(i,Ai,zero,one))
    val andr3 = AndRightEquivalenceRule1(andr2, And(A2, BigAnd(i,Ai,zero,one)), BigAnd(i,Ai,zero,two))
    val contrl2 = ContractionLeftRule(andr3, A0)
    val contrl3 = ContractionLeftRule(contrl2, Or(Neg(A0),A1))
    val andleq3 = AndLeftEquivalenceRule3(contrl3, Or(Neg(A0),A1), BigAnd(i, Or(Neg(Ai),Ai1), zero, zero))
    val andlb = AndLeftRule(andleq3, Or(Neg(A1),A2), BigAnd(i, Or(Neg(Ai),Ai1), zero, zero))
    val base = AndLeftEquivalenceRule1(andlb, And(Or(Neg(A1),A2), BigAnd(i, Or(Neg(Ai),Ai1), zero, zero)), BigAnd(i, Or(Neg(Ai),Ai1), zero, one))

    //----------- end of definition of \psi_base

    //-------- Definition of \psi_step

    val pl2 = SchemaProofLinkRule(FSequent(A0::BigAnd(i,orneg,zero,n1)::Nil, BigAnd(i,Ai,zero,n2)::Nil), "\\psi", k)
    val wl2 = WeakeningLeftRule(pl2, Neg(An2))
    val pl3 = SchemaProofLinkRule(FSequent(A0::BigAnd(i,orneg,zero,n1)::Nil, BigAnd(i,Ai,zero,n2)::Nil), "\\psi", k)
    val wl3 = WeakeningLeftRule(pl3, An3)
    val orl5 = OrLeftRule(wl2, wl3, Neg(An2), An3)
    val cont1l = ContractionLeftRule(orl5, A0)
    val cont2l = ContractionLeftRule(cont1l, BigAnd(i,orneg,zero,n1))
    val pr2 = ContractionRightRule(cont2l, BigAnd(i,Ai,zero,n2))

    val pl1 = SchemaProofLinkRule(FSequent(A0::BigAnd(i,orneg,zero,n1)::Nil, BigAnd(i,Ai,zero,n2)::Nil), "\\psi", k)
    val ax66 = Axiom(Sequent(An2::Nil, An2::Nil))
    val andl222 = AndLeft2Rule(ax66, BigAnd(i,Ai,zero,n1), An2)
    val eq4 = AndLeftEquivalenceRule1(andl222, And(BigAnd(i,Ai,zero,n1), An2), BigAnd(i,Ai,zero,n2))
    val cut1 = CutRule(pl1, eq4, BigAnd(i,Ai,zero,n2))
    val neg4l = NegLeftRule(cut1, An2)
    val ax7 = Axiom(Sequent(An3::Nil, An3::Nil))
    val pr3 = OrLeftRule(neg4l, ax7, Neg(An2), An3)

    val andr5 = AndRightRule(pr2, pr3, BigAnd(i,Ai,zero,n2), An3)
    val equiv = AndRightEquivalenceRule1(andr5, And(BigAnd(i,Ai,zero,n2), An3), BigAnd(i,Ai,zero,n3))
    val contr5 = ContractionLeftRule(equiv, A0)
    val contr55 = ContractionLeftRule(contr5, BigAnd(i,orneg,zero,n1))
    val contr555 = ContractionLeftRule(contr55, Or(Neg(An2), An3))
    val andl555 = AndLeftRule(contr555, BigAnd(i,orneg,zero,n1), Or(Neg(An2), An3))
    val eq33 = AndLeftEquivalenceRule1(andl555, And(BigAnd(i,orneg,zero,n1), Or(Neg(An2), An3)), BigAnd(i,orneg,zero,n2))
    val negr33 = NegRightRule(eq33, A0)
    val pl13 = OrRightRule(negr33, Neg(A0), BigAnd(i,Ai,zero,n3))

    val ax10 = Axiom(Sequent(A0::Nil, A0::Nil))
    val nl6 = NegLeftRule(ax10, A0)
    val khin3 = SchemaProofLinkRule(FSequent(BigAnd(i,Ai,zero,n3)::Nil, BigAnd(i,Ai,zero,n3)::Nil), "\\chi", n3)
    val orl10 = OrLeftRule(nl6, khin3, Neg(A0), BigAnd(i,Ai,zero,n3))
    val step = CutRule(pl13, orl10, Or(Neg(A0), BigAnd(i,Ai,zero,n3)))

    //----------- end of definition of \psi_step

    //----------- Definition of \chi_0

    val chi0a = Axiom(Sequent(A0::Nil, A0::Nil))
    val eqq1 = AndLeftEquivalenceRule3(chi0a, A0, BigAnd(i,Ai,zero,zero))
    val chi0 = AndRightEquivalenceRule3(eqq1, A0, BigAnd(i,Ai,zero,zero))

    //----------- end of definition of \chi_0

    //----------- Definition of \chi_k+1

    val prh = SchemaProofLinkRule(FSequent(BigAnd(i,Ai,zero,k)::Nil, BigAnd(i,Ai,zero,k)::Nil), "\\chi", k)
    val ax8 = Axiom(Sequent(An1::Nil, An1::Nil))
    val andr6 = AndRightRule(prh, ax8, BigAnd(i,Ai,zero,k), An1)
    val eq44 = AndRightEquivalenceRule1(andr6, And(BigAnd(i,Ai,zero,k), An1), BigAnd(i,Ai,zero,n1))
    val andlc = AndLeftRule(eq44, BigAnd(i,Ai,zero,k), An1)
    val chin = AndLeftEquivalenceRule1(andlc, And(BigAnd(i,Ai,zero,k), An1), BigAnd(i,Ai,zero,n1))

    //----------- end of definition of \chi_k+1

    SchemaProofDB.clear
    SchemaProofDB.put(new SchemaProof("\\chi", k::Nil, FSequent(BigAnd(i,Ai,zero,k)::Nil, BigAnd(i,Ai,zero,k)::Nil), chi0, chin))
    SchemaProofDB.put(new SchemaProof("\\psi", k::Nil, FSequent(A0::BigAnd(i, orneg, zero, n1)::Nil, BigAnd(i,Ai,zero,n2)::Nil), base, step))

    db.addProofs(List(("\\chi", chi0), ("\\chi", chin), ("\\psi", base), ("\\psi", step)))
    ProofToolPublisher.publish(ProofDbChanged)

  //  checkProofLinks( base )
  //  checkProofLinks( step )
  //  checkProofLinks( chi0 )
  //  checkProofLinks( chin )

  /*  try {
      val cs = StandardClauseSet.transformStructToClauseSet( StructCreators.extractStruct( "\\psi", n ) )
     // (new FileWriter("cs-psi.tex") with SequentsListLatexExporter with HOLTermArithmeticalExporter).exportSequentList(cs.map(so => so.getSequent), Nil).close
      body.contents = new Launcher(Some(("Schema CL List", cs)), 16)
    } catch {
      case e: Exception =>
        val t = e.toString + "\n\n" + e.getStackTraceString
        var k = 0
        val index = t.indexWhere( (x => {if (x == '\n') k += 1; if (k == 51) true; else false}))
        errorMessage(t.dropRight(t.size - index - 1))
    }  */
    body.contents = new Launcher(Some("\\psi", step), 16)
  }

  def testSchematicClauseSet : Unit = try {
    import at.logic.transformations.ceres.struct._
    import at.logic.language.schema._
    import at.logic.utils.ds.Multisets.HashMultiset

      val n = IntVar(new VariableStringSymbol("n"))

      val s = StructCreators.extractStruct( "\\psi", n)
      val cs : List[Sequent] = DeleteRedundantSequents( DeleteTautology( StandardClauseSet.transformStructToClauseSet(s) ))

      val m_empty = HashMultiset[SchemaFormula]()
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
      case e: AnyRef =>
        val t = e.toString
        errorMessage("Couldn't compute ClList!\n\n"+t.replaceAll(",","\n"))
  } finally ProofToolPublisher.publish(ProofDbChanged)

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

  val body = new MyScrollPane
  val db = new FileParser
  private val chooser = new FileChooser {
    fileFilter = new FileFilter {
      def accept(f: File): Boolean = {
        if (f.getName.endsWith(".lks") || f.isDirectory) true
        else false
      }

      def getDescription: String = ".lks"
    }

    fileFilter = new FileFilter {
      def accept(f: File): Boolean = {
        if (f.getName.endsWith(".xml") || f.getName.endsWith(".xml.gz") || f.isDirectory) true
        else false
      }

      def getDescription: String = ".xml and .gz"
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
