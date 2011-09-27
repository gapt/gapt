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
import at.logic.calculi.lk.base.{Sequent, LKProof}
import at.logic.calculi.treeProofs.TreeProof
import at.logic.transformations.ReductiveCutElim
import javax.swing.filechooser.FileFilter
import java.io.File
import swing.Dialog.Message
import scala.collection.immutable.Seq

object Main extends SimpleSwingApplication {

  override def startup(args: Array[String]) = {
    showFrame
    if (args.length >= 1) loadProof(args(0),12)
  }

  def showFrame: Unit = {
    val t = top
    t.pack
    t.location = new Point(100,50)
    t.size = new Dimension(700,500)
    t.visible = true
  }

  // Used for displaying things directly from Scala shell
  def display(name: String, obj: AnyRef): Unit = {
    showFrame
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(Some(name, obj), 12)
    body.cursor = java.awt.Cursor.getDefaultCursor
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

  // Used for ShowProof menu, loads proof directly
  def loadProof(proof: LKProof): Unit = {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(Some(proof.name, proof), 14)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used for ShowProof menu
  def loadProof(proof: (String, TreeProof[_])): Unit = {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(Some(proof), 12)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used by startup and open dialog
  def loadProof(path: String, fontSize: Int): Unit = {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    db.parseFile(path)
    val proofs = db.getProofs
    if (proofs.size > 0) body.contents = new Launcher(Some(proofs.head), fontSize)
    else body.contents = new Launcher(None, fontSize)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }

  // Used by Show Clause List menu
  def loadClauseSet(clList: (String, List[Sequent])): Unit = {
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(Some(clList), 12)
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
    import at.logic.language.hol.{HOLFormula}

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
      contents += new MenuItem(Action("ShowLeaves") { StructPublisher.publish(ShowLeaf) }) {
        border = customBorder
        enabled = false
        listenTo(StructPublisher)
        reactions += {
          case Loaded => this.enabled = true
          case UnLoaded => this.enabled = false
        }
      }
      contents += new Separator

      contents += new MenuItem(Action("Compute ClList") { computeClList }) {
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => this.enabled = true
          case UnLoaded => this.enabled = false
        }
      }
      contents += new MenuItem(Action("Compute ClList (Only Quantified Cuts)") { computeClListOnlyQuantifiedCuts }) {
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => this.enabled = true
          case UnLoaded => this.enabled = false
        }
      }
      contents += new Separator
      contents += new MenuItem(Action("Gentzen Method") { gentzen }) { border = customBorder }
      contents += new Separator
      contents += new MenuItem(Action("TestRefutation") { testRefutation }) { border = customBorder }
      contents += new MenuItem(Action("TestSchemata") { testSchemata }) { border = customBorder }
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
            val l = db.getProofs
            contents.clear
            for (i <- l) contents += new MenuItem(Action(i._1) { loadProof(i) }) { border = customBorder }
          case GentzenLoaded =>
            val l = ReductiveCutElim.proofs
            contents.clear
            for (i <- l) contents += new MenuItem(Action(i.name) { loadProof(i) }) { border = customBorder }
        }
      }
      contents += new Menu("Show Clause List") {
        mnemonic = Key.C
        border = customBorder
        listenTo(ProofToolPublisher)
        reactions += {
          case ProofDbChanged =>
            import at.logic.calculi.occurrences._
            import at.logic.calculi.lk.base.types.FSequent
            implicit val factory = defaultFormulaOccurrenceFactory
            implicit def fo2occ(f:HOLFormula) = factory.createFormulaOccurrence(f, Seq.empty[FormulaOccurrence])
            implicit def fseq2seq(s : FSequent) = Sequent(s._1 map fo2occ, s._2 map fo2occ  )
            val l = db.getSequentLists.map(pair => Pair(pair._1, pair._2.map(fs => fseq2seq(fs))))
            contents.clear
            for (i <- l) contents += new MenuItem(Action(i._1) { loadClauseSet(i) }) { border = customBorder }
          case GentzenLoaded =>
            contents.clear
        }
      }
      contents += new MenuItem(Action("Show Struct") { showStruct }) {
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => enabled = true
          case UnLoaded => enabled = false
        }
      }
      contents += new MenuItem(Action("Show Struct (OnlyQuantifiedCuts)") { showStructOnlyQuantifiedCuts }) {
        border = customBorder
        enabled = false
        listenTo(ProofToolPublisher)
        reactions += {
          case Loaded => enabled = true
          case UnLoaded => enabled = false
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
    val csPre : List[Sequent] = StandardClauseSet.transformStructToClauseSet(s)
    body.contents = new Launcher(Some("cllist",csPre),16)
  } catch {
      case e: AnyRef =>
        val t = e.toString
        Dialog.showMessage(body,"Couldn't compute ClList!\n\n"+t.replaceAll(",","\n"))
  }
  def computeClListOnlyQuantifiedCuts = try {
    import at.logic.transformations.skolemization.lksk.LKtoLKskc
    import at.logic.transformations.ceres.struct.StructCreators
    import at.logic.transformations.ceres.clauseSets.StandardClauseSet

    val proof_sk = LKtoLKskc( body.getContent.getData.get._2.asInstanceOf[LKProof] )
    //commented by Cvetan
//    val s = StructCreators.extract( proof_sk, f => f.containsQuantifier )
    val s = StructCreators.extract( proof_sk)
    val csPre : List[Sequent] = StandardClauseSet.transformStructToClauseSet(s)
    body.contents = new Launcher(Some("cllist",csPre),16)
  } catch {
      case e: AnyRef =>
        val t = e.toString
        Dialog.showMessage(body,"Couldn't compute ClList!\n\n"+t.replaceAll(",","\n"))
  }


  def showStruct = try {
    import at.logic.transformations.skolemization.lksk.LKtoLKskc
    import at.logic.transformations.ceres.struct.{StructCreators, structToExpressionTree}

    val proof_sk = LKtoLKskc( body.getContent.getData.get._2.asInstanceOf[LKProof] )
    val s = structToExpressionTree( StructCreators.extract( proof_sk ) )
    body.contents = new Launcher(Some("Struct",s),12)
  } catch {
      case e: AnyRef =>
        val t = e.toString
        Dialog.showMessage(body,"Couldn't compute Struct!\n\n"+t.replaceAll(",","\n"))
  }

  // Computes the struct, ignoring propositional cuts
  def showStructOnlyQuantifiedCuts = try {
    import at.logic.transformations.skolemization.lksk.LKtoLKskc
    import at.logic.transformations.ceres.struct.{StructCreators, structToExpressionTree}

    val proof_sk = LKtoLKskc( body.getContent.getData.get._2.asInstanceOf[LKProof] )
//commented by Cvetan
//    val s = structToExpressionTree( StructCreators.extract( proof_sk, f => f.containsQuantifier ) )
    val s = StructCreators.extract( proof_sk)

    body.contents = new Launcher(Some("Struct",s),12)
  } catch {
      case e: AnyRef =>
        val t = e.toString
        Dialog.showMessage(body,"Couldn't compute Struct!\n\n"+t.replaceAll(",","\n"))
  }

  def gentzen = try {
    val steps = Dialog.showConfirmation(body, "Do you want to see intermediary steps?",
      "ProofTool", Dialog.Options.YesNo, Message.Question) match {
      case Dialog.Result.Yes => true
      case _ => false
    }
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val proof = ReductiveCutElim(body.getContent.getData.get._2.asInstanceOf[LKProof], steps)
    body.contents = new Launcher(Some("Gentzen Result", proof),14)
    body.cursor = java.awt.Cursor.getDefaultCursor
  } catch {
    case e: Exception =>
        val t = e.toString + "\n\n" + e.getStackTraceString
        var k = 0
        val index = t.indexWhere( (x => {if (x == '\n') k += 1; if (k == 51) true; else false}))
        Dialog.showMessage(body, t.dropRight(t.size - index - 1))
  } finally ProofToolPublisher.publish(GentzenLoaded)


                 //commendet by Cvetan
  def testRefutation =  { /*
    import at.logic.calculi.resolution.andrews._
    import at.logic.calculi.resolution.base.InitialSequent
    import at.logic.language.hol._
    import logicSymbols.ConstantStringSymbol
    import at.logic.calculi.occurrences._

    implicit val factory = defaultFormulaOccurrenceFactory
      val a = Atom(ConstantStringSymbol("p"), Nil)
      val s = Sequent(Seq.empty[FormulaOccurrence], factory.createFormulaOccurrence(Neg(Or(a, Neg(a))), Seq.empty[FormulaOccurrence]) +: Seq.empty[FormulaOccurrence])

      val p0 = InitialSequent[Sequent](s)
      val p1 = NotT( p0, p0.root.succedent.head )
      val p2 = OrFL( p1, p1.root.antecedent.head )
      val p3 = OrFR( p1, p1.root.antecedent.head )
      val p4 = NotF( p3, p3.root.antecedent.head )
      val p5 = Cut( p4, p2, p4.root.succedent.head, p2.root.antecedent.head )
    body.contents = new Launcher(Some("resolution refutation",p5),16)
*/  }

  def testSchemata = {
  /*  import org.scilab.forge.jlatexmath._
    import java.awt.image.BufferedImage
    import java.awt.Color

    val string = "\\bigwedge_{i=0}^{n} A_{i} \\vdash \\bigvee_{i=0}^n A_{i}"
    val formula = new TeXFormula(string)

    val icon = formula.createTeXIcon(TeXConstants.STYLE_DISPLAY, 30)
	  icon.setInsets(new Insets(5, 5, 5, 5))

    val image = new BufferedImage(icon.getIconWidth(), icon.getIconHeight(), BufferedImage.TYPE_INT_ARGB)
    val g2 = image.createGraphics()
	  g2.setColor(Color.white)
	  g2.fillRect(0,0,icon.getIconWidth(),icon.getIconHeight())
	  val jl = new Label
	  jl.foreground = new Color(0, 0, 0)
	  icon.paintIcon(jl.peer, g2, 0, 0)
    jl.icon = icon
    body.viewportView = jl*/

    import at.logic.calculi.lk.macroRules.AndLeftRule
    import at.logic.calculi.lk.base._
    import at.logic.language.schema._
    import at.logic.calculi.slk._
    import at.logic.calculi.lk.propositionalRules._
    import at.logic.language.lambda.symbols.VariableStringSymbol
    import at.logic.language.hol.logicSymbols.ConstantStringSymbol
    import at.logic.calculi.occurrences._
    import at.logic.transformations.ceres.struct._
    import at.logic.transformations.ceres.clauseSets.StandardClauseSet
    import at.logic.parsing.writers.FileWriter
//    import at.logic.parsing.calculi.latex.SequentsListLatexExporter
    //import at.logic.parsing.language.arithmetic.HOLTermArithmeticalExporter

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
    import at.logic.language.hol.{HOLFormula}

    //-- Definition of psi_base
    val orl0 = OrLeftRule(NegLeftRule( Axiom(a0 +: Seq.empty[HOLFormula], a0 +: Seq.empty[HOLFormula]), a0 ), Axiom( a1 +: Seq.empty[HOLFormula], a1 +: Seq.empty[HOLFormula]), Neg(a0), a1)
    val psi_0 = AndEquivalenceRule3(orl0, not_a0_lor_a1, and_0_0_not_ai_lor_asi)
    // end of definition of psi_base --//
    import at.logic.calculi.lk.base.types.FSequent
    implicit def fo2occ(f:HOLFormula) = factory.createFormulaOccurrence(f, Seq.empty[FormulaOccurrence])
    implicit def fseq2seq(s : FSequent) = Sequent(s._1 map fo2occ, s._2 map fo2occ  )

    //-- Definition of psi_step
    val psi_k = SchemaProofLinkRule(Pair(a0 +: and_0_k_not_ai_lor_asi +: Seq.empty[HOLFormula], ask +: Seq.empty[HOLFormula]), "\\psi", k::Nil)
    val orlsk = OrLeftRule(NegLeftRule( Axiom( ask +: Seq.empty[HOLFormula], ask +: Seq.empty[HOLFormula]), ask ), Axiom( assk +: Seq.empty[HOLFormula], assk +: Seq.empty[HOLFormula]), Neg(ask), assk)
    val cut = CutRule(psi_k, orlsk, ask)
    val psi_sk = AndEquivalenceRule1(AndLeftRule(cut, and_0_k_not_ai_lor_asi, not_ask_lor_assk),
      And(and_0_k_not_ai_lor_asi, not_ask_lor_assk), and_0_sk_not_ai_lor_asi)
    // end of definition of psi_step --//

    SchemaProofDB.clear
    SchemaProofDB.put( new SchemaProof( "\\psi", k::Nil,
        Pair(a0 +: and_0_k_not_ai_lor_asi +: Seq.empty[HOLFormula], ask +: Seq.empty[HOLFormula]),
        psi_0, psi_sk ))

    checkProofLinks( psi_0 )
    checkProofLinks( psi_sk )

    val cs = StandardClauseSet.transformStructToClauseSet( StructCreators.extractStruct( "\\psi", n ) )
  //  (new FileWriter("cs-psi.tex") with SequentsListLatexExporter with HOLTermArithmeticalExporter).exportSequentList(cs.map(so => so.getSequent), Nil).close
   // body.contents = new Launcher(Some("Schema CL List", cs.map(x => x.getSequent)), 16)
    body.contents = new Launcher(Some("Schema psi_sn", psi_sk), 16)
  }

  val body = new MyScrollPane
  val db = new FileParser
  private val chooser = new FileChooser {
    fileFilter = new FileFilter {
      def accept(f: File): Boolean = {
        if (f.getName.endsWith(".xml") || f.getName.endsWith(".xml.gz") || f.isDirectory) true
        else false
      }

      def getDescription: String = ".xml and .gz"
    }
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
