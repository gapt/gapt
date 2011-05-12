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
    showFrame
    if (args.length >= 1) loadProof(args(0),12)
    else test
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
      contents += new Separator
      contents += new MenuItem(Action("TestRefutation") { testRefutation }) { border = customBorder }
      contents += new MenuItem(Action("test") { test }) { border = customBorder }
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
      contents += new MenuItem(Action("Show Struct") { showStruct }) {
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
    val csPre : List[Sequent] = StandardClauseSet.transformStructToClauseSet(s).map(_.getSequent)
    body.contents = new Launcher(Some("cllist",csPre),16)
  } catch {
      case e: AnyRef =>
        val t = e.toString
        Dialog.showMessage(new Label(t),"Couldn't compute ClList!\n\n"+t.replaceAll(",","\n"))
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

  def test = {
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

     implicit val factory = PointerFOFactoryInstance
    //--  Create LKS proof (Alex's example) --//

    //-- Some formula definitions
    val i = IntVar(new VariableStringSymbol("i"))
    val n = IntVar(new VariableStringSymbol("k"))
    val k = IntVar(new VariableStringSymbol("n"))
    val ai = IndexedPredicate(new ConstantStringSymbol("A"), i::Nil)
    val a0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero()::Nil)
    val a1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(IntZero())::Nil)
    val a_sn = IndexedPredicate(new ConstantStringSymbol("A"), Succ(n)::Nil)
    val a_ssn = IndexedPredicate(new ConstantStringSymbol("A"), Succ(Succ(n))::Nil)
    val and_0_0_ai = BigAnd(i, ai,IntZero(),IntZero())
    val and_0_1_ai = BigAnd(i, ai,IntZero(), Succ(IntZero()))
    val and_0_n_ai = BigAnd(i, ai,IntZero(), n)
    val and_0_sn_ai = BigAnd(i, ai,IntZero(), Succ(n))
    val and_0_ssn_ai = BigAnd(i, ai,IntZero(), Succ(Succ(n)))
    val or_0_0_not_ai = BigOr(i, Neg(ai), IntZero(), IntZero())
    val or_0_1_not_ai = BigOr(i, Neg(ai), IntZero(), Succ(IntZero()))
    val or_0_n_not_ai = BigOr(i, Neg(ai), IntZero(), n)
    val or_0_sn_not_ai = BigOr(i, Neg(ai), IntZero(), Succ(n))
    val or_0_ssn_not_ai = BigOr(i, Neg(ai), IntZero(), Succ(Succ(n)))
    // end of formula definitions --//

     //-- Some subproofs of varPhi_0 proof
    val psi0 = SchemaProofLinkRule(Sequent(and_0_0_ai::Or(or_0_0_not_ai, a1)::Nil, and_0_1_ai::Nil),
        "\\psi", IntZero()::Nil)
    val xi0 = SchemaProofLinkRule(Sequent(and_0_1_ai::or_0_1_not_ai::Nil, Nil), "\\xi", Succ(IntZero())::Nil)
    val p0 = NegRightRule(xi0, or_0_1_not_ai)
    // end of subproofs of varPhi_0 proof --//

    val varPhi_0 = CutRule(psi0, p0, and_0_1_ai)


     //-- Some subproofs of varPhi_n proof
    val psi = SchemaProofLinkRule(Sequent(and_0_sn_ai::Or(or_0_sn_not_ai, a_ssn)::Nil, and_0_ssn_ai::Nil),
        "\\psi", Succ(n)::Nil)
    val xi = SchemaProofLinkRule(Sequent(and_0_ssn_ai::or_0_ssn_not_ai::Nil, Nil), "\\xi", Succ(Succ(n))::Nil)
    val p = NegRightRule(xi, or_0_ssn_not_ai)
    // end of subproofs of varPhi_n proof --//

    val varPhi_sn = CutRule(psi, p, and_0_ssn_ai)


    //-- Some subproofs of xi_0 proof
    val x01 = AndEquivalenceRule3(Axiom(Sequent(a0::Nil, a0::Nil)), a0, and_0_0_ai)
    val x02 = NegLeftRule(x01, a0)
    // end of subproofs of xi_0 proof --//

    val xi_0 = OrEquivalenceRule3(x02, x02.prin.head, or_0_0_not_ai)

    //-- Some subproofs of xi_sn proof
    val x1 = NegLeftRule(Axiom(Sequent(a_sn::Nil, a_sn::Nil)), a_sn)
    val x2 = SchemaProofLinkRule(Sequent(and_0_n_ai::or_0_n_not_ai::Nil, Nil), "\\xi", n::Nil)
    val x3 = OrLeftRule(x2, x1, or_0_n_not_ai, Neg(a_sn))
    val x4 = OrEquivalenceRule1(x3, x3.prin.head, or_0_sn_not_ai)
    val x5 = AndLeftRule(x4, and_0_n_ai, a_sn)
    // end of subproofs of xi_sn proof --//

    val xi_sn = AndEquivalenceRule1(x5, x5.prin.head, and_0_sn_ai)

    //-- Some subproofs of phi_0 proof
    val y0 = AndEquivalenceRule3(Axiom(Sequent(a0::Nil, a0::Nil)), a0, and_0_0_ai)
    // end of subproofs of phi_sn proof --//

    val phi_0 = AndEquivalenceRule3(y0, a0, and_0_0_ai)


    //-- Some subproofs of phi_sn proof
    val y1 = AndRightRule(SchemaProofLinkRule(Sequent(and_0_n_ai::Nil, and_0_n_ai::Nil), "\\phi", n::Nil),
      Axiom(Sequent(a_sn::Nil, a_sn::Nil)), and_0_n_ai, a_sn)
    val y2 = AndEquivalenceRule1(y1, y1.prin.head, and_0_sn_ai)
    val y3 = AndLeftRule(y2, and_0_n_ai, a_sn)
    // end of subproofs of phi_sn proof --//

    val phi_sn = AndEquivalenceRule1(y3, y3.prin.head, and_0_sn_ai)


    //-- Some subproofs of psi_0 proof
    val z01 = OrLeftRule(SchemaProofLinkRule(Sequent(and_0_0_ai::or_0_0_not_ai::Nil, Nil), "\\xi", IntZero()::Nil),
      Axiom(Sequent(a1::Nil, a1::Nil)), or_0_0_not_ai, a1)
    val z02 = AndRightRule(SchemaProofLinkRule(Sequent(and_0_0_ai::Nil, and_0_0_ai::Nil), "\\phi", IntZero()::Nil),
      z01, and_0_0_ai, a1)
    val z03 = AndEquivalenceRule1(z02, z02.prin.head, and_0_1_ai)
    // end of subproofs of psi_0 proof --//

    val psi_0 = ContractionLeftRule(z03, and_0_0_ai)


    //-- Some subproofs of psi_sn proof
    val z1 = OrLeftRule(SchemaProofLinkRule(Sequent(and_0_sn_ai::or_0_sn_not_ai::Nil, Nil), "\\xi", Succ(n)::Nil),
      Axiom(Sequent(a_ssn::Nil, a_ssn::Nil)), or_0_sn_not_ai, a_ssn)
    val z2 = AndRightRule(SchemaProofLinkRule(Sequent(and_0_sn_ai::Nil, and_0_sn_ai::Nil), "\\phi", Succ(n)::Nil),
      z1, and_0_sn_ai, a_ssn)
    val z3 = AndEquivalenceRule1(z2, z2.prin.head, and_0_ssn_ai)
    // end of subproofs of psi_sn proof --//

    val psi_sn = ContractionLeftRule(z3, and_0_sn_ai)


          SchemaProofDB.clear
      SchemaProofDB.put( new SchemaProof( "\\xi", n::Nil,
        new Sequent(and_0_n_ai::or_0_n_not_ai::Nil, Nil),
        xi_0, xi_sn ) )
      SchemaProofDB.put( new SchemaProof( "\\phi", n::Nil,
        new Sequent(and_0_n_ai::Nil, and_0_n_ai::Nil),
        phi_0, phi_sn ) )
      SchemaProofDB.put( new SchemaProof( "\\psi", n::Nil,
        new Sequent(and_0_n_ai::Or(or_0_n_not_ai, a_sn)::Nil, and_0_sn_ai::Nil),
        psi_0, psi_sn ))
      SchemaProofDB.put( new SchemaProof( "\\varphi", n::Nil,
        new Sequent(and_0_n_ai::Or(or_0_n_not_ai, a_sn)::Nil, Neg(or_0_sn_not_ai)::Nil),
        varPhi_0, varPhi_sn ) )

      checkProofLinks( xi_0 )
      checkProofLinks( xi_sn )
      checkProofLinks( phi_0 )
      checkProofLinks( phi_sn )
      checkProofLinks( psi_0 )
      checkProofLinks( psi_sn )
      checkProofLinks( varPhi_0 )
      checkProofLinks( varPhi_sn )

      val cs = StandardClauseSet.transformStructToClauseSet( StructCreators.extractStruct( "\\varphi", k ) )
 //   body.contents = new Launcher(Some("Schema CL List", cs.map(x => x.getSequent)), 16)
    body.contents = new Launcher(Some("Schema varphi_sn", varPhi_sn), 16)
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