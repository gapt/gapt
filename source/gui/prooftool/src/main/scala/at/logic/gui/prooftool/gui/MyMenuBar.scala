package at.logic.gui.prooftool.gui

import java.awt.Color

import at.logic.algorithms.lk.getCutsAsProofs
import at.logic.calculi.lk._
import at.logic.calculi.lk.base.LKProof
import at.logic.calculi.proofs.TreeProof
import at.logic.gui.prooftool.parser._
import at.logic.language.hol._
import at.logic.language.lambda.types.{To, Ti}

import scala.swing.event.Key
import scala.swing._

/**
 * Created by marty on 10/14/14.
 * The Menubar has not too much logic and mainly calls the Main object to perform tasks.
 */
class MyMenubar extends MenuBar {
  import javax.swing.KeyStroke
  import java.awt.event.{KeyEvent, ActionEvent => JActionEvent}

  val history_menu = new Menu("History") {
    mnemonic = Key.I
  }

  def updateHistoryMenu(history : List[(String, AnyRef, Int)]) = {
    history_menu.contents.clear()
    history_menu.contents += new MenuItem(Action("Clear History") {
      Main.clearLauncherHistory()
    })
    history_menu.contents += new Separator
    for ( (name,obj, size) <- history )
      history_menu.contents += new MenuItem(
        Action(name +" ("+size+")") {
          Main.updateLauncher(name, obj, size)
        })
  }

  focusable = true
  val customBorder = Swing.EmptyBorder(5,3,5,3)
  contents += new Menu("File") {
    mnemonic = Key.F
    contents += new MenuItem(Action("Open...") { Main.fOpen() }) {
      mnemonic = Key.O
      this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_O, JActionEvent.CTRL_MASK))
      border = customBorder
    }
    contents += new MenuItem(Action("Save as...") { Main.fSave(Main.body.getContent.getData.get) }) {
      mnemonic = Key.S
      this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_S, JActionEvent.CTRL_MASK))
      border = customBorder
      enabled = false
      listenTo(ProofToolPublisher)
      reactions += {
        case Loaded => enabled = true
        case UnLoaded => enabled = false
      }
    }
    contents += new MenuItem(Action("Save all as...") { Main.fSaveAll() }) {
      mnemonic = Key.A
      this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_A, JActionEvent.CTRL_MASK))
      border = customBorder
      listenTo(ProofToolPublisher)
      reactions += {
        case DisableMenus => enabled = false
        case EnableMenus => enabled = true
      }
    }
    contents += new Separator
    contents += new MenuItem(Action("Export to PDF") { Main.fExportPdf(Main.body.getContent.contents.headOption) }) {
      mnemonic = Key.D
      this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_D, JActionEvent.CTRL_MASK))
      border = customBorder
      listenTo(ProofToolPublisher)
      reactions += {
        case DisableMenus => enabled = false
        case EnableMenus => enabled = true
      }
    }
    contents += new MenuItem(Action("Export to PNG") { Main.fExportPng(Main.body.getContent.contents.headOption) }) {
      mnemonic = Key.N
      this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_N, JActionEvent.CTRL_MASK))
      border = customBorder
      listenTo(ProofToolPublisher)
      reactions += {
        case DisableMenus => enabled = false
        case EnableMenus => enabled = true
      }
    }
    contents += new Separator
    contents += new MenuItem(Action("Exit") { Main.fExit() }) {
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
    contents += new MenuItem(Action("Search...") { Main.search() }) {
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
      ProofToolPublisher.publish(new ShowAllRules(Main.body.getContent.getData.get._2.asInstanceOf[TreeProof[_]]))
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
    contents += new MenuItem(Action("Hide All Formulas") { Main.hideAllFormulas() }) {
      border = customBorder
      enabled = false
      listenTo(ProofToolPublisher)
      reactions += {
        case Loaded => this.enabled = true
        case UnLoaded => this.enabled = false
      }
    }
    contents += new MenuItem(Action("Hide Sequent Contexts") { Main.hideSequentContext() }) {
      border = customBorder
      enabled = false
      listenTo(ProofToolPublisher)
      reactions += {
        case Loaded => this.enabled = true
        case UnLoaded => this.enabled = false
      }
    }
    contents += new MenuItem(Action("Show All Formulas") { Main.showAllFormulas() }) {
      border = customBorder
      enabled = false
      listenTo(ProofToolPublisher)
      reactions += {
        case Loaded => this.enabled = true
        case UnLoaded => this.enabled = false
      }
    }
    contents += new Separator
    contents += new MenuItem(Action("Mark Cut-Ancestors") { Main.markCutAncestors() }) {
      border = customBorder
      enabled = false
      listenTo(ProofToolPublisher)
      reactions += {
        case Loaded => this.enabled = true
        case UnLoaded => this.enabled = false
      }
    }
    contents += new MenuItem(Action("Mark Ω-Ancestors") { Main.markOmegaAncestors() }) {
      border = customBorder
      enabled = false
      listenTo(ProofToolPublisher)
      reactions += {
        case Loaded => this.enabled = true
        case UnLoaded => this.enabled = false
      }
    }
    contents += new MenuItem(Action("Remove Marking") {
      ProofToolPublisher.publish(ChangeFormulaColor(Set(),Color.white,reset=true)) }) {
      border = customBorder
    }
    contents += new Separator
    contents += new MenuItem(Action("Extract Cut-Formulas") { Main.extractCutFormulas() }) {
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
    contents += new MenuItem(Action("Zoom In") { Main.zoomIn() }) {
      this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_UP , JActionEvent.ALT_MASK))
      border = customBorder
    }
    contents += new MenuItem(Action("Zoom Out") { Main.zoomOut() }) {
      this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_DOWN, JActionEvent.ALT_MASK))
      border = customBorder
    }
    contents += new MenuItem(Action("Jump To End-sequent") { Main.scrollToProof(Main.body.getContent.getData.get._2.asInstanceOf[LKProof])}) {
      this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_ENTER, JActionEvent.ALT_MASK))
      border = customBorder
      enabled = false
      listenTo(ProofToolPublisher)
      reactions += {
        case Loaded => this.enabled = true
        case UnLoaded => this.enabled = false
      }
    }
    contents += new MenuItem(Action("Find Cuts") {
      Main.setSearchResult(getCutsAsProofs(Main.body.getContent.getData.get._2.asInstanceOf[LKProof]))
    }) {
      this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_C, JActionEvent.ALT_MASK))
      border = customBorder
      enabled = false
      listenTo(ProofToolPublisher)
      reactions += {
        case Loaded => this.enabled = true
        case UnLoaded => this.enabled = false
      }
    }
    contents += new MenuItem(Action("Cycle through cuts") {
      Main.focusNextCut()
    }) {
      this.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_N, JActionEvent.ALT_MASK))
      border = customBorder
      enabled = false
      listenTo(ProofToolPublisher)
      reactions += {
        case Loaded => this.enabled = true
        case UnLoaded => this.enabled = false
      }
    }
    contents += new Separator
    contents += new Menu("View Proof") {
      MenuScroller.setScrollerFor(this.peer)
      mnemonic = Key.P
      border = customBorder
      listenTo(ProofToolPublisher)
      reactions += {
        case ProofDbChanged =>
          val l = Main.db.getProofs
          contents.clear()
          for (i <- l) contents += new MenuItem(Action(i._1) { Main.loadProof(i) }) { border = customBorder }
      }
    }
    contents += new Menu("View Clause List") {
      MenuScroller.setScrollerFor(this.peer)
      mnemonic = Key.C
      border = customBorder
      listenTo(ProofToolPublisher)
      reactions += {
        case ProofDbChanged =>
          val l = Main.db.getSequentLists
          contents.clear()
          for (i <- l) contents += new MenuItem(Action(i._1) { Main.loadClauseSet(i) }) { border = customBorder }
      }
    }
    contents += new Menu("View Resolution Proof") {
      MenuScroller.setScrollerFor(this.peer)
      mnemonic = Key.P
      border = customBorder
      listenTo(ProofToolPublisher)
      reactions += {
        case ProofDbChanged =>
          val l = Main.db.getResolutionProofs
          contents.clear()
          for (i <- l) contents += new MenuItem(Action(i._1) { Main.loadResolutionProof(i) }) { border = customBorder }
      }
    }
    contents += new MenuItem(Action("View Definition List") { Main.loadClauseSet(("Definition List", Main.db.getDefinitions.toList)) }) {
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
          val l = Main.db.getTermTrees
          contents.clear()
          for (i <- l) contents += new MenuItem(Action(i._1) { Main.loadStruct((i._1,i._3)) }) { border = customBorder }
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
      contents += new MenuItem(Action("All Cuts") { Main.computeClList() }) { border = customBorder }
      contents += new MenuItem(Action("Only Quantified Cuts") { Main.computeClListOnlyQuantifiedCuts() }) { border = customBorder }
    }
    contents += new Menu("Compute Struct") {
      contents += new MenuItem(Action("All Cuts") { Main.computeStruct() }) { border = customBorder }
      contents += new MenuItem(Action("Only Quantified Cuts") { Main.computeStructOnlyQuantifiedCuts() }) { border = customBorder }
    }
    contents += new MenuItem(Action("Compute Projections") { Main.computeProjections() }) { border = customBorder }
    contents += new Separator
    contents += new MenuItem(Action("Apply Gentzen's Method") { Main.gentzen(Main.body.getContent.getData.get._2.asInstanceOf[LKProof]) }) { border = customBorder }
    contents += new Separator
    contents += new MenuItem(Action("Extract Expansion Tree") { Main.expansionTree() }) { border = customBorder }
    contents += new Separator
    contents += new MenuItem(Action("Eliminate Definitions") { Main.eliminateDefsLK() }) { border = customBorder }
    contents += new MenuItem(Action("Skolemize") { Main.skolemizeProof() }) { border = customBorder }
    contents += new MenuItem(Action("Regularize") { Main.regularizeProof() }) { border = customBorder }
  }
  contents += new Menu("LKS Proof") {
    mnemonic = Key.P
    listenTo(ProofToolPublisher)
    reactions += {
      case DisableMenus => enabled = false
      case EnableMenus => enabled = true
    }
    contents += new MenuItem(Action("Compute Clause Set") { Main.computeSchematicClauseSet() }) {
      border = customBorder
      enabled = false
      listenTo(ProofToolPublisher)
      reactions += {
        case Loaded => enabled = true
        case UnLoaded => enabled = false
      }
    }
    contents += new MenuItem(Action("Compute Struct") { Main.computeSchematicStruct() }) {
      border = customBorder
      enabled = false
      listenTo(ProofToolPublisher)
      reactions += {
        case Loaded => enabled = true
        case UnLoaded => enabled = false
      }
    }
    contents += new MenuItem(Action("Compute Projection Term") { Main.computeSchematicProjectionTerm() }) {
      border = customBorder
      enabled = false
      listenTo(ProofToolPublisher)
      reactions += {
        case Loaded => enabled = true
        case UnLoaded => enabled = false
      }
    }
    contents += new MenuItem(Action("Compute ACNF") { Main.computeACNF() }) { border = customBorder }
    contents += new MenuItem(Action("Specify Resolution Schema") { Main.specifyResolutionSchema() } )  { border = customBorder }
    contents += new MenuItem(Action("Compute Instance") { Main.computeInstance() } )  { border = customBorder }
  }
  contents += new Menu("Sunburst") {
    contents += new MenuItem(Action("Sunburst View") { Main.sunburstView() }) {
      border = customBorder
      enabled = false
      listenTo(ProofToolPublisher)
      reactions += {
        case Loaded => enabled = true
        case UnLoaded => enabled = false
      }

    }
  }

  contents += history_menu

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
      val p = HOLVar("p", Ti -> To)
      val a = HOLVar("a", Ti)
      val b = HOLVar("b", Ti)
      val q = HOLVar("q", Ti -> To)
      val x = HOLVar("x", Ti)
      val px = Atom(p, x::Nil) // p(x)
      val pa = Atom(p, a::Nil) // p(a)
      val pb = Atom(p, b::Nil) // p(b)
      val qa = Atom(q, a::Nil) // q(a)
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

      Main.updateLauncher("Proof", andlft, Main.defaultFontSize)
      ProofToolPublisher.publish(EnableMenus)
    }) { border = customBorder }
    contents += new MenuItem(Action("Non-Prenex Proof 2") {
      val p = HOLVar("p", Ti -> To)
      val a = HOLVar("a", Ti)
      val b = HOLVar("b", Ti)
      val q = HOLVar("q", Ti -> To)
      val x = HOLVar("x", Ti)
      val y = HOLVar("y", Ti)
      val px = Atom(p, x::Nil) // p(x)
      val pa = Atom(p, a::Nil) // p(a)
      val pb = Atom(p, b::Nil) // p(b)
      val qy = Atom(q, y::Nil) // q(a)
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

      Main.updateLauncher("Proof", orrght, Main.defaultFontSize)
      ProofToolPublisher.publish(EnableMenus)
    }) { border = customBorder }
    contents += new MenuItem(Action("Nested Proof 1") {
      val p = HOLVar("p", Ti -> To)
      val a = HOLVar("a", Ti)
      val b = HOLVar("b", Ti)
      val q = HOLVar("q", Ti -> To)
      val x = HOLVar("x", Ti)
      val y = HOLVar("y", Ti)
      val px = Atom(p, x::Nil) // p(x)
      val pa = Atom(p, a::Nil) // p(a)
      val pb = Atom(p, b::Nil) // p(b)
      val qa = Atom(q, a::Nil) // q(a)
      val qy = Atom(q, y::Nil) // q(a)
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

      Main.updateLauncher("Proof", all3, Main.defaultFontSize)
      ProofToolPublisher.publish(EnableMenus)
    }) { border = customBorder }
  }
}
