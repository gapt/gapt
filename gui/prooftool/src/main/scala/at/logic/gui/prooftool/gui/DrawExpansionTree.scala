package at.logic.gui.prooftool.gui

/**
 * Created with IntelliJ IDEA.
 * User: mrukhaia
 * Date: 9/13/12
 * Time: 12:51 PM
 */

import swing._
import event.{UIElementResized, MouseClicked}
import java.awt.{Font, Dimension, Color}
import java.awt.Font._
import java.awt.event.MouseEvent
import at.logic.language.hol._
import at.logic.calculi.expansionTrees.ExpansionTree
import at.logic.utils.ds.trees.{NonTerminalNodeA}

class DrawExpansionTree(val expansionTree: (Seq[ExpansionTree],Seq[ExpansionTree]), private val fSize: Int) extends SplitPane(Orientation.Vertical) {
  background = new Color(255,255,255)
  private val ft = new Font(SANS_SERIF, PLAIN, fSize)
  //private val width = toolkit.getScreenSize.width - 150
  //private val height = toolkit.getScreenSize.height - 150
  preferredSize = calculateOptimalSize
  dividerLocation = preferredSize.width / 2
  leftComponent = new SplitedExpansionTree(expansionTree._1, "Antecedent", ft)
  rightComponent = new SplitedExpansionTree(expansionTree._2, "Consequent", ft)

  def calculateOptimalSize = {
    val width = Main.top.size.width
    val height = Main.top.size.height
    if (width > 100 && height > 200)
      new Dimension(Main.top.size.width - 70, Main.top.size.height - 150)
    else new Dimension(width, height)
  }

  listenTo(Main.top)
  reactions += {
    case UIElementResized(Main.top) =>
      preferredSize = calculateOptimalSize
      revalidate
  }
}

class SplitedExpansionTree(val formulas: Seq[ExpansionTree], val label: String, private val ft: Font) extends BoxPanel(Orientation.Vertical) {
  contents += new Label(label) {
    font = ft.deriveFont(Font.BOLD)
    opaque = true
    border = Swing.EmptyBorder(10)
  }
  contents += new ScrollPane {
    peer.getVerticalScrollBar.setUnitIncrement( 20 )
    peer.getHorizontalScrollBar.setUnitIncrement( 20 )
    contents = new BoxPanel(Orientation.Vertical) {
      background = new Color(255,255,255)
      formulas.foreach( f => {
        val comp = formulaToComponent(f.asInstanceOf[NonTerminalNodeA[Option[HOLFormula],_]].node.get)
        comp.border = Swing.EmptyBorder(10)
        contents += comp
      })
    }
  }

  def formulaToComponent(t: HOLFormula): Component = t match {
    case Neg(f) => new BoxPanel(Orientation.Horizontal) {
      background = new Color(255,255,255)
      yLayoutAlignment = 0.5
      contents += label("¬",ft)
      contents += formulaToComponent(f)
    }
    case And(f1,f2) => new BoxPanel(Orientation.Horizontal) {
      background = new Color(255,255,255)
      yLayoutAlignment = 0.5
      contents += label("(",ft)
      contents += formulaToComponent(f1)
      contents += label("∧",ft)
      contents += formulaToComponent(f2)
      contents += label(")",ft)
    }
    case Or(f1,f2) => new BoxPanel(Orientation.Horizontal) {
      background = new Color(255,255,255)
      yLayoutAlignment = 0.5
      contents += label("(",ft)
      contents += formulaToComponent(f1)
      contents += label("∨",ft)
      contents += formulaToComponent(f2)
      contents += label(")",ft)
    }
    case Imp(f1,f2) => new BoxPanel(Orientation.Horizontal) {
      background = new Color(255,255,255)
      yLayoutAlignment = 0.5
      contents += label("(",ft)
      contents += formulaToComponent(f1)
      contents += label("⊃",ft)
      contents += formulaToComponent(f2)
      contents += label(")",ft)
    }
    case ExVar(v, f) => new BoxPanel(Orientation.Horizontal) {
      background = new Color(255,255,255)
      yLayoutAlignment = 0.5
      val lbl = DrawSequent.latexToLabel("(" + """\exists """ + DrawSequent.formulaToLatexString(v) + ")",ft)
      lbl.reactions += {
        case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 => PopupMenu(lbl, e.point.x, e.point.y)
      }
      contents += lbl
      contents += formulaToComponent(f)
    }
    case AllVar(v, f) => new BoxPanel(Orientation.Horizontal) {
      background = new Color(255,255,255)
      yLayoutAlignment = 0.5
      val lbl = DrawSequent.latexToLabel("(" + """\forall """ + DrawSequent.formulaToLatexString(v) + ")",ft)
      lbl.reactions += {
        case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 => PopupMenu(lbl, e.point.x, e.point.y)
      }
      contents += lbl
      contents += formulaToComponent(f)
    }
    case _ => val lbl = DrawSequent.formulaToLabel(t,ft)
      lbl.deafTo(lbl.mouse.moves, lbl.mouse.clicks)
      lbl
  }

  def label(s: String, fnt: Font) = new Label(s) {
    background = new Color(255,255,255)
    yLayoutAlignment = 0.5
    opaque = true
    font = fnt
  }
}