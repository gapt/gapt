package at.logic.gui.prooftool.gui

/**
 * Created with IntelliJ IDEA.
 * User: mrukhaia
 * Date: 10/22/12
 * Time: 3:22 PM
 */

// This file displays pairs of sequences.
// Mainly used to display FSequent and ExpansionTrees.

import swing._
import java.awt.{Dimension, Font, Color}
import java.awt.Font._
import swing.event.UIElementResized
import at.logic.language.hol.HOLFormula
import at.logic.calculi.expansionTrees.ExpansionTree


class DrawHerbrandSequent[T](val hSequent: (Seq[T], Seq[T]), private val fSize: Int) extends SplitPane(Orientation.Vertical) {
  background = new Color(255,255,255)
  private val ft = new Font(SANS_SERIF, PLAIN, fSize)
  //private val width = toolkit.getScreenSize.width - 150
  //private val height = toolkit.getScreenSize.height - 150
  preferredSize = calculateOptimalSize
  dividerLocation = preferredSize.width / 2
  leftComponent = side(hSequent._1, "Antecedent", ft)
  rightComponent = side(hSequent._2, "Consequent", ft)

  listenTo(Main.top)
  reactions += {
    case UIElementResized(Main.top) =>
      preferredSize = calculateOptimalSize
      revalidate()
  }

  def calculateOptimalSize = {
    val width = Main.top.size.width
    val height = Main.top.size.height
    if (width > 100 && height > 200)
      new Dimension(Main.top.size.width - 70, Main.top.size.height - 150)
    else new Dimension(width, height)
  }

  def side(hFormulas: Seq[T], label: String, ft: Font) = new BoxPanel(Orientation.Vertical) {
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
        hFormulas.foreach( f => contents += draw(f) )
      }
    }
  }

  def draw(hFormula: T) = hFormula match {
    case f: HOLFormula =>
      val comp = DrawSequent.formulaToLabel(f,ft)
      comp.border = Swing.EmptyBorder(10)
      comp
    case et: ExpansionTree =>
      import ExpansionTreeState._
      val comp = new DrawExpansionTree(et,Closed,ft)
      comp.border = Swing.EmptyBorder(10)
      comp
    case _ => new Label(hFormula.toString) {
      font = ft
    }
  }
}