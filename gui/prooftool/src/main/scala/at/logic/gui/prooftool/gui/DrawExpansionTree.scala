package at.logic.gui.prooftool.gui

/**
 * Created with IntelliJ IDEA.
 * User: mrukhaia
 * Date: 9/13/12
 * Time: 12:51 PM
 */

import at.logic.calculi.lk.base.Sequent
import swing._
import event.MouseClicked
import java.awt.{Font, Dimension, Color}
import at.logic.calculi.occurrences.FormulaOccurrence
import java.awt.Font._
import java.awt.event.MouseEvent

class DrawExpansionTree(val expansionTree: Sequent, private val fSize: Int) extends SplitPane(Orientation.Vertical) {
  background = new Color(255,255,255)
  private val ft = new Font(SANS_SERIF, PLAIN, fSize)
  //private val width = toolkit.getScreenSize.width - 150
  //private val height = toolkit.getScreenSize.height - 150
  preferredSize = calculateOptimalSize
  dividerLocation = preferredSize.width / 2
  leftComponent = new SplitedExpansionTree(expansionTree.antecedent, "Antecedents", ft)
  rightComponent = new SplitedExpansionTree(expansionTree.succedent, "Consequents", ft)

  def calculateOptimalSize = {
    val width = Main.top.size.width
    val height = Main.top.size.height
    if (width > 100 && height > 200)
      new Dimension(Main.top.size.width - 70, Main.top.size.height - 150)
    else new Dimension(width, height)
  }
}

class SplitedExpansionTree(val formulas: Seq[FormulaOccurrence], val label: String, private val ft: Font) extends BoxPanel(Orientation.Vertical) {
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
      formulas.foreach( fo => {
        val lbl = DrawSequent.formulaToLabel(fo.formula, ft)
        lbl.border = Swing.EmptyBorder(10)
        lbl.reactions += {
          case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 => PopupMenu(lbl, e.point.x, e.point.y)
        }
        contents += lbl
      })
    }
  }
}