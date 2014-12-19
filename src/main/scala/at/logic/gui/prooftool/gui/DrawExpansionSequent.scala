package at.logic.gui.prooftool.gui

// The code in this file displays expansion sequents.

import at.logic.utils.logging.Logger

import swing._
import java.awt.{Dimension, Font, Color}
import java.awt.Font._
import scala.swing.event.{MouseExited, MouseEntered, UIElementResized, MouseClicked, Event}
import at.logic.calculi.expansionTrees._
import java.awt.event.MouseEvent
import at.logic.calculi.expansionTrees.MultiExpansionTree
import at.logic.algorithms.expansionTrees.compressQuantifiers
import org.slf4j.LoggerFactory

trait DrawExpSeqLogger extends Logger{
  override def loggerName = "DrawExpSeqLogger"
}

/**
 * These events are used to tell a CedentPanel that two expansion trees should be switched, necessitating a redraw.
 * @param from Number of the first tree to be switched
 * @param to Number of the second tree to be switched
 */
private[gui] class SwitchEvent(val from: Int, val to: Int) extends Event

/**
 * This class takes care of drawing an ExpansionSequent.
 * @param expSequent The expansion sequent to be displayed
 * @param fSize The font size.
 */
class DrawExpansionSequent(val expSequent: ExpansionSequent, private val fSize: Int) extends SplitPane(Orientation.Vertical) with DrawExpSeqLogger {

  //Code for window geometry and appearance
  background = new Color(255,255,255)
  private val ft = new Font(SANS_SERIF, PLAIN, fSize)
  preferredSize = calculateOptimalSize
  dividerLocation =
    if (expSequent.antecedent.isEmpty)
      preferredSize.width / 5
    else if (expSequent.succedent.isEmpty)
      preferredSize.width * 4/5
    else
      preferredSize.width / 2

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

  //Code for contents
  val mExpSequent = compressQuantifiers(expSequent) //The input sequent is converted to MultiExpansionTrees
  val antecedentPanel: CedentPanel = new CedentPanel(mExpSequent.antecedent, "Antecedent", ft)
  val succedentPanel: CedentPanel = new CedentPanel(mExpSequent.succedent, "Succedent", ft)
  leftComponent = antecedentPanel
  rightComponent = succedentPanel
}

/**
 * Class for displaying a list of expansion trees and a title.
 * @param cedent The list of expansion trees to be displayed
 * @param title The title to be displayed at the top
 * @param ft The font to be used
 */
class CedentPanel(val cedent: Seq[MultiExpansionTree], val title: String, val ft: Font) extends BoxPanel(Orientation.Vertical) with DrawExpSeqLogger {

  //Code for the title label
  val titleLabel = new Label(title) {
    font = ft.deriveFont(Font.BOLD)
    opaque = true
    border = Swing.EmptyBorder(10)
    listenTo(mouse.clicks, mouse.moves)
    reactions += {
      case e: MouseEntered => foreground = Color.blue
      case e: MouseExited => foreground = Color.black
      case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
      PopupMenu(CedentPanel.this, e.point.x, e.point.y) //This brings up the menu that lets the user close/open/expand all trees on this side
    }
  }

  //Code for the expansion tree list
  var treeList = new TreeListPanel(cedent, ft)//treeList is the panel that contains the list of trees. It's contained in a ScrollPane.
  val scrollPane = new ScrollPane {
    peer.getVerticalScrollBar.setUnitIncrement( 20 )
    peer.getHorizontalScrollBar.setUnitIncrement( 20 )
    
    contents = treeList
  }

  //Add the title label and the scroll pane to the contents
  contents += titleLabel
  contents += scrollPane
}

/**
 * Class that displays a list of expansion trees.
 * @param trees The list of trees to be displayed
 * @param ft The font
 */
class TreeListPanel(trees: Seq[MultiExpansionTree], ft: Font) extends BoxPanel(Orientation.Vertical) with DrawExpSeqLogger {
  background = new Color(255, 255, 255)

  val n = trees.length
  var selected: Option[NumLabel] = None // We note which numLabel is currently selected (if any).
  val numLabels = (1 to n).map(i => new NumLabel(i)) // Generate numLabels from 1 to n
  numLabels.foreach{listenTo(_)}

  val drawnTrees = new Array[DrawExpansionTree](n) // Draw all the trees. This is a mutable array so we can reorder the drawn trees.
  for (i <- 0 to n-1)
    drawnTrees(i) = new DrawExpansionTree(trees(i), ft)

  drawLines()

  private def drawLines() {
    contents.clear()
    val lines = numLabels zip drawnTrees

    for ((iLabel, det) <- lines) {
      val line = new BoxPanel(Orientation.Horizontal) {
        // Each line consists of a numLabel and an expansion tree
        background = new Color(255, 255, 255)
        yLayoutAlignment = 0.5
        xLayoutAlignment = 0

        border = Swing.EmptyBorder(10)
        contents += iLabel
        contents += det
      }

      contents += line
    }
  }

  //Reactions for handling SwitchEvents, i.e. switch the trees, update members, and redraw.
  reactions += {
    case e: SwitchEvent =>
      val (to, from) = (e.to-1, e.from-1)
      val tmp = drawnTrees(to)
      drawnTrees(to) = drawnTrees(from)
      drawnTrees(from) = tmp

      drawLines()
      revalidate()
      repaint()
  }

  /**
   * A label that displays a number n as "n: ".
   * It can be selected and deselected by left-clicking. If first one and then another of these in the same panel is
   * selected, a SwitchEvent will be published.
   * @param number The number to be displayed
   */
  class NumLabel(val number: Int) extends Label {
    text = number + ": "
    val panel = TreeListPanel.this // We need access to the TreeListPanel this is contained in

    listenTo(this.mouse.clicks)

    reactions += {
      case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 => // If it registers a left click, there are 3 cases.
        panel.selected match {
          case None => // If no numLabel is selected, this becomes selected.
            select()
          case Some(that) =>
            if (that == this) // If this is already selected, it becomes deselected.
              deselect()
            else { // If another numLabel is selected, a SwitchEvent is published and the other label is deselected.
              publish(new SwitchEvent(this.number, that.number))
              that.deselect()
            }
        }
    }

    /**
     * Determines what happens when a numLabel is selected.
     */
    def select(): Unit = {
      foreground = Color.green
      panel.selected = Some(this.asInstanceOf[panel.type#NumLabel])
    }

    /**
      * Determines what happens when a numLabel is deselected.
      */
    def deselect(): Unit = {
      foreground = Color.black
      panel.selected = None
    }
  }
}
