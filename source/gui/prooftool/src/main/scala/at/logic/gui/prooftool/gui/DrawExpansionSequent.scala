package at.logic.gui.prooftool.gui

// The code in this file displays expansion sequents.

import scala.collection.mutable
import swing._
import java.awt.{Dimension, Font, Color}
import java.awt.Font._
import scala.swing.event.{MouseExited, MouseEntered, UIElementResized, MouseClicked, Event}
import at.logic.calculi.expansionTrees._
import java.awt.event.MouseEvent
import at.logic.calculi.expansionTrees.multi.MultiExpansionTree
import at.logic.algorithms.expansionTrees.compressQuantifiers
import org.slf4j.LoggerFactory

/** These events are used to tell a CedentPane that two expansion trees should be switched, necessitating a redraw.
 *
 * @param from Number of the first tree to be switched
 * @param to Number of the second tree to be switched
 */
class SwitchEvent(val from: Int, val to: Int) extends Event

/** This class takes care of drawing an ExpansionSequent.
 *
 * @param expSequent The expansion sequent to be displayed
 * @param fSize The font size.
 */
class DrawExpansionSequent(val expSequent: ExpansionSequent, private val fSize: Int) extends SplitPane(Orientation.Vertical) {

  //Code for window geometry and appearance
  background = new Color(255,255,255)
  private val ft = new Font(SANS_SERIF, PLAIN, fSize)
  preferredSize = calculateOptimalSize
  dividerLocation = preferredSize.width / 2

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
  val logger = LoggerFactory.getLogger("drawExpSeqLogger")
  val mExpSequent = compressQuantifiers(expSequent) //The input sequent is converted to MultiExpansionTrees
  leftComponent = new CedentPanel(mExpSequent.antecedent, "Antecedent", ft)
  rightComponent = new CedentPanel(mExpSequent.succedent, "Succedent", ft)
}

/** Class for displaying a list of expansion trees and a title. Also takes care of swapping trees.
 *
 * @param cedent The list of expansion trees to be displayed
 * @param title The title to be displayed at the top
 * @param ft The font to be used
 */
class CedentPanel(cedent: Seq[MultiExpansionTree], val title: String, ft: Font) extends BoxPanel(Orientation.Vertical) {
  val logger = LoggerFactory.getLogger("drawExpSeqLogger")

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
  val n = cedent.length
  val expansionTrees = new mutable.ArraySeq[MultiExpansionTree](n) //This is mutable so we can reorder the trees

  for (i <- 0 to n-1) {
    expansionTrees.update(i, cedent(i))
  }

  var treeList = updateTreeList() //treeList is the panel that contains the list of trees. It's contained in a ScrollPane.
  val scrollPane = new ScrollPane {
    peer.getVerticalScrollBar.setUnitIncrement( 20 )
    peer.getHorizontalScrollBar.setUnitIncrement( 20 )
    
    contents = treeList
  }

  /** Returns a TreeListPanel corresponding to the current order of the expansion trees.
    * It gets called at the beginning and every time trees are switched.
   *
   * @return A new TreeListPanel that displays the trees in the current order.
   */
  def updateTreeList(): TreeListPanel = {
    val list = new TreeListPanel(expansionTrees.toSeq, ft)
    list.numLabels.foreach(listenTo(_)) //We listen to the numLabels so we can receive SwitchEvents.
    list
  }

  //Add the title label and the scroll pane to the contents
  contents += titleLabel
  contents += scrollPane

  //Reactions for handling SwitchEvents, i.e. switch the trees, update members, and redraw.
  reactions += {
    case e: SwitchEvent =>
      val (to, from) = (e.to-1, e.from-1)
      val tmp = expansionTrees(to)
      expansionTrees.update(to, expansionTrees(from))
      expansionTrees.update(from, tmp)
      treeList = updateTreeList()
      scrollPane.contents = treeList
      revalidate()
  }
}

/** Class that displays a list of expansion trees.
 *
 * @param trees The list of trees to be displayed
 * @param ft The font
 */
class TreeListPanel(trees: Seq[MultiExpansionTree], ft: Font) extends BoxPanel(Orientation.Vertical) {
  val logger = LoggerFactory.getLogger("drawExpSeqLogger")
  background = new Color(255, 255, 255)

  val n = trees.length
  var selected: Option[NumLabel] = None // We note which numLabel is currently selected (if any).
  val numLabels = (1 to n).map(i => new NumLabel(i)) // Generate numLabels from 1 to n
  val drawnExpansionTrees = trees.map(t => new DrawExpansionTree(t, ft)) // Draw all the trees
  val lines = numLabels zip drawnExpansionTrees

  lines.foreach{ p =>
    val (iLabel, det) = p
    val line = new BoxPanel(Orientation.Horizontal) { // Each line consists of a numLabel and an expansion tree
      background = new Color(255, 255, 255)
      yLayoutAlignment = 0.5
      xLayoutAlignment = 0

      border = Swing.EmptyBorder(10)
      contents += iLabel
      contents += det
    }

    contents += line
  }

  /** A label that displays a number n as "n: ".
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

    /** Determines what happens when a numLabel is selected.
     *
     */
    def select(): Unit = {
      foreground = Color.green
      panel.selected = Some(this.asInstanceOf[panel.type#NumLabel])
    }

    /** Determines what happens when a numLabel is deselected.
      *
      */
    def deselect(): Unit = {
      foreground = Color.black
      panel.selected = None
    }
  }
}
