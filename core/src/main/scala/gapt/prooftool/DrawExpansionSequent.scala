package gapt.prooftool

// The code in this file displays expansion sequents.

import swing._
import java.awt.{ Color, Dimension, Font }
import java.awt.Font._

import scala.swing.event.{ Event, MouseClicked, MouseEntered, MouseExited, UIElementResized }
import gapt.proofs.expansion._
import java.awt.event.MouseEvent

/**
 * These events are used to tell a CedentPanel that two expansion trees should be switched, necessitating a redraw.
 * @param from Number of the first tree to be switched
 * @param to Number of the second tree to be switched
 */
private[prooftool] case class SwitchEvent( from: Int, to: Int ) extends Event

/**
 * This class takes care of drawing an ExpansionSequent.
 * @param main: The main window that this belongs to.
 * @param expSequent The expansion sequent to be displayed
 */
class DrawExpansionSequent(
    val main:       ExpansionSequentViewer,
    val expSequent: ExpansionSequent ) extends SplitPane( Orientation.Vertical ) {
  //Code for window geometry and appearance
  background = new Color( 255, 255, 255 )

  //Code for contents
  val mExpSequent = expSequent
  val antecedentPanel: CedentPanel = new CedentPanel( main, mExpSequent.antecedent, "Antecedent" )
  val succedentPanel: CedentPanel = new CedentPanel( main, mExpSequent.succedent, "Succedent" )
  leftComponent = antecedentPanel
  rightComponent = succedentPanel
}

/**
 * Class for displaying a list of expansion trees and a title.
 * @param cedent The list of expansion trees to be displayed
 * @param title The title to be displayed at the top
 */
class CedentPanel( val main: ExpansionSequentViewer, val cedent: Seq[ExpansionTree], val title: String ) extends BoxPanel( Orientation.Vertical ) {

  //Code for the title label
  val titleLabel = new Label( title ) {
    font = main.font.deriveFont( Font.BOLD )
    opaque = true
    border = Swing.EmptyBorder( 10 )
    listenTo( mouse.clicks, mouse.moves )
    reactions += {
      case e: MouseEntered => foreground = Color.blue
      case e: MouseExited  => foreground = Color.black
      case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
        gapt.prooftool.PopupMenu( main, CedentPanel.this, e.point.x, e.point.y ) //This brings up the menu that lets the user close/open/expand all trees on this side
    }
  }

  //Code for the expansion tree list
  var treeList = new TreeListPanel( main, cedent ) //treeList is the panel that contains the list of trees. It's contained in a ScrollPane.
  val scrollPane = new ScrollPane {
    peer.getVerticalScrollBar.setUnitIncrement( 20 )
    peer.getHorizontalScrollBar.setUnitIncrement( 20 )

    contents = treeList
  }

  //Add the title label and the scroll pane to the contents
  contents += titleLabel
  contents += scrollPane

  listenTo( main.publisher )

  reactions += {
    case FontChanged =>
      titleLabel.font = main.font.deriveFont( Font.BOLD )
  }
}

/**
 * Class that displays a list of expansion trees.
 * @param trees The list of trees to be displayed
 */
class TreeListPanel( main: ExpansionSequentViewer, trees: Seq[ExpansionTree] ) extends BoxPanel( Orientation.Vertical ) {
  background = new Color( 255, 255, 255 )

  val n = trees.length
  var selected: Option[NumLabel] = None // We note which numLabel is currently selected (if any).
  val numLabels = ( 1 to n ).map( i => new NumLabel( i ) ) // Generate numLabels from 1 to n
  numLabels.foreach { listenTo( _ ) }

  val drawnTrees = new Array[DrawExpansionTree]( n ) // Draw all the trees. This is a mutable array so we can reorder the drawn trees.
  for ( i <- 0 until n )
    drawnTrees( i ) = DrawExpansionTree( main, trees( i ) )

  drawLines()

  private def drawLines(): Unit = {
    contents.clear()
    val lines = numLabels zip drawnTrees

    for ( ( iLabel, det ) <- lines ) {
      val line = new BoxPanel( Orientation.Horizontal ) {
        // Each line consists of a numLabel and an expansion tree
        background = new Color( 255, 255, 255 )
        yLayoutAlignment = 0.5
        xLayoutAlignment = 0

        border = Swing.EmptyBorder( 10 )
        contents += iLabel
        contents += det
      }

      contents += line
    }
  }

  //Reactions for handling SwitchEvents, i.e. switch the trees, update members, and redraw.
  reactions += {
    case e: SwitchEvent =>
      val ( to, from ) = ( e.to - 1, e.from - 1 )
      val tmp = drawnTrees( to )
      drawnTrees( to ) = drawnTrees( from )
      drawnTrees( from ) = tmp

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
  class NumLabel( val number: Int ) extends Label {
    text = s"${number}: "
    val panel = TreeListPanel.this // We need access to the TreeListPanel this is contained in

    listenTo( this.mouse.clicks )

    reactions += {
      case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 => // If it registers a left click, there are 3 cases.
        panel.selected match {
          case None => // If no numLabel is selected, this becomes selected.
            select()
          case Some( that ) =>
            if ( that == this ) // If this is already selected, it becomes deselected.
              deselect()
            else { // If another numLabel is selected, a SwitchEvent is published and the other label is deselected.
              publish( SwitchEvent( this.number, that.number ) )
              that.deselect()
            }
        }
    }

    /**
     * Determines what happens when a numLabel is selected.
     */
    def select(): Unit = {
      foreground = Color.green
      panel.selected = Some( this.asInstanceOf[panel.type#NumLabel] )
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
