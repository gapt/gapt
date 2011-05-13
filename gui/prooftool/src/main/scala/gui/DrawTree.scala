package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/6/11
 * Time: 1:38 PM
 */

import scala.swing._
import event._
import BorderPanel._
import java.awt.Font._
import java.awt.{RenderingHints, BasicStroke}
import at.logic.utils.ds.trees._
import at.logic.language.hol.HOLExpression
import ProoftoolSequentFormatter._
import at.logic.gui.prooftool.parser.{StructPublisher, ShowLeaf, HideLeaf}
import at.logic.transformations.ceres.struct.structToExpressionTree.{TimesC, PlusC, EmptyTimesC, EmptyPlusC}

class DrawTree(private val struct: Tree[_], private val fSize: Int) extends BorderPanel {
  background = new Color(255,255,255)
  opaque = false
  val ft = new Font(SANS_SERIF, PLAIN, fSize)
  val bd = Swing.EmptyBorder(0,fSize,0,fSize)
  private val tx = formulaToString(struct.vertex.asInstanceOf[HOLExpression])
  private var drawLines = true

  struct match {
    case tree: UnaryTree[_] =>
      val label = new Label(tx) {
        border = bd
        font = ft
        listenTo(mouse.clicks, StructPublisher)
        reactions += {
          case ShowLeaf => text = tx
          case e: MouseClicked =>
            if (text == "x") {
              text = tx
              drawLines = true
              publish(ShowLeaf)
            }
            else {
              text = "x"
              drawLines = false
              publish(HideLeaf)
            }
        }
      }
      layout(label) = Position.North
      layout(new DrawTree(tree.t, fSize) {
        listenTo(label, StructPublisher)
        reactions += {
          case ShowLeaf => visible = true
          case HideLeaf => visible = false
        }
      }) = Position.Center
    case tree: BinaryTree[_] =>
      val label = new Label(tx) {
        tree.vertex match {
          case TimesC => foreground = new Color(255,0,0)
          case PlusC => foreground = new Color(0,0,255)
          case _ =>
        }
        border = bd
        font = ft
        listenTo(mouse.clicks, StructPublisher)
        reactions += {
          case ShowLeaf => text = tx
          case e: MouseClicked =>
            if (text == "x") {
              text = tx
              drawLines = true
              publish(ShowLeaf)
            }
            else {
              text = "x"
              drawLines = false
              publish(HideLeaf)
            }
        }
      }
      layout(label) = Position.North
      layout(new DrawTree(tree.t1, fSize) {
        listenTo(label, StructPublisher)
        reactions += {
          case ShowLeaf => visible = true
          case HideLeaf => visible = false
        }
      }) = Position.West
      layout(new DrawTree(tree.t2, fSize) {
        listenTo(label, StructPublisher)
        reactions += {
          case ShowLeaf => visible = true
          case HideLeaf => visible = false
        }
      }) = Position.East
    case tree: LeafTree[_] =>
      layout(new Label("x") {
        tree.vertex match {
          case EmptyTimesC | EmptyPlusC => foreground = new Color(0,255,0)
          case _ =>
        }
        border = bd
        font = ft
        listenTo(mouse.clicks, StructPublisher)
        reactions += {
          case ShowLeaf => text = tx
          case e: MouseClicked =>
            if (text == "x") text = tx
            else text = "x"
        }
      }) = Position.North
  }

  override def paintComponent(g: Graphics2D) = {
    super.paintComponent(g)

    g.setStroke(new BasicStroke(fSize / 25, BasicStroke.CAP_ROUND, BasicStroke.JOIN_ROUND))
    g.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING,RenderingHints.VALUE_TEXT_ANTIALIAS_LCD_HRGB)

    if (drawLines) struct match {
      case p: UnaryTree[_] => {
        val north = this.layout.find(x => x._2 == Position.North).get._1
        val north_width = north.size.width
        val north_height = north.size.height
        val center = this.layout.find(x => x._2 == Position.Center).get._1
        val center_width = center.size.width
        val center_height = center.size.height

        g.drawLine(north_width / 2, north_height - fSize / 4, center_width / 2, north_height + fSize / 6)
      }
      case p: BinaryTree[_] => {
        val north = this.layout.find(x => x._2 == Position.North).get._1
        val northWidth = north.size.width
        val northHeight = north.size.height
        val left = this.layout.find(x => x._2 == Position.West).get._1
        val leftWidth = left.size.width
        val leftHeight = left.size.height
        val right = this.layout.find(x => x._2 == Position.East).get._1
        val rightWidth = right.size.width
        val rightHeight = right.size.height

        g.drawLine(northWidth / 2, northHeight - fSize / 4, leftWidth / 2, northHeight + fSize / 6)
        g.drawLine(northWidth / 2, northHeight - fSize / 4, leftWidth + rightWidth / 2, northHeight + fSize / 6)
      }
      case _ =>
    }
  }
}