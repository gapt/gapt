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
import DrawSequent._
import at.logic.gui.prooftool.parser.{StructPublisher, ShowLeaf, HideLeaf, HideTree}
import at.logic.transformations.ceres.struct.structToExpressionTree.{TimesC, PlusC}
import at.logic.transformations.ceres.PStructToExpressionTree.{PWeakC, PTimesC, PPlusC}
import java.awt.event.MouseEvent
import at.logic.calculi.lk.base.Sequent
import javax.swing.Icon

class DrawTree(private val struct: Tree[_], private val fSize: Int) extends BorderPanel {
  background = new Color(255,255,255)
  opaque = false

  private val ft = new Font(SANS_SERIF, PLAIN, fSize)
  private val bd = Swing.EmptyBorder(fSize / 2)
  private val tx = struct.vertex match {
    case PWeakC(seq) => "w^{" + sequentToLatexString(seq) + "}"
    case he: HOLExpression => formulaToLatexString(he)
    case seq: Sequent => sequentToLatexString(seq)
    case _ => struct.vertex.toString
  }
  private var drawLines = true

  struct match {
    case tree: UnaryTree[_] =>
      val mylabel = tree.vertex match {
        case PWeakC(_) => latexToLabel(tx, ft)
        case _ => new Label(tx) {
          font = ft
          val myicon : Icon = null
        }
      }
      mylabel.opaque = false
      mylabel.border = bd
      mylabel.listenTo(mouse.clicks, StructPublisher)
      mylabel.reactions += {
        case ShowLeaf =>
          if (mylabel.myicon != null) {
            mylabel.icon = mylabel.myicon
            mylabel.text = ""
          } else mylabel.text = tx
          drawLines = true
        case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
          if (mylabel.myicon != null) {
            if (mylabel.text == "") {
              mylabel.text = "x"
              mylabel.icon = null
              drawLines = false
              mylabel.publish(HideTree)
            }
            else {
              mylabel.icon = mylabel.myicon
              mylabel.text = ""
              drawLines = true
              mylabel.publish(ShowLeaf)
            }
          } else {
            if (mylabel.text == "x") {
              mylabel.text = tx
              drawLines = true
              mylabel.publish(ShowLeaf)
            }
            else {
              mylabel.text = "x"
              drawLines = false
              mylabel.publish(HideTree)
            }
          }
        case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
          if (mylabel.myicon != null) {
            mylabel.text = "x"
            mylabel.icon = null
          } else mylabel.text = "x"
      }
      layout(mylabel) = Position.North
      layout(new DrawTree(tree.t, fSize) {
        listenTo(mylabel, StructPublisher)
        reactions += {
          case ShowLeaf => visible = true
          case HideTree => visible = false
        }
      }) = Position.Center
    case tree: BinaryTree[_] =>
      val label = new Label(tx) {
        tree.vertex match {
          case TimesC | PTimesC(_) => foreground = new Color(255,0,0)
          case PlusC | PPlusC => foreground = new Color(0,0,255)
          case _ =>
        }
        border = bd
        font = ft
        listenTo(mouse.clicks, StructPublisher)
        reactions += {
          case ShowLeaf =>
            text = tx
            drawLines = true
          case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
            if (text == "x") {
              text = tx
              drawLines = true
              publish(ShowLeaf)
            }
            else {
              text = "x"
              drawLines = false
              publish(HideTree)
            }
          case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 => text = "x"
        }
      }
      layout(label) = Position.North
      layout(new DrawTree(tree.t1, fSize) {
        listenTo(label, StructPublisher)
        reactions += {
          case ShowLeaf => visible = true
          case HideTree => visible = false
        }
      }) = Position.West
      layout(new DrawTree(tree.t2, fSize) {
        listenTo(label, StructPublisher)
        reactions += {
          case ShowLeaf => visible = true
          case HideTree => visible = false
        }
      }) = Position.East
    case tree: LeafTree[_] =>
      val mylabel = latexToLabel(tx, ft)
      mylabel.opaque = false
      mylabel.border = bd
      mylabel.listenTo(mouse.clicks, StructPublisher)
      mylabel.reactions += {
        case ShowLeaf =>
          mylabel.icon = mylabel.myicon
          mylabel.text = ""
        case HideLeaf =>
          mylabel.text = "x"
          mylabel.icon = null
        case e: MouseClicked =>
          if (mylabel.text == "") {
            mylabel.text = "x"
            mylabel.icon = null
          }
          else {
            mylabel.icon = mylabel.myicon
            mylabel.text = ""
          }
      }
      layout(mylabel) = Position.North
  }

  override def paintComponent(g: Graphics2D) {
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

        g.drawLine(north_width / 2, north_height - fSize/2, center_width / 2, north_height + fSize/2)
      }
      case p: BinaryTree[_] => {
        val north = this.layout.find(x => x._2 == Position.North).get._1
        val northWidth = north.size.width
        val northHeight = north.size.height
        val left = this.layout.find(x => x._2 == Position.West).get._1
        val leftWidth = left.size.width
        val right = this.layout.find(x => x._2 == Position.East).get._1
        val rightWidth = right.size.width

        g.drawLine(northWidth / 2, northHeight - fSize /2, left.location.x + leftWidth / 2, northHeight + fSize /2)
        g.drawLine(northWidth / 2, northHeight - fSize /2, right.location.x + rightWidth / 2, northHeight + fSize /2)
      }
      case _ =>
    }
  }
}