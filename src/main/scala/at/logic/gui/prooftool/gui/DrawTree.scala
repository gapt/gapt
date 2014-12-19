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
import at.logic.calculi.lk.base.Sequent
import java.awt.event.{MouseMotionListener, MouseEvent}

class DrawTree(val tree: Tree[_], private val fSize: Int, private var str: String) extends BorderPanel with MouseMotionListener {
  background = new Color(255,255,255)
  opaque = false

  private val ft = new Font(SANS_SERIF, PLAIN, fSize)
  private val bd = Swing.EmptyBorder(fSize / 2)
  private val tx = tree.vertex match {
    case PWeakC(seq) => "w^{" + sequentToLatexString(seq) + "}"
    case he: HOLExpression => formulaToLatexString(he)
    case seq: Sequent => sequentToLatexString(seq)
    case _ => tree.vertex.toString
  }
  private var drawLines = true

  initialize()

  def search_=(s: String) {
    str = s
    initialize()
  }
  def search = str

  def initialize() { tree match {
    case utree: UnaryTree[_] =>
      val mylabel = utree.vertex match {
        case PWeakC(_) => LatexLabel(ft, tx)
        case _ => new Label(tx) {
          font = ft
          val myicon = icon
        }
      }
      if (! str.isEmpty && tx.contains(str)) {
        mylabel.opaque = true  // This is not nice when searched. Find a solution!
        mylabel.background = new Color(0,255,0)
      }
      else mylabel.opaque = false
      mylabel.border = bd
      mylabel.listenTo(mouse.clicks, StructPublisher)
      mylabel.reactions += {
        case ShowLeaf =>
          if (mylabel.myicon != null) {
            mylabel.icon = mylabel.myicon
            mylabel.text = ""
          } else mylabel.text = tx
          drawLines = true
        case HideLeaf if tx.contains("w^{") =>
          mylabel.text = "w*"
          mylabel.icon = null
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
            mylabel.text = "w*"
            mylabel.icon = null
          }
      }
      layout(mylabel) = Position.North
      layout(new DrawTree(utree.t, fSize, str) {
        listenTo(mylabel, StructPublisher)
        reactions += {
          case ShowLeaf => visible = true
          case HideTree => visible = false
        }
      }) = Position.Center
    case btree: BinaryTree[_] =>
      val label = new Label(tx) {
        btree.vertex match {
          case TimesC | PTimesC(_) => foreground = new Color(255,0,0)
          case PlusC | PPlusC => foreground = new Color(0,0,255)
          case _ =>
        }
        if (! str.isEmpty && tx.contains(str)) {
          background = new Color(0,255,0)
          opaque = true
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
        }
      }
      layout(label) = Position.North
      layout(new DrawTree(btree.t1, fSize, str) {
        listenTo(label, StructPublisher)
        reactions += {
          case ShowLeaf => visible = true
          case HideTree => visible = false
        }
      }) = Position.West
      layout(new DrawTree(btree.t2, fSize, str) {
        listenTo(label, StructPublisher)
        reactions += {
          case ShowLeaf => visible = true
          case HideTree => visible = false
        }
      }) = Position.East
    case ltree: LeafTree[_] =>
      val mylabel = LatexLabel(ft, tx)
      if (! str.isEmpty && tx.contains(str)) mylabel.background = new Color(0,255,0)
      else mylabel.opaque = false
      mylabel.border = bd
      mylabel.listenTo(mouse.clicks, StructPublisher)
      mylabel.reactions += {
        case ShowLeaf =>
          mylabel.icon = mylabel.myicon
          mylabel.text = ""
        case HideLeaf =>
          mylabel.text = "x"
          mylabel.icon = null
        case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
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
  }}

  override def paintComponent(g: Graphics2D) {
    super.paintComponent(g)

    g.setStroke(new BasicStroke(fSize / 25, BasicStroke.CAP_ROUND, BasicStroke.JOIN_ROUND))
    g.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING,RenderingHints.VALUE_TEXT_ANTIALIAS_LCD_HRGB)

    if (drawLines) tree match {
      case p: UnaryTree[_] =>
        val north = this.layout.find(x => x._2 == Position.North).get._1
        val north_width = north.size.width
        val north_height = north.size.height
        val center = this.layout.find(x => x._2 == Position.Center).get._1
        val center_width = center.size.width

        g.drawLine(north_width / 2, north_height - fSize/2, center_width / 2, north_height + fSize/2)
      case p: BinaryTree[_] =>
        val north = this.layout.find(x => x._2 == Position.North).get._1
        val northWidth = north.size.width
        val northHeight = north.size.height
        val left = this.layout.find(x => x._2 == Position.West).get._1
        val leftWidth = left.size.width
        val right = this.layout.find(x => x._2 == Position.East).get._1
        val rightWidth = right.size.width

        g.drawLine(northWidth / 2, northHeight - fSize /2, left.location.x + leftWidth / 2, northHeight + fSize /2)
        g.drawLine(northWidth / 2, northHeight - fSize /2, right.location.x + rightWidth / 2, northHeight + fSize /2)
      case _ =>
    }
  }

  listenTo(mouse.moves, mouse.clicks, mouse.wheel)
  reactions += {
    case e: MouseDragged =>
      Main.body.cursor = new java.awt.Cursor(java.awt.Cursor.MOVE_CURSOR)
    case e: MouseReleased =>
      Main.body.cursor = java.awt.Cursor.getDefaultCursor
    case e: MouseWheelMoved =>
      Main.body.peer.dispatchEvent(e.peer)
  }

  this.peer.setAutoscrolls(true)
  this.peer.addMouseMotionListener(this)

  def mouseMoved(e: MouseEvent) {}
  def mouseDragged(e: MouseEvent) {
    //The user is dragging us, so scroll!
    val r = new Rectangle(e.getX, e.getY, 1, 1)
    this.peer.scrollRectToVisible(r)
  }
}