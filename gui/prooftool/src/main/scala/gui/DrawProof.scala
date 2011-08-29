package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 4:24 PM
 */

import scala.swing._
import BorderPanel._
import event._
import java.awt.Font._
import java.awt.{RenderingHints, BasicStroke}
import at.logic.calculi.treeProofs._
import at.logic.calculi.lk.base.SequentOccurrence
import ProoftoolSequentFormatter._
import java.awt.event.{MouseMotionListener, MouseEvent}
import at.logic.calculi.slk.SchemaProofLinkRule

class DrawProof(private val proof: TreeProof[_], private val fSize: Int) extends BorderPanel with MouseMotionListener {
  background = new Color(255,255,255)
  opaque = false
  private val blue = new Color(0,0,255)
  private val black = new Color(0,0,0)
  private val bd = Swing.EmptyBorder(0,fSize*3,0,fSize*3)
  private val ft = new Font(SANS_SERIF, PLAIN, fSize)
  private val labelFont = new Font(MONOSPACED, ITALIC, fSize-2)
  private val tx = proof.root match {
    case so: SequentOccurrence => sequentOccurenceToString(so)
    case _ => proof.root.toString
  }

  listenTo(mouse.moves, mouse.clicks, mouse.wheel)
  reactions += {
    case e: MouseDragged =>
      Main.body.cursor = new java.awt.Cursor(java.awt.Cursor.MOVE_CURSOR)
    case e: MouseReleased =>
      Main.body.cursor = java.awt.Cursor.getDefaultCursor
  }

  proof match {
//    case SchemaProofLinkRule(_, link, indices) =>
//      layout(new Label("(" + link + ", " + indices.toString + ")") {
//          font = ft
//        }) = Position.Center
//      layout(new Label(tx) {
//          font = ft
//        }) = Position.South
    case p: UnaryTreeProof[_] =>
      border = bd
      layout(new DrawProof(p.uProof.asInstanceOf[TreeProof[_]], fSize)) = Position.Center
      layout(new Label(tx) {
        font = ft
        listenTo(mouse.moves, mouse.clicks, mouse.wheel)
        reactions += {
          case e: MouseEntered => foreground = blue
          case e: MouseExited => foreground = black
          case e: MouseClicked => PopupMenu(proof, this, e.point.x, e.point.y)
        }
      }) = Position.South
    case p: BinaryTreeProof[_] =>
      border = bd
      layout(new DrawProof(p.uProof1.asInstanceOf[TreeProof[_]], fSize)) = Position.West
      layout(new DrawProof(p.uProof2.asInstanceOf[TreeProof[_]], fSize)) = Position.East
      layout(new Label(tx) {
        font = ft
        listenTo(mouse.moves, mouse.clicks, mouse.wheel)
        reactions += {
          case e: MouseEntered => foreground = blue
          case e: MouseExited => foreground = black
          case e: MouseClicked => PopupMenu(proof, this, e.point.x, e.point.y)
        }
      }) = Position.South
    case p: NullaryTreeProof[_] =>
      layout(new Label(tx) {
        border = Swing.EmptyBorder(0,fSize,0,fSize)
        font = ft
        listenTo(mouse.moves, mouse.clicks, mouse.wheel)
        reactions += {
          case e: MouseEntered => foreground = blue
          case e: MouseExited => foreground = black
          case e: MouseClicked => PopupMenu(proof, this, e.point.x, e.point.y)
        }
      }) = Position.South
  }

  override def paintComponent(g: Graphics2D) = {
    import scala.math.max

    super.paintComponent(g)

    val metrics = g.getFontMetrics(ft)

    g.setFont(labelFont)
    // g.setStroke(new BasicStroke(fSize / 25))
    g.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING,RenderingHints.VALUE_TEXT_ANTIALIAS_LCD_HRGB)

    proof match {
      case p: UnaryTreeProof[_] => {
        val center = this.layout.find(x => x._2 == Position.Center).get._1
        val width = center.size.width + fSize*6
        val height = center.size.height
        val seqLength = p.root match {
          case so: SequentOccurrence =>
            max(metrics.stringWidth(sequentOccurenceToString(p.uProof.root.asInstanceOf[SequentOccurrence])),
              metrics.stringWidth(sequentOccurenceToString(so)))
          case _ =>
            max(metrics.stringWidth(p.uProof.root.toString),
              metrics.stringWidth(p.root.toString))
        }

        g.drawLine((width - seqLength) / 2, height, (width + seqLength) / 2, height)
        g.drawString(p.name, (fSize / 4 + width + seqLength) / 2, height + metrics.getMaxDescent)
      }
      case p: BinaryTreeProof[_] => {
        val left = this.layout.find(x => x._2 == Position.West).get._1
        val leftWidth = left.size.width + fSize*6
        val right = this.layout.find(x => x._2 == Position.East).get._1
        val rightWidth = right.size.width
        val height = max(left.size.height, right.size.height)
        val leftSeqLength = p.uProof1.root match {
          case so: SequentOccurrence => metrics.stringWidth(sequentOccurenceToString(so))
          case _ =>  metrics.stringWidth(p.uProof1.root.toString)
        }
        val rightSeqLength = p.uProof2.root match {
          case so: SequentOccurrence => metrics.stringWidth(sequentOccurenceToString(so))
          case _ =>  metrics.stringWidth(p.uProof2.root.toString)
        }

        val lineLength = right.location.x + (rightWidth + rightSeqLength) / 2

        g.drawLine((leftWidth - leftSeqLength) / 2, height, lineLength, height)
        g.drawString(p.name, lineLength + fSize / 4, height + metrics.getMaxDescent)
      }
      case _ =>
    }
  }

  this.peer.setAutoscrolls(true)
  this.peer.addMouseMotionListener(this)

  def mouseMoved(e: MouseEvent) {}
  def mouseDragged(e: MouseEvent) {
    //The user is dragging us, so scroll!
    val r = new Rectangle(e.getX(), e.getY(), 1, 1);
    this.peer.scrollRectToVisible(r);
  }
}
