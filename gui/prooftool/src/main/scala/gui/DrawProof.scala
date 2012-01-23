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
import at.logic.calculi.treeProofs._
import java.awt.event.{MouseMotionListener, MouseEvent}
import at.logic.calculi.slk.SchemaProofLinkRule
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.occurrences.FormulaOccurrence
import java.awt.{RenderingHints, BasicStroke}
import at.logic.gui.prooftool.parser.{ShowAllRules, HideStructuralRules, ProofToolPublisher, HideStructural}
import at.logic.calculi.lk.propositionalRules._

class DrawProof(val proof: TreeProof[_], private val fSize: Int, private var colored_occurrences : Set[FormulaOccurrence])
  extends BorderPanel with MouseMotionListener {
  background = white
  opaque = false
  private val blue = new Color(0,0,255)
  private val black = new Color(0,0,0)
  private val white = new Color(255,255,255)
  private val bd = Swing.EmptyBorder(0,fSize*2,0,fSize*2)
  private val ft = new Font(SANS_SERIF, PLAIN, fSize)
  private val labelFont = new Font(SANS_SERIF, ITALIC, fSize-2)
  private var hideRules = false
  private val tx = proof.root match {
    case so: Sequent =>
      val ds = DrawSequent(so, ft, colored_occurrences)
      ds.listenTo(mouse.moves, mouse.clicks, mouse.wheel, ProofToolPublisher)
      ds.reactions += {
        case e: MouseEntered => ds.contents.foreach(x => x.foreground = blue)
        case e: MouseExited => ds.contents.foreach(x => x.foreground = black)
        case e: MouseClicked => PopupMenu(proof, this, e.point.x, e.point.y)
        case e: HideStructural if e.proof == proof => println("hide structural matched")
          ds.visible = false
      }
      ds
    case _ => new Label(proof.root.toString) { font = ft }
  }

  listenTo(mouse.moves, mouse.clicks, mouse.wheel, ProofToolPublisher)
  reactions += {
    case e: MouseDragged =>
      Main.body.cursor = new java.awt.Cursor(java.awt.Cursor.MOVE_CURSOR)
    case e: MouseReleased =>
      Main.body.cursor = java.awt.Cursor.getDefaultCursor
    case HideStructuralRules => hideStructuralRules
    case ShowAllRules => showAllRules
  }

  initialize
  // end of constructor

  def showAllRules = {
    hideRules = false
    initialize
    revalidate
  }

  def hideStructuralRules = {
    hideRules = true
    initialize
    revalidate
  }

  def setColoredOccurrences(s : Set[FormulaOccurrence]) {
    colored_occurrences = s
    initialize
  }

  def initialize = proof match {
    case p: UnaryTreeProof[_] =>
      border = bd
      if (hideRules) p.rule match {
        case ContractionLeftRuleType | ContractionRightRuleType | WeakeningLeftRuleType | WeakeningRightRuleType =>
          ProofToolPublisher.publish(new HideStructural(p.uProof.asInstanceOf[TreeProof[_]]))
        case _ =>
      }
      layout(new DrawProof(p.uProof.asInstanceOf[TreeProof[_]], fSize, colored_occurrences)) = Position.Center
      layout(tx) = Position.South
    case p: BinaryTreeProof[_] =>
      border = bd
      layout(new DrawProof(p.uProof1.asInstanceOf[TreeProof[_]], fSize, colored_occurrences)) = Position.West
      layout(new DrawProof(p.uProof2.asInstanceOf[TreeProof[_]], fSize, colored_occurrences)) = Position.East
      layout(tx) = Position.South
    case p: NullaryTreeProof[_] => p match {
      case SchemaProofLinkRule(_, link, indices) =>
        layout(new BoxPanel(Orientation.Vertical) {
          background = white
          contents += new Label("(" + link + ", " + DrawSequent.formulaToLatexString(indices.head) + ")") {
            font = ft
            xLayoutAlignment = 0.5
            border = Swing.EmptyBorder(0,0,5,0)
          }
          tx.xLayoutAlignment = 0.5
          tx.border = Swing.MatteBorder(2,0,0,0, new Color(255,0,0))
          contents += tx
        }) = Position.South
      case _ =>
        tx.border = Swing.EmptyBorder(0,fSize,0,fSize)
        layout(tx) = Position.South
    }
  }

  def getSequentWidth(g: Graphics2D) = tx match {
    case label: Label => g.getFontMetrics(ft).stringWidth(label.text)
    case fPanel: FlowPanel => fPanel.contents.foldLeft(0)((width, x) => width + x.size.width + 5)
  }

  override def paintComponent(g: Graphics2D) = {
    import scala.math.max

    super.paintComponent(g)

    val metrics = g.getFontMetrics(labelFont)
    val em = metrics.charWidth('M')
    g.setFont(labelFont)
    // g.setStroke(new BasicStroke(fSize / 25))
    g.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING,RenderingHints.VALUE_TEXT_ANTIALIAS_LCD_HRGB)

    proof match {
      case p: UnaryTreeProof[_] => {
        val center = this.layout.find(x => x._2 == Position.Center).get._1.asInstanceOf[DrawProof]
        val width = center.size.width + fSize*4
        val height = center.size.height
        val seqLength = max(center.getSequentWidth(g), getSequentWidth(g))

        g.drawLine((width - seqLength) / 2, height, (width + seqLength) / 2, height)
        g.drawString(p.name, (fSize / 4 + width + seqLength) / 2, height + metrics.getMaxDescent)
      }
      case p: BinaryTreeProof[_] => {
        val left = this.layout.find(x => x._2 == Position.West).get._1.asInstanceOf[DrawProof]
        val leftWidth = left.size.width + fSize*4
        val right = this.layout.find(x => x._2 == Position.East).get._1.asInstanceOf[DrawProof]
        val rightWidth = right.size.width
        val height = max(left.size.height, right.size.height)
        val leftSeqLength = left.getSequentWidth(g)
        val rightSeqLength = right.getSequentWidth(g)
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
