package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 4:24 PM
 */

import scala.swing._
import BorderPanel._
import java.awt.Font._
import java.awt.{RenderingHints, BasicStroke}
import at.logic.calculi.treeProofs.{BinaryTreeProof, UnaryTreeProof, TreeProof}

/*import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.equationalRules._ */
import at.logic.calculi.lk.base.SequentOccurrence
import at.logic.calculi.proofs.{BinaryProof, UnaryProof, Proof, RuleTypeA}
import ProoftoolSequentFormatter._

class DrawProof(private val proof: TreeProof[SequentOccurrence], private val fSize: Int) extends BorderPanel {
  background = new Color(255,255,255)
  opaque = false
  val bd = Swing.MatteBorder(0,0,0,0, new Color(0,0,0))
  val ft = new Font(SANS_SERIF, PLAIN, fSize)
  val labelFont = new Font(MONOSPACED, ITALIC, fSize-1)

  proof match {
    case p: UnaryTreeProof[SequentOccurrence] =>
      border = Swing.EmptyBorder(0,0,0, fSize * 4)
      layout(new DrawProof(p.uProof.asInstanceOf[TreeProof[SequentOccurrence]], fSize)) = Position.Center
      layout(new Label(sequentOccurenceToString(p.root)) { border = bd; font = ft }) = Position.South
    case p: BinaryTreeProof[SequentOccurrence] =>
      border = Swing.EmptyBorder(0,0,0, fSize * 4)
      layout(new DrawProof(p.uProof1.asInstanceOf[TreeProof[SequentOccurrence]], fSize)) = Position.West
      layout(new Label("       ") {
        opaque = false
        font = labelFont
        verticalAlignment = Alignment.Bottom
      }) = Position.Center
      layout(new DrawProof(p.uProof2.asInstanceOf[TreeProof[SequentOccurrence]], fSize)) = Position.East
      layout(new Label(sequentOccurenceToString(p.root)) { border = bd; font = ft }) = Position.South
    case _ => layout(new Label(sequentOccurenceToString(proof.root)) { font = ft }) = Position.South
  }

/*  def ruleName(rule: RuleTypeA) = rule match {
    // structural rules
    case WeakeningLeftRuleType    => "w:l"
    case WeakeningRightRuleType   => "w:r"
    case ContractionLeftRuleType  => "c:l"
    case ContractionRightRuleType => "c:r"
    case CutRuleType => "cut"

    // Propositional rules
    case AndRightRuleType => "\u2227:r"
    case AndLeft1RuleType => "\u2227:l1"
    case AndLeft2RuleType => "\u2227:l2"
    case OrRight1RuleType => "\u2228:r1"
    case OrRight2RuleType => "\u2228:r2"
    case OrLeftRuleType   => "\u2228:l"
    case ImpRightRuleType => "\u2283:r"
    case ImpLeftRuleType  => "\u2283:l"
    case NegLeftRuleType  => "\u00ac:l"
    case NegRightRuleType => "\u00ac:r"

    // Quanitifier rules
    case ForallLeftRuleType  => "\u2200:l"
    case ForallRightRuleType => "\u2200:r"
    case ExistsLeftRuleType  => "\u2203:l"
    case ExistsRightRuleType => "\u2203:r"

    // Definition rules
    case DefinitionLeftRuleType  => "d:l"
    case DefinitionRightRuleType => "d:r"

    // Equation rules
    case EquationLeft1RuleType  => "e:l1"
    case EquationLeft2RuleType  => "e:l2"
    case EquationRight1RuleType => "e:r1"
    case EquationRight2RuleType => "e:r2"

    // axioms
    case InitialRuleType => ""
    case _ => "unmatched rule type"
  } */

  override def paintComponent(g: Graphics2D) = {
    import scala.math.max

    super.paintComponent(g)

    val metrics = g.getFontMetrics(labelFont)
    val lineHeight = metrics.getHeight
    val space = metrics.charWidth('w')

    g.setFont(labelFont)
    // g.setStroke(new BasicStroke(space / 5))
    g.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING,RenderingHints.VALUE_TEXT_ANTIALIAS_LCD_HRGB)

    proof match {
      case p: UnaryTreeProof[SequentOccurrence] => {
        val center = this.layout.find(x => x._2 == Position.Center).get._1
        val width = center.size.width
        val height = center.size.height
        val seqLength = max(metrics.stringWidth(p.uProof.root.toString), metrics.stringWidth(p.root.toString))

        g.drawLine((width - seqLength - fSize * 4) / 2, height, (width + seqLength) / 2, height)
        g.drawString(p.name, (space + width + seqLength) / 2, height + metrics.getMaxDescent)
      }
      case p: BinaryTreeProof[SequentOccurrence] => {
        val left = this.layout.find(x => x._2 == Position.West).get._1
        val right = this.layout.find(x => x._2 == Position.East).get._1
        val leftWidth = left.size.width
        val rightWidth = right.size.width
        val height = max(left.size.height, right.size.height)
        val leftSeqLength = metrics.stringWidth(sequentOccurenceToString(p.uProof1.root))
        val rightSeqLength = metrics.stringWidth(sequentOccurenceToString(p.uProof2.root))
        val seqLength = leftWidth + space * 7 + (rightWidth + rightSeqLength) / 2

        g.drawLine((leftWidth - leftSeqLength - fSize * 4) / 2, height, seqLength, height)
        g.drawString(p.name, seqLength + space/2, height + metrics.getMaxDescent)
      }
      case _ =>
    }
  }
}
