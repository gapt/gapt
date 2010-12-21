package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Oct 30, 2010
 * Time: 5:43:38 PM
 */

import scala.swing._
import BorderPanel._
import java.awt.Font._
import java.awt.{RenderingHints, BasicStroke}
import at.logic.language.lambda.typedLambdaCalculus.{Abs, Var, App, LambdaExpression}
import at.logic.language.lambda.types.{To, ->, Ti}
import at.logic.calculi.proofs.RuleTypeA
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.equationalRules._

class MyScrollPane extends ScrollPane {
  background = new Color(255,255,255)

  def getContent: Launcher = contents.last.asInstanceOf[Launcher]
}

class Launcher(private val proofLK: LKProof, private val fSize: Int) extends GridBagPanel {
  import GridBagPanel._

  val c = new Constraints
  c.fill = Fill.Horizontal
  c.grid = (0,0)
  layout(new DrawProof(proofLK, fSize)) = c

  background = new Color(255,255,255)
  border = Swing.EmptyBorder(10)

  def fontSize = fSize
  def proof = proofLK
}

class DrawProof(private val proof: LKProof, private val fSize: Int) extends BorderPanel {
  import ProoftoolSequentFormatter._
  background = new Color(255,255,255)
  opaque = false
  val bd = Swing.MatteBorder(0,0,0,0, new Color(0,0,0))
  val ft = new Font(SANS_SERIF, PLAIN, fSize)
  val labelFont = new Font(MONOSPACED, ITALIC, fSize-1)

  proof match {
    case p: UnaryLKProof =>
      border = Swing.EmptyBorder(0,0,0, fSize * 4)
      layout(new DrawProof(p.uProof, fSize)) = Position.Center
      layout(new Label(sequentOccurenceToString(p.root)) { border = bd; font = ft }) = Position.South
    case p: BinaryLKProof =>
      border = Swing.EmptyBorder(0,0,0, fSize * 4)
      layout(new DrawProof(p.uProof1, fSize)) = Position.West
      layout(new Label("       ") { font = labelFont }) = Position.Center
      layout(new DrawProof(p.uProof2, fSize)) = Position.East
      layout(new Label(sequentOccurenceToString(p.root)) { border = bd; font = ft }) = Position.South
    case _ => layout(new Label(sequentOccurenceToString(proof.root)) { font = ft }) = Position.South
  }

  def ruleName(rule: RuleTypeA) = rule match {
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
  }

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
      case p: UnaryLKProof => {
        val center = this.layout.find(x => x._2 == Position.Center).get._1
        val width = center.size.width
        val height = center.size.height
        val seqLength = max(metrics.stringWidth(p.uProof.root.toString), metrics.stringWidth(p.root.toString))

        g.drawLine((width - seqLength - fSize * 4) / 2, height, (width + seqLength) / 2, height)
        g.drawString(ruleName(p.rule), (space + width + seqLength) / 2, height + metrics.getMaxDescent)
      }
      case p: BinaryLKProof => {
        val left = this.layout.find(x => x._2 == Position.West).get._1
        val right = this.layout.find(x => x._2 == Position.East).get._1
        val leftWidth = left.size.width 
        val rightWidth = right.size.width
        val height = max(left.size.height, right.size.height)
        val leftSeqLength = metrics.stringWidth(p.uProof1.root.toString)
        val rightSeqLength = metrics.stringWidth(p.uProof2.root.toString)
        val seqLength = leftWidth + space * 7 + (rightWidth + rightSeqLength) / 2

        g.drawLine((leftWidth - leftSeqLength - fSize * 4) / 2, height, seqLength, height)
        g.drawString(ruleName(p.rule), seqLength + space/2, height + metrics.getMaxDescent)
      }
      case _ =>
    }
  }
}

object ProoftoolSequentFormatter {
  //formats a lambda term to a readable string, distinguishing function and logical symbols
  def formulaToString(f:LambdaExpression) : String = f match {
    case App(x,y) => x match {
      case App(Var(name,tp),z) =>        
        if (name.toString.matches("""[\w\p{InGreek}]*""")) name.toString+"("+formulaToString(z)+","+formulaToString(y)+")"
        else "("+formulaToString(z)+" "+name.toString()+" "+formulaToString(y)+")"
/*    this code does not produce nice output for prime proof
      tp match {
        case ->(Ti(),->(Ti(),To())) =>
          if (name.toString.contains("<") || name.toString.contains("=") || name.toString.contains(">"))
            "("+formulaToString(z)+" "+name.toString()+" "+formulaToString(y)+")"
          else name.toString+"("+formulaToString(z)+","+formulaToString(y)+")"
        case ->(To(),->(To(),To())) => "("+formulaToString(z)+" "+name.toString()+" "+formulaToString(y)+")"
        case _ =>
          if (name.toString.contains("+") || name.toString.contains("*"))
            "("+formulaToString(z)+" "+name.toString()+" "+formulaToString(y)+")"
          else name.toString+"("+formulaToString(z)+","+formulaToString(y)+")"
      } */
      case Var(name,tp) => tp match {
        case ->(To(), To()) => name.toString+formulaToString(y)
        case _ => y match {
          case Abs(x1,y1) => "("+name.toString+formulaToString(x1)+")"+formulaToString(y1)
          case _ => name.toString()+"("+formulaToString(y)+")"
        }
      }
      case _ => formulaToString(x) +"("+ formulaToString(y) +")"
    }
    case Var(name,t) => name.toString()
    case  x : Any    => "(unmatched class: "+x.getClass() + ")"
  }

  // formats a sequent to a readable string
  def sequentToString(s : Sequent) : String = {
    var sb = new scala.StringBuilder()
    var first = true
    for (f <- s.antecedent) {
      if (! first) sb.append(", ")
      else first = false
      sb.append(formulaToString(f))
    }
    sb.append(" \u22a2 ")
    first =true
    for (f <- s.succedent) {
      if (! first) sb.append(", ")
      else first = false
      sb.append(formulaToString(f))
    }
    sb.toString
  }

  def sequentOccurenceToString(s: SequentOccurrence) : String = sequentToString(s.getSequent)
}