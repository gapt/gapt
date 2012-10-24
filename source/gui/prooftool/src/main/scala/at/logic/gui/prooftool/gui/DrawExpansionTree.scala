package at.logic.gui.prooftool.gui

/**
 * Created with IntelliJ IDEA.
 * User: mrukhaia
 * Date: 9/13/12
 * Time: 12:51 PM
 */

import swing._
import event.{UIElementResized, MouseClicked}
import java.awt.{Font, Dimension, Color}
import java.awt.Font._
import java.awt.event.MouseEvent
import at.logic.language.hol._
import at.logic.calculi.expansionTrees.ExpansionTree
import at.logic.utils.ds.trees.{NonTerminalNodeA}
import org.scilab.forge.jlatexmath.{TeXConstants, TeXFormula}
import java.awt.image.BufferedImage

class DrawExpansionTree(val expansionTree: (Seq[ExpansionTree],Seq[ExpansionTree]), private val fSize: Int) extends SplitPane(Orientation.Vertical) {
  background = new Color(255,255,255)
  private val ft = new Font(SANS_SERIF, PLAIN, fSize)
  //private val width = toolkit.getScreenSize.width - 150
  //private val height = toolkit.getScreenSize.height - 150
  preferredSize = calculateOptimalSize
  dividerLocation = preferredSize.width / 2
  leftComponent = new SplitedExpansionTree(expansionTree._1, "Antecedent", ft)
  rightComponent = new SplitedExpansionTree(expansionTree._2, "Consequent", ft)

  def calculateOptimalSize = {
    val width = Main.top.size.width
    val height = Main.top.size.height
    if (width > 100 && height > 200)
      new Dimension(Main.top.size.width - 70, Main.top.size.height - 150)
    else new Dimension(width, height)
  }

  listenTo(Main.top)
  reactions += {
    case UIElementResized(Main.top) =>
      preferredSize = calculateOptimalSize
      revalidate
  }
}

class SplitedExpansionTree(val formulas: Seq[ExpansionTree], val label: String, private val ft: Font) extends BoxPanel(Orientation.Vertical) {
  contents += new Label(label) {
    font = ft.deriveFont(Font.BOLD)
    opaque = true
    border = Swing.EmptyBorder(10)
  }
  contents += new ScrollPane {
    peer.getVerticalScrollBar.setUnitIncrement( 20 )
    peer.getHorizontalScrollBar.setUnitIncrement( 20 )
    contents = new BoxPanel(Orientation.Vertical) {
      background = new Color(255,255,255)
      formulas.foreach( f => {
        val comp = formulaToComponent(f.asInstanceOf[NonTerminalNodeA[Option[HOLFormula],_]].node.get)
        comp.border = Swing.EmptyBorder(10)
        contents += comp
      })
    }
  }

  def formulaToComponent(t: HOLFormula): BoxPanel = new BoxPanel(Orientation.Horizontal) {
    background = new Color(255,255,255)
    yLayoutAlignment = 0.5

    t match {
      case Neg(f) =>
        contents += label("¬",ft)
        contents += formulaToComponent(f)
      case And(f1,f2) =>
        val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
        contents += parenthesis._1
        contents += formulaToComponent(f1)
        contents += label("∧",ft)
        contents += formulaToComponent(f2)
        contents += parenthesis._2
      case Or(f1,f2) =>
        val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
        contents += parenthesis._1
        contents += formulaToComponent(f1)
        contents += label("∨",ft)
        contents += formulaToComponent(f2)
        contents += parenthesis._2
      case Imp(f1,f2) =>
        val parenthesis = connectParenthesis(label("(",ft), label(")",ft))
        contents += parenthesis._1
        contents += formulaToComponent(f1)
        contents += label("⊃",ft)
        contents += formulaToComponent(f2)
        contents += parenthesis._2
      case ExVar(v, f) =>
        val lbl = DrawSequent.latexToLabel("(" + """\exists """ + DrawSequent.formulaToLatexString(v) + ")",ft)
        lbl.reactions += {
          case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 => PopupMenu(lbl, e.point.x, e.point.y)
        }
        contents += lbl
        contents += formulaToComponent(f)
      case AllVar(v, f) =>
        val lbl = DrawSequent.latexToLabel("(" + """\forall """ + DrawSequent.formulaToLatexString(v) + ")",ft)
        lbl.reactions += {
          case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 => PopupMenu(lbl, e.point.x, e.point.y)
        }
        contents += lbl
        contents += formulaToComponent(f)
      case _ =>
        val lbl = DrawSequent.formulaToLabel(t,ft)
        lbl.deafTo(lbl.mouse.moves, lbl.mouse.clicks)
        contents += lbl
    }
  }

  def label(s: String, fnt: Font) = new MyLabel {
    background = Color.white
    yLayoutAlignment = 0.5
    opaque = true
    font = fnt

    val formula = new TeXFormula(s)
    val myicon = formula.createTeXIcon(TeXConstants.STYLE_DISPLAY, fnt.getSize)
    val myimage = new BufferedImage(myicon.getIconWidth(), myicon.getIconHeight(), BufferedImage.TYPE_INT_ARGB)
    val g2 = myimage.createGraphics()
    g2.setColor(Color.white)
    g2.fillRect(0,0,myicon.getIconWidth(),myicon.getIconHeight())
    myicon.paintIcon(peer, g2, 0, 0)

    icon = myicon
    if (s == "(" || s == ")")
      tooltip = "Click to mark/unmark."
      listenTo(mouse.clicks)
      reactions += {
        case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 =>
          val color = RGBColorChooser(this,e.point.x,e.point.y)
          if (color != None) {
            backgroundColor = color.get
            peer.dispatchEvent(new MouseEvent(peer,e.peer.getID,e.peer.getWhen,e.modifiers,e.point.x,e.point.y,e.clicks,e.triggersPopup,MouseEvent.BUTTON1))
          }
      }
  }

  def connectParenthesis(left: MyLabel, right: MyLabel) = {
    left.reactions += {
      case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
        if (left.background == Color.white || left.background != left.backgroundColor) {
          left.background = left.backgroundColor
          right.background = left.backgroundColor
        } else {
          left.background = Color.white
          right.background = Color.white
        }
    }
    right.reactions += {
      case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON1 =>
        if (right.background == Color.white || right.background != right.backgroundColor) {
          left.background = right.backgroundColor
          right.background = right.backgroundColor
        } else {
          left.background = Color.white
          right.background = Color.white
        }
    }
    (left,right)
  }
}