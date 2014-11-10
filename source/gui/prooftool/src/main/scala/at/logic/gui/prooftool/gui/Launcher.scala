package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Oct 30, 2010
 * Time: 5:43:38 PM
 */

import java.awt.Font._
import java.awt.event.{MouseEvent, MouseMotionListener}
import scala.swing._
import event.{MouseWheelMoved, MouseReleased, MouseDragged}
import at.logic.gui.prooftool.parser.{UnLoaded, Loaded, ProofToolPublisher, StructPublisher}
import at.logic.utils.ds.trees.Tree
import at.logic.calculi.proofs.TreeProof
import at.logic.calculi.expansionTrees.ExpansionSequent
import at.logic.language.hol.HOLFormula
import at.logic.calculi.proofs.Proof
import at.logic.transformations.ceres.struct.{structToExpressionTree, Struct}

class Launcher(private val option: Option[(String, AnyRef)], private val fSize: Int) extends GridBagPanel with MouseMotionListener {
  option match {
    case Some((name: String, obj: AnyRef)) =>
      val c = new Constraints
      c.grid = (0,0)
      c.insets.set(15, 15, 15, 15)
      val actualname = setWindowContent(obj,c) match {
        case Some(s) => s
        case None => name
      }

      val nice_name:String = actualname match {
        case s:String if s == "\\psi" || s == "psi" => "ψ"
        case s:String if s == "\\chi" || s == "chi" => "χ"
        case s:String if s == "\\varphi" || s == "varphi" => "φ"
        case s:String if s == "\\phi" || s == "phi" => "ϕ"
        case s:String if s == "\\rho" || s == "rho" => "ρ"
        case s:String if s == "\\sigma" || s == "sigma" => "σ"
        case s:String if s == "\\tau" || s == "tau" => "τ"
        case s:String if s == "\\omega" || s == "omega" => "Ω"
        case _ => actualname
      }
      val bd = Swing.TitledBorder(Swing.LineBorder(new Color(0,0,0), 2), " "+nice_name+" ")
      bd.setTitleFont(new Font(SERIF, BOLD, 16))
      border = bd
    case _ =>
  }

  background = new Color(255,255,255)

  def fontSize = fSize
  def getData = option

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

  def setWindowContent(obj : AnyRef, c : Constraints) : Option[String] = obj match {
    case (s: String, p : AnyRef ) =>
      setWindowContent(p,c)
      Some(s)
    case proof: TreeProof[_] =>
      layout(new DrawProof(proof, fSize, None, "")) = c
      ProofToolPublisher.publish(Loaded)
      StructPublisher.publish(UnLoaded)
      None
    case resProof: Proof[_] =>
      layout(new DrawResolutionProof(resProof, fSize, None, "")) = c
      ProofToolPublisher.publish(UnLoaded)
      StructPublisher.publish(UnLoaded)
      None
    case tree: Tree[_] =>
      layout(new DrawTree(tree, fSize, "")) = c
      ProofToolPublisher.publish(UnLoaded)
      StructPublisher.publish(Loaded)
      None
    case list: List[_] =>
      layout(new DrawList(list, fSize)) = c
      ProofToolPublisher.publish(UnLoaded)
      StructPublisher.publish(UnLoaded)
      None
    case set: Set[_] => // use the case for lists for sets, too
      layout(new DrawList(set.toList, fSize)) = c
      ProofToolPublisher.publish(UnLoaded)
      StructPublisher.publish(UnLoaded)
      None
    case formula: HOLFormula => // use the case for lists for single formulas, too
      layout(new DrawList(formula::Nil, fSize)) = c
      ProofToolPublisher.publish(UnLoaded)
      StructPublisher.publish(UnLoaded)
      None
/*
 * do we need (vertical) display of sequents in prooftool?
 *
    case fSequent: FSequent =>
      layout(new DrawHerbrandSequent[HOLFormula]((fSequent.antecedent,fSequent.succedent), fSize)) = c
      ProofToolPublisher.publish(UnLoaded)
      StructPublisher.publish(UnLoaded)
      None
*/
    case expSequent: ExpansionSequent =>
      layout(new DrawExpansionSequent(expSequent, fSize)) = c
      ProofToolPublisher.publish(UnLoaded)
      StructPublisher.publish(UnLoaded)
      None
    case struct : Struct =>
      setWindowContent(structToExpressionTree.prunedTree(struct),c)

    case _ =>
      layout(new Label("Cannot match the "+option.get._2.getClass.toString + " : " + option.get._2){
        font = new Font(SANS_SERIF, BOLD, 16)
      }) = c
      ProofToolPublisher.publish(UnLoaded)
      StructPublisher.publish(UnLoaded)
      None
  }


  def mouseMoved(e: MouseEvent) {
    //println("mouse: " + e.getX + "/" + e.getY)
  }
  def mouseDragged(e: MouseEvent) {
    //The user is dragging us, so scroll!
    val r = new Rectangle(e.getX, e.getY, 1, 1)
    this.peer.scrollRectToVisible(r)
  }

  // returns the location of the end-sequent
  // of a proof
  def getLocationOfProof[S](proof: TreeProof[S]) = 
  {
    val dp = contents.head.asInstanceOf[DrawProof]
    dp.getLocationOfProof(proof)
  }
}
