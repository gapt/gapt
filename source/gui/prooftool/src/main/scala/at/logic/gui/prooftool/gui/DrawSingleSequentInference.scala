package at.logic.gui.prooftool.gui

import scala.swing._
import at.logic.calculi.lk.base._
import java.awt.Color
import at.logic.calculi.lk.{ExistsRightRule, ForallLeftRule}

/**
 *
 * Created by marty on 3/26/14.
 */

class DrawSingleSequentInference(var orientation : Orientation.Value) extends ScrollPane {

  private var _p : Option[LKProof] = None
  def p() : Option[LKProof] = _p
  def p_=(np : Option[LKProof]) = {
    this._p = np
    init()
    revalidate()
    repaint()
  }

  val auxiliaries = new BoxPanel(Orientation.Vertical) {
    border = Swing.TitledBorder(Swing.LineBorder(new Color(0,0,0), 1), " Auxiliary: ")
    background = new Color(255,255,255)
    minimumSize = new Dimension(50,20)
    xLayoutAlignment = 0
  }

  val primaries = new BoxPanel(Orientation.Vertical) {
    border = Swing.TitledBorder(Swing.LineBorder(new Color(0,0,0), 1), " Primary: ")
    background = new Color(255,255,255)
    minimumSize = new Dimension(50,20)
    xLayoutAlignment = 0
  }

  val rule =  new BoxPanel(Orientation.Vertical) {
    border = Swing.TitledBorder(Swing.LineBorder(new Color(0,0,0), 1), " Inference: ")
    background = new Color(255,255,255)
    minimumSize = new Dimension(50,20)
    xLayoutAlignment = 0
  }

  val substitution =  new BoxPanel(Orientation.Vertical) {
    border = Swing.TitledBorder(Swing.LineBorder(new Color(0,0,0), 1), " Substitution: ")
    background = new Color(255,255,255)
    minimumSize = new Dimension(50,20)
    xLayoutAlignment = 0
  }

  def setContents() {
    contents = new BoxPanel(orientation) {
      contents += rule
      contents += auxiliaries
      contents += primaries
      contents += substitution
    }
  }

  setContents()

  def init() {
    rule.contents.clear()
    if (p() != None) rule.contents += LatexLabel(font, p().get.name)
    rule.contents += Swing.Glue

    auxiliaries.contents.clear()
    val aux = p() match {
      case Some(a : UnaryLKProof with AuxiliaryFormulas) =>
        val r = a.uProof.root
        List(Sequent(r.antecedent.filter(a.aux(0).contains), r.succedent.filter(a.aux(0).contains)))
      case Some(a : BinaryLKProof with AuxiliaryFormulas) =>
        val r1 = a.uProof1.root
        val r2 = a.uProof2.root
        List(Sequent(r1.antecedent.filter(a.aux(0).contains), r1.succedent.filter(a.aux(0).contains)),
          Sequent(r2.antecedent.filter(a.aux(1).contains), r2.succedent.filter(a.aux(1).contains)))

      case _ =>
        List()
    }
    aux.foreach( x => { auxiliaries.contents += DrawSequent(x, font, "" ) } )
    auxiliaries.contents += Swing.Glue

    primaries.contents.clear()
    val primary = p() match {
      case Some(pf : PrincipalFormulas) =>
        val r = p().get.root
        Some(Sequent(r.antecedent.filter(pf.prin.contains), r.succedent.filter(pf.prin.contains)))
      case Some(p : NullaryLKProof) =>
        Some(p.root)

      case _ => None
    }
    if (primary != None) primaries.contents += DrawSequent(primary.get, font, "" )
    primaries.contents += Swing.Glue

    substitution.contents.clear()
    p() match {
      case Some(ForallLeftRule(_,_,_,_,term)) =>
        substitution.contents += LatexLabel(font, DrawSequent.formulaToLatexString(term))
      case Some(ExistsRightRule(_,_,_,_,term)) =>
        substitution.contents += LatexLabel(font, DrawSequent.formulaToLatexString(term))
      case _ =>
    }
    substitution.contents += Swing.Glue
  }

  def adjustOrientation(o: Orientation.Value) {
    val new_orientation = if (o == Orientation.Vertical || auxiliaries.size.width > bounds.width)
      Orientation.Vertical
    else Orientation.Horizontal
    if (orientation != new_orientation) {
      orientation = new_orientation
      setContents()
      revalidate()
      repaint()
    }
  }

}