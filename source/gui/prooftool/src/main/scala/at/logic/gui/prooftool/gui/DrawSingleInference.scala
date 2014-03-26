package at.logic.gui.prooftool.gui

import scala.swing._
import at.logic.calculi.agraphProofs.{BinaryAGraphProof, UnaryAGraphProof, AGraphProof}
import at.logic.calculi.lk.base._
import java.awt.{Color, Font}
import java.awt.Font._
import scala.Some
import scala.Some
import scala.Some

/**
 * Created by marty on 3/26/14.
 */
class DrawSingleSequentInference extends ScrollPane {

  def DrawSingleSequentInference() = {
    init()
  }

  private var _p : Option[LKProof] = None;
  def p() : Option[LKProof] = _p
  def p_=(np : Option[LKProof]) = {
    this._p = np
    init();
  }

  private var orientation = Orientation.Vertical
  private var box : BoxPanel = null

  private var aux : List[Sequent] = List()

  private var primary : Option[Sequent] = None

  val auxlabel = new Label("Auxiliary: ")
  val primlabel = new Label("Primary: ")

  this.background = Color.WHITE

  def init() {
    this.box = new BoxPanel(orientation)
    this.viewportView = box


    aux = p match {
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

    primary = p match {
      case Some(pf : PrincipalFormulas) =>
        val r = p.get.root
        Some(Sequent(r.antecedent.filter(pf.prin.contains), r.succedent.filter(pf.prin.contains)))

      case _ => None
    }

    box.contents.clear()
    this.ignoreRepaint = true

    if (aux.nonEmpty) {
      val bp = new BoxPanel(Orientation.Vertical)
      bp.background = this.background
      val sequents = aux.map(x => {
        val ds = DrawSequent(x, this.font, "" )
        val box = new BoxPanel(Orientation.Horizontal)
        ds.background = this.background
        box.background = this.background
        box.contents += auxlabel
        box.contents += ds
        box
      }
      )
      bp.contents ++= sequents
      box.contents += bp
    }

    if (primary.nonEmpty) {
      val bp = new BoxPanel(Orientation.Horizontal)
      bp.background = this.background
      val sequent = DrawSequent(primary.get, this.font, "" )
      sequent.background = this.background
      bp.contents += primlabel
      bp.contents += sequent
      box.contents += bp
    }

    this.ignoreRepaint = false
    this.revalidate()
    this.repaint()
  }


}
