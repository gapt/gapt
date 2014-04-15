package at.logic.gui.prooftool.gui

import scala.swing._
import at.logic.calculi.agraphProofs.{BinaryAGraphProof, UnaryAGraphProof, AGraphProof}
import at.logic.calculi.lk.base._
import java.awt.{Color, Font}
import scala.swing.BorderPanel.Position
import javax.swing.border.TitledBorder
import scala.Some

/**
 * Created by marty on 3/26/14.
 */
class DrawSingleSequentInference(var orientation : Orientation.Value) extends ScrollPane {

  def DrawSingleSequentInference() {
    init()
  }

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
  }

  val primaries = new BoxPanel(Orientation.Vertical) {
    border = Swing.TitledBorder(Swing.LineBorder(new Color(0,0,0), 1), " Primary: ")
    background = new Color(255,255,255)
    preferredSize = new Dimension(50,20)
  }

  contents = new BoxPanel(orientation) {
    contents += auxiliaries
    contents += primaries
  }

  def init() {
    val aux = p match {
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

    val primary = p match {
      case Some(pf : PrincipalFormulas) =>
        val r = p.get.root
        Some(Sequent(r.antecedent.filter(pf.prin.contains), r.succedent.filter(pf.prin.contains)))
      case _ => None
    }

    auxiliaries.contents.clear()
    primaries.contents.clear()

    aux.foreach( x => { auxiliaries.contents += DrawSequent(x, font, "" ) } )
    auxiliaries.contents += Swing.Glue
    if (primary != None) primaries.contents += DrawSequent(primary.get, font, "" )
    primaries.contents += Swing.Glue
  }

  def adjustOrientation(o: Orientation.Value) {
    orientation = if (o == Orientation.Vertical || auxiliaries.size.width > bounds.width)
      Orientation.Vertical
    else Orientation.Horizontal
    contents = new BoxPanel(orientation) {
      contents += auxiliaries
      contents += primaries
    }
    revalidate()
    repaint()
  }

}


/*
class DrawSingleSequentInference(var orientation : Orientation.Value) extends ScrollPane {

  def DrawSingleSequentInference() = {
    init()
  }

  private var _p : Option[LKProof] = None;
  def p() : Option[LKProof] = _p
  def p_=(np : Option[LKProof]) = {
    this._p = np
    init();
  }

  private var box : BoxPanel = null

  private var aux : List[Sequent] = List()

  private var primary : Option[Sequent] = None

  val auxlabel = new Label("Auxiliary: ")
  auxlabel.horizontalAlignment = Alignment.Left
  auxlabel.verticalAlignment = Alignment.Top
  auxlabel.background = Color.GREEN
  auxlabel.horizontalTextPosition = Alignment.Left
  auxlabel.verticalTextPosition = Alignment.Top

  val primlabel = new Label("Primary: ")
  primlabel.horizontalAlignment = Alignment.Left
  primlabel.verticalAlignment = Alignment.Top
  primlabel.background = this.background
  primlabel.horizontalTextPosition = Alignment.Left
  primlabel.verticalTextPosition = Alignment.Top

  this.background = Color.WHITE

  def init() {
    this.box = new BoxPanel(noflip(orientation))
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
    box.background = this.background
    this.ignoreRepaint = true

    noflip(this.orientation) match {
      case Orientation.Horizontal =>
        //println("Horizontal layout")
        if (aux.nonEmpty) {
          val bp = new BoxPanel(noflip(orientation))
          bp.background = this.background
          val sequents = aux.map(x => {
            val ds = DrawSequent(x, this.font, "" )
            val box = new BoxPanel(flip(orientation))
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
          val bp = new BoxPanel(noflip(orientation))
          bp.background = this.background
          val sequent = DrawSequent(primary.get, this.font, "" )
          sequent.background = this.background
          bp.contents += primlabel
          bp.contents += sequent
          box.contents += bp
        }
        box.contents += Swing.HGlue

      case Orientation.Vertical =>
        //println("Vertical layout")
        if (aux.nonEmpty) {
          val bp = new BorderPanel()
          bp.layout(auxlabel) = BorderPanel.Position.West
          bp.background = this.background
          bp.revalidate()
          box.contents +=  bp
        }


        box.contents ++= aux.map(x => {
          val ds = DrawSequent(x, this.font, "" )
          ds.background = this.background
          val bp = new BorderPanel()
          bp.layout(ds) = Position.West
          bp.revalidate()
          bp.background = this.background
          bp
        }
        )

        if (primary.nonEmpty) {
          val bp = new BorderPanel()
          bp.layout(primlabel) = BorderPanel.Position.West
          bp.background = this.background
          bp.revalidate()
          box.contents += bp

          val sequent = DrawSequent(primary.get, this.font, "" )
          sequent.background = this.background

          val bp2 = new BorderPanel()
          bp2.layout(sequent) = Position.West
          bp2.background = this.background
          bp2.revalidate()
          box.contents += bp2
        }

        box.contents += Swing.Glue
        box.revalidate()
    }


    this.ignoreRepaint = false
    this.revalidate()
    this.repaint()
  }

  private def noflip(o : Orientation.Value) =
    if (o == Orientation.Vertical) Orientation.Vertical
    else Orientation.Horizontal
  private def flip(o : Orientation.Value) =
    if (o == Orientation.Vertical) Orientation.Horizontal
    else Orientation.Vertical


}
*/