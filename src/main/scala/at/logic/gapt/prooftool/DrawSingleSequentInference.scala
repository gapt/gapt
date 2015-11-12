package at.logic.gapt.prooftool

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.proofs.SequentProof
import at.logic.gapt.proofs.lkNew.{ ExistsRightRule, ForallLeftRule }

import scala.swing._
import java.awt.Color

/**
 *
 * Created by marty on 3/26/14.
 */

class DrawSingleSequentInference[F <: HOLFormula, T <: SequentProof[F, T]]( var orientation: Orientation.Value ) extends ScrollPane {

  private var _p: Option[SequentProof[F, T]] = None
  def p(): Option[SequentProof[F, T]] = _p
  def p_=( np: Option[SequentProof[F, T]] ) = {
    this._p = np
    init()
    revalidate()
    repaint()
  }

  val auxiliaries = new BoxPanel( Orientation.Vertical ) {
    border = Swing.TitledBorder( Swing.LineBorder( new Color( 0, 0, 0 ), 1 ), " Auxiliary: " )
    background = new Color( 255, 255, 255 )
    minimumSize = new Dimension( 50, 20 )
    xLayoutAlignment = 0
  }

  val primaries = new BoxPanel( Orientation.Vertical ) {
    border = Swing.TitledBorder( Swing.LineBorder( new Color( 0, 0, 0 ), 1 ), " Primary: " )
    background = new Color( 255, 255, 255 )
    minimumSize = new Dimension( 50, 20 )
    xLayoutAlignment = 0
  }

  val rule = new BoxPanel( Orientation.Vertical ) {
    border = Swing.TitledBorder( Swing.LineBorder( new Color( 0, 0, 0 ), 1 ), " Inference: " )
    background = new Color( 255, 255, 255 )
    minimumSize = new Dimension( 50, 20 )
    xLayoutAlignment = 0
  }

  val substitution = new BoxPanel( Orientation.Vertical ) {
    border = Swing.TitledBorder( Swing.LineBorder( new Color( 0, 0, 0 ), 1 ), " Substitution: " )
    background = new Color( 255, 255, 255 )
    minimumSize = new Dimension( 50, 20 )
    xLayoutAlignment = 0
  }

  def setContents() {
    contents = new BoxPanel( orientation ) {
      contents += rule
      contents += auxiliaries
      contents += primaries
      contents += substitution
    }
  }

  setContents()

  def init() {
    rule.contents.clear()
    if ( p() != None ) rule.contents += LatexLabel( font, p().get.name )
    rule.contents += Swing.Glue

    auxiliaries.contents.clear()
    val aux = for ( proof <- p().toList; ( auxIndices, premise ) <- proof.auxIndices zip proof.premises )
      yield for ( ( f, i ) <- premise.zipWithIndex if auxIndices contains i ) yield f
    for ( x <- aux ) auxiliaries.contents += DrawSequent( x, font, "" )
    auxiliaries.contents += Swing.Glue

    primaries.contents.clear()
    val primary = for ( proof <- p() ) yield for ( ( f, i ) <- proof.conclusion.zipWithIndex if proof.mainIndices contains i ) yield f
    for ( prim <- primary ) primaries.contents += DrawSequent( prim, font, "" )
    primaries.contents += Swing.Glue

    substitution.contents.clear()
    p() match {
      case Some( proof: ForallLeftRule ) =>
        substitution.contents += LatexLabel( font, DrawSequent.formulaToLatexString( proof.term ) )
      case Some( proof: ExistsRightRule ) =>
        substitution.contents += LatexLabel( font, DrawSequent.formulaToLatexString( proof.term ) )
      case _ =>
    }
    substitution.contents += Swing.Glue
  }

  def adjustOrientation( o: Orientation.Value ) {
    val new_orientation = if ( o == Orientation.Vertical || auxiliaries.size.width > bounds.width )
      Orientation.Vertical
    else Orientation.Horizontal
    if ( orientation != new_orientation ) {
      orientation = new_orientation
      setContents()
      revalidate()
      repaint()
    }
  }

}