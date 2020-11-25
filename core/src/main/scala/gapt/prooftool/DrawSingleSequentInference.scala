package gapt.prooftool

import java.awt.Color

import gapt.formats.latex.LatexExporter
import gapt.proofs.SequentProof
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ForallLeftRule

import scala.swing._

class DrawSingleSequentInference[F, T <: SequentProof[F, T]](
    main:                     ProofToolViewer[_],
    var orientation:          Orientation.Value,
    sequent_element_renderer: F => String ) extends ScrollPane {

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

  def setContents(): Unit = {
    contents = new BoxPanel( orientation ) {
      contents += rule
      contents += auxiliaries
      contents += primaries
      contents += substitution
    }
  }

  setContents()

  def init(): Unit = {
    rule.contents.clear()
    if ( p() != None ) rule.contents += LatexLabel( main, p().get.name )
    rule.contents += Swing.Glue

    auxiliaries.contents.clear()
    val aux = for ( proof <- p().toList; ( auxIndices, premise ) <- proof.auxIndices zip proof.premises )
      yield for ( ( f, i ) <- premise.zipWithIndex if auxIndices contains i ) yield f
    for ( x <- aux ) auxiliaries.contents += DrawSequent( main, x, sequent_element_renderer )
    auxiliaries.contents += Swing.Glue

    primaries.contents.clear()
    val primary = for ( proof <- p() ) yield for {
      ( f, i ) <- proof.conclusion.zipWithIndex
      if proof.mainIndices contains i
    } yield f
    for ( prim <- primary ) primaries.contents += DrawSequent( main, prim, sequent_element_renderer )
    primaries.contents += Swing.Glue

    substitution.contents.clear()
    p() match {
      case Some( proof: ForallLeftRule ) =>
        substitution.contents += LatexLabel( main, LatexExporter( proof.term ) )
      case Some( proof: ExistsRightRule ) =>
        substitution.contents += LatexLabel( main, LatexExporter( proof.term ) )
      case _ =>
    }
    substitution.contents += Swing.Glue
  }

}
