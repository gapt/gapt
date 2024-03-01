package gapt.formats.tptp

import gapt.expr._
import gapt.expr.formula.Formula
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.hol.universalClosure
import gapt.proofs.{ Sequent, SequentProof, RichFormulaSequent }

import scala.collection.mutable

class sequentProofToTptp[Proof <: SequentProof[Formula, Proof]] {

  def line( label: String, role: FormulaRole, inf: Proof, annotations: Seq[GeneralTerm] ): TptpInput =
    AnnotatedFormula( "fof", label, role, universalClosure( inf.conclusion.toFormula ), annotations )

  private def convertInference(
    labelMap: collection.Map[Proof, String],
    inf:      Proof ): TptpInput = {
    val label = labelMap( inf )
    inf match {
      case p =>
        val inferenceName = p.longName.flatMap {
          case c if c.isUpper => "_" + c.toLower
          case c              => c.toString
        }.dropWhile( _ == '_' ).stripSuffix( "_rule" )

        val parents = p.immediateSubProofs.map( labelMap )

        line( label, "plain", inf,
          Seq( TptpTerm( "inference", FOLConst( inferenceName ),
            GeneralList(), GeneralList( parents.map( FOLConst( _ ) ) ) ) ) )
    }
  }

  def apply( proof: Proof ): TptpFile = {
    val inputs = Seq.newBuilder[TptpInput]

    val labelMap = mutable.Map[Proof, String]()
    for ( ( p, i ) <- proof.dagLike.postOrder.zipWithIndex ) {
      labelMap( p ) = s"p$i"
      inputs += convertInference( labelMap, p )
    }

    TptpFile( inputs.result() )
  }

}

object sequentProofToTptp {
  def apply[Proof <: SequentProof[Formula, Proof]]( p: Proof ): TptpFile =
    new sequentProofToTptp().apply( p )
}
