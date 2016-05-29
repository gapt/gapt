package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.expansion.ExpansionProofToLK
import at.logic.gapt.proofs.lk._

import scala.collection.mutable
import scalaz.\/-

object ResolutionToLKProof {

  def apply( proof: ResolutionProof ): LKProof =
    apply( proof, in => in.sequent match {
      case Sequent( Seq(), Seq( f ) ) if freeVariables( f ).isEmpty => LogicalAxiom( f )
      case Sequent( Seq( f ), Seq() ) if freeVariables( f ).isEmpty => LogicalAxiom( f )
      case seq =>
        val fvs = freeVariables( seq ).toSeq
        ( solvePropositional( seq.toDisjunction +: seq ): @unchecked ) match {
          case \/-( proj ) =>
            ForallLeftBlock( proj, All.Block( fvs, seq.toDisjunction ), fvs )
        }
    } )

  def asDerivation( proof: ResolutionProof ): LKProof =
    apply( proof, in => TheoryAxiom( in.sequent.map( _.asInstanceOf[HOLAtom] ) ) )

  def apply( proof: ResolutionProof, input: Input => LKProof ): LKProof = {
    val memo = mutable.Map[ResolutionProof, LKProof]()

    def f( p: ResolutionProof ): LKProof = memo.getOrElseUpdate( p, ContractionMacroRule( p match {
      case in: Input       => input( in )
      case Taut( formula ) => LogicalAxiom( formula )
      case Refl( term )    => ReflexivityAxiom( term )

      case Factor( q, i1, i2 ) =>
        if ( i1 isAnt )
          ContractionLeftRule( f( q ), q.conclusion( i1 ) )
        else
          ContractionRightRule( f( q ), q.conclusion( i1 ) )
      case Resolution( q1, i1, q2, i2 ) =>
        CutRule( f( q1 ), f( q2 ), q1.conclusion( i1 ) )
      case Subst( q, subst ) =>
        subst( f( q ) )
      case p @ Paramod( q1, i1, ltr, q2, i2, ctx: Abs ) =>
        if ( i2 isAnt )
          ParamodulationLeftRule( f( q1 ), q1.conclusion( i1 ), f( q2 ), q2.conclusion( i2 ), ctx )
        else
          ParamodulationRightRule( f( q1 ), q1.conclusion( i1 ), f( q2 ), q2.conclusion( i2 ), ctx )

      // FIXME: add axiom reduction as in LKsk
      case _ =>
        val expansion = ResolutionToExpansionProof.withDefs( p )
        ( ExpansionProofToLK( expansion ): @unchecked ) match {
          case \/-( lk ) => lk
        }
    }, p.conclusion, strict = false ) )

    f( proof )
  }

}
