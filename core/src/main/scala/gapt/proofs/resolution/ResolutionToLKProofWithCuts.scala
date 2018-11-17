package gapt.proofs.resolution
import gapt.expr.{ Abs, All, Formula, Imp, freeVariables }
import gapt.expr.hol.universalClosure
import gapt.proofs.{ HOLClause, HOLSequent, Suc }
import gapt.proofs.lk._

object ResolutionToLKProofWithCuts {

  def mkFormula( p: ResolutionProof ): Formula =
    mkFormula( p.assertions, p.conclusion )
  def mkFormula( assertions: HOLClause, sequent: HOLSequent ): Formula =
    Imp.Block(
      assertions.map( identity, -_ ).elements,
      All.Block( freeVariables( sequent ).toSeq, sequent.toDisjunction ) )

  def oneStep( p: ResolutionProof ): LKProof = {
    val evs = freeVariables( p.conclusion ).toSeq
    def mkForallR( q: LKProof ): LKProof = ForallRightBlock( q, mkFormula( p ), evs )
    p match {
      case Refl( t ) => mkForallR( ReflexivityAxiom( t ) )
      case Taut( a ) => mkForallR( OrRightRule( NegRightRule( LogicalAxiom( a ), a ), -a, a ) )
      case DefIntro( q, _, _, _ ) =>
        DefinitionRightRule( LogicalAxiom( mkFormula( q ) ), Suc( 0 ), mkFormula( p ) )
      case TopL( q, i ) =>
        ???
    }
  }

}
