package gapt.proofs.lk
import gapt.expr._
import gapt.expr.hol.inductionPrinciple
import gapt.proofs.{ Ant, SequentConnector }

object makeInductionExplicit extends LKVisitor[Unit] {

  override def recurse( p: LKProof, otherArg: Unit ): ( LKProof, SequentConnector ) =
    contractAfter( super.recurse )( p, otherArg )

  def apply( p: LKProof ): LKProof = apply( p, () )

  override def visitInduction( proof: InductionRule, otherArg: Unit ): ( LKProof, SequentConnector ) = {
    val indty = proof.indTy
    val constrs = proof.cases.map { _.constructor }

    val hyps = proof.cases.map { indCase =>
      val constr = indCase.constructor
      val FunctionType( `indty`, argtypes ) = constr.ty
      val vars = indCase.eigenVars

      var p: LKProof = ExchangeRightMacroRule( indCase.proof, indCase.conclusion )
      for ( i <- indCase.hypotheses.reverse )
        p = ImpRightRule( p, indCase.proof.conclusion( i ), p.conclusion.indices.last )

      ForallRightBlock( p, All.Block( vars, p.conclusion.elements.last ), vars )
    }

    val indprin = inductionPrinciple( indty, constrs )

    val hypP = hyps.reduceLeft( ( p, hyp ) =>
      AndRightRule( p, p.conclusion.indices.last,
        hyp, hyp.conclusion.indices.last ) )

    val explicitFOLp =
      ProofBuilder.
        c( LogicalAxiom( proof.mainFormula ) ).
        u( ForallLeftRule( _, Ant( 0 ), All( proof.quant, proof.qfFormula ), proof.term ) ).
        u( ImpLeftRule( hypP, hypP.conclusion.indices.last, _, Ant( 0 ) ) ).
        qed
    val explicitHOLp =
      ForallLeftRule( explicitFOLp, indprin, Abs( proof.quant, proof.qfFormula ) )

    val ( proof_, occConn ) = recurse( explicitHOLp, () )
    ( proof_, occConn * SequentConnector.guessInjection( fromLower = proof.conclusion, toUpper = explicitHOLp.conclusion ).inv )
  }
}
