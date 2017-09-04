package at.logic.gapt.proofs.lk
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Ant, SequentConnector }

object makeInductionExplicit extends LKVisitor[Unit] {
  def inductionPrinciple( indty: Ty, constrs: Seq[Const] ) = {
    val pred = Var( "X", indty -> To )

    val hyps = constrs.map { constr =>
      val FunctionType( `indty`, argtypes ) = constr.ty
      val vars = for ( ( at, i ) <- argtypes.zipWithIndex ) yield Var( s"x$i", at )

      All.Block( vars, vars.filter { _.ty == indty }.foldRight( pred( constr( vars: _* ) ) )( ( v, f ) => pred( v ) --> f ) )
    }

    hof"∀X (${And( hyps )} ⊃ ∀x $pred x)"
  }

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
    ( proof_, occConn * SequentConnector.guessInjection( explicitHOLp.conclusion, proof.conclusion ).inv )
  }
}
